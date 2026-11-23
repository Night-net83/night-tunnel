#!/usr/bin/env python3
"""night-tunnel: multi-transport, anti-DPI tunnel manager.

Engine : gost v3 (relay over tls/mtls/wss/mwss/grpc/quic/kcp/...)
Carriers: WireGuard / GRE / VXLAN (L3 links the gost relay can also ride on)
Panel  : HTTPS web panel with random path/user/password
Roles  : foreign (exit server) and iran (entry server)
"""
import ast
import base64
import getpass
import concurrent.futures
import hashlib
import hmac
import html
import ipaddress
import json
import os
import random
import re
import secrets
import shlex
import shutil
import socket
import ssl
import string
import subprocess
import sys
import tarfile
import tempfile
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlencode, urlparse

NAME = "night-tunnel"
VERSION = "1.7.0"
BASE = os.environ.get("NT_BASE", "/etc/night-tunnel")
STATE = BASE + "/state.json"
GOST_CFG = BASE + "/gost.json"
CERT = BASE + "/cert.pem"
KEY = BASE + "/key.pem"
OPT = "/opt/night-tunnel"
FW = BASE + "/fw.json"
ERR = "!"

# id -> (gost type, udp based, description, default enabled)
CATALOG = {
    "mtls": ("mtls", False, "TLS + multiplex", True),
    "tls": ("tls", False, "TLS", True),
    "wss": ("wss", False, "WebSocket over TLS", True),
    "mwss": ("mwss", False, "WebSocket+TLS + multiplex", True),
    "grpc": ("grpc", False, "gRPC (HTTP/2)", True),
    "quic": ("quic", True, "QUIC (UDP)", True),
    "kcp": ("kcp", True, "KCP (UDP, low latency / gaming)", True),
    "h2": ("h2", False, "HTTP/2", False),
    "ws": ("ws", False, "WebSocket (plain)", False),
    "mws": ("mws", False, "WebSocket + multiplex", False),
    "otls": ("otls", False, "obfs-tls", False),
    "ohttp": ("ohttp", False, "obfs-http", False),
    "mtcp": ("mtcp", False, "TCP + multiplex", False),
    "tcp": ("tcp", False, "Plain TCP", False),
    "udp": ("udp", True, "Plain UDP relay", False),
}
TLS_DIALERS = {"tls", "mtls", "wss", "mwss", "grpc", "h2"}
WS_TYPES = {"ws", "wss", "mws", "mwss"}
CARRIERS = {
    "wg": ("WireGuard", "10.66.0"),
    "gre": ("GRE", "10.67.0"),
    "vxlan": ("VXLAN", "10.68.0"),
    "ipip": ("IPIP", "10.69.0"),
    "geneve": ("GENEVE", "10.70.0"),
    "fou": ("IPIP over UDP (FOU)", "10.71.0"),
}
DEV = {"wg": "nt-wg", "gre": "nt-gre", "vxlan": "nt-vx", "ipip": "nt-ipip",
       "geneve": "nt-gnv", "fou": "nt-fou"}
# carriers that use a UDP port / that are raw IP protocols (need a protocol firewall rule)
UDP_CARRIERS = {"wg", "vxlan", "geneve", "fou"}
IPPROTO = {"gre": "gre", "ipip": "4"}
# layer map used when the user picks a tunnel to build
LAYERS = [
    ("L7  web camouflage", ["wss", "mwss", "ws", "mws", "grpc", "h2", "ohttp"]),
    ("L5  TLS", ["mtls", "tls", "otls"]),
    ("L4  TCP/UDP", ["mtcp", "tcp", "quic", "kcp", "udp"]),
    ("L3  kernel tunnels", ["wg", "gre", "ipip", "vxlan", "geneve", "fou"]),
]
KCHAIN = "NT-K"
KPOST = "NT-KP"
KLOCK = "NT-LOCK"
# transports whose payload is encrypted end-to-end (TLS / QUIC); WireGuard is the only encrypted carrier
ENCRYPTED = {"tls", "mtls", "wss", "mwss", "grpc", "h2", "quic"}
BOOT = BASE + "/boot.json"           # panel-only config (panel started before any tunnel exists)
TGBASE = BASE + "-tg"                # Telegram proxy lives apart from the tunnel config (survives a tunnel reset)
TG_STATE = TGBASE + "/tg.json"
TG_CFG = TGBASE + "/mtg.toml"

G, Y, R, N = "\033[32m", "\033[33m", "\033[31m", "\033[0m"


# ----------------------------------------------------------------- helpers
def sh(cmd, inp=None):
    return subprocess.run(cmd, shell=True, input=inp, capture_output=True, text=True)


def say(msg, color=N):
    print(f"{color}{msg}{N}")


def need_root():
    if os.geteuid() != 0 and not os.environ.get("NT_BASE"):
        say("Run as root.", R)
        sys.exit(1)


def load():
    with open(STATE) as f:
        return json.load(f)


def save(st):
    os.makedirs(BASE, exist_ok=True)
    tmp = STATE + ".tmp"
    with open(tmp, "w") as f:
        json.dump(st, f, indent=1)
    os.chmod(tmp, 0o600)
    os.replace(tmp, STATE)


def rnd(n=16):
    a = string.ascii_letters + string.digits
    return "".join(secrets.choice(a) for _ in range(n))


def can_bind(p):
    for kind in (socket.SOCK_STREAM, socket.SOCK_DGRAM):
        s = socket.socket(socket.AF_INET, kind)
        try:
            s.bind(("0.0.0.0", p))
        except OSError:
            return False
        finally:
            s.close()
    return True


def free_port(used):
    while True:
        p = random.randint(20000, 60000)
        if p not in used and can_bind(p):
            used.add(p)
            return p


def ask(prompt, default=""):
    v = input(f"{prompt}" + (f" [{default}]" if default else "") + ": ").strip()
    return v or default


def valid_host(h):
    return bool(re.fullmatch(r"[A-Za-z0-9.-]{1,253}", h))


def valid_ip(h):
    try:
        ipaddress.IPv4Address(h)
        return True
    except ValueError:
        return False


def public_ip():
    for u in ("https://api.ipify.org", "https://ifconfig.me", "https://icanhazip.com"):
        r = sh(f"curl -s4 --max-time 6 {u}")
        ip = r.stdout.strip()
        if valid_ip(ip):
            return ip
    return ""


def local_ip(remote):
    m = re.search(r"src (\S+)", sh(f"ip -4 route get {remote}").stdout)
    return m.group(1) if m else ""


def wg_keypair():
    priv = sh("wg genkey").stdout.strip()
    pub = sh("wg pubkey", inp=priv + "\n").stdout.strip()
    return priv, pub


def fw_list():
    try:
        with open(FW) as f:
            return json.load(f)
    except (OSError, ValueError):
        return []


def _fw_apply(key, add):
    pk = next((k for k in IPPROTO if key.startswith(k + ":")), None)
    if pk:
        cmd = f"-p {IPPROTO[pk]} -s {key[len(pk) + 1:]} -j ACCEPT"
        if add and sh(f"iptables -C INPUT {cmd}").returncode != 0:
            sh(f"iptables -I INPUT {cmd}")
        elif not add:
            sh(f"iptables -D INPUT {cmd}")
    elif sh("ufw status").stdout.startswith("Status: active"):
        sh(f"ufw {'allow' if add else 'delete allow'} {key}")


def fw_add(key):
    _fw_apply(key, True)
    lst = fw_list()
    if key not in lst:
        lst.append(key)
    os.makedirs(BASE, exist_ok=True)
    with open(FW, "w") as f:
        json.dump(lst, f)


def fw_del(key):
    _fw_apply(key, False)
    lst = [k for k in fw_list() if k != key]
    if os.path.isdir(BASE):
        with open(FW, "w") as f:
            json.dump(lst, f)


def fw_open(port, proto="tcp"):
    fw_add(f"{int(port)}/{proto}")


def fw_close(port, proto="tcp"):
    fw_del(f"{int(port)}/{proto}")


def fw_gre(src):
    fw_add("gre:" + src)


def fw_carrier(st, name, add=True):
    """Open/close the firewall for one L3 carrier (UDP port or raw IP protocol)."""
    c = (st.get("l3") or {}).get(name, {})
    peer = st["iran_ip"] if st["role"] == "foreign" else st["foreign_ip"]
    if name in UDP_CARRIERS and c.get("port"):
        (fw_open if add else fw_close)(c["port"], "udp")
    if name in IPPROTO:
        (fw_add if add else fw_del)(f"{name}:{peer}")


def fw_clear():
    for k in fw_list():
        _fw_apply(k, False)
    if os.path.exists(FW):
        os.remove(FW)


# ------------------------------------------------------------ certificates
HOOK = "/etc/letsencrypt/renewal-hooks/deploy/night-tunnel.sh"


def make_cert(domain, sni):
    os.makedirs(BASE, exist_ok=True)
    if domain:
        if not shutil.which("certbot"):
            sh("apt-get install -y certbot")
        r = sh(f"certbot certonly --standalone -d {domain} --non-interactive "
               f"--agree-tos --register-unsafely-without-email")
        live = f"/etc/letsencrypt/live/{domain}"
        if os.path.exists(live + "/fullchain.pem"):
            shutil.copy(live + "/fullchain.pem", CERT)
            shutil.copy(live + "/privkey.pem", KEY)
            os.chmod(KEY, 0o600)
            os.makedirs(os.path.dirname(HOOK), exist_ok=True)
            with open(HOOK, "w") as f:
                f.write(f"#!/bin/sh\ncp {live}/fullchain.pem {CERT}\n"
                        f"cp {live}/privkey.pem {KEY}\nchmod 600 {KEY}\n"
                        f"systemctl restart night-tunnel-gost night-tunnel-panel\n")
            os.chmod(HOOK, 0o755)
            say(f"Let's Encrypt certificate issued for {domain} (auto-renew on).", G)
            return True
        say("Let's Encrypt failed (is port 80 free and the domain pointing here?):", R)
        print((r.stderr or r.stdout)[-400:])
        say("Falling back to a self-signed certificate.", Y)
    sh(f'openssl req -x509 -newkey rsa:2048 -nodes -days 3650 -keyout {KEY} '
       f'-out {CERT} -subj "/CN={sni or "localhost"}"')
    os.chmod(KEY, 0o600)
    return False


# --------------------------------------------------------------- L3 carriers
def l3_down():
    try:
        fp = (load().get("l3") or {}).get("fou", {}).get("port")
    except (OSError, ValueError):
        fp = None
    for dev in DEV.values():
        sh(f"ip link del {dev}")
    if fp:
        sh(f"ip fou del port {int(fp)}")
    kernel_fw_clear()


def l3_up():
    st = load()
    l3 = st.get("l3") or {}
    l3_down()
    lock_fw(st)
    if not l3:
        return
    foreign = st["role"] == "foreign"
    remote = st["iran_ip"] if foreign else st["foreign_ip"]
    local = local_ip(remote)
    for name, c in l3.items():
        mine = c["f_ip"] if foreign else c["i_ip"]
        dev = DEV[name]
        cmds = []
        if name == "wg":
            keyf = BASE + "/wg.key"
            with open(keyf, "w") as f:
                f.write((c["f_priv"] if foreign else c["i_priv"]) + "\n")
            os.chmod(keyf, 0o600)
            cmds.append(f"ip link add {dev} type wireguard")
            if foreign:
                cmds.append(f"wg set {dev} private-key {keyf} listen-port {c['port']} "
                            f"peer {c['i_pub']} allowed-ips {c['i_ip']}/32")
            else:
                cmds.append(f"wg set {dev} private-key {keyf} peer {c['f_pub']} "
                            f"allowed-ips {c['f_ip']}/32 endpoint {remote}:{c['port']} "
                            f"persistent-keepalive 15")
            mtu = 1380
        elif name == "gre":
            cmds.append(f"ip tunnel add {dev} mode gre local {local} remote {remote} ttl 255")
            mtu = 1400
        elif name == "ipip":
            cmds.append(f"ip tunnel add {dev} mode ipip local {local} remote {remote} ttl 255")
            mtu = 1400
        elif name == "geneve":
            cmds.append(f"ip link add {dev} type geneve id {c['vni']} remote {remote} dstport {c['port']}")
            mtu = 1380
        elif name == "fou":
            sh("modprobe fou; modprobe ipip")
            cmds.append(f"ip fou add port {c['port']} ipproto 4")
            cmds.append(f"ip link add {dev} type ipip local {local} remote {remote} "
                        f"encap fou encap-sport auto encap-dport {c['port']}")
            mtu = 1380
        else:
            cmds.append(f"ip link add {dev} type vxlan id {c['vni']} local {local} "
                        f"remote {remote} dstport {c['port']}")
            mtu = 1380
        cmds += [f"ip addr add {mine}/30 dev {dev}", f"ip link set {dev} mtu {mtu} up"]
        for cmd in cmds:
            r = sh(cmd)
            if r.returncode != 0:
                print(f"[{name}] {cmd}\n  -> {r.stderr.strip()}")
                break
        if not foreign:  # entry side must also accept the peer's packets
            fw_carrier(st, name, True)
    kernel_fw(st)


def make_l3(carriers, st, used=None):
    used = used if used is not None else {st["panel"]["port"]}
    l3 = {}
    for c in carriers:
        base = CARRIERS[c][1]
        e = {"f_ip": base + ".1", "i_ip": base + ".2"}
        if c == "wg":
            e["port"] = free_port(used)
            e["f_priv"], e["f_pub"] = wg_keypair()
            e["i_priv"], e["i_pub"] = wg_keypair()
        elif c in ("vxlan", "geneve"):
            e["port"] = free_port(used)
            e["vni"] = random.randint(100, 9999)
        elif c == "fou":
            e["port"] = free_port(used)
        l3[c] = e
    return l3


# ------------------------------------------------- kernel-level port forwarding
def _ipt(args):
    return sh(f"iptables -w {args}")


def kernel_fw_clear():
    lock_clear()
    hooks = (("nat", "PREROUTING", KCHAIN), ("nat", "POSTROUTING", KPOST),
             ("filter", "INPUT", KCHAIN), ("filter", "FORWARD", KCHAIN))
    for tbl, hook, ch in hooks:
        for _ in range(5):
            if _ipt(f"-t {tbl} -D {hook} -j {ch}").returncode != 0:
                break
    for tbl, ch in (("nat", KCHAIN), ("nat", KPOST), ("filter", KCHAIN)):
        _ipt(f"-t {tbl} -F {ch}")
        _ipt(f"-t {tbl} -X {ch}")


def kernel_ports(st):
    """Forwarded ports that bypass gost and ride a kernel tunnel (iptables DNAT)."""
    l3 = st.get("l3") or {}
    return [p for p in st.get("ports", []) if p.get("via") in l3]


def kernel_fw(st):
    """(Re)build the iptables rules for kernel-mode forwarding.
    Iran   : DNAT port P -> <foreign inner ip>:target over the carrier + MASQUERADE.
    Foreign: everything arriving on a carrier (except the gost relay ports) is redirected to 127.0.0.1,
             so a kernel-forwarded port P reaches 127.0.0.1:P just like the relay pool does."""
    kernel_fw_clear()
    l3 = st.get("l3") or {}
    if not l3:
        return
    foreign = st["role"] == "foreign"
    nat, post, flt = [], [], []
    if foreign:
        for name, c in l3.items():
            dev, ip = DEV[name], c["f_ip"]
            sh(f"sysctl -qw net.ipv4.conf.{dev}.route_localnet=1 net.ipv4.conf.{dev}.rp_filter=0")
            for t in st["transports"]:
                if t["via"] == name:
                    nat.append(f"-i {dev} -d {ip} -p tcp --dport {t['port']} -j RETURN")
            for proto in ("tcp", "udp"):
                nat.append(f"-i {dev} -d {ip} -p {proto} -j DNAT --to-destination 127.0.0.1")
            flt.append(f"-i {dev} -j ACCEPT")
        hook = "INPUT"
    else:
        kp = kernel_ports(st)
        if not kp:
            return
        sh("sysctl -qw net.ipv4.ip_forward=1")
        devs = set()
        for p in kp:
            tgt = f"{l3[p['via']]['f_ip']}:{p.get('target') or p['port']}"
            for proto in (["tcp", "udp"] if p["proto"] == "both" else [p["proto"]]):
                nat.append(f"-p {proto} --dport {p['port']} -j DNAT --to-destination {tgt}")
            devs.add(DEV[p["via"]])
        for dev in sorted(devs):
            post.append(f"-o {dev} -j MASQUERADE")
            flt += [f"-i {dev} -j ACCEPT", f"-o {dev} -j ACCEPT"]
        hook = "FORWARD"
    for tbl, ch, hk, rules in (("nat", KCHAIN, "PREROUTING", nat), ("nat", KPOST, "POSTROUTING", post),
                               ("filter", KCHAIN, hook, flt)):
        if not rules:
            continue
        _ipt(f"-t {tbl} -N {ch}")
        for r in rules:
            _ipt(f"-t {tbl} -A {ch} {r}")
        _ipt(f"-t {tbl} -I {hk} -j {ch}")


# ------------------------------------------------------------ security mode
def is_secure(st):
    """True = relay login (user/password) is required. False = 'no password' mode: the foreign server
    only accepts relay connections from the Iran server's IP (firewall) instead."""
    return st.get("secure", True)


def auth_of(st):
    return {"username": st["auth"]["u"], "password": st["auth"]["p"]}


def enc_of(t):
    """'yes' if the tunnel payload is encrypted end-to-end, else 'no'."""
    if t["via"] == "direct":
        return "yes" if ttype(t) in ENCRYPTED else "no"
    return "yes" if t["via"] == "wg" else "no"


def lock_clear():
    for _ in range(5):
        if _ipt(f"-D INPUT -j {KLOCK}").returncode != 0:
            break
    _ipt(f"-F {KLOCK}")
    _ipt(f"-X {KLOCK}")


def lock_fw(st):
    """No-password mode on the foreign server: relay ports answer only to the Iran server's IP."""
    lock_clear()
    if st["role"] != "foreign" or is_secure(st):
        return
    rules = []
    for t in st["transports"]:
        if t["enabled"] and t["via"] == "direct":
            proto = "udp" if CATALOG[ttype(t)][1] else "tcp"
            rules += [f"-p {proto} --dport {t['port']} -s {st['iran_ip']} -j ACCEPT",
                      f"-p {proto} --dport {t['port']} -j DROP"]
    if not rules:
        return
    _ipt(f"-N {KLOCK}")
    for r in rules:
        _ipt(f"-A {KLOCK} {r}")
    _ipt(f"-I INPUT -j {KLOCK}")


def op_security(st, secure):
    if st["role"] != "foreign":
        return ERR + "Change the security mode on the foreign server, then Sync token on the Iran server."
    if bool(secure) == is_secure(st):
        return "Security mode unchanged."
    st["secure"] = bool(secure)
    if secure:
        st["auth"] = {"u": "u" + rnd(6), "p": rnd(20)}  # fresh credentials when the password comes back
    detached_panel_restart()  # the tester's port is derived from the credentials
    if secure:
        return ("Password mode ON: relay login required, new credentials generated. "
                "Copy the new token to the Iran server (Sync token).")
    return ("NO-PASSWORD mode ON: no login, but relay ports accept only the Iran server's IP "
            f"({st['iran_ip']}) and plain transports are NOT encrypted. Copy the new token to the Iran server.")


# ------------------------------------------------------------ gost config
def ttype(t):
    """Catalog type of a transport entry (an entry may be a named instance of a type)."""
    return t.get("type") or t["id"]


def tp_meta(t):
    md = {}
    if ttype(t) in WS_TYPES:
        if t.get("path"):
            md["path"] = t["path"]
        if t.get("host"):
            md["host"] = t["host"]
    return md


def dial_node(st, t):
    """gost chain node (Iran side) for one transport entry; also used by the tunnel tester."""
    if t["via"] == "direct":
        addr, dtype = f"{st['foreign_ip']}:{t['port']}", CATALOG[ttype(t)][0]
    else:
        addr, dtype = f"{st['l3'][t['via']]['f_ip']}:{t['port']}", "tcp"
    dialer = {"type": dtype}
    if dtype in TLS_DIALERS:
        dialer["tls"] = {"serverName": t.get("sni") or st.get("sni") or "localhost"}
    md = tp_meta(t) if t["via"] == "direct" else {}
    if md:
        dialer["metadata"] = md
    conn = {"type": "relay"}
    if is_secure(st):
        conn["auth"] = auth_of(st)
    return {"name": "n-" + t["id"], "addr": addr, "connector": conn, "dialer": dialer}


def gen_gost(st):
    on = [t for t in st["transports"] if t["enabled"]]
    if st["role"] == "foreign":
        svcs = []
        for t in on:
            if t["via"] == "direct":
                addr, ltype = f":{t['port']}", CATALOG[ttype(t)][0]
            else:
                addr, ltype = f"{st['l3'][t['via']]['f_ip']}:{t['port']}", "tcp"
            lis = {"type": ltype}
            md = {k: v for k, v in tp_meta(t).items() if k == "path"}
            if md and t["via"] == "direct":
                lis["metadata"] = md
            handler = {"type": "relay"}
            if is_secure(st):
                handler["auth"] = auth_of(st)
            svcs.append({"name": "in-" + t["id"], "addr": addr, "handler": handler, "listener": lis})
        return {"log": {"level": "warn"}, "tls": {"certFile": CERT, "keyFile": KEY},
                "services": svcs}
    nodes = [dial_node(st, t) for t in on]
    chain = {"name": "pool", "hops": [{
        "name": "hop",
        "selector": {"strategy": st.get("strategy", "fifo"), "maxFails": 1, "failTimeout": "30s"},
        "nodes": nodes}]}
    svcs = []
    for p in st.get("ports", []):
        if p.get("via") in (st.get("l3") or {}):
            continue  # kernel-forwarded port: handled by iptables, not gost
        protos = ["tcp", "udp"] if p["proto"] == "both" else [p["proto"]]
        for proto in protos:
            svcs.append({"name": f"fwd-{proto}-{p['port']}", "addr": f":{p['port']}",
                         "handler": {"type": proto, "chain": "pool"},
                         "listener": {"type": proto},
                         "forwarder": {"nodes": [{"name": "t",
                                                  "addr": f"127.0.0.1:{p.get('target') or p['port']}"}]}})
    return {"log": {"level": "warn"}, "services": svcs, "chains": [chain]}



# ------------------------------------------------- isolated gost processes (tests + self-heal)
def _gostbin():
    return shutil.which("gost") or "/usr/local/bin/gost"


def _svc_port(svc):
    return int(svc["addr"].rsplit(":", 1)[1])


def _last_line(path):
    try:
        with open(path, errors="replace") as f:
            ls = [x.strip() for x in f if x.strip()]
        return ls[-1][-160:] if ls else ""
    except OSError:
        return ""


def _spawn_cfg(cfg, tag):
    os.makedirs(BASE, exist_ok=True)
    path, lg = f"{BASE}/{tag}.json", f"{BASE}/{tag}.log"
    with open(path, "w") as f:
        json.dump(cfg, f)
    os.chmod(path, 0o600)
    fh = open(lg, "wb")
    try:
        return subprocess.Popen([_gostbin(), "-C", path], stdout=fh, stderr=fh), path, lg
    finally:
        fh.close()


def _wait_bound(procs_ports, wait):
    end = time.time() + wait
    while time.time() < end:
        if all(p.poll() is not None or all(not can_bind(x) for x in ports) for p, ports in procs_ports):
            break
        time.sleep(0.05)


def spawn_gost(services, chains=None, tls=None, tag="nt-tmp", wait=2.5):
    """Start gost for a set of services. ONE bad service (type this gost build lacks) normally kills the whole
    process, so if the combined start fails every missing service is retried alone: returns (procs, bad, files)
    with bad = {service name: reason}."""
    def cfg_for(svcs):
        c = {"log": {"level": "error"}, "services": svcs}
        used = {s["handler"].get("chain") for s in svcs} - {None}
        ch = [x for x in (chains or []) if x["name"] in used]
        if ch:
            c["chains"] = ch
        if tls:
            c["tls"] = tls
        return c
    procs, files, bad = [], [], {}
    p, path, lg = _spawn_cfg(cfg_for(services), tag)
    procs.append(p)
    files += [path, lg]
    _wait_bound([(p, [_svc_port(x) for x in services])], wait)
    missing = [x for x in services if can_bind(_svc_port(x))]
    if not missing:
        return procs, bad, files
    if p.poll() is None and len(missing) == len(services):
        p.terminate()
    solo = []
    for i, svc in enumerate(missing):
        q, qp, ql = _spawn_cfg(cfg_for([svc]), f"{tag}-{i}")
        procs.append(q)
        files += [qp, ql]
        solo.append((svc, q, ql))
    _wait_bound([(q, [_svc_port(svc)]) for svc, q, _ in solo], 1.5)
    for svc, q, ql in solo:
        if q.poll() is not None or can_bind(_svc_port(svc)):
            bad[svc["name"]] = _last_line(ql) or "this gost build cannot start it"
    return procs, bad, files


def stop_gost(procs, files=()):
    for p in procs:
        if p.poll() is None:
            p.terminate()
    for p in procs:
        try:
            p.wait(3)
        except subprocess.TimeoutExpired:
            p.kill()
    for f in files:
        try:
            os.remove(f)
        except OSError:
            pass


def gost_selfheal(st):
    """If gost died because ONE transport is unsupported/broken, find it, switch only it off and restart.
    Without this a single bad type makes every tunnel look down."""
    if not shutil.which("systemctl"):
        return []
    time.sleep(1.5)
    if sh("systemctl is-active night-tunnel-gost").stdout.strip() == "active":
        return []
    sh("systemctl stop night-tunnel-gost")
    on = [t for t in st["transports"] if t["enabled"]]
    used = {st["panel"]["port"]}
    bad = []

    def trial(t):
        if st["role"] == "foreign":
            cfg = gen_gost(st)
            svc = next((x for x in cfg["services"] if x["name"] == "in-" + t["id"]), None)
            if not svc:
                return None
            tls, chains = cfg.get("tls"), []
        else:
            port = free_port(used)
            node = dial_node(st, t)
            chains = [{"name": "c", "hops": [{"name": "h", "nodes": [node]}]}]
            svc = {"name": "s", "addr": f"127.0.0.1:{port}", "handler": {"type": "tcp", "chain": "c"},
                   "listener": {"type": "tcp"}, "forwarder": {"nodes": [{"name": "t", "addr": "127.0.0.1:9"}]}}
            tls = None
        pr, b, fl = spawn_gost([svc], chains, tls, tag="nt-heal-" + t["id"], wait=1.5)
        stop_gost(pr, fl)
        return b.get(svc["name"])
    for t in on:
        why = trial(t)
        if why:
            t["enabled"], t["broken"] = False, why
            bad.append(t["id"])
    if bad and any(t["enabled"] for t in st["transports"]):
        save(st)
        cfg = gen_gost(st)
        with open(GOST_CFG, "w") as f:
            json.dump(cfg, f, indent=1)
        sh("systemctl restart night-tunnel-gost")
    elif not bad:
        sh("systemctl restart night-tunnel-gost")
    return bad


# ------------------------------------------------- temporary test listeners (destination side)
TEST = {"procs": [], "files": [], "fw": [], "lock": threading.Lock()}
TEST_FW = BASE + "/testfw.json"


def test_end():
    with TEST["lock"]:
        stop_gost(TEST["procs"], TEST["files"])
        keys = list(TEST["fw"])
        try:
            with open(TEST_FW) as f:
                keys += json.load(f)
        except (OSError, ValueError):
            pass
        for k in set(keys):
            _fw_apply(k, False)
        if os.path.exists(TEST_FW):
            os.remove(TEST_FW)
        TEST.update(procs=[], files=[], fw=[])


def test_listen(st, ttl=150):
    """Destination side: open a throw-away listener for EVERY transport type (own random ports and password),
    independent of what is enabled in the real config. Closed again by test_end() / after ttl seconds."""
    test_end()
    creds = {"u": "t" + rnd(6), "p": rnd(20)}
    used = ports_taken(st) | {bench_port(st)}
    ports = {k: free_port(used) for k in CATALOG}
    svcs = [{"name": "in-" + k, "addr": f":{ports[k]}",
             "handler": {"type": "relay", "auth": {"username": creds["u"], "password": creds["p"]}},
             "listener": {"type": CATALOG[k][0]}} for k in CATALOG]
    keys = [f"{ports[k]}/{'udp' if CATALOG[k][1] else 'tcp'}" for k in CATALOG]
    os.makedirs(BASE, exist_ok=True)
    with open(TEST_FW, "w") as f:
        json.dump(keys, f)
    for k in keys:
        _fw_apply(k, True)
    with TEST["lock"]:
        procs, bad, files = spawn_gost(svcs, None, {"certFile": CERT, "keyFile": KEY}, tag="nt-testlisten")
        TEST.update(procs=procs, files=files, fw=keys)
    tm = threading.Timer(ttl, test_end)
    tm.daemon = True
    tm.start()
    return {"ok": True, "ports": ports, "user": creds["u"], "pw": creds["p"],
            "bad": {k[3:]: v for k, v in bad.items()}}


def apply(st=None):
    st = st or load()
    kernel_fw(st)
    lock_fw(st)
    cfg = gen_gost(st)
    if not cfg["services"] or (st["role"] == "iran" and not cfg["chains"][0]["hops"][0]["nodes"]):
        sh("systemctl stop night-tunnel-gost")
        return bool(kernel_ports(st))  # kernel-only forwarding needs no gost
    with open(GOST_CFG, "w") as f:
        json.dump(cfg, f, indent=1)
    os.chmod(GOST_CFG, 0o600)
    sh("systemctl restart night-tunnel-gost")
    if gost_selfheal(st):
        return True
    return True


# ---------------------------------------------------------------- presets
def preset(st, name):
    ids = [t["id"] for t in st["transports"]]
    carriers = [i for i in ids if i in CARRIERS]
    plan = {
        "stealth": (["wss", "mwss", "tls", "mtls", "grpc"], "rand", False),
        "balanced": (["mtls", "tls", "wss", "grpc", "quic", "kcp"], "fifo", True),
        "game": (["quic", "kcp", "udp"], "fifo", True),
        "rotate": (["mtls", "tls", "wss", "mwss", "grpc", "quic", "kcp"], "rand", True),
    }[name]
    first = [i for i in plan[0] if i in ids]
    back = carriers if plan[2] else []
    order = first + back
    rest = [i for i in ids if i not in order]
    byid = {t["id"]: t for t in st["transports"]}
    st["transports"] = [byid[i] for i in order + rest]
    for t in st["transports"]:
        t["enabled"] = t["id"] in order
    st["strategy"] = plan[1]


# ------------------------------------------------------------------ tokens
def make_token(st):
    d = {"v": 1, "foreign_ip": st["foreign_ip"], "iran_ip": st["iran_ip"],
         "auth": st["auth"], "sni": st.get("sni", ""), "secure": is_secure(st),
         "transports": [t for t in st["transports"] if t["enabled"]], "l3": {}}
    for k, c in st.get("l3", {}).items():
        e = {x: c[x] for x in ("f_ip", "i_ip", "port", "vni", "f_pub", "i_priv") if x in c}
        d["l3"][k] = e
    raw = json.dumps(d, separators=(",", ":")).encode()
    return "NT1:" + base64.urlsafe_b64encode(raw).decode()


def parse_token(tok):
    tok = tok.strip()
    if not tok.startswith("NT1:"):
        raise ValueError("bad token")
    return json.loads(base64.urlsafe_b64decode(tok[4:].encode()))


# ------------------------------------------------------------- panel auth
def hash_pw(pw, salt):
    return hashlib.scrypt(pw.encode(), salt=bytes.fromhex(salt), n=2 ** 14, r=8, p=1).hex()


def new_panel(domain, host):
    used = set()
    pw = rnd(16)
    salt = secrets.token_hex(16)
    p = {"port": free_port(used), "path": rnd(14), "user": "nt" + rnd(5).lower(),
         "salt": salt, "pass_hash": hash_pw(pw, salt), "host": domain or host}
    return p, pw


def panel_url(st):
    p = st["panel"]
    return f"https://{p['host']}:{p['port']}/{p['path']}/"


# ------------------------------------------------------------------ probes
def probe(st, t):
    if not t.get("enabled", True):
        return "off"
    udp = CATALOG.get(ttype(t), ("", False))[1] if t["via"] == "direct" else False
    if udp:
        return "udp"
    if st["role"] == "foreign":
        host = "127.0.0.1" if t["via"] == "direct" else st["l3"][t["via"]]["f_ip"]
    else:
        host = st["foreign_ip"] if t["via"] == "direct" else st["l3"][t["via"]]["f_ip"]
    try:
        with socket.create_connection((host, t["port"]), timeout=2):
            return "up"
    except OSError:
        return "down"


def probe_all(st):
    with concurrent.futures.ThreadPoolExecutor(max_workers=16) as ex:
        res = list(ex.map(lambda t: probe(st, t), st["transports"]))
    return {t["id"]: r for t, r in zip(st["transports"], res)}


def desc(t):
    extra = "".join(f" [{k}={t[k]}]" for k in ("sni", "path", "host") if t.get(k))
    lock = " [enc]" if enc_of(t) == "yes" else " [plain]"
    if t["via"] == "direct":
        return CATALOG[ttype(t)][2] + extra + lock
    return f"Relay over {CARRIERS[t['via']][0]} link" + lock


# --------------------------------------------------------------- operations
# Shared by the CLI menu and the web panel. Return a message; ERR prefix = error.
def ports_taken(st):
    taken = {st["panel"]["port"]} | {t["port"] for t in st["transports"]}
    taken |= {c["port"] for c in st.get("l3", {}).values() if c.get("port")}
    return taken


def find_tp(st, tid):
    return next((t for t in st["transports"] if t["id"] == tid), None)


def only_foreign(st):
    if st["role"] != "foreign":
        return ERR + "Do this on the foreign server, then use Sync token here."
    return None


def op_set_ids(st, ids):
    byid = {t["id"]: t for t in st["transports"]}
    ids = [i for i in ids if i in byid]
    if not ids:
        return ERR + "No valid transport ids."
    rest = [i for i in byid if i not in ids]
    st["transports"] = [byid[i] for i in ids + rest]
    for t in st["transports"]:
        t["enabled"] = t["id"] in ids
    return "Active (in priority order): " + ", ".join(ids)


def op_tp_port(st, tid, port):
    e = only_foreign(st)
    if e:
        return e
    t = find_tp(st, tid)
    if not t:
        return ERR + "Unknown transport."
    try:
        port = int(port)
        assert 1 <= port <= 65535 and port != 22
    except (ValueError, AssertionError):
        return ERR + "Invalid port."
    if port == t["port"]:
        return "Port unchanged."
    if port in ports_taken(st):
        return ERR + "Port already used by the tunnel."
    if t["via"] == "direct" and not can_bind(port):
        return ERR + "Port is in use by another program."
    old, t["port"] = t["port"], port
    if t["via"] == "direct":
        proto = "udp" if CATALOG[ttype(t)][1] else "tcp"
        fw_close(old, proto)
        fw_open(port, proto)
    return f"{tid}: port {old} -> {port}. Copy the new token to the Iran server (Sync token)."


def _l3_fw_remove(st, name):
    fw_carrier(st, name, False)


def op_tp_edit(st, tid, port="", sni=None, path=None, host=None, new_type=""):
    """Edit one transport: port, TLS SNI, WebSocket path/host, or switch its transport type
    (e.g. mtls -> wss) while keeping its name. Empty string clears sni/path/host."""
    e = only_foreign(st) if (port or new_type or path is not None or host is not None) else None
    if e:
        return e
    t = find_tp(st, tid)
    if not t:
        return ERR + "Unknown transport."
    out = []
    if new_type and new_type != ttype(t):
        if t["via"] != "direct":
            return ERR + "Kernel-carrier relays have no type to switch (delete / add the carrier instead)."
        if new_type not in CATALOG or new_type in CARRIERS:
            return ERR + "Unknown transport type."
        oldp = "udp" if CATALOG[ttype(t)][1] else "tcp"
        newp = "udp" if CATALOG[new_type][1] else "tcp"
        if oldp != newp:
            fw_close(t["port"], oldp)
            fw_open(t["port"], newp)
        t["type"] = new_type
        if new_type not in WS_TYPES:
            t.pop("path", None)
            t.pop("host", None)
        out.append(f"type -> {new_type}")
    if port and str(port) != str(t["port"]):
        m = op_tp_port(st, tid, port)
        if m.startswith(ERR):
            return m
        out.append(f"port -> {t['port']}")
    for key, val in (("sni", sni), ("path", path), ("host", host)):
        if val is None:
            continue
        val = val.strip()
        if key == "path" and val and not val.startswith("/"):
            val = "/" + val
        if val and not re.fullmatch(r"[A-Za-z0-9._/~-]{1,120}", val):
            return ERR + f"Invalid {key}."
        if key in ("path", "host") and ttype(t) not in WS_TYPES:
            continue
        if val:
            t[key] = val
        else:
            t.pop(key, None)
        out.append(f"{key} -> {val or 'default'}")
    if not out:
        return "Nothing changed."
    return f"{tid}: " + ", ".join(out) + ". Copy the new token to the Iran server (Sync token)."


def op_tp_del(st, tid):
    e = only_foreign(st)
    if e:
        return e
    t = find_tp(st, tid)
    if not t:
        return ERR + "Unknown transport."
    if len(st["transports"]) <= 1:
        return ERR + "At least one transport must remain."
    st["transports"].remove(t)
    if t["via"] == "direct":
        fw_close(t["port"], "udp" if CATALOG[ttype(t)][1] else "tcp")
    else:
        _l3_fw_remove(st, t["via"])
        st["l3"].pop(t["via"], None)
        save(st)
        sh("systemctl restart night-tunnel-l3")
    if not any(x["enabled"] for x in st["transports"]):
        st["transports"][0]["enabled"] = True
    return f"Transport {tid} deleted. Copy the new token to the Iran server (Sync token)."


def op_tp_add(st, tid, name="", port="", sni="", path="", host=""):
    """Add a transport of catalog type `tid`. `name` lets you build several instances of the
    same type (e.g. wss + wss-cdn on different ports / SNI)."""
    e = only_foreign(st)
    if e:
        return e
    if tid in CARRIERS:
        return op_carrier_add(st, tid)
    name = (name or tid).strip()
    if tid not in CATALOG or not re.fullmatch(r"[a-z0-9][a-z0-9_-]{0,23}", name):
        return ERR + "Transport type unknown or invalid name."
    if find_tp(st, name) or name in CARRIERS:
        return ERR + "A tunnel with this name already exists (pick another name)."
    if port:
        try:
            port = int(port)
            assert 1 <= port <= 65535 and port != 22
        except (ValueError, AssertionError):
            return ERR + "Invalid port."
        if port in ports_taken(st) or not can_bind(port):
            return ERR + "Port already in use."
    else:
        port = free_port(ports_taken(st))
    t = {"id": name, "port": port, "enabled": True, "via": "direct"}
    if name != tid:
        t["type"] = tid
    st["transports"].append(t)
    fw_open(port, "udp" if CATALOG[tid][1] else "tcp")
    if sni or path or host:
        m = op_tp_edit(st, name, sni=sni or None, path=path or None, host=host or None)
        if m.startswith(ERR):
            return m
    return f"Tunnel {name} ({tid}) added on port {port}. Copy the new token to the Iran server."


def op_carrier_add(st, c):
    e = only_foreign(st)
    if e:
        return e
    if c not in CARRIERS or c in st.get("l3", {}) or find_tp(st, c):
        return ERR + "Carrier unknown or already present."
    used = ports_taken(st)
    st.setdefault("l3", {})[c] = make_l3([c], st, used)[c]
    st["transports"].append({"id": c, "port": free_port(used), "enabled": True, "via": c})
    fw_carrier(st, c, True)
    save(st)
    sh("systemctl restart night-tunnel-l3")
    return f"Carrier {CARRIERS[c][0]} added. Copy the new token to the Iran server."


def port_check(st, port, exclude=None):
    try:
        port = int(port)
        assert 1 <= port <= 65535 and port not in (22, st["panel"]["port"])
    except (ValueError, AssertionError):
        return None, ERR + "Invalid port."
    if port != exclude and any(p["port"] == port for p in st["ports"]):
        return None, ERR + "Port already forwarded."
    return port, None


def _target(v):
    v = str(v or "").strip()
    return int(v) if v.isdigit() and 1 <= int(v) <= 65535 else None


def _fw_ports(p, add):
    for pr in (["tcp", "udp"] if p["proto"] == "both" else [p["proto"]]):
        (fw_open if add else fw_close)(p["port"], pr)


def _via(st, via):
    """'' / 'pool' = gost transport pool; a carrier name = kernel forwarding over that carrier."""
    via = (via or "").strip()
    if via in ("", "pool"):
        return "", None
    if via not in (st.get("l3") or {}):
        return None, ERR + "Kernel path unknown (carriers available: " + (", ".join(st.get("l3") or {}) or "none") + ")."
    return via, None


def op_port_add(st, port, proto="tcp", target="", via=""):
    if st["role"] != "iran":
        return ERR + "Ports are forwarded on the Iran server."
    port, err = port_check(st, port)
    if err:
        return err
    if proto not in ("tcp", "udp", "both"):
        return ERR + "Invalid protocol."
    via, err = _via(st, via)
    if err:
        return err
    p = {"port": port, "proto": proto}
    if _target(target):
        p["target"] = _target(target)
    if via:
        p["via"] = via
    st["ports"].append(p)
    _fw_ports(p, True)
    return f"Port {port}/{proto} added" + (f" (kernel path: {via})." if via else " (relay pool).")


def op_port_edit(st, old, port, proto, target, via=None):
    if st["role"] != "iran":
        return ERR + "Ports are forwarded on the Iran server."
    p = next((x for x in st["ports"] if str(x["port"]) == str(old)), None)
    if not p:
        return ERR + "Unknown port."
    new, err = port_check(st, port, exclude=p["port"])
    if err:
        return err
    if proto not in ("tcp", "udp", "both"):
        return ERR + "Invalid protocol."
    nvia = p.get("via", "")
    if via is not None:
        nvia, err = _via(st, via)
        if err:
            return err
    _fw_ports(p, False)
    p["port"], p["proto"] = new, proto
    p.pop("target", None)
    p.pop("via", None)
    if _target(target):
        p["target"] = _target(target)
    if nvia:
        p["via"] = nvia
    _fw_ports(p, True)
    return (f"Port updated: {new}/{proto}" + (f" -> remote {p['target']}" if p.get("target") else "")
            + (f" (kernel path: {nvia})" if nvia else " (relay pool)"))


def op_port_del(st, port):
    if st["role"] != "iran":
        return ERR + "Ports are forwarded on the Iran server."
    p = next((x for x in st["ports"] if str(x["port"]) == str(port)), None)
    if not p:
        return ERR + "Unknown port."
    st["ports"].remove(p)
    _fw_ports(p, False)
    return f"Port {port} removed."


def op_import_token(st, tok):
    if st["role"] != "iran":
        return ERR + "Token import is for the Iran server."
    try:
        d = parse_token(tok)
        assert d["transports"]
    except Exception:
        return ERR + "Invalid token."
    old = {t["id"]: t for t in st["transports"]}
    order = [t["id"] for t in st["transports"]]
    new = [dict(t) for t in d["transports"]]
    new.sort(key=lambda t: order.index(t["id"]) if t["id"] in order else 999)
    for t in new:
        t["enabled"] = old[t["id"]]["enabled"] if t["id"] in old else True
    if not any(t["enabled"] for t in new):
        new[0]["enabled"] = True
    st.update({"foreign_ip": d["foreign_ip"], "iran_ip": d["iran_ip"], "auth": d["auth"],
               "sni": d.get("sni", ""), "secure": d.get("secure", True),
               "transports": new, "l3": d.get("l3", {})})
    dropped = [p["port"] for p in st.get("ports", []) if p.get("via") and p["via"] not in st["l3"]]
    for p in st.get("ports", []):
        if p.get("via") and p["via"] not in st["l3"]:
            p.pop("via")  # its kernel carrier was deleted on the foreign server: fall back to the pool
    save(st)
    sh("systemctl restart night-tunnel-l3")
    msg = f"Token synced: {len(new)} transports from the foreign server."
    if dropped:
        msg += f" Ports {dropped} lost their kernel carrier and now use the relay pool."
    return msg


def op_update_tunnel(st, foreign_ip="", iran_ip="", sni="", rotate=False):
    """Update tunnel settings in place: server IPs (e.g. after getting a new IP), the decoy SNI, and
    (foreign only) rotate the relay credentials + WireGuard keys. Ports/transports are kept."""
    out = []
    if foreign_ip and not valid_ip(foreign_ip) or iran_ip and not valid_ip(iran_ip):
        return ERR + "Invalid IP."
    if sni and not valid_host(sni):
        return ERR + "Invalid SNI."
    if rotate and st["role"] != "foreign":
        return ERR + "Rotating keys is done on the foreign server, then use Sync token here."
    ip_proto = [c for c in (st.get("l3") or {}) if c in IPPROTO]
    for c in ip_proto:
        fw_carrier(st, c, False)  # protocol rules are tied to the old peer IP
    if foreign_ip and foreign_ip != st["foreign_ip"]:
        out.append(f"foreign IP {st['foreign_ip']} -> {foreign_ip}")
        st["foreign_ip"] = foreign_ip
    if iran_ip and iran_ip != st["iran_ip"]:
        out.append(f"Iran IP {st['iran_ip']} -> {iran_ip}")
        st["iran_ip"] = iran_ip
    for c in ip_proto:
        fw_carrier(st, c, True)
    if sni and sni != st.get("sni"):
        st["sni"] = sni
        out.append(f"SNI -> {sni}")
        if st["role"] == "foreign" and not st.get("le"):
            make_cert("", sni)  # self-signed certificate follows the SNI
            detached_panel_restart()
    if rotate:
        st["auth"] = {"u": "u" + rnd(6), "p": rnd(20)}
        for c in (st.get("l3") or {}).values():
            if "f_priv" in c:
                c["f_priv"], c["f_pub"] = wg_keypair()
                c["i_priv"], c["i_pub"] = wg_keypair()
        out.append("credentials and WireGuard keys rotated")
    if not out:
        return "Nothing changed."
    save(st)
    sh("systemctl restart night-tunnel-l3")
    tail = (" Copy the new token to the Iran server (Sync token)." if st["role"] == "foreign"
            else " Make the same change on the foreign server (Update tunnel), then Sync token.")
    return "Tunnel updated: " + "; ".join(out) + "." + tail


def detached_panel_restart():
    sh("systemd-run --no-block --collect sh -c 'sleep 2; systemctl restart night-tunnel-panel'")


# ------------------------------------------------------------ tunnel tester
# Foreign server : a tiny authenticated bench server (inside the panel process) on 127.0.0.1:<bench_port>.
# Iran server    : for every transport a throw-away gost client is pointed at that bench server through
#                  the real transport; kernel carriers are tested with ping + a TCP bench over the link.
BENCH = BASE + "/bench.json"
BENCH_STATE = {"running": False, "log": [], "live": [], "done": 0, "total": 0}
STEALTH = {"wss", "mwss", "tls", "mtls", "grpc", "h2", "ws", "mws", "otls", "ohttp"}


def bench_port(st):
    h = hashlib.sha256(("nt-bench" + st["auth"]["p"]).encode()).digest()
    return 20000 + int.from_bytes(h[:2], "big") % 40000


def _mac(key, mode, n, ts):
    return hmac.new(key.encode(), f"{mode}:{n}:{ts}".encode(), hashlib.sha256).hexdigest()[:32]


def bench_conn(c):
    try:
        key = load()["auth"]["p"]
        c.settimeout(30)
        f = c.makefile("rb")
        parts = f.readline(200).decode(errors="ignore").split()
        if len(parts) != 5 or parts[0] != "NTB":
            return
        mode, n, ts, mac = parts[1], int(parts[2]), int(parts[3]), parts[4]
        if abs(time.time() - ts) > 3600 or not hmac.compare_digest(mac, _mac(key, mode, n, ts)):
            return
        if mode == "ping":
            while f.read(1):
                c.sendall(b"K")
        elif mode == "down":
            blk, sent, end = os.urandom(65536), 0, time.time() + 30
            while sent < min(n, 1 << 29) and time.time() < end:
                c.sendall(blk)
                sent += len(blk)
        elif mode == "up":
            left = min(n, 1 << 28)
            while left > 0:
                b = f.read(min(65536, left))
                if not b:
                    break
                left -= len(b)
            c.sendall(b"K")
    except Exception:
        pass
    finally:
        c.close()


def bench_serve(st):
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    try:
        s.bind(("127.0.0.1", bench_port(st)))
    except OSError:
        return
    s.listen(16)
    gate = threading.BoundedSemaphore(8)

    def one(c):
        with gate:
            bench_conn(c)
    while True:
        c, _ = s.accept()
        threading.Thread(target=one, args=(c,), daemon=True).start()


def _bench_open(host, port, key, mode, n, timeout):
    s = socket.create_connection((host, port), timeout=timeout)
    s.settimeout(timeout)
    ts = int(time.time())
    s.sendall(f"NTB {mode} {n} {ts} {_mac(key, mode, n, ts)}\n".encode())
    return s


def bench_latency(host, port, key, count=8, timeout=6):
    t0 = time.time()
    s = _bench_open(host, port, key, "ping", 0, timeout)
    setup, rtts, lost = None, [], 0
    try:
        for _ in range(count):
            a = time.time()
            try:
                s.sendall(b"x")
                if not s.recv(1):
                    raise OSError("closed")
            except OSError:
                lost += 1
                if setup is None:
                    break
                continue
            b = time.time()
            if setup is None:
                setup = (b - t0) * 1000
            else:
                rtts.append((b - a) * 1000)
            time.sleep(0.05)
    finally:
        s.close()
    if setup is None:
        raise OSError("no reply through the tunnel")
    rtts = rtts or [setup]
    srt = sorted(rtts)
    return {"ok": True, "setup": round(setup, 1), "rtt": round(srt[len(srt) // 2], 1),
            "jitter": round(max(rtts) - min(rtts), 1), "loss": round(lost / count, 2)}


def bench_down(host, port, key, secs):
    s = _bench_open(host, port, key, "down", 1 << 29, 8)
    got, t1, end = 0, None, None
    try:
        while True:
            d = s.recv(262144)
            if not d:
                break
            now = time.time()
            if t1 is None:
                t1, end = now, now + secs
                continue
            got += len(d)
            if now >= end:
                break
    except OSError:
        pass
    finally:
        s.close()
    return round(got * 8 / max(time.time() - t1, 0.001) / 1e6, 1) if t1 else 0.0


def bench_up(host, port, key, nbytes):
    s = _bench_open(host, port, key, "up", nbytes, 25)
    blk, sent = os.urandom(65536), 0
    t0 = time.time()
    try:
        while sent < nbytes:
            s.sendall(blk[:min(65536, nbytes - sent)])
            sent += min(65536, nbytes - sent)
        if not s.recv(1):
            return 0.0
    except OSError:
        return 0.0
    finally:
        s.close()
    return round(nbytes * 8 / max(time.time() - t0, 0.001) / 1e6, 1)


def bench_speed(host, port, key, secs, r):
    try:
        r["down"] = bench_down(host, port, key, secs)
    except OSError:
        r["down"] = 0.0
    n = int(min(max((r["down"] or 2) * 1e6 / 8 * secs, 262144), 48 << 20))
    try:
        r["up"] = bench_up(host, port, key, n)
    except OSError:
        r["up"] = 0.0


def ping_host(ip, count=6):
    out = sh(f"ping -n -c {count} -i 0.25 -W 2 {ip}").stdout
    m = re.search(r"([\d.]+)% packet loss", out)
    a = re.search(r"= [\d.]+/([\d.]+)/[\d.]+/([\d.]+)", out)
    return {"loss": float(m.group(1)) / 100 if m else 1.0,
            "rtt": float(a.group(1)) if a else None, "jitter": float(a.group(2)) if a else None}


def bench_score(r):
    if not r.get("ok"):
        return 0.0
    if "down" in r:
        sp = max(((r.get("down") or 0) + (r.get("up") or 0)) / 2, 0.1)
    else:
        sp = 100.0 / (1 + r.get("jitter", 0) / 20)
    return round(sp * (1 - r.get("loss", 0)) / (1 + r.get("rtt", 0) / 300), 2)


def bench_recommend(st, res):
    ok = [r for r in res if r.get("ok")]
    bad = [r for r in res if not r.get("ok")]
    lines, order = [], []
    if not ok:
        return {"lines": ["Nothing connected. Check that the foreign server runs the same version of this script "
                          "(run Sync token after updating it), the firewall, and the server IPs."], "order": []}
    relays = sorted([r for r in ok if r["kind"] == "relay"], key=lambda r: -r["score"])
    order = [r["name"] for r in relays]
    kern = sorted([r for r in ok if r["kind"] == "kernel"], key=lambda r: -r["score"])
    if relays and "down" in relays[0]:
        f = max(relays, key=lambda r: (r.get("down", 0) + r.get("up", 0)))
        lines.append(f"Fastest relay: {f['name']} (down {f.get('down', 0)} / up {f.get('up', 0)} Mbps).")
    lat = min(ok, key=lambda r: (r.get("rtt") or 9e9))
    lines.append(f"Lowest latency (gaming / voice): {lat['name']} ({lat.get('rtt')} ms).")
    stab = min(ok, key=lambda r: (r.get("loss", 0), r.get("jitter") or 9e9))
    lines.append(f"Most stable (least loss/jitter): {stab['name']}.")
    by_id = {t["id"]: t for t in st["transports"]}
    stealth = [r for r in relays if r["name"] in by_id and by_id[r["name"]]["via"] == "direct"
               and ttype(by_id[r["name"]]) in STEALTH]
    if stealth:
        lines.append(f"Best stealth (looks like TLS/web traffic): {stealth[0]['name']}.")
    if kern and relays and kern[0]["score"] > 1.3 * relays[0]["score"]:
        kn = kern[0]["name"].replace("kernel:", "")
        lines.append(f"Kernel tunnel {kn} is clearly faster than any relay: forward heavy ports over it "
                     f"(Ports -> path 'kernel: {kn}'). Caveat: no obfuscation, DPI can fingerprint it.")
    elif kern:
        lines.append("Kernel tunnels work but are not faster than the best relay; keep them as backup.")
    opened = [r["name"] for r in ok if r.get("auth") == "OPEN"]
    if opened:
        lines.append("WARNING: these tunnels accepted a WRONG password (login not enforced): "
                     + ", ".join(opened) + ". Rotate credentials (Update tunnel) and re-test.")
    elif st.get("secure", True) and any(r.get("auth") == "enforced" for r in ok):
        lines.append("Password check passed: connects with the right password, refused with a wrong one.")
    elif not st.get("secure", True):
        lines.append("No-password mode: nothing to verify; the foreign server limits relay ports to the Iran IP.")
    plain = [r["name"] for r in ok if r.get("enc") == "no"]
    if plain:
        lines.append("Not encrypted (plain payload): " + ", ".join(plain) + ".")
    if bad:
        lines.append("Did not connect: " + ", ".join(r["name"] for r in bad)
                     + " (blocked, filtered, disabled on the foreign server, or UDP dropped on this path).")
    lines.append("Suggested priority (failover order): " + ", ".join(order) if order else "")
    return {"lines": [x for x in lines if x], "order": order}


def bench_live(res, full, n_kernel):
    """Publish progress for the panel: one line per tunnel plus a done/total counter."""
    lines, pending = [], 0
    for r in res:
        if not r.get("ok"):
            lines.append(f"{r['name']}: failed ({r.get('err') or 'no reply'})")
        elif "down" in r:
            lines.append(f"{r['name']}: {r['rtt']} ms, down {r['down']} / up {r['up']} Mb/s")
        else:
            if full and r.get("kind") == "relay":
                pending += 1
            lines.append(f"{r['name']}: {r['rtt']} ms" + (" ... speed test pending" if full else ""))
    n_relay = sum(1 for r in res if r.get("kind") == "relay")
    BENCH_STATE["live"] = lines
    BENCH_STATE["total"] = n_relay + n_kernel
    BENCH_STATE["done"] = len(res) - pending


def run_bench(st, full=True, secs=4, log=print):
    """Run from the Iran server. Returns (report, error)."""
    if st["role"] != "iran":
        return None, ERR + "Run the tunnel test on the Iran server (the entry side)."
    key, bp = st["auth"]["p"], bench_port(st)
    nk = len(st.get("l3") or {})
    BENCH_STATE.update(live=[], done=0, total=0)
    gostbin = shutil.which("gost") or "/usr/local/bin/gost"
    secure = is_secure(st)
    used, local, bad, svcs, chains = {bp, st["panel"]["port"]}, {}, {}, [], []

    def add_chain(cn, node, port):
        chains.append({"name": cn, "hops": [{"name": "h", "nodes": [node]}]})
        svcs.append({"name": "s-" + cn, "addr": f"127.0.0.1:{port}",
                     "handler": {"type": "tcp", "chain": cn}, "listener": {"type": "tcp"},
                     "forwarder": {"nodes": [{"name": "t", "addr": f"127.0.0.1:{bp}"}]}})
    for t in st["transports"]:
        local[t["id"]] = free_port(used)
        add_chain("c-" + t["id"], dial_node(st, t), local[t["id"]])
        if secure:  # same transport, WRONG password: the foreign server must refuse it
            bad[t["id"]] = free_port(used)
            node = dial_node(st, t)
            node["name"] += "-bad"
            node["connector"] = {"type": "relay", "auth": {"username": st["auth"]["u"],
                                                           "password": "wrong-" + rnd(10)}}
            add_chain("w-" + t["id"], node, bad[t["id"]])
    res, proc = [], None
    cfg = BASE + "/test-gost.json"
    try:
        if svcs:
            with open(cfg, "w") as f:
                json.dump({"log": {"level": "error"}, "services": svcs, "chains": chains}, f)
            os.chmod(cfg, 0o600)
            proc = subprocess.Popen([gostbin, "-C", cfg], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            for _ in range(50):
                if all(not can_bind(p) for p in list(local.values()) + list(bad.values())) \
                        or proc.poll() is not None:
                    break
                time.sleep(0.1)
            if proc.poll() is not None:
                return None, ERR + "Could not start the test engine (is gost installed?)."
        log(f"Checking connectivity of {len(local)} transports...")

        def lat(t):
            try:
                return bench_latency("127.0.0.1", local[t["id"]], key, count=16 if full else 8)
            except (OSError, ValueError) as e:
                return {"ok": False, "err": str(e) or e.__class__.__name__}
        with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex:
            lats = list(ex.map(lat, st["transports"]))
        for t, r in zip(st["transports"], lats):
            r.update(name=t["id"], kind="relay", enc=enc_of(t),
                     layer="L3 relay" if t["via"] != "direct" else "relay")
            res.append(r)
        bench_live(res, full, nk)
        # password check: right password connected above; the wrong one must be rejected
        by_tid = {t["id"]: t for t in st["transports"]}
        if secure:
            log("Password check (wrong password must be refused)...")

            def chk(r):
                if not r["ok"]:
                    return "-"
                try:
                    bench_latency("127.0.0.1", bad[r["name"]], key, count=1, timeout=4)
                    return "OPEN"      # connected with a wrong password: login is NOT enforced
                except (OSError, ValueError):
                    return "enforced"
            with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex:
                for r, a in zip(res, list(ex.map(chk, res))):
                    r["auth"] = a
        else:
            for r in res:
                r["auth"] = "no password" if r["ok"] else "-"
        for r in res:
            if r["ok"] and full:
                log(f"Speed test: {r['name']} ...")
                bench_speed("127.0.0.1", local[r["name"]], key, secs, r)
                bench_live(res, full, nk)
        for name, c in (st.get("l3") or {}).items():
            log(f"Kernel tunnel {name}: ping + TCP ...")
            pg = ping_host(c["f_ip"])
            r = {"name": "kernel:" + name, "kind": "kernel", "layer": "L3 kernel", "ok": False,
                 "enc": "yes" if name == "wg" else "no", "auth": "key" if name == "wg" else "none"}
            try:
                r.update(bench_latency(c["f_ip"], bp, key))
                r["loss"] = max(r["loss"], round(pg["loss"], 2))
                if full:
                    bench_speed(c["f_ip"], bp, key, secs, r)
            except OSError as e:
                r["err"] = ("ping ok but TCP failed (update + restart the foreign side)" if pg["loss"] < 1
                            else str(e) or "no reply")
            r["ping_ms"] = pg["rtt"]
            res.append(r)
            bench_live(res, full, nk)
    finally:
        if proc and proc.poll() is None:
            proc.terminate()
            try:
                proc.wait(5)
            except subprocess.TimeoutExpired:
                proc.kill()
        if os.path.exists(cfg):
            os.remove(cfg)
    for r in res:
        r["score"] = bench_score(r)
    rep = {"ts": int(time.time()), "full": full, "results": res}
    rep["rec"] = bench_recommend(st, res)
    with open(BENCH, "w") as f:
        json.dump(rep, f)
    return rep, None


def bench_table(rep):
    out = [f"{'TUNNEL':14}{'LAYER':11}{'STATE':7}{'RTT ms':8}{'JITTER':8}{'LOSS':6}{'DOWN Mb/s':11}{'UP Mb/s':9}"
           f"{'ENC':5}{'PASSWORD':12}SCORE"]
    for r in sorted(rep["results"], key=lambda r: -r["score"]):
        if r["ok"]:
            out.append(f"{r['name']:14}{r['layer']:11}{'OK':7}{r['rtt']:<8}{r['jitter']:<8}{r['loss']:<6}"
                       f"{r.get('down', '-'):<11}{r.get('up', '-'):<9}{r.get('enc', '-'):5}"
                       f"{r.get('auth', '-'):12}{r['score']}")
        else:
            out.append(f"{r['name']:14}{r['layer']:11}{'FAIL':7}{r.get('err', '')}")
    return "\n".join(out)


def op_bench_apply(st, rep=None):
    """Make the tester's suggested order the active priority (working relays only, failover mode)."""
    if rep is None:
        try:
            rep = json.load(open(BENCH))
        except (OSError, ValueError):
            return ERR + "Run the tunnel test first."
    order = rep.get("rec", {}).get("order") or []
    msg = op_set_ids(st, order)
    if not msg.startswith(ERR):
        st["strategy"] = "fifo"
    return msg


def bench_verdict(r):
    """Plain-language rating of one test result for people who do not read numbers."""
    if not r.get("ok"):
        return "failed"
    loss, rtt = r.get("loss", 0), r.get("rtt") or 0
    if loss >= 0.3:
        return "weak"
    if "down" in r:
        sp = ((r.get("down") or 0) + (r.get("up") or 0)) / 2
        if sp >= 30 and loss <= 0.05 and rtt <= 250:
            return "excellent"
        if sp >= 10 and loss <= 0.1:
            return "good"
        return "ok" if sp >= 3 else "weak"
    if loss <= 0.05 and rtt <= 120:
        return "excellent"
    if loss <= 0.1 and rtt <= 250:
        return "good"
    return "ok" if rtt <= 500 else "weak"


def bench_stab(r):
    """Stability 0-100 from packet loss and jitter over the probe window (higher = steadier)."""
    if not r.get("ok"):
        return 0
    rtt, jit = max(r.get("rtt") or 1, 1), r.get("jitter") or 0
    return max(0, min(100, round(100 * (1 - min(r.get("loss", 0) * 2, 1)) * (1 - 0.5 * min(jit / rtt, 1)))))


def bench_best(rep):
    """Name of the best working relay tunnel of a test report (highest score), or None."""
    ok = [r for r in rep.get("results", []) if r.get("ok") and r.get("kind") == "relay"]
    return max(ok, key=lambda r: r.get("score", 0))["name"] if ok else None


def op_use_tunnel(st, name, only=False):
    """Iran side: make ONE tested tunnel carry the traffic.
    relay name  -> it becomes first (failover); only=True also switches every other relay tunnel off.
    kernel:<c>  -> every forwarded port goes through that kernel tunnel.
    pool        -> kernel-routed ports go back to the relay pool."""
    if st["role"] != "iran":
        return ERR + "Choose the tunnel on the Iran server (the entry side)."
    ports = st.get("ports", [])
    if name == "pool":
        back = [p for p in ports if p.get("via")]
        for p in back:
            p.pop("via")
        return f"{len(back)} port(s) sent back to the relay pool." if back else "No port used a kernel tunnel."
    if name.startswith("kernel:"):
        c = name[7:]
        if c not in (st.get("l3") or {}):
            return ERR + "Unknown kernel tunnel."
        if not ports:
            return ERR + "Add a forwarded port first (Ports tab)."
        for p in ports:
            p["via"] = c
        return (f"All {len(ports)} forwarded port(s) now go through the {CARRIERS[c][0]} kernel tunnel "
                "(fast, but no obfuscation and no failover).")
    if not find_tp(st, name):
        return ERR + "Unknown tunnel."
    others = [t["id"] for t in st["transports"] if t["enabled"] and t["id"] != name]
    msg = op_set_ids(st, [name] if only else [name] + others)
    if msg.startswith(ERR):
        return msg
    st["strategy"] = "fifo"
    back = [p for p in ports if p.get("via")]
    for p in back:
        p.pop("via")
    out = f"Now using {name}" + (" only." if only else " as the main tunnel; the others stay as backup.")
    if back:
        out += f" {len(back)} kernel-routed port(s) moved back to the relay pool."
    return out


def op_use_best(st, only=False):
    try:
        with open(BENCH) as f:
            rep = json.load(f)
    except (OSError, ValueError):
        return ERR + "Run the tunnel test first."
    name = bench_best(rep)
    if not name:
        return ERR + "No working tunnel in the last test."
    return op_use_tunnel(st, name, only)


def op_all_models(st):
    """Foreign side: build + enable every tunnel model so the Iran test can compare ALL of them."""
    e = only_foreign(st)
    if e:
        return e
    added, failed = [], []
    for k in CATALOG:
        if not find_tp(st, k):
            (failed if op_tp_add(st, k).startswith(ERR) else added).append(k)
    for c in CARRIERS:
        if c not in (st.get("l3") or {}) and not find_tp(st, c):
            try:
                m = op_carrier_add(st, c)
            except Exception as ex:  # a kernel without that module must not stop the rest
                m = ERR + str(ex)
            (failed if m.startswith(ERR) else added).append(c)
    for t in st["transports"]:
        t["enabled"] = True
    if not added and failed:
        return ERR + "Could not build: " + ", ".join(failed)
    if not added:
        return "Every tunnel model is already built."
    tail = f" Could not build: {', '.join(failed)}." if failed else ""
    return (f"Built {len(added)} more model(s): {', '.join(added)}.{tail} Copy the new token to the Iran server "
            "(Sync token), then run the test there. Afterwards switch off the models you do not use.")


def bench_bg(st, full):
    BENCH_STATE.update(running=True, log=[])
    try:
        _, err = run_bench(st, full=full, log=lambda m: BENCH_STATE["log"].append(m))
        if err:
            BENCH_STATE["log"].append(err)
    except Exception as e:  # never let the panel thread die silently
        BENCH_STATE["log"].append(ERR + f"Test failed: {e}")
    finally:
        BENCH_STATE["running"] = False


# ------------------------------------------------- update / reset / uninstall
def remote_version():
    try:
        raw = open(OPT + "/repo").read().strip()
    except OSError:
        return None
    r = sh(f"curl -fsSL --max-time 10 {shlex.quote(raw + '/nt.py')}")
    m = re.search(r'^VERSION = "([^"]+)"', r.stdout, re.M)
    return m.group(1) if m else None


def update_script():
    try:
        raw = open(OPT + "/repo").read().strip()
    except OSError:
        return ERR + "Repo URL unknown; reinstall with the one-line command."
    tmp = OPT + "/nt.py.new"
    if sh(f"curl -fsSL --max-time 30 {shlex.quote(raw + '/nt.py')} -o {tmp}").returncode != 0:
        return ERR + "Download failed."
    try:
        src = open(tmp).read()
        ast.parse(src)
        assert 'NAME = "night-tunnel"' in src
    except Exception:
        os.remove(tmp)
        return ERR + "Downloaded file is invalid; kept the current version."
    m = re.search(r'^VERSION = "([^"]+)"', src, re.M)
    os.replace(tmp, OPT + "/nt.py")
    os.chmod(OPT + "/nt.py", 0o700)
    sh("systemd-run --no-block --collect sh -c 'sleep 2; systemctl restart night-tunnel-panel'")
    return f"Script updated {VERSION} -> {m.group(1) if m else '?'}. Panel restarts in a moment."


def update_gost():
    arch = {"x86_64": "amd64", "aarch64": "arm64", "arm64": "arm64", "armv7l": "armv7"}.get(os.uname().machine)
    if not arch:
        return ERR + "Unsupported architecture."
    r = sh("curl -fsSL --max-time 20 https://api.github.com/repos/go-gost/gost/releases/latest")
    try:
        urls = [a["browser_download_url"] for a in json.loads(r.stdout)["assets"]]
        url = next(u for u in urls if u.endswith(f"_linux_{arch}.tar.gz"))
    except Exception:
        return ERR + "Could not find a gost release (GitHub unreachable?)."
    d = tempfile.mkdtemp()
    try:
        if sh(f"curl -fsSL --max-time 120 {shlex.quote(url)} -o {d}/g.tgz").returncode != 0:
            return ERR + "gost download failed."
        with tarfile.open(d + "/g.tgz") as tf:
            data = tf.extractfile("gost").read()
        before = sh("/usr/local/bin/gost -V").stdout.strip()
        shutil.copy("/usr/local/bin/gost", "/usr/local/bin/gost.bak")
        with open("/usr/local/bin/gost.new", "wb") as f:
            f.write(data)
        os.chmod("/usr/local/bin/gost.new", 0o755)
        if sh("/usr/local/bin/gost.new -V").returncode != 0:
            os.remove("/usr/local/bin/gost.new")
            return ERR + "New gost binary does not run; kept the old one."
        os.replace("/usr/local/bin/gost.new", "/usr/local/bin/gost")
        sh("systemctl restart night-tunnel-gost")
        after = sh("/usr/local/bin/gost -V").stdout.strip()
        return f"gost updated: {before or '?'} -> {after or '?'} (backup: gost.bak)."
    except Exception as e:
        return ERR + f"gost update failed: {e}"
    finally:
        shutil.rmtree(d, ignore_errors=True)


def teardown(full=False, purge=False):
    """Reset = delete the tunnel config (stay installed). full = remove everything."""
    le = ""
    try:
        le = load().get("le", "")
    except (OSError, ValueError):
        pass
    for s in ("night-tunnel-panel", "night-tunnel-gost", "night-tunnel-l3"):
        sh(f"systemctl disable --now {s}")
    l3_down()
    fw_clear()
    if le and valid_host(le):
        sh(f"certbot delete --cert-name {shlex.quote(le)} --non-interactive")
    if os.path.exists(HOOK):
        os.remove(HOOK)
    shutil.rmtree(BASE, ignore_errors=True)
    if full:
        op_tg_remove(purge)
        for s in ("night-tunnel-panel", "night-tunnel-gost", "night-tunnel-l3"):
            p = f"/etc/systemd/system/{s}.service"
            os.path.exists(p) and os.remove(p)
        for p in ("/usr/local/bin/night-tunnel", "/usr/local/bin/gost.bak") + (("/usr/local/bin/gost",) if purge else ()):
            os.path.exists(p) and os.remove(p)
        sh("systemctl daemon-reload")
        shutil.rmtree(OPT, ignore_errors=True)


def detached(*args):
    sh(f"systemd-run --no-block --collect python3 {OPT}/nt.py {' '.join(args)}")


# ------------------------------------------------------------- web panel
CSS = r"""
:root{--bg:#070b14;--panel:rgba(17,25,42,.74);--line:rgba(148,163,184,.14);--line2:rgba(148,163,184,.26);
--tx:#e8eef8;--mu:#8b99b5;--ac:#7c8cff;--ac2:#35d0ff;--ok:#34d399;--bad:#f87171;--warn:#fbbf24;--r:14px;color-scheme:dark}
*{box-sizing:border-box}
html{scroll-behavior:smooth}
body{margin:0;min-height:100vh;color:var(--tx);font:14px/1.55 system-ui,-apple-system,"Segoe UI",Tahoma,Vazirmatn,sans-serif;
background:radial-gradient(900px 520px at 88% -8%,rgba(124,140,255,.2),transparent 62%),
radial-gradient(760px 460px at -6% 108%,rgba(53,208,255,.13),transparent 62%),var(--bg);background-attachment:fixed}
a{color:var(--ac2)}
b{font-weight:650}
.mu{color:var(--mu)}.mono,code{font-family:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;direction:ltr;unicode-bidi:plaintext}
.ic{width:18px;height:18px;flex:none}
.app{display:grid;grid-template-columns:236px minmax(0,1fr);min-height:100vh}
.side{position:sticky;top:0;height:100vh;padding:20px 12px;display:flex;flex-direction:column;gap:4px;
border-inline-end:1px solid var(--line);background:rgba(7,11,20,.62);backdrop-filter:blur(16px);overflow-y:auto}
.brand{display:flex;align-items:center;gap:11px;padding:2px 10px 20px;font-weight:700;font-size:16px;letter-spacing:-.01em}
.logo{width:36px;height:36px;border-radius:11px;flex:none;background:linear-gradient(135deg,var(--ac),var(--ac2));
display:grid;place-items:center;box-shadow:0 8px 26px rgba(124,140,255,.38)}
.logo svg{width:19px;height:19px}
.nav-i{font:inherit;color:var(--mu);background:none;border:0;cursor:pointer;display:flex;align-items:center;gap:11px;
padding:9px 12px;border-radius:11px;text-align:start;white-space:nowrap;transition:background .15s,color .15s}
.nav-i:hover{background:rgba(148,163,184,.08);color:var(--tx)}
.nav-i.on{color:#fff;background:linear-gradient(135deg,rgba(124,140,255,.28),rgba(53,208,255,.14));box-shadow:inset 0 0 0 1px rgba(124,140,255,.35)}
.main{padding:26px clamp(16px,3vw,42px) 70px;max-width:1140px;width:100%}
.top{display:flex;align-items:center;gap:10px;flex-wrap:wrap;margin-bottom:22px}
.top h1{margin:0;font-size:23px;letter-spacing:-.015em;margin-inline-end:6px}
.grow{flex:1}
.tab{display:none}
.tab.on{display:block;animation:in .28s ease}
@keyframes in{from{opacity:0;transform:translateY(7px)}to{opacity:1;transform:none}}
.card{background:var(--panel);border:1px solid var(--line);border-radius:var(--r);padding:18px 20px;margin-bottom:16px;backdrop-filter:blur(10px)}
.card>h2{margin:0 0 12px;font-size:15px;font-weight:650}
.card>h2+.hint{margin-top:-8px}
.card.ok{border-color:rgba(52,211,153,.4)}.card.bad{border-color:rgba(248,113,113,.4)}
.card.bad>h2{color:var(--bad)}.card.ok>h2{color:var(--ok)}
.hint{color:var(--mu);font-size:13px;margin:6px 0 12px}
.grid{display:grid;gap:14px;grid-template-columns:repeat(auto-fit,minmax(190px,1fr));margin-bottom:16px}
.stat{background:var(--panel);border:1px solid var(--line);border-radius:var(--r);padding:15px 17px;position:relative;overflow:hidden}
.stat::before{content:"";position:absolute;inset-inline-start:0;top:0;bottom:0;width:3px;background:linear-gradient(var(--ac),var(--ac2));opacity:.7}
.stat .k{color:var(--mu);font-size:12px;text-transform:uppercase;letter-spacing:.05em}
.stat .v{font-size:22px;font-weight:700;margin:6px 0 2px;min-height:32px;display:flex;align-items:center}
.stat .s{color:var(--mu);font-size:12px;min-height:18px}
.scroll{overflow-x:auto}
.tbl{width:100%;border-collapse:collapse}
.tbl th{font-weight:600;color:var(--mu);font-size:12px;text-transform:uppercase;letter-spacing:.04em;text-align:start;padding:8px 10px;border-bottom:1px solid var(--line);white-space:nowrap}
.tbl td{padding:10px;border-bottom:1px solid var(--line);vertical-align:middle}
.tbl tr:last-child td{border-bottom:0}
input,select,textarea{font:inherit;color:var(--tx);background:rgba(6,10,18,.72);border:1px solid var(--line2);border-radius:10px;
padding:8px 11px;outline:none;max-width:100%;transition:border-color .15s,box-shadow .15s}
input:focus,select:focus,textarea:focus{border-color:var(--ac);box-shadow:0 0 0 3px rgba(124,140,255,.22)}
input::placeholder,textarea::placeholder{color:#59667f}
input[type=checkbox]{accent-color:var(--ac);width:16px;height:16px;padding:0}
textarea{width:100%;min-height:92px;font-family:ui-monospace,Menlo,Consolas,monospace;font-size:12.5px;resize:vertical;direction:ltr;text-align:left}
input[type=password],input[name=ip],input[name=port],input[name=remote_ip],input[name=ports],input[name=udp],input[name=foreign_ip],
input[name=iran_ip],input[name=sni],input[name=path],input[name=host],input[name=target],input[name=ssh_key],input[name=ssh_port],input[name=ssh_user],input.ltr{direction:ltr;text-align:left}
.row{display:flex;flex-wrap:wrap;gap:10px;align-items:flex-end}
.f{display:flex;flex-direction:column;gap:5px;font-size:12px;color:var(--mu)}
.f input,.f select{font-size:14px}
.ck{display:inline-flex;align-items:center;gap:8px;color:var(--tx);font-size:13px;padding:8px 0}
.w-xs{width:64px}.w-s{width:92px}.w-m{width:150px}.w-l{width:250px}.w-f{width:100%}
.btn{font:inherit;font-weight:600;cursor:pointer;color:#fff;border:0;border-radius:10px;padding:8px 15px;
background:linear-gradient(135deg,var(--ac),#5a6bff);box-shadow:0 5px 18px rgba(90,107,255,.3);
display:inline-flex;align-items:center;justify-content:center;gap:8px;transition:transform .1s,filter .15s;text-decoration:none}
.btn:hover{filter:brightness(1.12)}.btn:active{transform:translateY(1px)}
.btn.g{background:rgba(148,163,184,.1);box-shadow:none;border:1px solid var(--line2);color:var(--tx)}
.btn.d{background:linear-gradient(135deg,#ef4444,#b91c1c);box-shadow:0 5px 18px rgba(239,68,68,.25)}
.btn.s{padding:5px 11px;font-size:13px}
.btn.busy{opacity:.65;pointer-events:none}
.btn.busy::after{content:"";width:13px;height:13px;border-radius:50%;border:2px solid rgba(255,255,255,.35);border-top-color:#fff;animation:sp .7s linear infinite}
@keyframes sp{to{transform:rotate(360deg)}}
.pill{display:inline-flex;align-items:center;gap:6px;padding:2px 10px;border-radius:99px;font-size:12px;font-weight:650;
border:1px solid var(--line2);color:var(--mu);white-space:nowrap}
.pill::before{content:"";width:7px;height:7px;border-radius:50%;background:currentColor}
.pill.up,.pill.active{color:var(--ok);background:rgba(52,211,153,.1);border-color:rgba(52,211,153,.32)}
.pill.down,.pill.failed,.pill.inactive{color:var(--bad);background:rgba(248,113,113,.1);border-color:rgba(248,113,113,.35)}
.pill.off{color:var(--mu,#8b93a7);background:rgba(139,147,167,.1);border-color:rgba(139,147,167,.3)}
.pill.udp,.pill.activating,.pill.warn{color:var(--warn);background:rgba(251,191,36,.1);border-color:rgba(251,191,36,.35)}
.pill.plain::before{display:none}
.sw{position:relative;width:40px;height:23px;display:inline-block;vertical-align:middle}
.sw input{opacity:0;position:absolute;inset:0;margin:0;width:100%;height:100%;cursor:pointer;z-index:1}
.sw i{position:absolute;inset:0;border-radius:99px;background:rgba(148,163,184,.26);transition:background .2s}
.sw i::after{content:"";position:absolute;top:3px;inset-inline-start:3px;width:17px;height:17px;border-radius:50%;background:#fff;transition:inset-inline-start .2s}
.sw input:checked+i{background:linear-gradient(135deg,var(--ac),var(--ac2))}
.sw input:checked+i::after{inset-inline-start:20px}
.flash{padding:11px 15px;border-radius:12px;margin-bottom:16px;border:1px solid rgba(52,211,153,.38);background:rgba(52,211,153,.1);color:#c1f5df;word-break:break-word}
.flash.e{border-color:rgba(248,113,113,.42);background:rgba(248,113,113,.1);color:#fecaca}
.presets{display:grid;grid-template-columns:repeat(auto-fit,minmax(170px,1fr));gap:10px}
.preset{display:flex;flex-direction:column;align-items:flex-start;justify-content:flex-start;font:inherit;color:var(--tx);text-align:start;cursor:pointer;padding:13px 15px;border-radius:12px;width:100%;
background:rgba(148,163,184,.06);border:1px solid var(--line2);transition:border-color .15s,transform .1s,background .15s}
.preset:hover{border-color:var(--ac);background:rgba(124,140,255,.1)}.preset:active{transform:translateY(1px)}
.preset b{display:block;margin-bottom:2px}.preset small{color:var(--mu);font-size:12px}
.item{display:flex;flex-wrap:wrap;gap:12px;align-items:flex-end;justify-content:space-between;padding:14px 0;border-bottom:1px solid var(--line)}
.item:last-child{border-bottom:0;padding-bottom:0}.item:first-child{padding-top:0}
.item .hd{display:flex;align-items:center;gap:9px;width:100%;margin-bottom:-2px;flex-wrap:wrap}
.kv{display:grid;grid-template-columns:max-content 1fr;gap:8px 18px;margin:0}
.kv dt{color:var(--mu)}.kv dd{margin:0;word-break:break-all}
.copy{display:flex;gap:8px;align-items:center}.copy input{flex:1;min-width:0;direction:ltr;text-align:left}
.seg{font:inherit;color:var(--mu);background:rgba(148,163,184,.07);border:1px solid var(--line2);padding:6px 13px;border-radius:99px;cursor:pointer}
.seg.on{color:#fff;border-color:var(--ac);background:rgba(124,140,255,.25)}
pre.log{background:#04070f;border:1px solid var(--line);border-radius:12px;padding:12px 14px;max-height:480px;min-height:140px;overflow:auto;
font:12px/1.55 ui-monospace,Menlo,Consolas,monospace;direction:ltr;text-align:left;white-space:pre-wrap;word-break:break-all;margin:12px 0 0;color:#b7c4dc}
.login{min-height:100vh;display:grid;place-items:center;padding:20px}
.login .card{width:100%;max-width:370px;padding:30px 28px;margin:0}
.login h1{margin:14px 0 4px;font-size:24px;letter-spacing:-.02em}
.login .logo{width:48px;height:48px;border-radius:14px}.login .logo svg{width:25px;height:25px}
.login form{display:grid;gap:12px;margin-top:20px}.login input{width:100%}
.dot{display:inline-block;width:8px;height:8px;border-radius:50%;background:var(--mu);margin-inline-end:8px}
ul.rec{margin:8px 0 0;padding-inline-start:20px}ul.rec li{margin:4px 0}
.bar{height:6px;border-radius:99px;background:rgba(148,163,184,.18);overflow:hidden;min-width:64px;margin-top:5px}
.bar>i{display:block;height:100%;background:linear-gradient(90deg,var(--ac),var(--ac2));transition:width .5s}
form.inl{display:inline-block;margin:2px 4px 2px 0}
details{margin-top:12px}summary{cursor:pointer;color:var(--ac2)}
.mgrp{margin:10px 0}.mgrp>b{display:block;font-size:12px;color:var(--mu);margin-bottom:2px}
.mgrp .ck{margin-inline-end:16px}
@media(max-width:860px){
.app{grid-template-columns:minmax(0,1fr)}
.side{position:sticky;top:0;z-index:5;height:auto;flex-direction:row;align-items:center;padding:9px 10px;gap:3px;overflow-x:auto;
border-inline-end:0;border-bottom:1px solid var(--line)}
.brand{padding:0 8px 0 4px}.brand span{display:none}
.nav-i{padding:8px 12px;font-size:13px}
.main{padding-top:18px}
.kv{grid-template-columns:1fr}
}
"""

JS_TPL = r"""
(function(){
var FA=__FA__;
var $=function(s,r){return (r||document).querySelector(s)};
var $$=function(s,r){return [].slice.call((r||document).querySelectorAll(s))};
var lang='en',cur='',logSvc='gost';
try{lang=localStorage.getItem('ntl')||'en'}catch(e){}
function tr(s){return lang==='fa'&&FA[s]?FA[s]:s}
function walk(){
 var w=document.createTreeWalker(document.body,NodeFilter.SHOW_TEXT,null),n,list=[];
 while((n=w.nextNode())){list.push(n)}
 list.forEach(function(n){
  if(n.__o===undefined){var p=n.parentNode&&n.parentNode.nodeName;if(p==='SCRIPT'||p==='STYLE'||p==='TEXTAREA'||p==='PRE'){n.__o=null}else{n.__o=n.nodeValue}}
  if(n.__o===null)return;
  var m=/^(\s*)([\s\S]*?)(\s*)$/.exec(n.__o);
  var key=m[2].replace(/\s+/g,' ');
  n.nodeValue=(lang==='fa'&&FA[key])?m[1]+FA[key]+m[3]:n.__o;
 });
 $$('[placeholder],[title],[data-c]').forEach(function(e){
  ['placeholder','title','data-c'].forEach(function(a){
   if(!e.hasAttribute(a))return;var k='_o_'+a;
   if(e[k]===undefined)e[k]=e.getAttribute(a);
   if(a!=='data-c')e.setAttribute(a,tr(e[k]));
  });
 });
}
function applyLang(){
 document.documentElement.lang=lang;document.documentElement.dir=lang==='fa'?'rtl':'ltr';
 walk();var b=$('#lang');if(b)b.textContent=lang==='fa'?'English':'فارسی';
 var t=$('#ttl'),on=$('.nav-i.on');if(t&&on)t.textContent=on.textContent.trim();
}
function show(t){
 var ids=$$('.tab').map(function(x){return x.id.slice(4)});
 if(!ids.length)return;
 if(ids.indexOf(t)<0)t=ids[0];
 cur=t;
 $$('.tab').forEach(function(x){x.classList.toggle('on',x.id==='tab-'+t)});
 $$('.nav-i').forEach(function(b){b.classList.toggle('on',b.dataset.tab===t)});
 var on=$('.nav-i.on'),h=$('#ttl');if(h&&on)h.textContent=on.textContent.trim();
 if(t==='logs')loadLog();
}
function loadLog(s){
 if(s)logSvc=s;var box=$('#logbox');if(!box)return;
 $$('[data-log]').forEach(function(b){b.classList.toggle('on',b.dataset.log===logSvc)});
 box.textContent='...';
 fetch('logs?svc='+logSvc+'&n='+$('#logn').value,{credentials:'same-origin',cache:'no-store'})
 .then(function(r){return r.text()}).then(function(t){box.textContent=t;box.scrollTop=box.scrollHeight})
 .catch(function(){box.textContent='Could not load the log.'});
}
function copyText(id){
 var e=$(id);if(!e)return;var v=e.value!==undefined?e.value:e.textContent;
 var done=function(){var b=$('[data-copy="'+id+'"]');if(b){var o=b.textContent;b.textContent=tr('Copied');setTimeout(function(){b.textContent=o},1400)}};
 if(navigator.clipboard&&window.isSecureContext){navigator.clipboard.writeText(v).then(done,function(){})}
 else{e.select&&e.select();try{document.execCommand('copy');done()}catch(x){}}
}
document.addEventListener('click',function(e){
 var t=e.target.closest('[data-tab]');if(t){location.hash=t.dataset.tab;return}
 t=e.target.closest('[data-log]');if(t){loadLog(t.dataset.log);return}
 t=e.target.closest('[data-gologs]');if(t){logSvc=t.dataset.gologs;location.hash='logs';show('logs');return}
 t=e.target.closest('[data-copy]');if(t){copyText(t.dataset.copy);return}
 t=e.target.closest('[data-reload]');if(t){loadLog();return}
 if(e.target.id==='lang'){lang=lang==='fa'?'en':'fa';try{localStorage.setItem('ntl',lang)}catch(x){}applyLang()}
});
document.addEventListener('submit',function(e){
 var f=e.target;
 if(f.dataset.c&&!confirm(tr(f.dataset.c))){e.preventDefault();return}
 if(f.method==='post'&&cur){var i=document.createElement('input');i.type='hidden';i.name='tab';i.value=cur;f.appendChild(i)}
 var b=e.submitter||$('button:not([type=button])',f);if(b)setTimeout(function(){b.classList.add('busy')},0);
});
var ln=$('#logn');if(ln)ln.addEventListener('change',function(){loadLog()});
window.addEventListener('hashchange',function(){show(location.hash.slice(1))});
show(location.hash.slice(1));applyLang();
// live status
var run=document.body.dataset.run==='1';
function poll(){
 if(document.hidden||!$('.app'))return;
 fetch('status',{credentials:'same-origin',cache:'no-store'}).then(function(r){return r.json()}).then(function(d){
  $$('[data-svc]').forEach(function(e){var s=d.svc[e.dataset.svc];if(s){e.className='pill '+s;e.textContent=tr(s)}});
  $$('[data-tp]').forEach(function(e){var s=d.tp[e.dataset.tp];if(s){e.className='pill '+s;e.textContent=tr(s)}});
  var u=$('[data-upcount]');if(u){var n=0;for(var k in d.tp)if(d.tp[k]==='up')n++;u.textContent=n}
  var w=$('#wg');if(w&&d.wg)w.textContent=d.wg;
  var bl=$('#benchlog');if(bl)bl.textContent=d.bench.log||'';
  $$('.wizlog').forEach(function(e){if(d.wiz.log)e.textContent=d.wiz.log});
  var bv=$('#benchlive');if(bv)bv.textContent=d.bench.live||'';
  var bb=$('#benchbar');if(bb)bb.style.width=(d.bench.pct||0)+'%';
  if(run&&!d.bench.running&&!d.wiz.running)location.reload();
 }).catch(function(){});
}
setInterval(poll,run?3500:9000);
})();
"""


FA_TEXT = {
    # navigation / titles
    "Overview": "نمای کلی", "Transports": "ترنسپورت‌ها", "Ports": "پورت‌ها", "Tunnels": "تانل‌ها", "Token": "توکن",
    "Test": "تست", "Telegram proxy": "پروکسی تلگرام", "Security": "امنیت", "Logs": "لاگ‌ها", "System": "سیستم",
    "Easy setup": "نصب آسان", "Logout": "خروج", "Login": "ورود", "Sign in to the control panel": "ورود به پنل مدیریت",
    "Iran · entry": "ایران · ورودی", "Foreign · exit": "خارج · خروجی", "Not configured": "تنظیم نشده",
    "user": "نام کاربری", "password": "رمز عبور", "Wrong credentials": "نام کاربری یا رمز اشتباه است",
    # states
    "up": "فعال", "down": "قطع", "active": "فعال", "inactive": "غیرفعال", "failed": "خطا", "off": "خاموش",
    "udp": "UDP", "unknown": "نامشخص", "none": "ندارد", "encrypted": "رمزگذاری‌شده", "plain": "بدون رمزنگاری",
    # overview
    "Engine (gost)": "موتور (gost)", "Relay pool": "استخر ریلی", "Kernel links": "لینک‌های کرنلی", "MTProto": "MTProto",
    "IP-locked": "قفل روی IP", "Relay login required": "ورود به ریلی اجباری است", "Only the Iran IP is allowed": "فقط IP ایران مجاز است",
    "Transports up": "ترنسپورت‌های فعال", "Forwarded ports": "پورت‌های فوروارد", "Transport health": "سلامت ترنسپورت‌ها",
    "Tunnel": "تانل", "Type": "نوع", "Port": "پورت", "Data": "داده", "State": "وضعیت", "Server": "سرور", "Role": "نقش",
    "Iran (entry)": "ایران (ورودی)", "Foreign (exit)": "خارج (خروجی)", "Foreign IP": "آی‌پی خارج", "Iran IP": "آی‌پی ایران",
    "Mode": "حالت", "WireGuard handshake": "هندشیک وایرگارد", "Version": "نسخه", "Quick actions": "اقدام‌های سریع",
    "Restart tunnel services": "ری‌استارت سرویس‌های تانل", "Quick connection test": "تست سریع اتصال", "View logs": "مشاهده لاگ",
    # transports
    "Transport pool": "استخر ترنسپورت", "On": "روشن", "Priority": "اولویت", "ID": "شناسه",
    "Failover (priority order)": "فیل‌اور (به ترتیب اولویت)", "Rotate (round-robin per connection)": "چرخشی (برای هر کانکشن)",
    "Random per connection": "تصادفی برای هر کانکشن", "Save & apply": "ذخیره و اعمال",
    "Turn transports on or off and set their order. Lower priority number = tried first.": "ترنسپورت‌ها را روشن/خاموش کنید و ترتیبشان را بدهید. عدد کمتر = اول امتحان می‌شود.",
    "Presets": "پریست‌ها", "Balanced": "متعادل", "Mixed transports with a backup": "ترکیب ترنسپورت‌ها همراه پشتیبان",
    "Stealth": "مخفی", "Looks like normal TLS / web traffic": "شبیه ترافیک عادی TLS / وب",
    "Gaming": "گیمینگ", "UDP transports first": "اول ترنسپورت‌های UDP", "Rotate": "چرخشی",
    "Spread connections over everything": "پخش کانکشن‌ها روی همه ترنسپورت‌ها",
    "One click re-orders and enables a sensible set.": "با یک کلیک ترتیب و فعال‌سازی مناسب اعمال می‌شود.",
    # ports
    "Protocol": "پروتکل", "Remote port": "پورت مقصد", "Path": "مسیر", "Save": "ذخیره", "Delete": "حذف",
    "Delete this port?": "این پورت حذف شود؟", "Add a port": "افزودن پورت", "Add port": "افزودن پورت",
    "No forwarded ports yet.": "هنوز پورتی فوروارد نشده.",
    "Each port on this server goes to 127.0.0.1 on the foreign server.": "هر پورت روی این سرور به 127.0.0.1 سرور خارج می‌رود.",
    # tunnels
    "Your tunnels": "تانل‌های شما", "SNI": "SNI", "Host": "هاست", "Name": "نام", "Build tunnel": "ساخت تانل",
    "Build a new tunnel": "ساخت تانل جدید", "Delete this tunnel?": "این تانل حذف شود؟",
    "Change a port, type, SNI, path or host. After any change copy the new token to the Iran server.": "پورت، نوع، SNI، مسیر یا هاست را تغییر دهید. بعد از هر تغییر توکن جدید را در سرور ایران وارد کنید.",
    "You can build several tunnels of one type (use different names, ports or SNI). Kernel tunnels (L3) can also be used as direct port paths on the Iran server.": "از هر نوع می‌توانید چند تانل بسازید (با نام، پورت یا SNI متفاوت). تانل‌های کرنلی (L3) را می‌توان مستقیم به‌عنوان مسیر پورت در سرور ایران هم استفاده کرد.",
    # token
    "Token for the Iran server": "توکن برای سرور ایران", "Copy": "کپی", "Copied": "کپی شد",
    "On the Iran server open Token and import this value (Sync token). Do it after every change here.": "در سرور ایران به بخش «توکن» بروید و این مقدار را وارد کنید (Sync). بعد از هر تغییر اینجا این کار را انجام دهید.",
    "Sync token": "همگام‌سازی توکن", "Import token": "وارد کردن توکن",
    "Paste the token from the foreign server's panel after you change anything there.": "بعد از هر تغییر در سرور خارج، توکن را از پنل آن اینجا پیست کنید.",
    # test
    "Test tunnels": "تست تانل‌ها", "Run the test from the Iran server's panel (the entry side). This server answers the test automatically.": "تست را از پنل سرور ایران (سمت ورودی) اجرا کنید. این سرور خودکار پاسخ می‌دهد.",
    "Full test (connect + speed)": "تست کامل (اتصال + سرعت)", "Quick test (connect + latency)": "تست سریع (اتصال + تأخیر)",
    "Speed tests use real bandwidth for about 10 seconds per tunnel.": "تست سرعت حدود ۱۰ ثانیه برای هر تانل از پهنای باند واقعی استفاده می‌کند.",
    "Layer": "لایه", "RTT ms": "RTT (ms)", "Jitter": "جیتر", "Loss": "لاس", "Down Mb/s": "دانلود Mb/s", "Up Mb/s": "آپلود Mb/s",
    "Encrypted": "رمزگذاری", "Score": "امتیاز", "Recommendation": "پیشنهاد", "Apply suggested order": "اعمال ترتیب پیشنهادی",
    "Enable only the working tunnels in the suggested order?": "فقط تانل‌های سالم به ترتیب پیشنهادی فعال شوند؟",
    # security
    "Security mode": "حالت امنیتی", "With password": "با رمز", "No password": "بدون رمز",
    "Relay login is required. TLS / QUIC / WireGuard tunnels are encrypted. Plain tunnels (tcp, ws, kcp, udp, ...) are authenticated but carry data unencrypted.": "ورود به ریلی اجباری است. تانل‌های TLS / QUIC / WireGuard رمزگذاری‌شده‌اند. تانل‌های ساده (tcp, ws, kcp, udp, ...) احراز هویت می‌شوند ولی داده رمزگذاری‌نشده است.",
    "Switch to NO password": "تغییر به حالت بدون رمز", "Switch to password mode": "تغییر به حالت با رمز",
    "Change the security mode? Then copy the new token to the Iran server.": "حالت امنیتی عوض شود؟ بعد توکن جدید را در سرور ایران وارد کنید.",
    "Change it on the foreign server, then Sync token here.": "آن را در سرور خارج تغییر دهید، سپس اینجا توکن را Sync کنید.",
    # telegram
    "Telegram proxy (MTProto, fake-TLS)": "پروکسی تلگرام (MTProto، فیک‌TLS)", "Cover domain": "دامنه پوششی",
    "Restart": "ری‌استارت", "New secret": "سکرت جدید", "Remove proxy": "حذف پروکسی",
    "Old links will stop working. Continue?": "لینک‌های قبلی از کار می‌افتند. ادامه می‌دهید؟",
    "Remove the Telegram proxy?": "پروکسی تلگرام حذف شود؟",
    "Runs on this server, independent of the tunnels. Share the link with people who need it.": "روی همین سرور و مستقل از تانل‌ها اجرا می‌شود. لینک را با کسانی که لازم دارند به اشتراک بگذارید.",
    "Change port or cover domain": "تغییر پورت یا دامنه پوششی", "Apply": "اعمال",
    "The secret is regenerated, so share the new link afterwards.": "سکرت دوباره ساخته می‌شود؛ بعدش لینک جدید را به اشتراک بگذارید.",
    "Server IP": "آی‌پی سرور", "Create proxy": "ساخت پروکسی",
    "Runs on this server, independent of the tunnels. Use a server that can reach Telegram (usually the foreign one). You get a link to share.": "روی همین سرور و مستقل از تانل‌ها اجرا می‌شود. سروری را انتخاب کنید که به تلگرام دسترسی دارد (معمولاً سرور خارج). یک لینک برای اشتراک می‌گیرید.",
    # logs
    "Engine": "موتور", "Panel": "پنل", "Telegram": "تلگرام", "Refresh": "تازه‌سازی",
    "Latest lines from the systemd journal.": "آخرین خط‌های ژورنال systemd.",
    # system
    "Update tunnel settings": "به‌روزرسانی تنظیمات تانل", "Rotate credentials + WireGuard keys": "چرخش رمزها و کلیدهای WireGuard",
    "Update tunnel": "به‌روزرسانی تانل", "SNI ": "SNI",
    "Use it after getting a new server IP or to rotate keys. Then copy the new token to the Iran server.": "بعد از گرفتن آی‌پی جدید یا برای چرخش کلیدها استفاده کنید. سپس توکن جدید را در سرور ایران وارد کنید.",
    "Use it after getting a new server IP or to rotate keys. Make the same change on the foreign server, then Sync token.": "بعد از گرفتن آی‌پی جدید یا برای چرخش کلیدها استفاده کنید. همین تغییر را در سرور خارج هم بدهید، سپس توکن را Sync کنید.",
    "Network speed (BBR)": "سرعت شبکه (BBR)", "Enable BBR": "فعال‌سازی BBR", "BBR on": "BBR فعال",
    "BBR usually gives better throughput on long, lossy links.": "BBR معمولاً روی لینک‌های طولانی و پرلاس سرعت بهتری می‌دهد.",
    "Panel password": "رمز پنل", "New password": "رمز جدید", "Repeat": "تکرار", "Change password": "تغییر رمز",
    "At least 8 characters. The panel login user stays the same.": "حداقل ۸ کاراکتر. نام کاربری پنل تغییر نمی‌کند.",
    "Maintenance": "نگهداری", "Check for update": "بررسی آپدیت", "Update night-tunnel": "آپدیت night-tunnel",
    "Update engine (gost)": "آپدیت موتور (gost)", "Update the script?": "اسکریپت آپدیت شود؟", "Update gost?": "gost آپدیت شود؟",
    "Restart tunnel": "ری‌استارت تانل", "Danger zone": "منطقه خطر", "Type DELETE to confirm.": "برای تأیید DELETE را تایپ کنید.",
    "Delete tunnel config (keep installed)": "حذف کانفیگ تانل (نصب بماند)", "also remove gost binary": "فایل gost هم حذف شود",
    "Uninstall night-tunnel completely": "حذف کامل night-tunnel",
    "UDP transports are not probed": "ترنسپورت‌های UDP تست نمی‌شوند", "Installed version": "نسخه نصب‌شده", "Last run": "آخرین اجرا",
    "Current congestion control": "الگوریتم فعلی کنترل ازدحام", "Failover": "فیل‌اور", "Random": "تصادفی",
    # wizard
    "Easy setup finished": "نصب آسان تمام شد", "Dismiss": "بستن", "Shown once - save it now.": "فقط یک‌بار نشان داده می‌شود؛ همین حالا ذخیره کنید.",
    "Other server's panel": "پنل سرور مقابل", "User": "کاربر", "Password": "رمز",
    "Setting up...": "در حال نصب...", "This page updates by itself. It can take a few minutes.": "این صفحه خودکار به‌روز می‌شود. ممکن است چند دقیقه طول بکشد.",
    "This server is the": "این سرور،", "Iran (entry) server": "سرور ایران (ورودی)", "foreign (exit) server": "سرور خارج (خروجی)",
    "IP of the OTHER server": "آی‌پی سرور مقابل", "SSH port": "پورت SSH", "SSH user": "یوزر SSH",
    "SSH password of the other server": "رمز SSH سرور مقابل", "or SSH key file on this server": "یا فایل کلید SSH روی همین سرور",
    "With password (encrypted, recommended)": "با رمز (رمزگذاری‌شده، پیشنهادی)", "No password (limited to the Iran IP)": "بدون رمز (محدود به IP ایران)",
    "Ports to forward on the Iran server": "پورت‌های فوروارد روی سرور ایران", "Ports that also need UDP (optional)": "پورت‌هایی که UDP هم می‌خواهند (اختیاری)",
    "Overwrite an existing night-tunnel config on the other server": "کانفیگ قبلی night-tunnel روی سرور مقابل بازنویسی شود",
    "Build the tunnel automatically": "ساخت خودکار تانل",
    "Give the other server's IP and root SSH login. This server installs night-tunnel there, creates both sides of the tunnel and runs a first test. The SSH password is used once and not stored.": "آی‌پی سرور مقابل و لاگین root آن را بدهید. این سرور night-tunnel را آنجا نصب می‌کند، هر دو سمت تانل را می‌سازد و یک تست اولیه می‌زند. پسورد SSH یک‌بار استفاده می‌شود و ذخیره نمی‌شود.",
}

FA_TEXT.update({
    "Servers": "سرورها", "Add a destination server": "افزودن سرور مقصد", "Add server": "افزودن سرور",
    "Name": "نام", "Server IP": "آی‌پی سرور", "Server": "سرور", "Remove": "حذف", "New code": "کد جدید",
    "You get ONE command to run once on that server. It installs night-tunnel there, builds every tunnel model and connects back here by itself. No SSH and no password are given to this panel.": "یک دستور می‌گیرید که فقط یک‌بار روی آن سرور اجرا می‌کنید. night-tunnel را همان‌جا نصب می‌کند، همه‌ی مدل‌های تانل را می‌سازد و خودش به این پنل وصل می‌شود. هیچ SSH یا رمزی به این پنل داده نمی‌شود.",
    "Waiting for the server": "منتظر سرور", "Joined": "متصل شد", "Tested": "تست شد", "Tunnel active": "تانل فعال",
    "Run this ONE line as root on that server (Debian/Ubuntu):": "این یک خط را با کاربر root روی آن سرور (Debian/Ubuntu) اجرا کنید:",
    "The server could not connect? Paste its token": "سرور نتوانست وصل شود؟ توکنش را پیست کنید",
    "Token printed on that server": "توکنی که روی آن سرور چاپ شد", "Use token": "استفاده از توکن",
    "Test speed & stability": "تست سرعت و پایداری", "Quick test": "تست سریع",
    "A test is running. Watch it in the Test tab.": "تست در حال اجراست. در تب Test دنبال کنید.",
    "Tests run through the real tunnels: connection, latency, stability (16 probes) and real speed.": "تست از داخل تانل‌های واقعی انجام می‌شود: اتصال، تأخیر، پایداری (۱۶ پروب) و سرعت واقعی.",
    "Build the tunnel": "ساخت تانل", "Tunnel type": "نوع تانل", "Create tunnel": "ساخت تانل",
    "Keep the other working tunnels as backup": "بقیه‌ی تانل‌های سالم به‌عنوان پشتیبان بمانند",
    "We suggest the best one, but you decide. Compare everything in the Test tab. The destination server is configured automatically.": "بهترین گزینه پیشنهاد می‌شود ولی انتخاب با شماست. همه‌چیز را در تب Test مقایسه کنید. سرور مقصد خودکار تنظیم می‌شود.",
    "Setting up...": "در حال نصب...", "Stability": "پایداری",
    "No server yet. Add the destination (exit) server above.": "هنوز سروری نیست. سرور مقصد (خروجی) را بالا اضافه کنید.",
    "Stability = how steady the connection was over 16 probes (loss and jitter). Speed tests use real bandwidth for about 10 seconds per tunnel. Only tunnels the foreign server has built are tested: to compare every model use Test, Build every tunnel model on the foreign panel, then Sync token here.": "پایداری = ثبات اتصال در ۱۶ پروب (افت بسته و جیتر). تست سرعت حدود ۱۰ ثانیه برای هر تانل از پهنای باند واقعی استفاده می‌کند. فقط تانل‌هایی تست می‌شوند که سرور خارج ساخته است.",
    "Excellent": "عالی", "Good": "خوب", "OK": "قابل‌قبول", "Weak": "ضعیف", "Failed": "ناموفق",
    "Main": "اصلی", "Backup": "پشتیبان", "In use": "در حال استفاده", "Verdict": "ارزیابی", "Choose": "انتخاب",
    "Use as main": "انتخاب به‌عنوان اصلی", "Use only this": "فقط همین",
    "Send my ports through it": "پورت‌های من از این رد شوند", "not encrypted": "رمزگذاری‌نشده",
    "Switch off every other tunnel and use only this one? (no backup if it fails)": "بقیه تانل‌ها خاموش شوند و فقط همین استفاده شود؟ (اگر قطع شود پشتیبانی نیست)",
    "Send all forwarded ports through this kernel tunnel? (no obfuscation, no failover)": "همه پورت‌ها از این تانل کرنلی رد شوند؟ (بدون ابفیوسکیشن و بدون فیل‌اور)",
    "Best for you": "بهترین گزینه برای شما",
    "Use it as main (others stay as backup)": "انتخاب به‌عنوان اصلی (بقیه پشتیبان می‌مانند)",
    "Use only this one": "فقط همین یکی",
    "The fastest working tunnel of the last test. Check the Encrypted column too: fast does not always mean safe from filtering.": "سریع‌ترین تانل سالم در آخرین تست. ستون «رمزگذاری» را هم ببینید: سریع بودن همیشه به معنی در امان بودن از فیلتر نیست.",
    "Send kernel-routed ports back to the relay pool": "پورت‌های کرنلی به استخر ریلی برگردند",
    "Speed tests use real bandwidth for about 10 seconds per tunnel. Only tunnels the foreign server has built are tested: to compare every model use Test, Build every tunnel model on the foreign panel, then Sync token here.": "تست سرعت حدود ۱۰ ثانیه برای هر تانل از پهنای باند واقعی استفاده می‌کند. فقط تانل‌هایی تست می‌شوند که سرور خارج ساخته است: برای مقایسه‌ی همه‌ی مدل‌ها در پنل سرور خارج بخش تست ← «ساخت همه‌ی مدل‌ها» را بزنید، بعد اینجا توکن را Sync کنید.",
    "Compare every tunnel model": "مقایسه‌ی همه‌ی مدل‌های تانل",
    "Build every tunnel model for testing": "ساخت همه‌ی مدل‌های تانل برای تست",
    "Build and enable every tunnel model? You must copy the new token to the Iran server afterwards.": "همه‌ی مدل‌های تانل ساخته و فعال شوند؟ بعدش باید توکن جدید را در سرور ایران وارد کنید.",
    "Every tunnel model is already built. Run the test on the Iran server.": "همه‌ی مدل‌ها از قبل ساخته شده‌اند. تست را روی سرور ایران اجرا کنید.",
    "1) Build all models here. 2) Copy the new token to the Iran server (Token tab, Sync). 3) Run the test in the Iran panel and pick the winner. 4) Switch off the models you do not use afterwards.": "۱) همه‌ی مدل‌ها را اینجا بسازید. ۲) توکن جدید را در سرور ایران Sync کنید. ۳) در پنل ایران تست بگیرید و برنده را انتخاب کنید. ۴) بعدش مدل‌های بلااستفاده را خاموش کنید.",
    "Open Token tab": "باز کردن توکن", "Setup finished": "نصب تمام شد",
    "Manual setup": "نصب دستی", "Manual setup: foreign (exit) server": "نصب دستی: سرور خارج (خروجی)",
    "Manual setup: Iran (entry) server": "نصب دستی: سرور ایران (ورودی)",
    "Same as menu 1 in the terminal. Build this side first, then copy its token to the Iran server. No SSH access needed.": "معادل منوی ۱ ترمینال. اول این سمت را بسازید، بعد توکنش را در سرور ایران وارد کنید. به SSH نیازی نیست.",
    "Same as menu 2 in the terminal. Paste the token from the foreign server.": "معادل منوی ۲ ترمینال. توکن سرور خارج را پیست کنید.",
    "Iran server IP": "آی‌پی سرور ایران", "Domain pointing to this server (optional, real SSL)": "دامنه‌ی متصل به این سرور (اختیاری، SSL واقعی)",
    "Domain pointing to this server (optional)": "دامنه‌ی متصل به این سرور (اختیاری)",
    "Decoy SNI (used when there is no domain)": "SNI پوششی (وقتی دامنه ندارید)", "Security": "امنیت",
    "Tunnels to build": "تانل‌هایی که ساخته شوند",
    "Recommended set (balanced + WireGuard backup)": "مجموعه‌ی پیشنهادی (متعادل + پشتیبان WireGuard)",
    "Every model (best for comparing speeds)": "همه‌ی مدل‌ها (مناسب مقایسه‌ی سرعت)",
    "Only the ones I tick below": "فقط مواردی که پایین تیک می‌زنم",
    "This server's public IP (only if it cannot be detected)": "آی‌پی عمومی این سرور (فقط اگر خودکار پیدا نشد)",
    "Pick tunnels": "انتخاب تانل‌ها", "Create foreign (exit) side": "ساخت سمت خارج (خروجی)",
    "Token from the foreign server": "توکن سرور خارج", "Ports to forward on this server": "پورت‌های فوروارد روی این سرور",
    "Create Iran (entry) side": "ساخت سمت ایران (ورودی)",
})

JS = JS_TPL.replace("__FA__", json.dumps(FA_TEXT, ensure_ascii=False))


# ---- helpers: status, logs, icons, small components
MODE_LABEL = {"fifo": "Failover", "round": "Rotate", "rand": "Random"}
SVCS = {"gost": "night-tunnel-gost", "l3": "night-tunnel-l3", "panel": "night-tunnel-panel", "tg": "night-tunnel-tg"}
ICONS = {
    "home": "<path d='M3 11l9-8 9 8v10a1 1 0 0 1-1 1h-5v-7H9v7H4a1 1 0 0 1-1-1z'/>",
    "layers": "<path d='M12 2l10 5-10 5L2 7z'/><path d='M2 17l10 5 10-5'/><path d='M2 12l10 5 10-5'/>",
    "swap": "<path d='M4 7h14l-3-3M20 17H6l3 3'/>",
    "tunnel": "<path d='M3 12h4l3-8 4 16 3-8h4'/>",
    "key": "<circle cx='8' cy='15' r='4'/><path d='M11 12l9-9M16 7l3 3'/>",
    "gauge": "<path d='M12 14l4-4'/><path d='M3.3 17a10 10 0 1 1 17.4 0'/>",
    "send": "<path d='M22 2L11 13'/><path d='M22 2l-7 20-4-9-9-4z'/>",
    "shield": "<path d='M12 22s8-4 8-10V5l-8-3-8 3v7c0 6 8 10 8 10z'/>",
    "terminal": "<path d='M4 17l6-6-6-6M12 19h8'/>",
    "settings": "<path d='M4 21v-7M4 10V3M12 21v-9M12 8V3M20 21v-5M20 12V3M1 14h6M9 8h6M17 16h6'/>",
    "wand": "<path d='M15 4V2M15 16v-2M8 9h2M20 9h2M17.8 11.8L19 13M17.8 6.2L19 5M3 21l9-9M12.2 6.2L11 5'/>",
}
MOON = ("<svg viewBox='0 0 24 24' fill='none' stroke='#fff' stroke-width='2' stroke-linecap='round' "
        "stroke-linejoin='round'><path d='M21 12.8A9 9 0 1 1 11.2 3a7 7 0 0 0 9.8 9.8z'/></svg>")


def ico(n):
    return (f"<svg class=ic viewBox='0 0 24 24' fill=none stroke=currentColor stroke-width=2 stroke-linecap=round "
            f"stroke-linejoin=round>{ICONS[n]}</svg>")


def svc_states():
    out = sh("systemctl is-active " + " ".join(SVCS.values())).stdout.split()
    s = dict(zip(SVCS, out)) if len(out) == len(SVCS) else {k: "unknown" for k in SVCS}
    if not tg_load():
        s["tg"] = "off"
    return s


def wg_age(st):
    if "wg" not in (st.get("l3") or {}):
        return ""
    out = sh(f"wg show {DEV['wg']} latest-handshakes").stdout.split()
    try:
        ts = max(int(x) for x in out[1::2])
    except ValueError:
        return "no handshake yet"
    if ts <= 0:
        return "no handshake yet"
    age = max(0, int(time.time()) - ts)
    return f"{age}s ago" if age < 120 else f"{age // 60}m ago"


def status_json(st):
    pr = probe_all(st) if st["role"] != "new" else {}
    last = lambda lg: (lg[-1] if lg else "").lstrip(ERR)
    return json.dumps({"svc": svc_states(), "tp": pr, "wg": wg_age(st),
                       "bench": {"running": BENCH_STATE["running"], "log": last(BENCH_STATE["log"]),
                         "live": "\n".join(BENCH_STATE.get("live", [])),
                         "pct": int(100 * BENCH_STATE.get("done", 0) / BENCH_STATE["total"])
                         if BENCH_STATE.get("total") else 0},
                       "wiz": {"running": WIZ["running"], "log": "\n".join(WIZ["log"])}})


def read_logs(svc, n):
    unit = SVCS.get(svc)
    if not unit:
        return "Unknown service."
    try:
        n = max(10, min(int(n), 500))
    except (TypeError, ValueError):
        n = 100
    r = sh(f"journalctl -u {unit} -n {n} --no-pager -o short-iso")
    return (r.stdout or r.stderr).strip() or "(no log lines)"


def esc(x):
    return html.escape(str(x))


def pill(state, **attrs):
    a = "".join(f" data-{k}='{esc(v)}'" for k, v in attrs.items())
    return f"<span class='pill {esc(state)}'{a}>{esc(state)}</span>"


def form(vals, inner, confirm="", cls=""):
    hid = "".join(f"<input type=hidden name={k} value='{esc(v)}'>" for k, v in vals.items())
    c = f" data-c='{esc(confirm)}'" if confirm else ""
    return f"<form method=post action=api class='{cls}'{c}>{hid}{inner}</form>"


def fld(label, inner):
    return f"<label class=f><span>{label}</span>{inner}</label>"


def tdesc(t):
    return desc(t).replace(" [enc]", "").replace(" [plain]", "")


def encpill(t):
    return "<span class='pill up'>encrypted</span>" if enc_of(t) == "yes" else "<span class='pill udp'>plain</span>"


def card(title, body, hint="", cls=""):
    h = f"<p class=hint>{hint}</p>" if hint else ""
    t = f"<h2>{title}</h2>" if title else ""
    return f"<div class='card {cls}'>{t}{h}{body}</div>"


def vsel(st, cur):
    return ("<select name=via><option value=pool>relay pool</option>" + "".join(
        f"<option value={k} {'selected' if cur == k else ''}>kernel: {CARRIERS[k][0]}</option>"
        for k in (st.get("l3") or {})) + "</select>")


# ---- tabs
def render_overview(st, states, pr):
    iran = st["role"] == "iran"
    up = sum(1 for v in pr.values() if v == "up")
    tcp = sum(1 for v in pr.values() if v != "udp")
    udp = len(pr) - tcp

    def stat(k, v, s=""):
        return f"<div class=stat><div class=k>{k}</div><div class=v>{v}</div><div class=s>{s}</div></div>"
    l3 = st.get("l3") or {}
    s = [stat("Engine (gost)", pill(states["gost"], svc="gost"), "Relay pool"),
         stat("Kernel links", pill(states["l3"], svc="l3") if l3 else "<span class='pill plain'>none</span>",
              esc(", ".join(CARRIERS[k][0] for k in l3))),
         stat("Telegram proxy", pill(states["tg"], svc="tg"), "MTProto"),
         stat("Security", "<span class='pill up'>password</span>" if is_secure(st)
              else "<span class='pill udp'>IP-locked</span>",
              "Relay login required" if is_secure(st) else "Only the Iran IP is allowed"),
         stat("Transports up", f"<span data-upcount>{up}</span>&nbsp;/&nbsp;{tcp}",
              f"<span class=mono>{udp}</span> <span>UDP transports are not probed</span>" if udp else "")]
    if iran:
        ports = st.get("ports", [])
        s.append(stat("Forwarded ports", len(ports), esc(", ".join(str(p["port"]) for p in ports[:8]))))
    else:
        s.append(stat("Tunnels", len(st["transports"]), ""))
    rows = "".join(
        f"<tr><td><b>{esc(t['id'])}</b></td><td class=mu>{esc(tdesc(t))}</td><td class=mono>{t['port']}</td>"
        f"<td>{encpill(t)}</td><td>{pill(pr.get(t['id'], 'down'), tp=t['id'])}</td></tr>"
        for t in st["transports"])
    health = card("Transport health",
                  "<div class=scroll><table class=tbl><tr><th>Tunnel</th><th>Type</th><th>Port</th><th>Data</th>"
                  f"<th>State</th></tr>{rows}</table></div>")
    wg = wg_age(st)
    info = ("<dl class=kv><dt>Role</dt><dd>" + ("Iran (entry)" if iran else "Foreign (exit)") + "</dd>"
            f"<dt>Foreign IP</dt><dd class=mono>{esc(st.get('foreign_ip', '-'))}</dd>"
            f"<dt>Iran IP</dt><dd class=mono>{esc(st.get('iran_ip', '-'))}</dd>"
            f"<dt>Mode</dt><dd>{MODE_LABEL.get(st.get('strategy', 'fifo'), 'Failover')}</dd>"
            + (f"<dt>WireGuard handshake</dt><dd id=wg>{esc(wg)}</dd>" if wg else "")
            + f"<dt>Version</dt><dd class=mono>v{VERSION}</dd></dl>")
    q = "<div class=row>" + form({"a": "restart"}, "<button class='btn g'>Restart tunnel services</button>")
    if iran:
        q += form({"a": "test", "full": "0"}, "<button class=btn>Quick connection test</button>")
    q += "<button type=button class='btn g' data-tab=logs>View logs</button></div>"
    return (render_wiz_result() + f"<div class=grid>{''.join(s)}</div>" + health
            + "<div class=grid style='grid-template-columns:repeat(auto-fit,minmax(300px,1fr))'>"
            + card("Server", info) + card("Quick actions", q) + "</div>")


def render_transports(st, pr):
    rows = ""
    for i, t in enumerate(st["transports"]):
        rows += (f"<tr><td><label class=sw><input type=checkbox name='en_{t['id']}' "
                 f"{'checked' if t['enabled'] else ''}><i></i></label></td>"
                 f"<td><input class=w-xs name='pr_{t['id']}' value='{i + 1}' inputmode=decimal></td>"
                 f"<td><b>{esc(t['id'])}</b></td><td class=mu>{esc(tdesc(t))}</td><td class=mono>{t['port']}</td>"
                 f"<td>{encpill(t)}</td><td>{pill(pr.get(t['id'], 'down'), tp=t['id'])}</td></tr>")
    strat = "".join(f"<option value={v} {'selected' if st.get('strategy') == v else ''}>{l}</option>"
                    for v, l in (("fifo", "Failover (priority order)"),
                                 ("round", "Rotate (round-robin per connection)"),
                                 ("rand", "Random per connection")))
    pool = card("Transport pool",
                form({"a": "save"},
                     "<div class=scroll><table class=tbl><tr><th>On</th><th>Priority</th><th>ID</th><th>Type</th>"
                     f"<th>Port</th><th>Data</th><th>State</th></tr>{rows}</table></div>"
                     "<div class=row style='margin-top:14px'>"
                     + fld("Mode", f"<select name=strategy>{strat}</select>")
                     + "<button class=btn>Save &amp; apply</button></div>"),
                "Turn transports on or off and set their order. Lower priority number = tried first.")
    pre = card("Presets", form({"a": "preset"},
               "<div class=presets>"
               "<button class=preset name=n value=balanced><b>Balanced</b><small>Mixed transports with a backup</small></button>"
               "<button class=preset name=n value=stealth><b>Stealth</b><small>Looks like normal TLS / web traffic</small></button>"
               "<button class=preset name=n value=game><b>Gaming</b><small>UDP transports first</small></button>"
               "<button class=preset name=n value=rotate><b>Rotate</b><small>Spread connections over everything</small></button>"
               "</div>"), "One click re-orders and enables a sensible set.")
    return pool + pre


def render_ports(st):
    items = ""
    for p in st.get("ports", []):
        sel = "".join(f"<option {'selected' if p['proto'] == x else ''}>{x}</option>" for x in ("tcp", "udp", "both"))
        items += ("<div class=item>"
                  + form({"a": "editport", "old": p["port"]},
                         fld("Port", f"<input name=port value={p['port']} class=w-s>")
                         + fld("Protocol", f"<select name=proto>{sel}</select>")
                         + fld("Remote port", f"<input name=target value='{esc(p.get('target', ''))}' placeholder=same class=w-s>")
                         + fld("Path", vsel(st, p.get("via", "")))
                         + "<button class='btn g'>Save</button>", cls="row")
                  + form({"a": "delport", "port": p["port"]}, "<button class='btn d s'>Delete</button>",
                         confirm="Delete this port?")
                  + "</div>")
    if not items:
        items = "<p class=hint>No forwarded ports yet.</p>"
    add = form({"a": "addport"},
               fld("Port", "<input name=port placeholder=443 class=w-s>")
               + fld("Protocol", "<select name=proto><option>tcp</option><option>udp</option><option>both</option></select>")
               + fld("Remote port", "<input name=target placeholder=same class=w-s>")
               + fld("Path", vsel(st, "")) + "<button class=btn>Add port</button>", cls="row")
    return (card("Forwarded ports", items, "Each port on this server goes to 127.0.0.1 on the foreign server.")
            + card("Add a port", add))


def render_tunnels(st):
    items = ""
    for t in st["transports"]:
        tt = ttype(t)
        f = ""
        if t["via"] == "direct":
            topts = "".join(f"<option {'selected' if k == tt else ''}>{k}</option>" for k in CATALOG)
            f += fld("Type", f"<select name=new_type>{topts}</select>")
        f += fld("Port", f"<input name=port value={t['port']} class=w-s>")
        if t["via"] == "direct" and tt in TLS_DIALERS:
            f += fld("SNI", f"<input name=sni value='{esc(t.get('sni', ''))}' placeholder=global class=w-m>")
        if t["via"] == "direct" and tt in WS_TYPES:
            f += (fld("Path", f"<input name=path value='{esc(t.get('path', ''))}' placeholder=/ws class=w-s>")
                  + fld("Host", f"<input name=host value='{esc(t.get('host', ''))}' class=w-m>"))
        items += ("<div class=item><div class=hd><b>" + esc(t["id"]) + "</b>" + encpill(t)
                  + f"<span class=mu>{esc(tdesc(t))}</span></div>"
                  + form({"a": "tpedit", "id": t["id"]}, f + "<button class='btn g'>Save</button>", cls="row")
                  + form({"a": "tpdel", "id": t["id"]}, "<button class='btn d s'>Delete</button>",
                         confirm="Delete this tunnel?") + "</div>")
    og = ""
    for layer, ids in LAYERS:
        og += f"<optgroup label='{layer}'>" + "".join(
            f"<option value={k}>{k} - {CATALOG[k][2] if k in CATALOG else CARRIERS[k][0] + ' (kernel)'}</option>"
            for k in ids if k in CATALOG or (k in CARRIERS and k not in st.get("l3", {}))) + "</optgroup>"
    add = form({"a": "tpadd"},
               fld("Type", f"<select name=id>{og}</select>") + fld("Name", "<input name=name placeholder='same as type' class=w-m>")
               + fld("Port", "<input name=port placeholder=random class=w-s>") + fld("SNI", "<input name=sni class=w-m>")
               + fld("Path", "<input name=path class=w-s>") + fld("Host", "<input name=host class=w-m>")
               + "<button class=btn>Build tunnel</button>", cls="row")
    return (card("Your tunnels", items, "Change a port, type, SNI, path or host. After any change copy the new token to the Iran server.")
            + card("Build a new tunnel", add,
                   "You can build several tunnels of one type (use different names, ports or SNI). "
                   "Kernel tunnels (L3) can also be used as direct port paths on the Iran server."))


def render_token(st):
    if st["role"] == "foreign":
        return card("Token for the Iran server",
                    "<div class=copy><textarea id=tok readonly>" + esc(make_token(st)) + "</textarea></div>"
                    "<p><button type=button class='btn g s' data-copy='#tok'>Copy</button></p>",
                    "On the Iran server open Token and import this value (Sync token). Do it after every change here.")
    return card("Sync token",
                form({"a": "importtoken"}, "<textarea name=token placeholder='NT1:...'></textarea>"
                     "<p><button class=btn>Import token</button></p>"),
                "Paste the token from the foreign server's panel after you change anything there.")


BV_LABEL = {"excellent": "Excellent", "good": "Good", "ok": "OK", "weak": "Weak", "failed": "Failed"}
BV_CLS = {"excellent": "up", "good": "up", "ok": "udp", "weak": "down", "failed": "down"}


def bpill(v):
    return f"<span class='pill {BV_CLS[v]}'>{BV_LABEL[v]}</span>"


def use_forms(name, kernel=False):
    if kernel:
        return form({"a": "usetunnel", "name": name, "only": "0"}, "<button class='btn g s'>Send my ports through it</button>",
                    confirm="Send all forwarded ports through this kernel tunnel? (no obfuscation, no failover)", cls="inl")
    return (form({"a": "usetunnel", "name": name, "only": "0"}, "<button class='btn s'>Use as main</button>", cls="inl")
            + form({"a": "usetunnel", "name": name, "only": "1"}, "<button class='btn g s'>Use only this</button>",
                   confirm="Switch off every other tunnel and use only this one? (no backup if it fails)", cls="inl"))


def render_bench_foreign(st):
    have = {t["id"] for t in st["transports"]} | set(st.get("l3") or {})
    missing = [k for k in list(CATALOG) + list(CARRIERS) if k not in have]
    top = card("Test tunnels", "", "Run the test from the Iran server's panel (the entry side). "
                                   "This server answers the test automatically.")
    if missing:
        body = (f"<p>{len(st['transports'])} tunnel(s) are built. Not built yet: <span class=mono>{esc(', '.join(missing))}</span></p>"
                + form({"a": "allmodels"}, "<button class=btn>Build every tunnel model for testing</button>",
                       confirm="Build and enable every tunnel model? You must copy the new token to the Iran server afterwards."))
    else:
        body = "<p>Every tunnel model is already built. Run the test on the Iran server.</p>"
    return top + card("Compare every tunnel model", body,
                      "1) Build all models here. 2) Copy the new token to the Iran server (Token tab, Sync). "
                      "3) Run the test in the Iran panel and pick the winner. 4) Switch off the models you do not use afterwards.")


def render_bench(st):
    if st["role"] != "iran":
        return render_bench_foreign(st)
    hint = ("Stability = how steady the connection was over 16 probes (loss and jitter). Speed tests use real bandwidth for about 10 seconds per tunnel. Only tunnels the foreign server has built are "
            "tested: to compare every model use Test, Build every tunnel model on the foreign panel, then Sync token here.")
    body = ""
    if BENCH_STATE["running"]:
        last = (BENCH_STATE["log"][-1] if BENCH_STATE["log"] else "starting").lstrip(ERR)
        tot = BENCH_STATE.get("total") or 0
        pct = int(100 * BENCH_STATE.get("done", 0) / tot) if tot else 0
        body += (f"<div class=flash><span class=dot></span><span id=benchlog>{esc(last)}</span></div>"
                 f"<div class=bar><i id=benchbar style='width:{pct}%'></i></div>"
                 f"<pre class=log id=benchlive>{esc(chr(10).join(BENCH_STATE.get('live', [])))}</pre>")
    else:
        err = next((x for x in reversed(BENCH_STATE["log"]) if x.startswith(ERR)), "")
        if err:
            body += f"<div class='flash e'>{esc(err.lstrip(ERR))}</div>"
        body += ("<div class=row>" + form({"a": "test", "full": "1"}, "<button class=btn>Full test (connect + speed)</button>")
                 + form({"a": "test", "full": "0"}, "<button class='btn g'>Quick test (connect + latency)</button>") + "</div>")
    try:
        with open(BENCH) as f:
            rep = json.load(f)
    except (OSError, ValueError):
        return card("Test tunnels", body, hint)
    active = [t["id"] for t in st["transports"] if t["enabled"]]
    kports = {p["via"] for p in st.get("ports", []) if p.get("via")}
    fifo = st.get("strategy", "fifo") == "fifo"
    ok = [r for r in rep["results"] if r["ok"]]
    topscore = max((r.get("score", 0) for r in ok), default=0) or 1
    rows = ""
    for r in sorted(rep["results"], key=lambda r: -r.get("score", 0)):
        nm, kern = r["name"], r.get("kind") == "kernel"
        mark = ""
        if kern and nm.replace("kernel:", "") in kports:
            mark = " <span class='pill up'>In use</span>"
        elif not kern and nm in active:
            mark = (" <span class='pill up'>Main</span>" if nm == active[0] else " <span class='pill plain'>Backup</span>") if fifo \
                else " <span class='pill up'>In use</span>"
        if r["ok"]:
            openp = r.get("auth") == "OPEN"
            pct = int(100 * r.get("score", 0) / topscore)
            rows += (f"<tr><td><b>{esc(nm)}</b>{mark}</td><td class=mu>{esc(r['layer'])}</td><td>{bpill(bench_verdict(r))}</td>"
                     f"<td>{r['rtt']}</td><td>{r['jitter']}</td><td>{int(r['loss'] * 100)}%</td>"
                     f"<td><b>{bench_stab(r)}%</b></td><td>{r.get('down', '-')}</td><td>{r.get('up', '-')}</td><td>{esc(r.get('enc', '-'))}</td>"
                     f"<td><span class='pill {'down' if openp else 'up'}'>{esc(r.get('auth', '-'))}</span></td>"
                     f"<td><b>{r.get('score', '-')}</b><div class=bar><i style='width:{pct}%'></i></div></td>"
                     f"<td>{use_forms(nm, kern)}</td></tr>")
        else:
            rows += (f"<tr><td><b>{esc(nm)}</b></td><td class=mu>{esc(r['layer'])}</td><td>{bpill('failed')}</td>"
                     f"<td colspan=9 class=mu>{esc(r.get('err', ''))}</td><td></td></tr>")
    when = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(rep["ts"]))
    body += (f"<p class=hint><span>Last run</span>: {when}</p><div class=scroll><table class=tbl><tr><th>Tunnel</th><th>Layer</th>"
             "<th>Verdict</th><th>RTT ms</th><th>Jitter</th><th>Loss</th><th>Stability</th><th>Down Mb/s</th><th>Up Mb/s</th>"
             f"<th>Encrypted</th><th>Password</th><th>Score</th><th>Choose</th></tr>{rows}</table></div>")
    hero = ""
    best = None if BENCH_STATE["running"] else bench_best(rep)
    if best:
        b = next(r for r in rep["results"] if r["name"] == best)
        sp = f"down {b['down']} / up {b['up']} Mb/s, " if "down" in b else ""
        warn = " <span class='pill udp'>not encrypted</span>" if b.get("enc") == "no" else ""
        hero = card("Best for you",
                    f"<p><b class=mono>{esc(best)}</b> {bpill(bench_verdict(b))}{warn} "
                    f"<span class=mu>{sp}latency {b['rtt']} ms, loss {int(b['loss'] * 100)}%</span></p><div class=row>"
                    + form({"a": "usebest", "only": "0"}, "<button class=btn>Use it as main (others stay as backup)</button>")
                    + form({"a": "usebest", "only": "1"}, "<button class='btn g'>Use only this one</button>",
                           confirm="Switch off every other tunnel and use only this one? (no backup if it fails)") + "</div>",
                    "The fastest working tunnel of the last test. Check the Encrypted column too: fast does not always mean safe from filtering.",
                    cls="ok")
    out = card("Test tunnels", body, hint)
    rec = "<ul class=rec>" + "".join(f"<li>{esc(x)}</li>" for x in rep["rec"]["lines"]) + "</ul>"
    if rep["rec"]["order"] and not BENCH_STATE["running"]:
        rec += form({"a": "benchapply"}, "<p><button class=btn>Apply suggested order</button></p>",
                    confirm="Enable only the working tunnels in the suggested order?")
    if kports:
        rec += form({"a": "usetunnel", "name": "pool"}, "<p><button class='btn g'>Send kernel-routed ports back to the relay pool</button></p>")
    return hero + out + card("Recommendation", rec)


def render_security(st):
    if is_secure(st):
        txt = ("<span class='pill up'>With password</span><p>Relay login is required. TLS / QUIC / WireGuard tunnels are "
               "encrypted. Plain tunnels (tcp, ws, kcp, udp, ...) are authenticated but carry data unencrypted.</p>")
    else:
        txt = ("<span class='pill udp'>No password</span><p class=mu>No relay login. The foreign server only accepts the "
               f"Iran server's IP (<span class=mono>{esc(st['iran_ip'])}</span>); plain tunnels carry data unencrypted.</p>")
    if st["role"] == "foreign":
        txt += form({"a": "security", "mode": "open" if is_secure(st) else "password"},
                    "<button class='btn g'>" + ("Switch to NO password" if is_secure(st) else "Switch to password mode")
                    + "</button>", confirm="Change the security mode? Then copy the new token to the Iran server.")
    else:
        txt += "<p class=hint>Change it on the foreign server, then Sync token here.</p>"
    return card("Security mode", txt)


def render_tg(st):
    t = tg_status()
    if t:
        ok = t["active"]
        body = ("<dl class=kv><dt>State</dt><dd>" + pill(ok, svc="tg") + f"</dd><dt>Port</dt><dd class=mono>{t['port']}</dd>"
                f"<dt>Cover domain</dt><dd class=mono>{esc(t['host'])}</dd></dl>"
                "<div style='margin-top:16px;display:grid;gap:10px'>"
                f"<div class=copy><input id=tglink readonly value='{esc(t['links']['https'])}'>"
                "<button type=button class='btn g s' data-copy='#tglink'>Copy</button></div>"
                f"<div class=copy><input id=tglink2 readonly value='{esc(t['links']['tg'])}'>"
                "<button type=button class='btn g s' data-copy='#tglink2'>Copy</button></div></div>"
                "<div class=row style='margin-top:16px'>"
                + form({"a": "tgrestart"}, "<button class='btn g'>Restart</button>")
                + form({"a": "tgrotate"}, "<button class='btn g'>New secret</button>",
                       confirm="Old links will stop working. Continue?")
                + "<button type=button class='btn g' data-gologs=tg>View logs</button>"
                + form({"a": "tgremove"}, "<button class='btn d'>Remove proxy</button>",
                       confirm="Remove the Telegram proxy?") + "</div>")
        edit = form({"a": "tgedit"},
                    fld("Port", f"<input name=port value={t['port']} class=w-s>")
                    + fld("Cover domain", f"<input name=host value='{esc(t['host'])}' class=w-l>")
                    + "<button class=btn>Apply</button>", cls="row")
        return (card("Telegram proxy (MTProto, fake-TLS)", body,
                     "Runs on this server, independent of the tunnels. Share the link with people who need it.")
                + card("Change port or cover domain", edit, "The secret is regenerated, so share the new link afterwards."))
    ip = st["panel"].get("host", "")
    ip = ip if valid_ip(ip) else ""
    create = form({"a": "tgcreate"},
                  fld("Server IP", f"<input name=ip value='{esc(ip)}' class=w-m placeholder='203.0.113.10'>")
                  + fld("Port", "<input name=port value=443 class=w-s>")
                  + fld("Cover domain", "<input name=host value='www.microsoft.com' class=w-l>")
                  + "<button class=btn>Create proxy</button>", cls="row")
    return card("Telegram proxy (MTProto, fake-TLS)", create,
                "Runs on this server, independent of the tunnels. Use a server that can reach Telegram "
                "(usually the foreign one). You get a link to share.")


def render_logs():
    segs = "".join(f"<button type=button class=seg data-log={k}>{l}</button>"
                   for k, l in (("gost", "Engine"), ("l3", "Kernel links"), ("panel", "Panel"), ("tg", "Telegram")))
    return card("Logs", f"<div class=row>{segs}<span class=grow></span>"
                "<select id=logn><option>50</option><option selected>100</option><option>300</option></select>"
                "<button type=button class='btn g s' data-reload=1>Refresh</button></div><pre class=log id=logbox></pre>",
                "Latest lines from the systemd journal.")


def render_update(st):
    f = st["role"] == "foreign"
    return card("Update tunnel settings",
                form({"a": "updtunnel"},
                     fld("Foreign IP", f"<input name=foreign_ip value='{esc(st['foreign_ip'])}' class=w-m>")
                     + fld("Iran IP", f"<input name=iran_ip value='{esc(st['iran_ip'])}' class=w-m>")
                     + fld("SNI", f"<input name=sni value='{esc(st.get('sni', ''))}' class=w-m>")
                     + ("<label class=ck><input type=checkbox name=rotate> Rotate credentials + WireGuard keys</label>" if f else "")
                     + "<button class=btn>Update tunnel</button>", cls="row"),
                "Use it after getting a new server IP or to rotate keys. "
                + ("Then copy the new token to the Iran server." if f else "Make the same change on the foreign server, then Sync token."))


def render_system(st):
    new = st["role"] == "new"
    cc = sh("sysctl -n net.ipv4.tcp_congestion_control").stdout.strip() or "?"
    bbr_on = cc == "bbr"
    o = ""
    if not new:
        o += render_update(st)
    o += card("Network speed (BBR)",
              f"<p><span>Current congestion control</span>: <b class=mono>{esc(cc)}</b> " + ("<span class='pill up'>BBR on</span>" if bbr_on else "") + "</p>"
              + ("" if bbr_on else form({"a": "bbr"}, "<button class=btn>Enable BBR</button>")),
              "BBR usually gives better throughput on long, lossy links.")
    o += card("Panel password",
              form({"a": "chpw"}, fld("New password", "<input type=password name=pw1 autocomplete=new-password class=w-m>")
                   + fld("Repeat", "<input type=password name=pw2 autocomplete=new-password class=w-m>")
                   + "<button class=btn>Change password</button>", cls="row"),
              "At least 8 characters. The panel login user stays the same.")
    m = ("<div class=row>" + form({"a": "checkver"}, "<button class='btn g'>Check for update</button>")
         + form({"a": "update_script"}, "<button class='btn g'>Update night-tunnel</button>", confirm="Update the script?")
         + form({"a": "update_gost"}, "<button class='btn g'>Update engine (gost)</button>", confirm="Update gost?")
         + ("" if new else form({"a": "restart"}, "<button class='btn g'>Restart tunnel</button>")) + "</div>")
    o += card("Maintenance", m, f"<span>Installed version</span> <span class=mono>v{VERSION}</span>")
    if not new:
        o += card("Danger zone",
                  form({"a": "reset"}, "<input name=confirm placeholder=DELETE class=w-s> "
                       "<button class='btn d'>Delete tunnel config (keep installed)</button>", cls="row")
                  + "<div style='height:12px'></div>"
                  + form({"a": "uninstall"}, "<input name=confirm placeholder=DELETE class=w-s> "
                         "<label class=ck><input type=checkbox name=purge> also remove gost binary</label> "
                         "<button class='btn d'>Uninstall night-tunnel completely</button>", cls="row"),
                  "Type DELETE to confirm.", cls="bad")
    return o


def render_wiz_result():
    r = WIZ.get("result")
    if not r:
        if not WIZ.get("notice"):
            return ""
        return card("Setup finished", f"<p>{esc(WIZ['notice'])}</p>"
                    + form({"a": "wizclear"}, "<p><button class='btn g'>Dismiss</button></p>"), cls="ok")
    o = r["other_panel"]
    h = (f"<p>Forwarded ports: <b class=mono>{esc(', '.join(map(str, r['ports'])))}</b> (Iran &rarr; foreign 127.0.0.1:port)</p>"
         "<dl class=kv><dt>Other server's panel</dt>"
         f"<dd class=mono>{esc(o['panel_url'])}</dd><dt>User</dt><dd class=mono>{esc(o['user'])}</dd>"
         f"<dt>Password</dt><dd class=mono>{esc(o['pw'])}</dd></dl>"
         "<p class=hint>Shown once - save it now.</p>")
    if r.get("test"):
        h += f"<pre class=log>{esc(r['test'])}</pre>"
    return card("Easy setup finished", h + form({"a": "wizclear"}, "<p><button class='btn g'>Dismiss</button></p>"), cls="ok")


def wiz_running():
    return card("Setting up...", "<pre class='log wizlog'>" + esc("\n".join(WIZ["log"])) + "</pre>",
                "This page updates by itself. It can take a few minutes.")


def render_manual():
    o = ""
    if WIZ["error"] and not WIZ["running"]:
        o += f"<div class='flash e'>{esc(WIZ['error'])}</div>"
    if WIZ["running"]:
        return o + wiz_running()
    sel = "".join(
        f"<div class=mgrp><b>{esc(layer)}</b>" + "".join(
            f"<label class=ck><input type=checkbox name='sel_{k}'{' checked' if (k in CATALOG and CATALOG[k][3]) or k == 'wg' else ''}> "
            f"<span class=mono>{k}</span> <span class=mu>{esc(CATALOG[k][2] if k in CATALOG else CARRIERS[k][0] + ' (kernel)')}</span></label>"
            for k in ids) + "</div>" for layer, ids in LAYERS)
    ff = form({"a": "mforeign"},
              "<div class=row>" + fld("Iran server IP", "<input name=iran_ip class='ltr w-m' placeholder='203.0.113.10'>")
              + fld("Domain pointing to this server (optional, real SSL)", "<input name=domain class='ltr w-l'>")
              + fld("Decoy SNI (used when there is no domain)", "<input name=sni value='www.microsoft.com' class='ltr w-l'>") + "</div>"
              "<div class=row style='margin-top:12px'>"
              + fld("Security", "<select name=mode><option value=password>With password (encrypted, recommended)</option>"
                    "<option value=open>No password (limited to the Iran IP)</option></select>")
              + fld("Tunnels to build", "<select name=pick><option value=recommended>Recommended set (balanced + WireGuard backup)</option>"
                    "<option value=all>Every model (best for comparing speeds)</option>"
                    "<option value=custom>Only the ones I tick below</option></select>")
              + fld("This server's public IP (only if it cannot be detected)", "<input name=local_ip class='ltr w-m'>") + "</div>"
              "<details><summary>Pick tunnels</summary>" + sel + "</details>"
              "<p><button class=btn>Create foreign (exit) side</button></p>")
    fi = form({"a": "miran"},
              fld("Token from the foreign server", "<textarea name=token placeholder='NT1:...'></textarea>")
              + "<div class=row style='margin-top:12px'>"
              + fld("Ports to forward on this server", "<input name=ports value=443 class='ltr w-m' placeholder='443,2053'>")
              + fld("Ports that also need UDP (optional)", "<input name=udp class='ltr w-m'>")
              + fld("Domain pointing to this server (optional)", "<input name=domain class='ltr w-l'>") + "</div>"
              "<p><button class=btn>Create Iran (entry) side</button></p>")
    return (o + card("Manual setup: foreign (exit) server", ff,
                     "Same as menu 1 in the terminal. Build this side first, then copy its token to the Iran server. No SSH access needed.")
            + card("Manual setup: Iran (entry) server", fi, "Same as menu 2 in the terminal. Paste the token from the foreign server."))


def manual_bg(kind, p):
    WIZ.update(running=True, log=[], result=None, error="", notice="")
    try:
        if os.path.exists(STATE):
            raise RuntimeError("this server already has a tunnel configured")
        if kind == "foreign":
            WIZ["log"].append("Detecting this server's IP ...")
            me = p["local_ip"] or public_ip()
            if not valid_ip(me):
                raise RuntimeError("could not detect this server's public IP; enter it")
            WIZ["log"].append("Creating the foreign (exit) side (certificate, firewall, services) ...")
            st, _ = core_foreign(me, p["iran_ip"], p["domain"], p["sni"], p["tp_ids"], p["carriers"], p["custom"],
                                 p["secure"], reuse_panel=True)
            start_bench(st)
            WIZ["notice"] = ("The foreign side is ready. Open the Token tab, copy the token and import it on the Iran server.")
        else:
            WIZ["log"].append("Creating the Iran (entry) side ...")
            core_iran(p["d"], p["domain"], p["ports"], reuse_panel=True)
            WIZ["notice"] = "The Iran side is ready. Open the Test tab to compare the tunnels and pick one."
    except Exception as e:
        WIZ["error"] = f"Setup failed: {e}"
    finally:
        WIZ["running"] = False


def manual_start(a, f):
    if WIZ["running"]:
        return ERR + "Setup is already running."
    if os.path.exists(STATE):
        return ERR + "This server already has a tunnel configured."
    domain = f.get("domain", "").strip()
    if domain and not valid_host(domain):
        return ERR + "Invalid domain."
    if a == "mforeign":
        iran, local = f.get("iran_ip", "").strip(), f.get("local_ip", "").strip()
        sni = domain or f.get("sni", "").strip() or "www.microsoft.com"
        if not valid_ip(iran):
            return ERR + "Enter the Iran server's IPv4 address."
        if not valid_host(sni):
            return ERR + "Invalid SNI."
        if local and not valid_ip(local):
            return ERR + "Invalid public IP."
        pick = f.get("pick", "recommended")
        if pick == "all":
            tps, car, custom = list(CATALOG), list(CARRIERS), True
        elif pick == "custom":
            tps = [k for k in CATALOG if "sel_" + k in f]
            car = [k for k in CARRIERS if "sel_" + k in f]
            custom = True
            if not tps and not car:
                return ERR + "Tick at least one tunnel."
        else:
            tps, car, custom = list(CATALOG), ["wg"], False
        p = {"iran_ip": iran, "domain": domain, "sni": sni, "local_ip": local, "tp_ids": tps, "carriers": car,
             "custom": custom, "secure": f.get("mode") != "open"}
        kind = "foreign"
    else:
        try:
            d = parse_token(f.get("token", ""))
            assert d["transports"] and d["auth"]
        except Exception:
            return ERR + "Invalid token."
        ports = parse_ports(f.get("ports", ""), f.get("udp", ""))
        if not ports:
            return ERR + "Enter at least one valid port to forward."
        p, kind = {"d": d, "domain": domain, "ports": ports}, "iran"
    WIZ.update(running=True, log=["starting"], error="", notice="", result=None)
    threading.Thread(target=manual_bg, args=(kind, p), daemon=True).start()
    return "Setup started. This page refreshes by itself."


def srv_activate(sid):
    """Make the Iran side talk to this server (create the Iran side on first use). Returns the state."""
    d = srv_load()
    s = srv_find(d, sid)
    if not s or not s.get("token"):
        raise RuntimeError("server is not ready")
    if os.path.exists(STATE):
        st = load()
        if st["role"] != "iran":
            raise RuntimeError("this panel is not the Iran (entry) side")
        if d["active"] != sid:
            msg = op_import_token(st, s["token"])
            if msg.startswith(ERR):
                raise RuntimeError(msg.lstrip(ERR))
            st = load()
            apply(st)
    else:
        WIZ["log"].append("Creating the Iran (entry) side ...")
        core_iran(parse_token(s["token"]), "", [], reuse_panel=True)
        st = load()
    d["active"] = sid
    srv_save(d)
    return st


def tcp_class(host, port, timeout=1.5):
    """Why a TCP port does not answer: closed / filtered / open."""
    try:
        socket.create_connection((host, port), timeout=timeout).close()
        return "open"
    except ConnectionRefusedError:
        return "closed"
    except OSError:
        return "filtered"


def run_probe(st, s, level="fast", log=print):
    """Pre-build test (Iran side). The destination opens a throw-away listener for EVERY transport type, so the
    result never depends on what is enabled there. Phase 1 (all in parallel, a few seconds): connect + stability.
    Phase 2: real speed for the best few. level: quick = phase 1 only, fast = speed top 6 (2 s), full = all (4 s)."""
    log("Opening test ports on the destination ...")
    try:
        info = agent_call(s, "testlisten")
    except Exception as e:
        return None, ERR + f"Destination did not answer ({e}). Is it online and joined?"
    key, bp = st["auth"]["p"], bench_port(st)
    st2 = dict(st, auth={"u": info["user"], "p": info["pw"]}, secure=True)
    tl = {k: {"id": k, "type": k, "port": info["ports"][k], "via": "direct", "enabled": True}
          for k in CATALOG if k in info["ports"]}
    used, local, svcs, chains = {bp, st["panel"]["port"]}, {}, [], []
    for k, t in tl.items():
        local[k] = free_port(used)
        chains.append({"name": "c-" + k, "hops": [{"name": "h", "nodes": [dial_node(st2, t)]}]})
        svcs.append({"name": "s-" + k, "addr": f"127.0.0.1:{local[k]}", "handler": {"type": "tcp", "chain": "c-" + k},
                     "listener": {"type": "tcp"}, "forwarder": {"nodes": [{"name": "t", "addr": f"127.0.0.1:{bp}"}]}})
    procs, files, res = [], [], []
    BENCH_STATE.update(live=[], done=0, total=len(tl) + len(st.get("l3") or {}))
    nk = len(st.get("l3") or {})
    try:
        procs, bad, files = spawn_gost(svcs, chains, None, tag="nt-probe")
        log(f"Testing {len(tl)} transports + {nk} kernel tunnels in parallel ...")
        cnt = 10 if level == "quick" else 8

        def one(k):
            t = tl[k]
            r = {"name": k, "kind": "relay", "enc": enc_of(t), "auth": "password",
                 "layer": next((re.sub(r"\s+", " ", n) for n, ids in LAYERS if k in ids), "relay"), "ok": False}
            if info.get("bad", {}).get(k):
                r["err"] = "destination cannot run it: " + info["bad"][k]
                return r
            if bad.get("s-" + k):
                r["err"] = "this gost build cannot start it: " + bad["s-" + k]
                return r
            udp = CATALOG[k][1]
            if not udp:
                c = tcp_class(st["foreign_ip"], t["port"])
                if c != "open":
                    r["err"] = ("blocked: the port does not answer (firewall / ISP filtering on the path)"
                                if c == "filtered" else "port refused (nothing listening on the destination)")
                    return r
            try:
                r.update(bench_latency("127.0.0.1", local[k], key, count=cnt, timeout=5))
            except (OSError, ValueError) as e:
                r["err"] = ("UDP is dropped or filtered on this path" if udp
                            else "port open but the tunnel handshake failed") + (f" ({e})" if str(e) else "")
            return r

        def kern(name):
            c = st["l3"][name]
            r = {"name": "kernel:" + name, "kind": "kernel", "layer": "L3 kernel", "ok": False,
                 "enc": "yes" if name == "wg" else "no", "auth": "key" if name == "wg" else "none"}
            pg = ping_host(c["f_ip"], 4)
            try:
                r.update(bench_latency(c["f_ip"], bp, key, count=cnt, timeout=4))
                r["loss"] = max(r["loss"], round(pg["loss"], 2))
            except OSError as e:
                r["err"] = ("ping ok but TCP failed (update the destination)" if pg["loss"] < 1 else "no reply") \
                    + (f" ({e})" if str(e) else "")
            r["ping_ms"] = pg["rtt"]
            return r
        with concurrent.futures.ThreadPoolExecutor(max_workers=24) as ex:
            futs = [ex.submit(one, k) for k in tl] + [ex.submit(kern, n) for n in (st.get("l3") or {})]
            for f in futs:
                res.append(f.result())
        BENCH_STATE["done"] = len(res)
        bench_live(res, level != "quick", nk)
        okr = sorted([r for r in res if r["ok"]], key=lambda r: (-bench_stab(r), r.get("rtt") or 9e9))
        log(f"{len(okr)} of {len(res)} connected.")
        if level != "quick" and okr:
            pick = okr if level == "full" else okr[:6]
            secs = 4 if level == "full" else 2
            BENCH_STATE["total"] = len(res) + len(pick)
            for r in pick:
                log(f"Speed test: {r['name']} ...")
                if r["kind"] == "kernel":
                    bench_speed(st["l3"][r["name"][7:]]["f_ip"], bp, key, secs, r)
                else:
                    bench_speed("127.0.0.1", local[r["name"]], key, secs, r)
                BENCH_STATE["done"] += 1
                bench_live(res, True, nk)
    finally:
        stop_gost(procs, files)
        try:
            agent_call(s, "testend")
        except Exception:
            pass
    for r in res:
        r["score"] = bench_score(r)
    rep = {"ts": int(time.time()), "full": level != "quick", "results": res,
           "rec": bench_recommend(dict(st, transports=list(tl.values()), secure=True), res)}
    with open(BENCH, "w") as f:
        json.dump(rep, f)
    return rep, None


def probe_bg(st, s, level):
    BENCH_STATE.update(running=True, log=[])
    try:
        _, err = run_probe(st, s, level, log=lambda m: BENCH_STATE["log"].append(m))
        if err:
            BENCH_STATE["log"].append(err)
    except Exception as e:
        BENCH_STATE["log"].append(ERR + f"Test failed: {e}")
    finally:
        BENCH_STATE["running"] = False


def srv_test_bg(sid, level):
    WIZ.update(running=True, log=["Preparing the connection to the server ..."], result=None, error="", notice="")
    try:
        st = srv_activate(sid)
    except Exception as e:
        WIZ["error"] = f"Could not prepare the test: {e}"
        WIZ["running"] = False
        BENCH_STATE["running"] = False
        return
    WIZ["running"] = False
    sv = srv_find(srv_load(), sid) or {}
    if sv.get("agent"):
        probe_bg(dict(st), sv, level)
    else:
        bench_bg(dict(st), level != "quick")
    try:
        with open(BENCH) as f:
            ts = json.load(f)["ts"]
        d = srv_load()
        s = srv_find(d, sid)
        if s and ts >= s.get("test_start", 0):
            s["status"], s["tested_ts"] = ("active" if s["status"] == "active" else "tested"), ts
            srv_save(d)
    except (OSError, ValueError, KeyError):
        pass


def srv_create(f):
    d = srv_load()
    s = srv_find(d, f.get("id", ""))
    if not s or d["active"] != s["id"] or not s.get("tested_ts"):
        return ERR + "Test this server's tunnels first."
    try:
        with open(BENCH) as fh:
            rep = json.load(fh)
        st = load()
    except (OSError, ValueError):
        return ERR + "Run the tunnel test first."
    if rep.get("ts") != s["tested_ts"]:
        return ERR + "The last test belongs to another server; test this server again."
    ports = parse_ports(f.get("ports", ""), f.get("udp", ""))
    if not ports:
        return ERR + "Enter at least one port to forward (e.g. 443)."
    name = f.get("tunnel", "")
    okr = [r["name"] for r in rep["results"] if r.get("ok") and r.get("kind") == "relay"]
    if name == "auto":
        name = bench_best(rep) or ""
    if name not in okr and not any(r["name"] == name and r.get("ok") for r in rep["results"]):
        return ERR + "Choose a tunnel that passed the test."
    if not name.startswith("kernel:") and s.get("agent"):
        ids = [name] + ([x for x in okr if x != name] if "backup" in f else [])
        try:   # the destination may have switched this model off earlier: enable it there first
            back = agent_call(s, "keep", ",".join(ids))
            m = op_import_token(st, back["token"])
            if m.startswith(ERR):
                return m
            st = load()
        except Exception as e:
            return ERR + f"Destination could not enable {name}: {e}"
    want = {p["port"] for p in ports}
    for p in list(st.get("ports", [])):
        if p["port"] not in want:
            op_port_del(st, str(p["port"]))
    have = {p["port"] for p in st.get("ports", [])}
    for p in ports:
        if p["port"] not in have:
            m = op_port_add(st, str(p["port"]), p["proto"], "", "")
            if m.startswith(ERR):
                return m
    msg = op_use_tunnel(st, name, only=True)
    if msg.startswith(ERR):
        return msg
    if "backup" in f and not name.startswith("kernel:"):
        op_set_ids(st, [name] + [x for x in okr if x != name])
        msg = f"Using {name} as the main tunnel; the other working tunnels stay as backup."
    save(st)
    apply(st)
    keep = [t["id"] for t in st["transports"] if t["enabled"]]
    note = ""
    if not name.startswith("kernel:"):
        try:
            agent_call(s, "keep", ",".join(keep))
            note = " The destination server now only runs the tunnels you kept."
        except Exception as e:
            note = f" (Could not tidy the destination server: {e}. It still runs every model.)"
    s["status"] = "active"
    srv_save(d)
    return msg + " Ports: " + ", ".join(str(p["port"]) for p in ports) + "." + note


def srv_act(f):
    a, d = f.get("a"), srv_load()
    s = srv_find(d, f.get("id", ""))
    if a == "srvadd":
        return srv_add(f.get("name", ""), f.get("ip", "").strip())
    if not s and a != "srvcreate":
        return ERR + "Unknown server."
    if a == "srvdel":
        if d["active"] == s["id"]:
            return ERR + "This server carries the active tunnel. Remove the tunnel first (System > Reset)."
        d["servers"].remove(s)
        srv_save(d)
        return "Server removed."
    if a == "srvrenew":
        if s["status"] != "waiting":
            return ERR + "This server already joined."
        s.update(secret=secrets.token_urlsafe(18), exp=int(time.time()) + 86400)
        srv_save(d)
        return "New join command created."
    if a == "srvtoken":
        try:
            t = parse_token(f.get("token", ""))
            assert t["transports"]
        except Exception:
            return ERR + "Invalid token."
        if t.get("foreign_ip") != s["ip"]:
            return ERR + f"This token belongs to {t.get('foreign_ip')}, not {s['ip']}."
        s.update(status="ready", token=f["token"].strip(), secret="", joined=int(time.time()))
        s.pop("agent", None)
        srv_save(d)
        return "Token accepted. You can test the tunnels now."
    if a == "srvtest":
        if BENCH_STATE["running"] or WIZ["running"]:
            return ERR + "Something is already running."
        if s["status"] == "waiting":
            return ERR + "This server has not joined yet."
        s["test_start"] = int(time.time())
        srv_save(d)
        BENCH_STATE.update(running=True, log=["starting"])
        threading.Thread(target=srv_test_bg, args=(s["id"], {"0": "quick", "2": "full"}.get(f.get("full"), "fast")), daemon=True).start()
        return "Test started. This page refreshes by itself."
    if a == "srvcreate":
        return srv_create(f)
    return ""


def render_servers(st):
    d = srv_load()
    o = ""
    if WIZ["error"] and not WIZ["running"]:
        o += f"<div class='flash e'>{esc(WIZ['error'])}</div>"
    if WIZ["running"]:
        o += wiz_running()
    o += card("Add a destination server",
              form({"a": "srvadd", "tab": "servers"},
                   "<div class=row>" + fld("Name", "<input name=name class=w-m placeholder='Germany-1'>")
                   + fld("Server IP", "<input name=ip class='ltr w-m' placeholder='203.0.113.10'>")
                   + "</div><p><button class=btn>Add server</button></p>"),
              "You get ONE command to run once on that server. It installs night-tunnel there, builds every tunnel "
              "model and connects back here by itself. No SSH and no password are given to this panel.")
    try:
        with open(BENCH) as fh:
            rep = json.load(fh)
    except (OSError, ValueError):
        rep = None
    for s in d["servers"]:
        o += render_server_card(st, d, s, rep)
    if not d["servers"]:
        o += card("Servers", "<p class=mu>No server yet. Add the destination (exit) server above.</p>")
    return o


def render_server_card(st, d, s, rep):
    sid = s["id"]
    pill = {"waiting": "<span class='pill udp'>Waiting for the server</span>",
            "ready": "<span class='pill up'>Joined</span>",
            "tested": "<span class='pill up'>Tested</span>",
            "active": "<span class='pill up'>Tunnel active</span>"}[s["status"]]
    head = f"<p><b>{esc(s['name'])}</b> <span class='mono mu'>{esc(s['ip'])}</span> {pill}</p>"
    rm = form({"a": "srvdel", "id": sid, "tab": "servers"}, "<button class='btn g s'>Remove</button>",
              confirm="Remove this server from the list?", cls="inl")
    if s["status"] == "waiting":
        left = max(0, int((s.get("exp", 0) - time.time()) / 3600))
        body = head + "<p>Run this ONE line as root on that server (Debian/Ubuntu):</p>"
        try:
            body += f"<pre class=log onclick='var r=document.createRange();r.selectNode(this);getSelection().removeAllRanges();getSelection().addRange(r)'>{esc(srv_command(s, st))}</pre>"
        except OSError:
            body += "<p class=mu>The panel certificate is not ready yet.</p>"
        body += f"<p class=hint>The code works once, only from {esc(s['ip'])}, for about {left} more hour(s).</p>"
        if s.get("last_reject"):
            body += (f"<div class='flash e'>A connection came from {esc(s['last_reject'])} instead of {esc(s['ip'])} "
                     "and was refused. Check the IP, or paste the token below.</div>")
        body += ("<details><summary>The server could not connect? Paste its token</summary>"
                 + form({"a": "srvtoken", "id": sid, "tab": "servers"},
                        fld("Token printed on that server", "<textarea name=token placeholder='NT1:...'></textarea>")
                        + "<p><button class=btn>Use token</button></p>") + "</details>")
        body += ("<div class=row>" + form({"a": "srvrenew", "id": sid, "tab": "servers"}, "<button class='btn g s'>New code</button>", cls="inl")
                 + rm + "</div>")
        return card("Server", body)
    busy = BENCH_STATE["running"] or WIZ["running"]
    body = head
    pan = s.get("panel") or {}
    if pan.get("url"):
        body += (f"<p class=hint>Its own panel: <span class=mono>{esc(pan['url'])}</span> user <span class=mono>{esc(pan.get('user', ''))}</span>"
                 + (f" password <span class=mono>{esc(pan['pw'])}</span>" if pan.get("pw") else "") + "</p>")
    if not busy:
        body += ("<div class=row>"
                 + form({"a": "srvtest", "id": sid, "full": "1", "tab": "servers"}, "<button class=btn>Test all tunnels (fast)</button>", cls="inl")
                 + form({"a": "srvtest", "id": sid, "full": "0", "tab": "servers"}, "<button class='btn g'>Quick check (connect only)</button>", cls="inl")
                 + form({"a": "srvtest", "id": sid, "full": "2", "tab": "servers"}, "<button class='btn g'>Full test (speed on all)</button>", cls="inl")
                 + rm + "</div>")
    else:
        body += "<p class=mu>A test is running. Watch it in the Test tab.</p>"
    out = card("Server", body, "Tests run through the real tunnels: connection, latency, stability (16 probes) and real speed.")
    if (not busy and rep and s.get("tested_ts") and rep.get("ts") == s["tested_ts"] and d["active"] == sid):
        best = bench_best(rep)
        ok = sorted([r for r in rep["results"] if r.get("ok")], key=lambda r: -r.get("score", 0))
        opts = "<option value=auto>Recommended" + (f" ({esc(best)})" if best else "") + "</option>" + "".join(
            f"<option value='{esc(r['name'])}'>{esc(r['name'])} - {BV_LABEL[bench_verdict(r)]}, "
            f"stability {bench_stab(r)}%"
            + (f", {r['down']}/{r['up']} Mb/s" if "down" in r else "") + "</option>" for r in ok)
        cur = ",".join(str(p["port"]) for p in st.get("ports", [])) or "443"
        hero = ""
        if best:
            b = next(r for r in rep["results"] if r["name"] == best)
            hero = (f"<p><b class=mono>{esc(best)}</b> {bpill(bench_verdict(b))} <span class=mu>latency {b['rtt']} ms, "
                    f"stability {bench_stab(b)}%" + (f", down {b['down']} / up {b['up']} Mb/s" if "down" in b else "") + "</span></p>")
        out += card("Build the tunnel",
                    hero + form({"a": "srvcreate", "id": sid, "tab": "servers"},
                                "<div class=row>" + fld("Tunnel type", f"<select name=tunnel>{opts}</select>")
                                + fld("Ports to forward on this server", f"<input name=ports value='{esc(cur)}' class='ltr w-m'>")
                                + fld("Ports that also need UDP (optional)", "<input name=udp class='ltr w-m'>") + "</div>"
                                "<p><label class=ck><input type=checkbox name=backup checked> Keep the other working tunnels as backup</label></p>"
                                "<p><button class=btn>Create tunnel</button></p>"),
                    "We suggest the best one, but you decide. Compare everything in the Test tab. "
                    "The destination server is configured automatically.", cls="ok")
    return out


def tabs_for(st):
    if st["role"] == "new":
        return [("servers", "Servers", "layers"), ("manual", "Manual setup", "tunnel"), ("telegram", "Telegram proxy", "send"),
                ("logs", "Logs", "terminal"), ("system", "System", "settings")]
    t = [("overview", "Overview", "home")]
    if st["role"] == "iran":
        t.append(("servers", "Servers", "layers"))
    t += [("transports", "Transports", "layers")]
    t.append(("ports", "Ports", "swap") if st["role"] == "iran" else ("tunnels", "Tunnels", "tunnel"))
    return t + [("token", "Token", "key"), ("test", "Test", "gauge"), ("telegram", "Telegram proxy", "send"),
                ("security", "Security", "shield"), ("logs", "Logs", "terminal"), ("system", "System", "settings")]


def render_page(st, msg=""):
    new = st["role"] == "new"
    states = svc_states()
    pr = {} if new else probe_all(st)
    secs = {"servers": lambda: render_servers(st), "manual": render_manual, "telegram": lambda: render_tg(st), "logs": render_logs,
            "system": lambda: render_system(st)}
    if not new:
        secs.update({"overview": lambda: render_overview(st, states, pr), "transports": lambda: render_transports(st, pr),
                     "ports": lambda: render_ports(st), "tunnels": lambda: render_tunnels(st),
                     "token": lambda: render_token(st), "test": lambda: render_bench(st),
                     "security": lambda: render_security(st)})
    tabs = tabs_for(st)
    nav = "".join(f"<button type=button class=nav-i data-tab={k}>{ico(i)}<span>{lbl}</span></button>" for k, lbl, i in tabs)
    body = "".join(f"<section class=tab id=tab-{k}>{secs[k]()}</section>" for k, _, _ in tabs)
    role = {"iran": "Iran &middot; entry", "foreign": "Foreign &middot; exit", "new": "Not configured"}[st["role"]]
    flash = ""
    if msg:
        extra = ""
        if st["role"] == "foreign" and "token" in msg.lower() and not msg.startswith(ERR):
            extra = " <button type=button class='btn g s' data-tab=token>Open Token tab</button>"
        flash = f"<div class='flash{' e' if msg.startswith(ERR) else ''}'>{esc(msg.lstrip(ERR))}{extra}</div>"
    run = "1" if (BENCH_STATE["running"] or WIZ["running"]) else "0"
    return (f"<!doctype html><html><meta charset=utf-8><meta name=viewport content='width=device-width,initial-scale=1'>"
            f"<title>night-tunnel</title><style>{CSS}</style><body data-run={run}><div class=app>"
            f"<aside class=side><div class=brand><div class=logo>{MOON}</div><span>night-tunnel</span></div>{nav}</aside>"
            f"<main class=main><div class=top><h1 id=ttl></h1><span class='pill plain'>{role}</span>"
            f"<span class='pill plain mono'>v{VERSION}</span><span class=grow></span>"
            "<button type=button class='btn g s' id=lang>&#1601;&#1575;&#1585;&#1587;&#1740;</button>"
            "<form method=post action=logout><button class='btn g s'>Logout</button></form></div>"
            f"{flash}{body}</main></div><script>{JS}</script>")


def login_page(err=""):
    e = f"<div class='flash e'>{esc(err)}</div>" if err else ""
    return (f"<!doctype html><html><meta charset=utf-8><meta name=viewport content='width=device-width,initial-scale=1'>"
            f"<title>night-tunnel</title><style>{CSS}</style><body><div class=login><div class=card>"
            f"<div class=logo>{MOON}</div><h1>night-tunnel</h1><div class=mu>Sign in to the control panel</div>{e}"
            "<form method=post action=login><input name=u placeholder=user autocomplete=username autofocus>"
            "<input name=p type=password placeholder=password autocomplete=current-password>"
            "<button class=btn>Login</button></form></div></div>")


def load_any():
    """State of the configured tunnel, or a stub ('new') when only the panel is up and no tunnel exists yet."""
    try:
        return load()
    except (OSError, ValueError):
        with open(BOOT) as f:
            b = json.load(f)
        return {"role": "new", "panel": b["panel"], "transports": [], "ports": [], "l3": {}}


def sys_act(st, a, f):
    """Panel actions that work in every state (with or without a tunnel). Returns a message or None."""
    if a == "wizclear":
        WIZ["result"] = None
        WIZ["notice"] = ""
        return ""
    if a == "chpw":
        return op_panel_pw(st, f.get("pw1", ""), f.get("pw2", ""))
    if a == "bbr":
        try:
            bbr()
        except Exception as e:
            return ERR + f"Could not enable BBR: {e}"
        return "BBR enabled."
    if a == "checkver":
        rv = remote_version()
        return f"Installed v{VERSION}, latest v{rv}." if rv else ERR + "Could not check (no repo URL / no access)."
    if a == "update_script":
        return update_script()
    if a == "update_gost":
        return update_gost()
    return tg_act(a, f)


class Handler(BaseHTTPRequestHandler):
    timeout = 15
    server_version = "nginx"
    sys_version = ""
    sessions = {}
    flash = {}
    fails = {}

    def log_message(self, *a):
        pass

    def reply(self, code, body="", ctype="text/html; charset=utf-8", extra=None):
        b = body.encode()
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(b)))
        self.send_header("X-Frame-Options", "DENY")
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Security-Policy", "default-src 'none'; style-src 'unsafe-inline'; "
                         "script-src 'unsafe-inline'; connect-src 'self'; form-action 'self'; base-uri 'none'; "
                         "frame-ancestors 'none'")
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(b)

    def sub(self, st):
        pre = "/" + st["panel"]["path"]
        if self.path == pre:
            return "/"
        if self.path.startswith(pre + "/"):
            return self.path[len(pre):].split("?")[0]
        return None

    def tok(self):
        for part in self.headers.get("Cookie", "").split(";"):
            k, _, v = part.strip().partition("=")
            if k == "nts" and self.sessions.get(v, 0) > time.time():
                return v
        return ""

    def authed(self):
        return bool(self.tok())

    def form(self):
        n = min(int(self.headers.get("Content-Length") or 0), 65536)
        return {k: v[0] for k, v in parse_qs(self.rfile.read(n).decode()).items()}

    def do_GET(self):
        st = load_any()
        s = self.sub(st)
        if s is None:
            return self.reply(404, "Not Found", "text/plain")
        if self.path == "/" + st["panel"]["path"]:
            return self.reply(301, "", extra={"Location": self.path + "/"})
        if s in ("/status", "/logs"):
            if not self.authed():
                return self.reply(403, "Forbidden", "text/plain")
            if s == "/status":
                return self.reply(200, status_json(st), "application/json")
            q = parse_qs(urlparse(self.path).query)
            return self.reply(200, read_logs(q.get("svc", [""])[0], q.get("n", ["100"])[0]), "text/plain; charset=utf-8")
        if s == "/" and self.authed():
            return self.reply(200, render_page(st, self.flash.pop(self.tok(), "")))
        self.reply(200, login_page())

    def do_POST(self):
        st = load_any()
        s = self.sub(st)
        if s is None:
            return self.reply(404, "Not Found", "text/plain")
        f = self.form()
        ip = self.client_address[0]
        if s == "/login":
            cnt, until = self.fails.get(ip, (0, 0))
            if cnt >= 8 and until > time.time():
                return self.reply(429, "Too many attempts", "text/plain")
            p = st["panel"]
            ok = hmac.compare_digest(f.get("u", ""), p["user"]) and hmac.compare_digest(
                hash_pw(f.get("p", ""), p["salt"]), p["pass_hash"])
            if not ok:
                self.fails[ip] = (cnt + 1, time.time() + 300)
                time.sleep(1)
                return self.reply(200, login_page("Wrong credentials"))
            self.fails.pop(ip, None)
            tok = secrets.token_urlsafe(32)
            self.sessions[tok] = time.time() + 6 * 3600
            return self.reply(303, "", extra={
                "Location": "./", "Set-Cookie": f"nts={tok}; Path=/; HttpOnly; Secure; SameSite=Strict"})
        if s == "/enroll":
            k = "enroll:" + ip
            cnt, until = self.fails.get(k, (0, 0))
            if cnt >= 8 and until > time.time():
                return self.reply(429, "Too many attempts", "text/plain")
            code, out = srv_enroll(ip, f)
            if code != 200:
                self.fails[k] = (cnt + 1, time.time() + 300)
            return self.reply(code, out, "text/plain")
        if s == "/agent":
            code, out = agent_serve(st, f, ip)
            return self.reply(code, out, "application/json")
        if not self.authed():
            return self.reply(303, "", extra={"Location": "./"})
        if s == "/logout":
            self.sessions.pop(self.tok(), None)
            return self.reply(303, "", extra={"Location": "./", "Set-Cookie": "nts=; Max-Age=0; Path=/"})
        if s != "/api":
            return self.reply(404, "Not Found", "text/plain")
        msg = self.act(st, f)
        if msg == "BYE":
            return self.reply(200, "<body style='background:#070b14;color:#e8eef8;font-family:sans-serif;padding:30px'>"
                                   "Removal started. The panel is going offline.")
        tab = re.sub(r"[^a-z]", "", f.get("tab", "").lower())[:12]
        self.flash[self.tok()] = msg
        self.reply(303, "", extra={"Location": "./" + ("#" + tab if tab else "")})

    def act_new(self, f):
        """Actions while no tunnel exists yet (panel started first)."""
        a = f.get("a")
        if a == "wizclear":
            WIZ["result"] = None
            WIZ["notice"] = ""
            return ""
        if a in ("mforeign", "miran"):
            return manual_start(a, f)
        if a and a.startswith("srv"):
            return srv_act(f)
        return sys_act({"role": "new", "panel": load_any()["panel"]}, a, f) or ""

    def act(self, st, f):
        a = f.get("a")
        if st["role"] == "new":
            return self.act_new(f)
        if a and a.startswith("srv"):
            return srv_act(f) if st["role"] == "iran" else ERR + "Servers are managed from the Iran (entry) panel."
        if a in ("tgcreate", "tgedit", "tgrestart", "tgrotate", "tgremove", "wizclear", "chpw", "bbr",
                 "checkver", "update_script", "update_gost"):
            return sys_act(st, a, f)
        if a == "save":
            prio = {}
            for t in st["transports"]:
                t["enabled"] = ("en_" + t["id"]) in f
                try:
                    prio[t["id"]] = float(f.get("pr_" + t["id"], 99))
                except ValueError:
                    prio[t["id"]] = 99
            st["transports"].sort(key=lambda t: prio[t["id"]])
            if not any(t["enabled"] for t in st["transports"]):
                return ERR + "Enable at least one transport."
            if f.get("strategy") in ("fifo", "round", "rand"):
                st["strategy"] = f["strategy"]
            msg = "Saved."
        elif a == "preset" and f.get("n") in ("balanced", "stealth", "game", "rotate"):
            preset(st, f["n"])
            msg = "Preset applied: " + f["n"]
        elif a == "addport":
            msg = op_port_add(st, f.get("port"), f.get("proto", "tcp"), f.get("target", ""), f.get("via", ""))
        elif a == "editport":
            msg = op_port_edit(st, f.get("old"), f.get("port"), f.get("proto", "tcp"), f.get("target", ""),
                               f.get("via", ""))
        elif a == "delport":
            msg = op_port_del(st, f.get("port"))
        elif a == "tpport":
            msg = op_tp_port(st, f.get("id"), f.get("port"))
        elif a == "tpdel":
            msg = op_tp_del(st, f.get("id"))
        elif a == "tpadd":
            msg = op_tp_add(st, f.get("id"), f.get("name", ""), f.get("port", ""), f.get("sni", ""),
                            f.get("path", ""), f.get("host", ""))
        elif a == "tpedit":
            msg = op_tp_edit(st, f.get("id"), f.get("port", ""), f.get("sni"), f.get("path"), f.get("host"),
                             f.get("new_type", ""))
        elif a == "updtunnel":
            msg = op_update_tunnel(st, f.get("foreign_ip", ""), f.get("iran_ip", ""), f.get("sni", ""),
                                   "rotate" in f)
        elif a == "test":
            if BENCH_STATE["running"]:
                return ERR + "A test is already running."
            if st["role"] != "iran":
                return ERR + "Run the test on the Iran server."
            threading.Thread(target=bench_bg, args=(dict(st), f.get("full") != "0"), daemon=True).start()
            BENCH_STATE.update(running=True, log=["starting"])
            return "Test started. This page refreshes by itself."
        elif a == "benchapply":
            msg = op_bench_apply(st)
        elif a == "usetunnel":
            msg = op_use_tunnel(st, f.get("name", ""), f.get("only") == "1")
        elif a == "usebest":
            msg = op_use_best(st, f.get("only") == "1")
        elif a == "allmodels":
            msg = op_all_models(st)
        elif a == "caradd":
            msg = op_carrier_add(st, f.get("c"))
        elif a == "security":
            msg = op_security(st, f.get("mode") != "open")
        elif a == "importtoken":
            msg = op_import_token(st, f.get("token", ""))
        elif a == "restart":
            sh("systemctl restart night-tunnel-l3 night-tunnel-gost")
            msg = "Restarted."
        elif a in ("reset", "uninstall"):
            if f.get("confirm") != "DELETE":
                return ERR + "Type DELETE to confirm."
            if a == "reset":
                detached("reset-yes")
            else:
                detached("uninstall-yes", "--purge" if f.get("purge") else "")
            return "BYE"
        else:
            return ""
        if msg.startswith(ERR):
            return msg
        save(st)
        if not apply(st):
            msg += " (nothing to run: add a port / enable a transport)"
        return msg




def run_panel():
    st = load_any()
    start_bench(st)
    srv = ThreadingHTTPServer(("0.0.0.0", st["panel"]["port"]), Handler)
    ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
    ctx.minimum_version = ssl.TLSVersion.TLSv1_2
    ctx.load_cert_chain(CERT, KEY)
    srv.socket = ctx.wrap_socket(srv.socket, server_side=True, do_handshake_on_connect=False)
    srv.serve_forever()



# ------------------------------------------------------ Telegram proxy (MTProto, fake-TLS)
# Independent of the tunnels: any server can run it. Engine: mtg (https://github.com/9seconds/mtg).
def tg_load():
    try:
        with open(TG_STATE) as f:
            return json.load(f)
    except (OSError, ValueError):
        return None


def tg_secret(host):
    """Fake-TLS secret: 'ee' + 16 random bytes + the cover hostname (all hex)."""
    return "ee" + secrets.token_hex(16) + host.encode().hex()


def tg_links(t):
    q = f"server={t['ip']}&port={t['port']}&secret={t['secret']}"
    return {"https": "https://t.me/proxy?" + q, "tg": "tg://proxy?" + q}


def tg_install_engine():
    """Install the mtg binary (GitHub release, or MTG_URL=<tar.gz link> for blocked servers)."""
    if shutil.which("mtg"):
        return ""
    arch = {"x86_64": "amd64", "aarch64": "arm64", "arm64": "arm64", "armv7l": "arm"}.get(os.uname().machine)
    if not arch:
        return "Unsupported architecture."
    url = os.environ.get("MTG_URL", "")
    if not url:
        r = sh("curl -fsSL --max-time 20 https://api.github.com/repos/9seconds/mtg/releases/latest")
        try:
            urls = [a["browser_download_url"] for a in json.loads(r.stdout)["assets"]]
            url = next(u for u in urls if u.endswith(f"linux-{arch}.tar.gz"))
        except Exception:
            return "Could not find an mtg release (GitHub unreachable?). Retry with MTG_URL=<tar.gz link>."
    d = tempfile.mkdtemp()
    try:
        if sh(f"curl -fsSL --max-time 120 {shlex.quote(url)} -o {d}/m.tgz").returncode != 0:
            return "mtg download failed."
        with tarfile.open(d + "/m.tgz") as tf:
            m = next((x for x in tf.getmembers() if x.isfile() and os.path.basename(x.name) == "mtg"), None)
            if not m:
                return "mtg binary not found inside the archive."
            data = tf.extractfile(m).read()
        with open("/usr/local/bin/mtg", "wb") as f:
            f.write(data)
        os.chmod("/usr/local/bin/mtg", 0o755)
        return "" if sh("/usr/local/bin/mtg --version").returncode == 0 else "The mtg binary does not run here."
    except Exception as e:
        return f"mtg install failed: {e}"
    finally:
        shutil.rmtree(d, ignore_errors=True)


def tg_write_cfg(t):
    os.makedirs(TGBASE, exist_ok=True)
    with open(TG_CFG, "w") as f:
        f.write(f'secret = "{t["secret"]}"\nbind-to = "0.0.0.0:{t["port"]}"\n')
    os.chmod(TG_CFG, 0o600)
    with open(TG_STATE, "w") as f:
        json.dump(t, f)
    os.chmod(TG_STATE, 0o600)


def tg_up(t):
    tg_write_cfg(t)
    write_units()
    sh("systemctl daemon-reload")
    sh("systemctl enable night-tunnel-tg")
    sh("systemctl restart night-tunnel-tg")
    time.sleep(1.5)
    return sh("systemctl is-active night-tunnel-tg").stdout.strip() == "active"


def op_tg_create(ip, port="", host="", reuse_port=False):
    if not valid_ip(ip):
        return ERR + "Enter this server's public IPv4 address."
    host = host or "www.microsoft.com"
    if not valid_host(host):
        return ERR + "Invalid cover domain."
    old = tg_load()
    if port:
        if not port.isdigit() or not 1 <= int(port) <= 65535:
            return ERR + "Invalid port."
        port = int(port)
    else:
        port = 443
    stopped = bool(old and old["port"] == port)
    if stopped:
        sh("systemctl stop night-tunnel-tg")   # free our own port before checking it
    if not can_bind(port):
        if port == 443 and not old:
            port = free_port(set())            # 443 busy: pick a free random port instead
        else:
            if stopped:
                sh("systemctl start night-tunnel-tg")
            return ERR + f"Port {port} is already in use."
    if old and old["port"] != port:
        _fw_apply(f"{old['port']}/tcp", False)
    err = tg_install_engine()
    if err:
        return ERR + err
    t = {"ip": ip, "port": port, "host": host, "secret": tg_secret(host)}
    _fw_apply(f"{port}/tcp", True)
    if not tg_up(t):
        return ERR + "The proxy did not start. See: journalctl -u night-tunnel-tg -n 30"
    return "Telegram proxy is running on port %d. Link: %s" % (port, tg_links(t)["https"])


def op_tg_rotate():
    t = tg_load()
    if not t:
        return ERR + "No Telegram proxy yet."
    t["secret"] = tg_secret(t["host"])
    if not tg_up(t):
        return ERR + "The proxy did not restart."
    return "New secret generated (old links stop working). Link: " + tg_links(t)["https"]


def op_tg_remove(purge=False):
    t = tg_load()
    sh("systemctl disable --now night-tunnel-tg")
    if t:
        _fw_apply(f"{t['port']}/tcp", False)
    p = "/etc/systemd/system/night-tunnel-tg.service"
    os.path.exists(p) and os.remove(p)
    sh("systemctl daemon-reload")
    shutil.rmtree(TGBASE, ignore_errors=True)
    if purge and os.path.exists("/usr/local/bin/mtg"):
        os.remove("/usr/local/bin/mtg")
    return "Telegram proxy removed."


def tg_status():
    t = tg_load()
    if not t:
        return None
    t = dict(t)
    t["active"] = sh("systemctl is-active night-tunnel-tg").stdout.strip()
    t["links"] = tg_links(t)
    return t


def tg_menu():
    need_root()
    while True:
        t = tg_status()
        say("\n=== Telegram proxy (MTProto, fake-TLS) ===", G)
        if t:
            print(f"State : {t['active']}   Port: {t['port']}   Cover domain: {t['host']}")
            print(f"Link  : {t['links']['https']}")
            print(f"Also  : {t['links']['tg']}")
            c = input("\na) new secret   b) change port / cover domain   c) logs   d) restart   e) remove   0) back : ").strip().lower()
        else:
            print("No proxy yet. It runs on THIS server and is independent of the tunnels.")
            say("Tip: use a server that can reach Telegram (normally the foreign server).", Y)
            c = "n" if ask("Create it now? (y/n)", "y") == "y" else "0"
        if c == "0":
            return
        if c == "n":
            ip = public_ip() or ask("This server's public IP")
            port = ask("Port", "443")
            host = ask("Cover domain for fake-TLS (a big real site)", "www.microsoft.com")
            m = op_tg_create(ip, port, host)
        elif c == "a":
            m = op_tg_rotate()
        elif c == "b":
            m = op_tg_create(t["ip"], ask("Port", str(t["port"])), ask("Cover domain", t["host"]))
        elif c == "c":
            print(sh("journalctl -u night-tunnel-tg -n 40 --no-pager").stdout)
            continue
        elif c == "d":
            sh("systemctl restart night-tunnel-tg")
            m = "Restarted."
        elif c == "e":
            if ask("Type DELETE to remove the Telegram proxy") != "DELETE":
                continue
            m = op_tg_remove()
        else:
            continue
        say(m.lstrip(ERR), R if m.startswith(ERR) else G)


# ------------------------------------------------------------- systemd units
UNITS = {
    "night-tunnel-l3": """[Unit]
Description=night-tunnel L3 carriers (WireGuard/GRE/VXLAN)
After=network-online.target
Wants=network-online.target
ConditionPathExists=/etc/night-tunnel/state.json
[Service]
Type=oneshot
RemainAfterExit=yes
ExecStart=/usr/bin/python3 /opt/night-tunnel/nt.py l3-up
ExecStop=/usr/bin/python3 /opt/night-tunnel/nt.py l3-down
[Install]
WantedBy=multi-user.target
""",
    "night-tunnel-gost": """[Unit]
Description=night-tunnel engine (gost)
After=network-online.target night-tunnel-l3.service
Wants=night-tunnel-l3.service
ConditionPathExists=/etc/night-tunnel/gost.json
[Service]
ExecStart=/usr/local/bin/gost -C /etc/night-tunnel/gost.json
Restart=always
RestartSec=3
LimitNOFILE=1048576
[Install]
WantedBy=multi-user.target
""",
    "night-tunnel-panel": """[Unit]
Description=night-tunnel web panel
After=network-online.target
ConditionPathExists=|/etc/night-tunnel/state.json
ConditionPathExists=|/etc/night-tunnel/boot.json
[Service]
ExecStart=/usr/bin/python3 /opt/night-tunnel/nt.py panel
Restart=always
RestartSec=3
[Install]
WantedBy=multi-user.target
""",
}


def write_units(names=None):
    """Write the systemd units (the single source of truth; install.sh and the remote installer call this)."""
    units = dict(UNITS)
    units["night-tunnel-tg"] = f"""[Unit]
Description=night-tunnel Telegram proxy (mtg)
After=network-online.target
Wants=network-online.target
ConditionPathExists={TG_CFG}
[Service]
ExecStart=/usr/local/bin/mtg run {TG_CFG}
Restart=always
RestartSec=3
LimitNOFILE=1048576
[Install]
WantedBy=multi-user.target
"""
    for n, body in units.items():
        if names and n not in names:
            continue
        with open(f"/etc/systemd/system/{n}.service", "w") as f:
            f.write(body)
    sh("systemctl daemon-reload")


# ------------------------------------------------------------------ setup
def enable_services():
    sh("systemctl daemon-reload")
    sh("systemctl enable --now night-tunnel-l3 night-tunnel-panel")
    sh("systemctl enable night-tunnel-gost")
    apply()


def show_catalog():
    for layer, ids in LAYERS:
        print(f"  {layer}")
        for i in ids:
            print(f"      {i:8} {CATALOG[i][2] if i in CATALOG else CARRIERS[i][0] + ' (kernel)'}")


def pick_tunnels():
    """Let the user choose which tunnels to build. Returns (transport ids, carriers, custom?)."""
    say("Tunnels you can build (by network layer):", Y)
    show_catalog()
    sel = ask("Pick ids, comma separated (e.g. wss,grpc,quic,wg) - 'all', or Enter for the recommended set", "")
    if not sel:
        return list(CATALOG), ["wg"], False
    if sel == "all":
        return list(CATALOG), list(CARRIERS), True
    ids = [x for x in sel.replace(" ", "").split(",") if x]
    tps = [i for i in ids if i in CATALOG]
    car = [i for i in ids if i in CARRIERS]
    if not tps and not car:
        say("No valid ids; using the recommended set.", Y)
        return list(CATALOG), ["wg"], False
    return tps, car, True


def pick_security():
    say("Security mode:", Y)
    print("  1) With password (recommended): relay login required; TLS / QUIC / WireGuard are encrypted")
    print("  2) No password: no relay login. The foreign server then only accepts the Iran server's IP,")
    print("     and plain transports (tcp/ws/kcp/udp/...) carry data unencrypted")
    secure = ask("Choose", "1") != "2"
    if not secure:
        say("No-password mode selected: use encrypted transports (tls/mtls/wss/grpc/quic) for sensitive traffic.", Y)
    return secure


def _boot_panel():
    """Panel config created by 'panel-init' (so the browser session survives the tunnel setup)."""
    try:
        with open(BOOT) as f:
            return json.load(f)
    except (OSError, ValueError):
        return None


def _finish_setup(st, domain, sni, boot):
    """Certificate + firewall + services shared by both roles."""
    save(st)
    if boot and boot.get("le") and os.path.exists(CERT) and not domain:
        st["le"] = boot["le"]      # keep the panel's Let's Encrypt certificate
    else:
        st["le"] = domain if make_cert(domain, sni) else ""
    save(st)


def core_foreign(me, iran, domain, sni, tp_ids, carriers, custom, secure=True, reuse_panel=False):
    """Create the foreign (exit) side. Non-interactive; returns (state, panel_password or None)."""
    st = {"role": "foreign", "foreign_ip": me, "iran_ip": iran, "sni": sni, "secure": secure,
          "auth": {"u": "u" + rnd(6), "p": rnd(20)}, "strategy": "fifo", "ports": []}
    boot = _boot_panel() if reuse_panel else None
    if boot:
        st["panel"], pw = boot["panel"], None
    else:
        st["panel"], pw = new_panel(domain, me)
    used = {st["panel"]["port"]}
    st["transports"] = [{"id": k, "port": free_port(used), "enabled": CATALOG[k][3] or custom, "via": "direct"}
                        for k in tp_ids]
    st["l3"] = make_l3(carriers, st, used)
    for c in carriers:
        st["transports"].append({"id": c, "port": free_port(used), "enabled": True, "via": c})
    if not custom:
        preset(st, "balanced")
    if not secure:  # no login: keep encrypted transports first, plain ones stay available but not default
        for t in st["transports"]:
            if enc_of(t) == "no" and t["via"] == "direct":
                t["enabled"] = t["enabled"] and custom
    _finish_setup(st, domain, sni, boot)
    for t in st["transports"]:
        if t["via"] == "direct":
            fw_open(t["port"], "udp" if CATALOG[ttype(t)][1] else "tcp")
    for c in st["l3"]:
        fw_carrier(st, c, True)
    fw_open(st["panel"]["port"], "tcp")
    enable_services()   # also builds the gost config + the Iran-only lock in no-password mode
    return st, pw


def core_iran(d, domain, ports, reuse_panel=False):
    """Create the Iran (entry) side from a token dict. Non-interactive; returns (state, panel_password)."""
    me = public_ip() or d["iran_ip"]
    st = {"role": "iran", "foreign_ip": d["foreign_ip"], "iran_ip": d["iran_ip"],
          "sni": d.get("sni", ""), "auth": d["auth"], "strategy": "fifo", "secure": d.get("secure", True),
          "transports": d["transports"], "l3": dict(d.get("l3", {})), "ports": ports}
    boot = _boot_panel() if reuse_panel else None
    if boot:
        st["panel"], pw = boot["panel"], None
    else:
        st["panel"], pw = new_panel(domain, me)
    _finish_setup(st, domain, st["sni"], boot)
    for p in ports:
        for pr in (["tcp", "udp"] if p["proto"] == "both" else [p["proto"]]):
            fw_open(p["port"], pr)
    fw_open(st["panel"]["port"], "tcp")
    enable_services()
    return st, pw


def parse_ports(text, udp_text=""):
    ports = []
    for x in text.replace(" ", "").split(","):
        if x.isdigit() and 1 <= int(x) <= 65535 and int(x) != 22 and all(p["port"] != int(x) for p in ports):
            ports.append({"port": int(x), "proto": "tcp"})
    for x in udp_text.replace(" ", "").split(","):
        for p in ports:
            if x.isdigit() and p["port"] == int(x):
                p["proto"] = "both"
    return ports


def setup_foreign():
    need_root()
    say("== Setup FOREIGN (exit) server ==", G)
    me = public_ip() or ask("This server's public IP")
    iran = ask("Iran server public IP")
    if not valid_ip(iran):
        return say("Invalid IP.", R)
    domain = ask("Domain pointing to this server (optional, for real SSL)")
    if domain and not valid_host(domain):
        return say("Invalid domain.", R)
    sni = domain or ask("Decoy SNI for the TLS certificate", "www.microsoft.com")
    secure = pick_security()
    tp_ids, carriers, custom = pick_tunnels()
    st, pw = core_foreign(me, iran, domain, sni, tp_ids, carriers, custom, secure, reuse_panel=True)
    show_panel(st, pw)
    say("\nPaste this token on the Iran server:\n", G)
    print(make_token(st))


def setup_iran():
    need_root()
    say("== Setup IRAN (entry) server ==", G)
    try:
        d = parse_token(ask("Token from the foreign server"))
    except Exception:
        return say("Invalid token.", R)
    domain = ask("Domain pointing to this server (optional, for real SSL on the panel)")
    if domain and not valid_host(domain):
        return say("Invalid domain.", R)
    ports = parse_ports(ask("Ports to forward, e.g. 443,2053,8443"),
                        ask("Ports that also need UDP (comma separated, optional)"))
    if not ports:
        return say("No valid ports.", R)
    st, pw = core_iran(d, domain, ports, reuse_panel=True)
    show_panel(st, pw)
    say("Tunnel is up. Each forwarded port P goes to 127.0.0.1:P on the foreign server.", G)


# ------------------------------------------- easy mode: install the OTHER server over SSH
# The beginner gives the other server's IP + SSH login; this server pushes itself there, installs the
# dependencies and the engine, creates the matching side of the tunnel and wires both ends together.
# The SSH password lives only in memory for the duration of the setup; nothing is written to disk.
SSH_USER_RE = re.compile(r"^[a-z_][a-z0-9_-]{0,31}$")
WIZ = {"running": False, "log": [], "result": None, "error": "", "notice": ""}


class Remote:
    def __init__(self, host, port=22, user="root", password="", key=""):
        self.host, self.port, self.user, self.password, self.key = host, int(port), user, password, key

    def _opts(self):
        o = ["-o", "StrictHostKeyChecking=accept-new", "-o", "ConnectTimeout=12",
             "-o", "ServerAliveInterval=15", "-o", "ServerAliveCountMax=8", "-o", "LogLevel=ERROR"]
        if self.key:
            o += ["-i", self.key, "-o", "IdentitiesOnly=yes", "-o", "BatchMode=yes"]
        elif self.password:
            o += ["-o", "PreferredAuthentications=password,keyboard-interactive", "-o", "PubkeyAuthentication=no"]
        else:
            o += ["-o", "BatchMode=yes"]
        return o

    def _go(self, argv, inp=None, timeout=900):
        env = dict(os.environ)
        if self.password and not self.key:
            env["SSHPASS"] = self.password          # never on the command line
            argv = ["sshpass", "-e"] + argv
        try:
            r = subprocess.run(argv, input=inp, capture_output=True, text=True, timeout=timeout, env=env)
        except subprocess.TimeoutExpired:
            return 255, "", "timed out"
        except FileNotFoundError as e:
            return 127, "", str(e)
        return r.returncode, r.stdout, r.stderr

    def run(self, cmd, inp=None, timeout=900):
        return self._go(["ssh", "-p", str(self.port)] + self._opts() + [f"{self.user}@{self.host}", cmd],
                        inp, timeout)

    def put(self, src, dst):
        return self._go(["scp", "-P", str(self.port)] + self._opts() + [src, f"{self.user}@{self.host}:{dst}"],
                        None, 300)


def ssh_explain(rc, err):
    e = (err or "").strip()
    if rc == 127:
        return "ssh / sshpass is not installed on this server."
    if "Permission denied" in e:
        return ("SSH login refused: wrong password/key, or the other server does not allow root password "
                "login (PermitRootLogin / PasswordAuthentication).")
    if "Host key verification failed" in e:
        return "The other server's SSH host key changed. Remove its line from ~/.ssh/known_hosts and retry."
    if any(x in e for x in ("timed out", "No route", "refused", "unreachable")):
        return "Cannot reach the other server over SSH (check IP, SSH port and its firewall)."
    return "SSH failed: " + (e[-300:] or "unknown error")


def ensure_ssh_tools(need_pass):
    want = ["ssh", "scp"] + (["sshpass"] if need_pass else [])
    if all(shutil.which(x) for x in want):
        return True
    sh("DEBIAN_FRONTEND=noninteractive apt-get install -y openssh-client sshpass")
    return all(shutil.which(x) for x in want)


def install_gost():
    """Install the gost engine (GitHub release, or GOST_URL=<tar.gz link>). Returns '' or an error text."""
    if shutil.which("gost"):
        return ""
    arch = {"x86_64": "amd64", "aarch64": "arm64", "arm64": "arm64", "armv7l": "armv7"}.get(os.uname().machine)
    if not arch:
        return "Unsupported architecture."
    url = os.environ.get("GOST_URL", "")
    if not url:
        r = sh("curl -fsSL --max-time 20 https://api.github.com/repos/go-gost/gost/releases/latest")
        try:
            url = next(a["browser_download_url"] for a in json.loads(r.stdout)["assets"]
                       if a["browser_download_url"].endswith(f"_linux_{arch}.tar.gz"))
        except Exception:
            return "Could not find a gost release (GitHub unreachable? set GOST_URL=<tar.gz link>)."
    d = tempfile.mkdtemp()
    try:
        if sh(f"curl -fsSL --max-time 120 {shlex.quote(url)} -o {d}/g.tgz").returncode != 0:
            return "gost download failed."
        with tarfile.open(d + "/g.tgz") as tf:
            data = tf.extractfile("gost").read()
        with open("/usr/local/bin/gost", "wb") as f:
            f.write(data)
        os.chmod("/usr/local/bin/gost", 0o755)
        return ""
    except Exception as e:
        return f"gost install failed: {e}"
    finally:
        shutil.rmtree(d, ignore_errors=True)


def remote_prepare(r, log, force=False):
    """Check the other server and install night-tunnel + dependencies + engine on it. Returns an error or ''."""
    log(f"Connecting to {r.host} over SSH ...")
    rc, out, err = r.run("id -u; uname -m; command -v apt-get >/dev/null && echo APT; "
                         "command -v gost >/dev/null && echo GOST; "
                         "[ -f /etc/night-tunnel/state.json ] && echo EXISTS; echo END")
    if rc != 0 or "END" not in out:
        return ERR + ssh_explain(rc, err)
    lines = out.split()
    if not lines or lines[0] != "0":
        return ERR + "The SSH user on the other server must be root."
    if "APT" not in lines:
        return ERR + "The other server must be Debian/Ubuntu."
    if "EXISTS" in lines and not force:
        return ERR + ("The other server already has a night-tunnel configuration. "
                      "Tick 'overwrite' to replace it, or remove it there first.")
    arch = lines[1] if len(lines) > 1 else ""
    log("Installing packages on the other server (1-2 minutes) ...")
    rc, out, err = r.run("export DEBIAN_FRONTEND=noninteractive; apt-get update -y >/dev/null 2>&1; "
                         "apt-get install -y python3 curl jq openssl iproute2 iptables wireguard-tools "
                         "iputils-ping ca-certificates >/dev/null 2>&1 && mkdir -p /opt/night-tunnel /etc/night-tunnel")
    if rc != 0:
        return ERR + "Package installation failed on the other server (apt mirrors / internet?). " + err[-200:]
    log("Copying night-tunnel ...")
    rc, _, err = r.put(os.path.abspath(__file__), "/opt/night-tunnel/nt.py")
    if rc != 0:
        return ERR + "Copy failed: " + ssh_explain(rc, err)
    try:
        with open(OPT + "/repo") as f:
            repo = f.read().strip()
    except OSError:
        repo = ""
    rc, _, err = r.run("chmod 700 /opt/night-tunnel/nt.py && cat > /usr/local/bin/night-tunnel && "
                       "chmod +x /usr/local/bin/night-tunnel" + (f" && echo {shlex.quote(repo)} > /opt/night-tunnel/repo" if repo else ""),
                       inp='#!/bin/sh\nexec python3 /opt/night-tunnel/nt.py "$@"\n')
    if rc != 0:
        return ERR + "Could not install the launcher: " + err[-200:]
    if "GOST" not in lines:
        local_gost = shutil.which("gost")
        if local_gost and os.uname().machine == arch:
            log("Copying the engine (gost) from this server ...")
            rc, _, err = r.put(local_gost, "/usr/local/bin/gost")
            if rc == 0:
                r.run("chmod 755 /usr/local/bin/gost")
        else:
            log("Downloading the engine (gost) on the other server ...")
            rc, out, err = r.run("python3 /opt/night-tunnel/nt.py install-engine")
            if rc != 0:
                return ERR + "Engine install failed on the other server: " + (out + err)[-250:]
    rc, _, err = r.run("python3 /opt/night-tunnel/nt.py install-units")
    if rc != 0:
        return ERR + "Could not create the services on the other server: " + err[-200:]
    if "EXISTS" in lines and force:
        r.run("python3 /opt/night-tunnel/nt.py reset-yes")
    return ""


def remote_configure(r, kind, params, log):
    """Run the non-interactive setup of one side on the other server; returns (result dict, error)."""
    log("Creating the tunnel on the other server ...")
    rc, out, err = r.run(f"python3 /opt/night-tunnel/nt.py auto-{kind}", inp=json.dumps(params), timeout=600)
    line = next((x for x in out.splitlines() if x.startswith("NT_RESULT:")), "")
    if rc != 0 or not line:
        return None, ERR + "Setup failed on the other server: " + (err or out)[-300:]
    try:
        return json.loads(base64.b64decode(line[10:])), ""
    except ValueError:
        return None, ERR + "Unreadable answer from the other server."


def auto_cmd(kind):
    """Non-interactive setup of one side (called over SSH by the other server): params on stdin."""
    need_root()
    try:
        p = json.loads(sys.stdin.read())
        if kind == "foreign":
            assert valid_ip(p["me"]) and valid_ip(p["iran_ip"])
            st, pw = core_foreign(p["me"], p["iran_ip"], "", p.get("sni") or "www.microsoft.com",
                                  list(CATALOG), ["wg"], False, bool(p.get("secure", True)))
            out = {"token": make_token(st)}
        else:
            d = parse_token(p["token"])
            ports = [{"port": int(x["port"]), "proto": x["proto"] if x["proto"] in ("tcp", "udp", "both") else "tcp"}
                     for x in p["ports"]]
            assert ports
            st, pw = core_iran(d, "", ports)
            out = {}
        out.update(panel_url=panel_url(st), user=st["panel"]["user"], pw=pw)
    except Exception as e:
        print("auto setup error:", e, file=sys.stderr)
        sys.exit(1)
    print("NT_RESULT:" + base64.b64encode(json.dumps(out).encode()).decode())


_BENCH_THREAD = []


# ------------------------------------------------------------- servers (destination side is joined, never SSH'd)
SERVERS = BASE + "/servers.json"
DEFAULT_REPO = "https://raw.githubusercontent.com/Night-net83/night-tunnel/main"
_SRV_LOCK = threading.Lock()


def srv_load():
    try:
        with open(SERVERS) as f:
            d = json.load(f)
    except (OSError, ValueError):
        d = {}
    d.setdefault("servers", [])
    d.setdefault("active", "")
    return d


def srv_save(d):
    os.makedirs(BASE, exist_ok=True)
    with _SRV_LOCK:
        fd = os.open(SERVERS + ".tmp", os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
        with os.fdopen(fd, "w") as f:
            json.dump(d, f)
        os.replace(SERVERS + ".tmp", SERVERS)


def srv_find(d, sid):
    return next((x for x in d["servers"] if x["id"] == sid), None)


def cert_fp(path=None):
    with open(path or CERT) as f:
        m = re.search(r"-----BEGIN CERTIFICATE-----.*?-----END CERTIFICATE-----", f.read(), re.S)
    return hashlib.sha256(ssl.PEM_cert_to_DER_cert(m.group(0))).hexdigest()


def pinned_post(host, port, path, fields, fp, timeout=20):
    """HTTPS POST that only talks to the server whose certificate has the expected SHA-256 (no CA needed)."""
    import http.client
    ctx = ssl.create_default_context()
    ctx.check_hostname = False
    ctx.verify_mode = ssl.CERT_NONE
    c = http.client.HTTPSConnection(host, port, timeout=timeout, context=ctx)
    try:
        c.connect()
        got = hashlib.sha256(c.sock.getpeercert(binary_form=True)).hexdigest()
        if not fp or not hmac.compare_digest(got, fp):
            raise ValueError("certificate does not match the pinned one (possible interception)")
        c.request("POST", path, urlencode(fields), {"Content-Type": "application/x-www-form-urlencoded"})
        r = c.getresponse()
        return r.status, r.read(1 << 20).decode(errors="replace")
    finally:
        c.close()


def repo_raw():
    try:
        with open(OPT + "/repo") as f:
            return f.read().strip() or DEFAULT_REPO
    except OSError:
        return DEFAULT_REPO


def srv_code(sv_item, st):
    p = st["panel"]
    j = {"h": p["host"], "p": p["port"], "t": p["path"], "i": sv_item["id"], "s": sv_item["secret"], "f": cert_fp()}
    return "NTJ1:" + base64.urlsafe_b64encode(json.dumps(j, separators=(",", ":")).encode()).decode()


def srv_command(sv_item, st):
    return f'bash <(curl -fsSL {repo_raw()}/install.sh) --join "{srv_code(sv_item, st)}"'


def srv_add(name, ip):
    name = name.strip()
    if not re.match(r"^[\w .-]{1,24}$", name):
        return ERR + "Give the server a short name (letters, numbers, space, dot, dash)."
    if not valid_ip(ip):
        return ERR + "Enter the destination server's IPv4 address."
    d = srv_load()
    if any(x["ip"] == ip for x in d["servers"]):
        return ERR + "This IP is already in the list."
    d["servers"].append({"id": rnd(8).lower(), "name": name, "ip": ip, "status": "waiting",
                         "secret": secrets.token_urlsafe(18), "exp": int(time.time()) + 86400})
    srv_save(d)
    return f"Server {name} added. Run the join command on it (shown below)."


def srv_enroll(ip, f):
    """A destination server that ran the join command reports in (single-use secret + must come from its IP)."""
    try:
        j = json.loads(base64.urlsafe_b64decode(f.get("d", "").encode()))
        tok = j["token"]
        parse_token(tok)
        ag = j.get("agent") or {}
        agent = {"port": int(ag["port"]), "path": re.sub(r"[^A-Za-z0-9]", "", str(ag["path"]))[:32],
                 "key": str(ag["key"])[:64], "fp": re.sub(r"[^0-9a-f]", "", str(ag["fp"]))[:64]}
    except Exception:
        return 400, "bad request"
    d = srv_load()
    s = srv_find(d, str(j.get("i", "")))
    if (not s or s["status"] != "waiting" or s.get("exp", 0) < time.time()
            or not hmac.compare_digest(s.get("secret", ""), str(j.get("s", "")))):
        return 403, "refused"
    if ip != s["ip"]:
        s["last_reject"] = ip
        srv_save(d)
        return 403, "refused"
    pan = j.get("panel") or {}
    s.update(status="ready", token=tok, agent=agent, secret="", joined=int(time.time()), last_reject="",
             panel={k: str(pan.get(k, ""))[:200] for k in ("url", "user", "pw")})
    srv_save(d)
    return 200, "ok"


def agent_serve(st, f, ip):
    """Control channel of a destination (foreign) server. Only the stored key opens it; few, narrow commands."""
    k = "agent:" + ip
    cnt, until = Handler.fails.get(k, (0, 0))
    if cnt >= 8 and until > time.time():
        return 429, '{"err":"too many attempts"}'
    key = st.get("agent_key", "")
    if st["role"] != "foreign" or not key or not hmac.compare_digest(f.get("k", ""), key):
        Handler.fails[k] = (cnt + 1, time.time() + 300)
        time.sleep(1)
        return 403, '{"err":"denied"}'
    cmd = f.get("cmd")
    if cmd == "ping":
        out = {"ok": True, "v": VERSION}
    elif cmd == "token":
        out = {"ok": True, "token": make_token(st)}
    elif cmd == "testlisten":
        out = test_listen(st)
    elif cmd == "testend":
        test_end()
        out = {"ok": True}
    elif cmd == "all":
        msg = op_all_models(st)
        save(st)
        apply(st)
        out = {"ok": not msg.startswith(ERR), "msg": msg, "token": make_token(st)}
    elif cmd == "keep":
        ids = [x for x in f.get("arg", "").split(",") if find_tp(st, x)]
        if not ids:
            return 400, '{"err":"no valid tunnel"}'
        msg = op_set_ids(st, ids)
        if msg.startswith(ERR):
            return 400, json.dumps({"err": msg.lstrip(ERR)})
        save(st)
        apply(st)
        out = {"ok": True, "msg": msg, "token": make_token(st)}
    else:
        return 400, '{"err":"unknown command"}'
    return 200, json.dumps(out)


def agent_call(s, cmd, arg=""):
    a = s.get("agent") or {}
    if not a.get("key"):
        raise RuntimeError("no control channel (this server was added by pasting a token)")
    code, out = pinned_post(s["ip"], a["port"], f"/{a['path']}/agent", {"k": a["key"], "cmd": cmd, "arg": arg},
                            a.get("fp", ""), 90)
    d = json.loads(out)
    if code != 200 or not d.get("ok"):
        raise RuntimeError(d.get("err") or d.get("msg") or f"agent error {code}")
    return d


def join_cmd(code=""):
    """Run ON the destination server (by the one-line command): builds the exit side with every tunnel model
    and reports back to the panel that created the code. No SSH, no password."""
    need_root()
    try:
        j = json.loads(base64.urlsafe_b64decode(code.strip()[5:].encode()))
        host, port, path, sid, secret, fp = j["h"], int(j["p"]), j["t"], j["i"], j["s"], j["f"]
        assert code.strip().startswith("NTJ1:")
    except Exception:
        return say("Invalid join code. Copy the whole command from the panel's Servers tab.", R)
    if os.path.exists(STATE):
        return say("This server already has a tunnel. Remove it first (menu 11), then run the command again.", R)
    me = public_ip()
    if not valid_ip(me):
        me = ask("This server's public IP")
    try:
        iran_ip = host if valid_ip(host) else socket.gethostbyname(host)
    except OSError:
        return say("Could not resolve the panel address.", R)
    say("Building the exit side (every tunnel model, so they can be tested)...", G)
    boot = bool(_boot_panel())
    st, pw = core_foreign(me, iran_ip, "", "www.microsoft.com", list(CATALOG), list(CARRIERS), True, True, reuse_panel=boot)
    st["agent_key"] = secrets.token_urlsafe(24)
    save(st)
    start_bench(st)
    tok = make_token(st)
    pan = st["panel"]
    payload = {"i": sid, "s": secret, "token": tok,
               "agent": {"port": pan["port"], "path": pan["path"], "key": st["agent_key"], "fp": cert_fp()},
               "panel": {"url": panel_url(st), "user": pan["user"], "pw": pw or ""}}
    try:
        status, out = pinned_post(host, port, f"/{path}/enroll",
                                  {"d": base64.urlsafe_b64encode(json.dumps(payload).encode()).decode()}, fp, 30)
    except Exception as e:
        status, out = 0, str(e)
    if status == 200:
        say("Done. This server reported to the panel. Go back to the panel (Servers tab) to test and build the tunnel.", G)
    else:
        say(f"This server is ready, but could not reach the panel ({out}).", Y)
        print("In the panel: Servers > your server > 'Paste token', and paste this token:\n\n" + tok + "\n")
    if pw:
        print(f"This server's own panel: {panel_url(st)}  user: {pan['user']}  password: {pw}")


def servers_menu():
    need_root()
    st = load_any()
    d = srv_load()
    for x in d["servers"]:
        print(f"  {x['name']:20} {x['ip']:16} {x['status']}")
    if ask("Add a destination server? (y/n)", "n") != "y":
        return
    msg = srv_add(ask("Name"), ask("Its public IP"))
    if msg.startswith(ERR):
        return say(msg.lstrip(ERR), R)
    x = srv_load()["servers"][-1]
    say("\nRun this ONE line as root on the destination server:\n", G)
    print(srv_command(x, st) + "\n")



def start_bench(st):
    """The foreign panel process answers the tunnel tester; start it once (also right after a panel-driven setup)."""
    if st["role"] == "foreign" and not _BENCH_THREAD:
        test_end()  # remove test listeners/firewall rules left by a crash
        t = threading.Thread(target=bench_serve, args=(st,), daemon=True)
        t.start()
        _BENCH_THREAD.append(t)


def _write_boot(boot):
    os.makedirs(BASE, exist_ok=True)
    with open(BOOT, "w") as f:
        json.dump(boot, f)
    os.chmod(BOOT, 0o600)


def panel_report(st, pw):
    """Show the panel login and verify the panel really answers on its port."""
    show_panel(st, pw)
    port = st["panel"]["port"]
    up = False
    for _ in range(20):
        try:
            with socket.create_connection(("127.0.0.1", port), timeout=1):
                up = True
                break
        except OSError:
            time.sleep(0.5)
    if up:
        say("The panel is running. Open the URL above in your browser (accept the self-signed certificate "
            "warning if you did not give a domain).", G)
        say(f"If it does not open: allow TCP port {port} in your hosting provider's firewall too.", Y)
    else:
        say("The panel did not start. Log:", R)
        print(sh("journalctl -u night-tunnel-panel -n 15 --no-pager").stdout)


def panel_init():
    """Create the web panel first (no tunnel yet): everything else is then done from the browser."""
    need_root()
    if os.path.exists(STATE):
        return say("A tunnel is already configured here; menu 9 shows the panel and resets its password.", Y)
    if _boot_panel():
        say("The web panel already exists: making sure it runs and giving you a NEW password.", Y)
        return reset_panel()
    domain = ask("Domain for the panel (optional - press Enter to use this server's IP)")
    if domain and not valid_host(domain):
        return say("Invalid domain.", R)
    ip = public_ip() or ask("This server's public IP")
    if not valid_ip(ip):
        return say("Invalid IP.", R)
    p, pw = new_panel(domain, ip)
    boot = {"panel": p, "le": ""}
    _write_boot(boot)
    if make_cert(domain, "localhost"):
        boot["le"] = domain
        _write_boot(boot)
    fw_open(p["port"], "tcp")
    write_units()
    sh("systemctl enable night-tunnel-panel")
    sh("systemctl restart night-tunnel-panel")
    panel_report({"panel": p}, pw)
    say("In the panel: 'Servers' gives you one command for each destination server, tests the tunnel types "
        "and builds the tunnel; 'Telegram proxy' makes a proxy on this server.", G)


def show_panel(st, pw=None):
    p = st["panel"]
    say("\n=== Web panel ===", G)
    print(f"URL      : {panel_url(st)}")
    print(f"Username : {p['user']}")
    print(f"Password : {pw if pw else '(unchanged: the one you got when the panel was created; menu 9 resets it)'}")


def reset_panel():
    st = load_any()           # works before any tunnel exists (web panel created first)
    pw = rnd(16)
    st["panel"]["salt"] = secrets.token_hex(16)
    st["panel"]["pass_hash"] = hash_pw(pw, st["panel"]["salt"])
    if st["role"] == "new":
        boot = _boot_panel() or {"le": ""}
        boot["panel"] = st["panel"]
        _write_boot(boot)
        write_units()
        sh("systemctl enable night-tunnel-panel")
    else:
        save(st)
    sh("systemctl restart night-tunnel-panel")
    panel_report(st, pw)


def need_state():
    try:
        return load()
    except (OSError, ValueError):
        say("Not configured yet: create the web panel (16) or add a server (15).", R)
        return None


def commit(st, msg):
    if msg.startswith(ERR):
        say(msg[len(ERR):], R)
        return
    save(st)
    if not apply(st):
        msg += " (nothing to run yet)"
    say(msg, G)


def list_transports(st):
    pr = probe_all(st)
    print(f"{'#':3}{'ID':13}{'PORT':8}{'ON':5}{'STATE':7}TYPE")
    for i, t in enumerate(st["transports"], 1):
        print(f"{i:<3}{t['id']:13}{t['port']:<8}{'yes' if t['enabled'] else 'no':5}{pr[t['id']]:7}{desc(t)}")
    print(f"Mode: {st.get('strategy', 'fifo')}   Security: "
          + ("password (relay login)" if is_secure(st) else "NO PASSWORD (relay ports limited to the Iran IP)"))
    if st["role"] == "iran" and kernel_ports(st):
        print("Kernel-forwarded ports: " + ", ".join(f"{p['port']}->{p['via']}" for p in kernel_ports(st)))


def transports_menu():
    while True:
        st = need_state()
        if not st:
            return
        list_transports(st)
        print("\na) set active + priority order   b) mode (fifo/round/rand)   c) preset"
              "\nd) BUILD a tunnel: pick transport / kernel tunnel (foreign)"
              "\ne) delete a tunnel (foreign)   f) change port (foreign)"
              "\ng) add kernel carrier directly (foreign)"
              "\nh) EDIT a tunnel: port / transport type / SNI / ws path / host"
              "\ni) build EVERY model (so the Iran test can compare them all)"
              "\n0) back")
        c = input("Choose: ").strip().lower()
        if c == "0":
            return
        if c == "a":
            ids = ask("Transport ids in priority order, comma separated (others get disabled)")
            commit(st, op_set_ids(st, [x.strip() for x in ids.split(",") if x.strip()]))
        elif c == "b":
            m = ask("Mode", st.get("strategy", "fifo"))
            if m in ("fifo", "round", "rand"):
                st["strategy"] = m
                commit(st, "Mode: " + m)
        elif c == "c":
            n = ask("Preset (balanced/stealth/game/rotate)", "balanced")
            if n in ("balanced", "stealth", "game", "rotate"):
                preset(st, n)
                commit(st, "Preset applied: " + n)
        elif c == "d":
            if st["role"] != "foreign":
                say("Build tunnels on the foreign server, then Sync token here.", Y)
                continue
            show_catalog()
            tid = ask("Type to build (id from the list)")
            if tid in CARRIERS:
                commit(st, op_carrier_add(st, tid))
            else:
                name = ask("Name for this tunnel (several of one type allowed)", tid)
                port = ask("Port (empty = random)")
                sni = ask("TLS SNI for this tunnel (empty = global)") if tid in TLS_DIALERS else ""
                path = ask("WebSocket path (empty = default)") if tid in WS_TYPES else ""
                host = ask("WebSocket Host header (empty = none)") if tid in WS_TYPES else ""
                commit(st, op_tp_add(st, tid, name, port, sni, path, host))
        elif c == "e":
            commit(st, op_tp_del(st, ask("Delete which tunnel id")))
        elif c == "f":
            commit(st, op_tp_port(st, ask("Transport id"), ask("New port")))
        elif c == "g":
            commit(st, op_carrier_add(st, ask("Carrier (" + "/".join(CARRIERS) + ")")))
        elif c == "h":
            tid = ask("Tunnel id to edit")
            t = find_tp(st, tid)
            if not t:
                say("Unknown tunnel.", R)
                continue
            say(f"Editing {tid} (empty = keep current, '-' = reset to default)", Y)
            kw = {}
            nt = ask("Transport type", ttype(t)) if t["via"] == "direct" else ""
            if nt and nt != ttype(t):
                kw["new_type"] = nt
            p = ask("Port", str(t["port"]))
            if p != str(t["port"]):
                kw["port"] = p
            if t["via"] == "direct":
                eff = nt or ttype(t)
                for key in ("sni", "path", "host"):
                    if key == "sni" and eff not in TLS_DIALERS:
                        continue
                    if key != "sni" and eff not in WS_TYPES:
                        continue
                    v = ask(key.upper(), t.get(key, ""))
                    if v != t.get(key, ""):
                        kw[key] = "" if v == "-" else v
            commit(st, op_tp_edit(st, tid, **kw))
        elif c == "i":
            commit(st, op_all_models(st))
        if c in ("d", "e", "f", "g", "h", "i") and st["role"] == "foreign":
            say("Copy the new token to the Iran server:", Y)
            print(make_token(st))


def ports_menu():
    while True:
        st = need_state()
        if not st:
            return
        if st["role"] != "iran":
            return say("Ports are managed on the Iran server.", Y)
        print(f"\n{'PORT':8}{'PROTO':8}{'REMOTE':8}PATH")
        for p in st["ports"]:
            print(f"{p['port']:<8}{p['proto']:8}{p.get('target', 'same'):<8}{'kernel:' + p['via'] if p.get('via') else 'relay pool'}")
        kv = "/".join(["pool"] + list((st.get("l3") or {})))
        c = input("\na) add   b) edit   c) delete   0) back : ").strip().lower()
        if c == "0":
            return
        if c == "a":
            commit(st, op_port_add(st, ask("Port"), ask("Protocol (tcp/udp/both)", "tcp"),
                                   ask("Remote port (empty = same)"), ask(f"Path ({kv})", "pool")))
        elif c == "b":
            old = ask("Port to edit")
            cur = next((p for p in st["ports"] if str(p["port"]) == old), {})
            commit(st, op_port_edit(st, old, ask("New port", old), ask("Protocol (tcp/udp/both)", "tcp"),
                                    ask("Remote port (empty = same)"),
                                    ask(f"Path ({kv})", cur.get("via", "pool"))))
        elif c == "c":
            commit(st, op_port_del(st, ask("Port to delete")))


def sync_menu():
    st = need_state()
    if not st:
        return
    if st["role"] == "foreign":
        say("Token for the Iran server:", G)
        print(make_token(st))
    else:
        commit(st, op_import_token(st, ask("Paste the new token from the foreign server")))


def test_menu():
    st = need_state()
    if not st:
        return
    if st["role"] != "iran":
        return say("Run the test on the Iran server (entry side). The foreign server answers automatically "
                   "while its panel service is running.", Y)
    need_root()
    full = ask("Test type: 1) quick (connect + latency)  2) full (+ speed, ~10s per tunnel)", "2") != "1"
    say("Running... (speed tests use real bandwidth; users on the tunnel may notice for a moment)", Y)
    rep, err = run_bench(st, full=full, log=lambda m: print("  " + m))
    if err:
        return say(err.lstrip(ERR), R)
    print("\n" + bench_table(rep))
    say("\nRecommendation", G)
    for ln in rep["rec"]["lines"]:
        print(" - " + ln)
    names = [r["name"] for r in rep["results"] if r.get("ok")]
    if names:
        pick = ask("\nType a tunnel name to use it now, add ' only' to switch the others off (e.g. 'wss only'; Enter = skip)")
        if pick:
            nm, _, only = pick.partition(" ")
            return commit(st, op_use_tunnel(st, nm, only.strip() == "only"))
    if rep["rec"]["order"] and ask("\nApply the suggested order now (enable only the working tunnels)? (y/n)", "n") == "y":
        commit(st, op_bench_apply(st, rep))


def security_menu():
    st = need_state()
    if not st:
        return
    print("Current mode: " + ("WITH password (relay login + encrypted transports)" if is_secure(st)
                              else "NO password (relay ports limited to the Iran IP, plain transports unencrypted)"))
    if st["role"] != "foreign":
        return say("Change it on the foreign server, then Sync token here.", Y)
    need_root()
    secure = ask("Set mode: 1) with password  2) no password", "1" if is_secure(st) else "2") != "2"
    commit(st, op_security(st, secure))
    say("Copy the new token to the Iran server:", Y)
    print(make_token(st))


def update_tunnel_menu():
    st = need_state()
    if not st:
        return
    need_root()
    print(f"Foreign IP: {st['foreign_ip']}   Iran IP: {st['iran_ip']}   SNI: {st.get('sni', '')}")
    print("Empty = keep.")
    kw = {"foreign_ip": ask("New foreign IP"), "iran_ip": ask("New Iran IP"), "sni": ask("New SNI")}
    if st["role"] == "foreign":
        kw["rotate"] = ask("Rotate credentials + WireGuard keys? (y/n)", "n") == "y"
    commit(st, op_update_tunnel(st, **kw))
    if st["role"] == "foreign":
        say("Copy the new token to the Iran server:", Y)
        print(make_token(st))


def update_menu():
    print(f"Installed: v{VERSION}")
    rv = remote_version()
    print(f"Latest   : {'v' + rv if rv else 'unknown (no repo URL / no access)'}")
    c = input("a) update night-tunnel   b) update engine (gost)   0) back : ").strip().lower()
    if c in ("a", "b"):
        need_root()
        m = update_script() if c == "a" else update_gost()
        say(m.lstrip(ERR), R if m.startswith(ERR) else G)


def remove_menu():
    need_root()
    print("a) Delete ALL tunnels / config (keep night-tunnel installed)\nb) Uninstall night-tunnel completely "
          "(tunnels + script + services)\nc) Delete ONE tunnel (the others stay)\n0) back")
    c = input("Choose: ").strip().lower()
    if c == "c":
        st = need_state()
        if st:
            list_transports(st)
            commit(st, op_tp_del(st, ask("Tunnel id to delete")))
            if st["role"] == "foreign":
                say("Copy the new token to the Iran server:", Y)
                print(make_token(st))
        return
    if c in ("a", "b"):
        if ask("Type DELETE to confirm") != "DELETE":
            return say("Cancelled.", Y)
        purge = c == "b" and ask("Also remove the gost binary? (y/n)", "n") == "y"
        teardown(full=(c == "b"), purge=purge)
        say("Done.", G)
        if c == "b":
            sys.exit(0)


def status():
    st = need_state()
    if not st:
        return
    print(sh("systemctl is-active night-tunnel-gost night-tunnel-panel night-tunnel-l3").stdout)
    list_transports(st)
    if "wg" in st.get("l3", {}):
        print("wg handshake:", sh(f"wg show {DEV['wg']} latest-handshakes").stdout.strip() or "-")


def bbr():
    need_root()
    conf = open("/etc/sysctl.conf").read()
    if "tcp_congestion_control=bbr" not in conf:
        with open("/etc/sysctl.conf", "a") as f:
            f.write("\nnet.core.default_qdisc=fq\nnet.ipv4.tcp_congestion_control=bbr\n")
        sh("sysctl -p")
    say("BBR enabled.", G)


def menu():
    if not os.path.exists(STATE) and not _boot_panel():
        say("No tunnel and no web panel on this server yet.", Y)
        print("The web panel lets you do everything from the browser: add a destination server, test the\n"
              "tunnel types, and build the tunnel.")
        if ask("Create the web panel now? (y/n)", "y") != "n":
            panel_init()
    while True:
        say(f"\n=== night-tunnel v{VERSION} ===", G)
        print("1) Setup FOREIGN server (exit)\n2) Setup IRAN server (entry)\n3) Transports (edit / add / delete)"
              "\n4) Forwarded ports (Iran: add / edit / delete)\n5) Sync token\n6) Status\n7) Logs\n8) Restart"
              "\n9) Panel info / reset panel password\n10) Update (script / engine)\n11) Remove (delete tunnel / uninstall all)"
              "\n12) Enable BBR\n13) TEST tunnels (connect + speed + recommendation)"
              "\n14) Update tunnel settings (IPs / SNI / rotate keys)"
              "\n15) SERVERS: add a destination server (prints the one-line join command)"
              "\n16) WEB PANEL: create it / show its URL + new password (set up everything from the browser)"
              "\n17) Telegram proxy (separate from the tunnels)"
              "\n18) Security mode (with / without password)\n0) Exit")
        c = input("Choose: ").strip()
        try:
            if c == "1":
                setup_foreign()
            elif c == "2":
                setup_iran()
            elif c == "3":
                transports_menu()
            elif c == "4":
                ports_menu()
            elif c == "5":
                sync_menu()
            elif c == "6":
                status()
            elif c == "7":
                print(sh("journalctl -u night-tunnel-gost -n 40 --no-pager").stdout)
            elif c == "8":
                sh("systemctl restart night-tunnel-l3 night-tunnel-gost night-tunnel-panel")
                say("Restarted.", G)
            elif c == "9":
                reset_panel()
            elif c == "10":
                update_menu()
            elif c == "11":
                remove_menu()
            elif c == "12":
                bbr()
            elif c == "13":
                test_menu()
            elif c == "14":
                update_tunnel_menu()
            elif c == "15":
                servers_menu()
            elif c == "16":
                panel_init()
            elif c == "17":
                tg_menu()
            elif c == "18":
                security_menu()
            elif c == "0":
                return
        except FileNotFoundError:
            say("Not configured yet: create the web panel (16) or add a server (15).", R)


def engine_cmd():
    err = install_gost()
    if err:
        print(err, file=sys.stderr)
        sys.exit(1)


def main():
    a = sys.argv[1] if len(sys.argv) > 1 else "menu"
    if a == "join":
        return join_cmd(sys.argv[2] if len(sys.argv) > 2 else "")
    if a == "reset-yes":
        return teardown()
    if a == "uninstall-yes":
        return teardown(full=True, purge="--purge" in sys.argv)
    {"menu": menu, "panel": run_panel, "l3-up": l3_up, "l3-down": l3_down,
     "status": status, "apply": apply, "test": test_menu, "setup-foreign": setup_foreign,
     "setup-iran": setup_iran, "servers": servers_menu, "join": join_cmd, "panel-init": panel_init, "tg": tg_menu,
     "install-units": write_units, "install-engine": engine_cmd,
     "auto-foreign": lambda: auto_cmd("foreign"), "auto-iran": lambda: auto_cmd("iran")}.get(a, menu)()


if __name__ == "__main__":
    main()
