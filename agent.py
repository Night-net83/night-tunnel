#!/usr/bin/env python3
"""Night Tunnel managed remote agent.

The agent opens an outbound TLS connection to the master panel. It accepts only
allow-listed Night Tunnel operations; it never accepts arbitrary shell commands.
"""
import hashlib
import http.client
import importlib.util
import json
import os
import ssl
import time
import threading
import traceback
import urllib.parse

CONFIG = "/etc/night-tunnel-agent/config.json"
CACHE = "/var/lib/night-tunnel-agent/result.json"
AGENT_VERSION = "1.7.0"


def read_json(path, default):
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return default


def write_json(path, data):
    os.makedirs(os.path.dirname(path), mode=0o700, exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, separators=(",", ":"))
    os.chmod(tmp, 0o600)
    os.replace(tmp, path)


def load_engine():
    path = "/opt/night-tunnel/nt.py"
    spec = importlib.util.spec_from_file_location("night_tunnel_engine", path)
    if not spec or not spec.loader:
        raise RuntimeError("Night Tunnel engine is missing")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def execute(action, params):
    if os.geteuid() != 0:
        raise RuntimeError("Agent must run as root")
    nt = load_engine()
    if action == "status":
        if not os.path.isfile(nt.STATE):
            return {"configured": False, "agent": AGENT_VERSION}
        st = nt.load()
        return {"configured": True, "role": st.get("role"), "agent": AGENT_VERSION}

    if action == "setup_foreign":
        me, iran = params.get("me", ""), params.get("iran_ip", "")
        if not nt.valid_ip(me) or not nt.valid_ip(iran):
            raise RuntimeError("Invalid public IP supplied for foreign setup")
        transports = params.get("transports", list(nt.CATALOG))
        carriers = params.get("carriers", list(nt.CARRIERS))
        if not isinstance(transports, list) or not transports or any(x not in nt.CATALOG for x in transports):
            raise RuntimeError("Invalid transport selection")
        if not isinstance(carriers, list) or any(x not in nt.CARRIERS for x in carriers):
            raise RuntimeError("Invalid carrier selection")
        err = nt.install_gost()
        if err:
            raise RuntimeError(err)
        password = None
        if os.path.exists(nt.STATE):
            st = nt.load()
            if st.get("role") != "foreign":
                raise RuntimeError("Destination is already configured as an Iran server")
            message = nt.op_all_models(st)
            if message.startswith(nt.ERR):
                raise RuntimeError(message.lstrip(nt.ERR))
            message = nt.op_update_tunnel(st, foreign_ip=me, iran_ip=iran,
                                          sni=st.get("sni", "") or params.get("sni", ""))
            if message.startswith(nt.ERR):
                raise RuntimeError(message.lstrip(nt.ERR))
            nt.save(st)
            if not nt.apply(st):
                raise RuntimeError("Could not apply updated foreign configuration")
        else:
            st, password = nt.core_foreign(me, iran, params.get("domain", ""),
                params.get("sni") or "www.microsoft.com", transports, carriers, True,
                bool(params.get("secure", True)), reuse_panel=True)
        nt.start_bench(st)
        return {"token": nt.make_token(st), "panel": {
            "url": nt.panel_url(st), "user": st["panel"]["user"], "password": password}}

    if action == "setup_iran":
        d = nt.parse_token(params.get("token", ""))
        ports = params.get("ports")
        if not isinstance(ports, list) or not ports:
            raise RuntimeError("At least one forwarding port is required")
        clean = []
        for item in ports:
            port = int(item.get("port", 0))
            proto = item.get("proto", "tcp")
            if not 1 <= port <= 65535 or port == 22 or proto not in ("tcp", "udp", "both"):
                raise RuntimeError("Invalid forwarding port")
            clean.append({"port": port, "proto": proto})
        err = nt.install_gost()
        if err:
            raise RuntimeError(err)
        password = None
        if os.path.exists(nt.STATE):
            st = nt.load()
            if st.get("role") != "iran":
                raise RuntimeError("Destination is already configured as a foreign server")
            message = nt.op_import_token(st, params.get("token", ""))
            if message.startswith(nt.ERR):
                raise RuntimeError(message.lstrip(nt.ERR))
            for transport in st.get("transports", []):
                transport["enabled"] = True
            known = {x["port"] for x in st.get("ports", [])}
            for item in clean:
                if item["port"] not in known:
                    message = nt.op_port_add(st, item["port"], item["proto"])
                    if message.startswith(nt.ERR):
                        raise RuntimeError(message.lstrip(nt.ERR))
            nt.save(st)
            if not nt.apply(st):
                raise RuntimeError("Could not apply updated Iran configuration")
        else:
            st, password = nt.core_iran(d, params.get("domain", ""), clean, reuse_panel=True)
        return {"panel": {"url": nt.panel_url(st), "user": st["panel"]["user"], "password": password}}

    if action in ("select_tunnel", "use_best"):
        if not os.path.isfile(nt.STATE):
            raise RuntimeError("Night Tunnel is not configured")
        st = nt.load()
        if st.get("role") != "iran":
            raise RuntimeError("Tunnel selection must be applied on the Iran entry server")
        if action == "use_best":
            message = nt.op_use_best(st, bool(params.get("only", False)))
        else:
            name = str(params.get("name", ""))[:80]
            message = nt.op_use_tunnel(st, name, bool(params.get("only", False)))
        if message.startswith(nt.ERR):
            raise RuntimeError(message.lstrip(nt.ERR))
        nt.save(st)
        if not nt.apply(st):
            message += " (no active forwarding route yet)"
        return {"message": message}

    if action == "test":
        if not os.path.isfile(nt.STATE):
            raise RuntimeError("Night Tunnel is not configured")
        st = nt.load()
        if st.get("role") != "iran":
            raise RuntimeError("Tests must run on the Iran entry server")
        report, error = nt.run_bench(st, full=bool(params.get("full", True)),
                                     secs=max(2, min(8, int(params.get("secs", 4)))))
        if error or not report:
            raise RuntimeError((error or "Test failed").lstrip(nt.ERR))
        return {"table": nt.bench_table(report), "lines": report.get("rec", {}).get("lines", []),
                "results": report.get("results", [])}

    raise RuntimeError("Unsupported agent operation")


def main():
    with open(CONFIG, "r", encoding="utf-8") as f:
        cfg = json.load(f)
    parsed = urllib.parse.urlparse(cfg["master"])
    host, port = parsed.hostname, parsed.port or 443
    expected = cfg.get("cert_sha256", "").lower().replace(":", "")
    tls_mode = cfg.get("tls_mode", "pin")
    if tls_mode == "system":
        context = ssl.create_default_context()
    else:
        if not expected:
            raise SystemExit("Missing master TLS certificate pin; refusing insecure connection")
        context = ssl._create_unverified_context()
    state = {"result": read_json(CACHE, {}), "inflight": None}
    lock = threading.Lock()

    def run_command(command):
        cid = command["id"]
        try:
            data = execute(command.get("action", ""), command.get("params") or {})
            result = {"id": cid, "ok": True, "data": data}
        except Exception as exc:
            result = {"id": cid, "ok": False, "error": str(exc)[:1000]}
        with lock:
            state["result"] = result
            state["inflight"] = None
            write_json(CACHE, result)

    def connect_pinned():
        c = http.client.HTTPSConnection(host, port, timeout=25, context=context)
        c.connect()
        if tls_mode == "pin":
            cert = c.sock.getpeercert(binary_form=True)
            if hashlib.sha256(cert).hexdigest() != expected:
                c.close()
                raise RuntimeError("Master TLS certificate fingerprint mismatch")
        return c

    headers = {"X-NT-Agent": cfg["id"], "X-NT-Token": cfg["token"],
               "User-Agent": "NightTunnel-Agent/" + AGENT_VERSION}
    while True:
        conn = None
        try:
            conn = connect_pinned()
            conn.request("GET", "/nt-agent/poll", headers=headers)
            response = conn.getresponse()
            raw = response.read()
            if response.status != 200:
                raise RuntimeError("Master rejected agent: HTTP %s" % response.status)
            payload = json.loads(raw.decode("utf-8"))
            command = payload.get("command")
            result = None
            if command and command.get("id"):
                cid = command["id"]
                with lock:
                    cached = state.get("result") or {}
                    if cached.get("id") == cid:
                        result = cached
                    elif state.get("inflight") != cid:
                        state["inflight"] = cid
                        threading.Thread(target=run_command, args=(command,), daemon=True).start()
                if result:
                    body = json.dumps(result, separators=(",", ":")).encode()
                    conn.close()
                    conn = connect_pinned()
                    conn.request("POST", "/nt-agent/result", body=body,
                                 headers={**headers, "Content-Type": "application/json",
                                          "Content-Length": str(len(body))})
                    ack = conn.getresponse()
                    ack.read()
                    if ack.status not in (200, 409):
                        raise RuntimeError("Master did not acknowledge command result")
                    with lock:
                        state["result"] = {}
                        write_json(CACHE, {})
        except Exception as exc:
            print("Night Tunnel Agent:", str(exc), flush=True)
        finally:
            if conn:
                conn.close()
        time.sleep(5)


if __name__ == "__main__":
    main()
