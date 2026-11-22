#!/usr/bin/env bash
# night-tunnel one-line installer (Debian/Ubuntu)
set -e
REPO_RAW="${NT_REPO_RAW:-https://raw.githubusercontent.com/Night-net83/night-tunnel/main}"
[ "$(id -u)" -ne 0 ] && { echo "Run as root."; exit 1; }
command -v apt-get >/dev/null || { echo "Debian/Ubuntu only."; exit 1; }
export DEBIAN_FRONTEND=noninteractive

echo "[1/4] Installing dependencies..."
apt-get update -y >/dev/null
apt-get install -y python3 curl jq openssl iproute2 iptables wireguard-tools iputils-ping ca-certificates openssh-client sshpass >/dev/null

echo "[2/4] Installing gost..."
if ! command -v gost >/dev/null 2>&1; then
  case "$(uname -m)" in
    x86_64) A=amd64;; aarch64|arm64) A=arm64;; armv7l) A=armv7;;
    *) echo "Unsupported arch"; exit 1;;
  esac
  URL="${GOST_URL:-}"
  if [ -z "$URL" ]; then
    URL=$(curl -fsSL https://api.github.com/repos/go-gost/gost/releases/latest \
      | jq -r --arg s "_linux_${A}.tar.gz" '.assets[].browser_download_url | select(endswith($s))' | head -1)
  fi
  [ -z "$URL" ] && { echo "Could not find gost release. Set GOST_URL=<tar.gz link> and retry."; exit 1; }
  T=$(mktemp -d)
  curl -fsSL "$URL" -o "$T/g.tgz"
  tar -xzf "$T/g.tgz" -C "$T" gost
  install -m 755 "$T/gost" /usr/local/bin/gost
  rm -rf "$T"
fi

echo "[3/4] Installing night-tunnel..."
mkdir -p /opt/night-tunnel /etc/night-tunnel
if [ -f "$(dirname "$0")/nt.py" ] && [ "${0##*/}" = "install.sh" ]; then
  cp "$(dirname "$0")/nt.py" /opt/night-tunnel/nt.py
else
  curl -fsSL "$REPO_RAW/nt.py" -o /opt/night-tunnel/nt.py
fi
echo "$REPO_RAW" > /opt/night-tunnel/repo
chmod 700 /opt/night-tunnel/nt.py
printf '#!/bin/sh\nexec python3 /opt/night-tunnel/nt.py "$@"\n' > /usr/local/bin/night-tunnel
chmod +x /usr/local/bin/night-tunnel

python3 /opt/night-tunnel/nt.py install-units

echo "[4/4] Done. Run: night-tunnel"
[ -n "${NT_NONINTERACTIVE:-}" ] && exit 0
exec night-tunnel </dev/tty
