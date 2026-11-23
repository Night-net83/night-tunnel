#!/usr/bin/env bash
# Night Tunnel installer (Debian/Ubuntu)
set -euo pipefail
REPO_RAW="${NT_REPO_RAW:-https://raw.githubusercontent.com/Night-net83/night-tunnel/main}"
[ "$(id -u)" -eq 0 ] || { echo "Run as root."; exit 1; }
command -v apt-get >/dev/null || { echo "Debian/Ubuntu only."; exit 1; }
export DEBIAN_FRONTEND=noninteractive

apt-get update -y
apt-get install -y python3 curl jq openssl iproute2 iptables wireguard-tools iputils-ping ca-certificates

mkdir -p /opt/night-tunnel /etc/night-tunnel
if [ -f "$(dirname "$0")/nt.py" ]; then
  cp "$(dirname "$0")/nt.py" /opt/night-tunnel/nt.py
  [ ! -f "$(dirname "$0")/agent.py" ] || cp "$(dirname "$0")/agent.py" /opt/night-tunnel/agent.py
else
  curl -fsSL "$REPO_RAW/nt.py" -o /opt/night-tunnel/nt.py
  curl -fsSL "$REPO_RAW/agent.py" -o /opt/night-tunnel/agent.py
fi
chmod 700 /opt/night-tunnel/nt.py
[ ! -f /opt/night-tunnel/agent.py ] || chmod 700 /opt/night-tunnel/agent.py
echo "$REPO_RAW" > /opt/night-tunnel/repo
chmod 600 /opt/night-tunnel/repo
printf '#!/bin/sh\nexec python3 /opt/night-tunnel/nt.py "$@"\n' > /usr/local/bin/night-tunnel
chmod +x /usr/local/bin/night-tunnel
python3 /opt/night-tunnel/nt.py install-units
python3 /opt/night-tunnel/nt.py install-engine

if [ -n "${NT_NONINTERACTIVE:-}" ]; then
  echo "Night Tunnel installed. Run: night-tunnel"
  exit 0
fi
exec night-tunnel </dev/tty
