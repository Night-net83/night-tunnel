# Night Tunnel 1.7.0 — Agent-managed servers

- Removed the SSH/password-based Easy Setup flow from the menu and web panel.
- Added server registration and a one-time, expiring bootstrap command.
- Added outbound Agent heartbeat over TLS with certificate pinning for self-signed panels and system CA verification for matching Let's Encrypt hostnames.
- Added authenticated command polling/results and an allow-list of Night Tunnel operations; no arbitrary shell command API.
- Added remote setup for foreign and Iran roles, including the full available GOST transport catalog and all configured L3 carrier models.
- Added full candidate connectivity, latency, jitter, packet-loss and throughput testing before the user selects the primary tunnel.
- Added remote selection controls when the master panel is on the foreign side.
- Added Agent update handling and regenerated bootstrap commands for offline destinations.

## Validation performed

- Python syntax compilation for `nt.py` and `agent.py`.
- Bash syntax check for `install.sh`.
- Smoke tests for server registration, one-time bootstrap, authenticated Agent polling/results, panel result rendering, remote tunnel selection UI, and Agent operation allow-list.

A live end-to-end test on two VPS instances has not been performed in this environment.
