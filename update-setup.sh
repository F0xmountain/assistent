#!/usr/bin/env bash
# Stelt automatisch bijwerken in: elke 10 minuten kijkt de laptop of bot.py
# op GitHub is veranderd. Zo ja: controleren, installeren, herstarten, en
# bij problemen terug naar de vorige versie. Je krijgt een Telegram-bericht.
#
# Gebruik: sudo bash update-setup.sh

set -euo pipefail

if [[ $EUID -ne 0 ]]; then
  echo "Start dit script met sudo: sudo bash update-setup.sh"
  exit 1
fi

echo "==> Updatescript schrijven"
cat > /usr/local/bin/assistent-update <<'SCRIPT'
#!/usr/bin/env bash
set -euo pipefail

REPO="https://raw.githubusercontent.com/F0xmountain/assistent/main"
DEST="/opt/assistent/bot.py"
BACKUP="/opt/assistent/bot.py.vorige"
ENV="/etc/assistent/assistent.env"

# Token en user-ID inlezen voor de Telegram-melding
set -a
source "$ENV"
set +a

melding() {
  wget -q -O /dev/null \
    --post-data "chat_id=${ALLOWED_USER_ID}&text=$1" \
    "https://api.telegram.org/bot${TELEGRAM_TOKEN}/sendMessage" || true
}

TMP=$(mktemp)
trap 'rm -f "$TMP"' EXIT

wget -q -O "$TMP" "$REPO/bot.py" || exit 0   # geen internet: later opnieuw

# Niets veranderd: klaar
if cmp -s "$TMP" "$DEST"; then
  exit 0
fi

# Is het geldige Python? Zo niet: oude versie laten draaien
if ! /opt/assistent/venv/bin/python -c "import ast,sys; ast.parse(open(sys.argv[1]).read())" "$TMP"; then
  melding "⚠️ Update afgebroken: bot.py op GitHub bevat een syntaxfout. De oude versie blijft draaien."
  exit 1
fi

cp -p "$DEST" "$BACKUP"
install -o root -g assistent -m 640 "$TMP" "$DEST"
systemctl restart assistent
sleep 20

if systemctl is-active --quiet assistent; then
  melding "✅ Bot bijgewerkt naar de nieuwste versie van GitHub."
else
  install -o root -g assistent -m 640 "$BACKUP" "$DEST"
  systemctl restart assistent
  melding "⚠️ Nieuwe versie startte niet. Terug naar de vorige versie. Kijk in het logboek: journalctl -u assistent"
fi
SCRIPT
chmod 755 /usr/local/bin/assistent-update

echo "==> Systemd-dienst en timer schrijven"
cat > /etc/systemd/system/assistent-update.service <<'EOF'
[Unit]
Description=Bot-code bijwerken vanaf GitHub
After=network-online.target
Wants=network-online.target

[Service]
Type=oneshot
ExecStart=/usr/local/bin/assistent-update
EOF

cat > /etc/systemd/system/assistent-update.timer <<'EOF'
[Unit]
Description=Elke 10 minuten controleren op nieuwe bot-code

[Timer]
OnBootSec=2min
OnUnitActiveSec=10min

[Install]
WantedBy=timers.target
EOF

systemctl daemon-reload
systemctl enable --now assistent-update.timer

echo
echo "Klaar. Controleren: systemctl list-timers assistent-update.timer"
