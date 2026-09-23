#!/usr/bin/env bash
# Installatiescript voor de Telegram-assistent op een schone Ubuntu.
#
# Gebruik:
#   sudo bash install.sh /media/msi-bot/NAAM/assistent.env
#
# Zonder pad maakt het script een leeg instellingenbestand aan dat je
# daarna zelf invult met: sudo nano /etc/assistent/assistent.env

set -euo pipefail

REPO="https://raw.githubusercontent.com/F0xmountain/assistent/main"
ENV_SRC="${1:-}"
ENV_DST="/etc/assistent/assistent.env"
ENV_MISSING=0

if [[ $EUID -ne 0 ]]; then
  echo "Start dit script met sudo: sudo bash install.sh"
  exit 1
fi

stap() { echo; echo "==> $1"; }

stap "1/9 Systeem bijwerken (kan even duren)"
apt-get update
DEBIAN_FRONTEND=noninteractive apt-get -y upgrade
DEBIAN_FRONTEND=noninteractive apt-get -y install \
  python3-venv python3-pip unattended-upgrades ufw wget

stap "2/9 Slaapstand uitschakelen"
systemctl mask sleep.target suspend.target hibernate.target hybrid-sleep.target

stap "3/9 Doordraaien met deksel dicht"
mkdir -p /etc/systemd/logind.conf.d
cat > /etc/systemd/logind.conf.d/deksel.conf <<'EOF'
[Login]
HandleLidSwitch=ignore
HandleLidSwitchExternalPower=ignore
HandleLidSwitchDocked=ignore
EOF

stap "4/9 Firewall: inkomend dicht, uitgaand open"
ufw default deny incoming
ufw default allow outgoing
ufw --force enable

stap "5/9 Automatische beveiligingsupdates en herstart om 04:00"
cat > /etc/apt/apt.conf.d/20auto-upgrades <<'EOF'
APT::Periodic::Update-Package-Lists "1";
APT::Periodic::Unattended-Upgrade "1";
EOF
cat > /etc/apt/apt.conf.d/52automatische-herstart <<'EOF'
Unattended-Upgrade::Automatic-Reboot "true";
Unattended-Upgrade::Automatic-Reboot-Time "04:00";
EOF

stap "6/9 Gebruiker 'assistent' aanmaken"
if ! id assistent &>/dev/null; then
  adduser --system --group --home /opt/assistent assistent
fi
install -d -o assistent -g assistent -m 750 /opt/assistent/data

stap "7/9 Python-omgeving en libraries"
sudo -u assistent python3 -m venv /opt/assistent/venv
sudo -u assistent /opt/assistent/venv/bin/pip install --upgrade \
  "python-telegram-bot[job-queue]" google-genai

stap "8/9 Code en dienst downloaden van GitHub"
wget -q -O /tmp/bot.py "$REPO/bot.py"
wget -q -O /tmp/assistent.service "$REPO/assistent.service"
install -o root -g assistent -m 640 /tmp/bot.py /opt/assistent/bot.py
install -m 644 /tmp/assistent.service /etc/systemd/system/assistent.service

stap "9/9 Instellingen en dienst"
mkdir -p /etc/assistent
if [[ -n "$ENV_SRC" && -f "$ENV_SRC" ]]; then
  install -o root -g assistent -m 640 "$ENV_SRC" "$ENV_DST"
  echo "Instellingen overgenomen van $ENV_SRC"
elif [[ ! -f "$ENV_DST" ]]; then
  cat > "$ENV_DST" <<'EOF'
TELEGRAM_TOKEN=
GEMINI_API_KEY=
GEMINI_MODEL=gemini-3.6-flash
ALLOWED_USER_ID=
EOF
  chown root:assistent "$ENV_DST"
  chmod 640 "$ENV_DST"
  ENV_MISSING=1
fi

systemctl daemon-reload
systemctl enable assistent
if [[ $ENV_MISSING -eq 0 ]]; then
  systemctl restart assistent
fi

echo
echo "=============================================="
echo " Klaar."
if [[ $ENV_MISSING -eq 1 ]]; then
  echo " Vul eerst je instellingen in:"
  echo "   sudo nano $ENV_DST"
  echo " en start daarna: sudo systemctl restart assistent"
else
  echo " Status bekijken: systemctl status assistent"
fi
echo " Herstart daarna de laptop via het menu, zodat"
echo " de deksel-instelling actief wordt."
echo "=============================================="
