#!/bin/bash
set -e

cd /opt/telegram-bot
git pull origin main
source venv/bin/activate && pip install -r requirements.txt --quiet
sudo systemctl restart telegram-bot

echo "Deploy completed at $(date)"
