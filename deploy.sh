#!/bin/bash
set -e

cd /opt/telegram-bot
git pull origin main
pip3 install -r requirements.txt --quiet
sudo systemctl restart telegram-bot

echo "Deploy completed at $(date)"
