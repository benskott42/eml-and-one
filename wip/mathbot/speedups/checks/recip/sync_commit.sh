#!/bin/bash
# sync speedups (minus __pycache__) into the checkpoint repo and commit locally (no push)
set -e
D=/workspace/mathbot-eao/wip/mathbot/speedups
rm -rf "$D"; mkdir -p "$D"
cp -a /workspace/eml-hub/speedups/. "$D/"
find "$D" -name __pycache__ -type d -prune -exec rm -rf {} +
cd /workspace/mathbot-eao
git add -A wip/mathbot
git -c user.name=mathbot -c user.email=mathbot@local commit -q -m "$1" && git rev-parse --short HEAD
