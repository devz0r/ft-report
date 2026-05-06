#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

python3.11 -B -m py_compile engine/fantasy_tracker.py
python3.11 -B engine/fantasy_tracker.py --audit-features
