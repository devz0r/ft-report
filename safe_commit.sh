#!/bin/bash
set -e

MSG="$1"

if [ -z "$MSG" ]; then
  echo "Usage: ./safe_commit.sh \"Commit message\""
  exit 1
fi

echo "Checking Python syntax..."
python3.11 -B -m py_compile engine/fantasy_tracker.py

echo "Running feature audit..."
python3.11 -B engine/fantasy_tracker.py --audit-features

echo "Current diff:"
git diff --stat

echo "Staging code only..."
git add engine/fantasy_tracker.py CODEX_PROJECT_BRIEF.md .gitignore 2>/dev/null || true

echo "Committing..."
git commit -m "$MSG"

echo "Rebasing on latest remote..."
git pull --rebase origin main

echo "Pushing..."
git push

echo "Done."
