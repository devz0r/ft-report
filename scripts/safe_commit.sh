#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if [[ $# -lt 1 || -z "${1:-}" ]]; then
  echo "Usage: scripts/safe_commit.sh \"Commit message\""
  exit 1
fi

MSG="$1"

echo "Cleaning generated files before commit..."
scripts/clean_generated.sh

if [[ -n "$(git status --porcelain)" ]]; then
  allowed_regex='^.. (engine/fantasy_tracker\.py|engine/requirements\.txt|engine/warehouse/[^/]+/\.gitkeep|scripts/.*|README\.md|CODEX_PROJECT_BRIEF\.md|\.gitignore)$'
  unexpected="$(git status --porcelain | grep -Ev "$allowed_regex" || true)"
  if [[ -n "$unexpected" ]]; then
    echo "Unstaged changes remain after cleanup. Review them before committing:"
    git status --short
    exit 1
  fi
fi

scripts/preflight.sh

echo "Current diff:"
git diff --stat

echo "Staging code/docs/scripts only..."
git add -- \
  engine/fantasy_tracker.py \
  engine/requirements.txt \
  engine/warehouse/*/.gitkeep \
  scripts \
  README.md \
  CODEX_PROJECT_BRIEF.md \
  .gitignore

if git diff --cached --quiet; then
  echo "No staged code/docs changes to commit."
  exit 0
fi

echo "Committing..."
git commit -m "$MSG"

echo "Rebasing on latest remote..."
git pull --rebase origin main

echo "Pushing..."
git push

echo "Done."
