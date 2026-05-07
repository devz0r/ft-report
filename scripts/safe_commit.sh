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

echo "Clearing any pre-existing staged changes..."
git restore --staged -- .

scripts/preflight.sh

echo "Current diff:"
git diff --stat

echo "Staging allowed project files only..."
git add -- \
  engine/fantasy_tracker.py \
  engine/requirements.txt \
  scripts \
  README.md \
  CODEX_PROJECT_BRIEF.md \
  .gitignore

while IFS= read -r path; do
  git add -- "$path"
done < <(find engine/warehouse -type f \( -name '.gitkeep' -o -name '*.py' -o -name '*.sql' -o -name '*.md' \) 2>/dev/null)

echo "Checking for unexpected unstaged/untracked files..."
unexpected="$(git status --porcelain --untracked-files=all | awk '
  {
    path = substr($0, 4)
    if (path ~ / -> /) {
      split(path, parts, " -> ")
      path = parts[2]
    }
    if ($1 == "??" || substr($0, 2, 1) != " ") {
      print $0
    }
  }
')"
if [[ -n "$unexpected" ]]; then
  echo "Unexpected files remain after staging allowed project files:"
  echo "$unexpected"
  echo
  echo "Review these before committing. Generated files should be cleaned, and real new paths should be added to safe_commit.sh intentionally."
  git status --short
  exit 1
fi

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
