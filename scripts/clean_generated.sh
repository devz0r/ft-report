#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

paths=(
  "engine/espn_players.json"
  "engine/learned_biases.json"
  "engine/predictions/*.jsonl"
  "engine/tracker_snapshots/*.json"
  "engine/streaming_cache/*.json"
  "engine/streaming_cache/**/*.json"
  "index.html"
  "tracker_report.html"
)

echo "Restoring tracked generated/cache/report files..."
tracked="$(git ls-files -- "${paths[@]}")"
if [[ -n "$tracked" ]]; then
  while IFS= read -r path; do
    git restore -- "$path"
  done <<< "$tracked"
fi

echo "Removing local warehouse Parquet files..."
find engine/warehouse/predictions -type f -name '*.parquet' -delete 2>/dev/null || true
find engine/warehouse/outcomes -type f -name '*.parquet' -delete 2>/dev/null || true
find engine/warehouse/features -type f -name '*.parquet' -delete 2>/dev/null || true

echo "Removing local generated IL snapshot files..."
if [[ -d engine/streaming_cache/il_snapshots ]]; then
  untracked_il_snapshots="$(git ls-files --others --exclude-standard -- 'engine/streaming_cache/il_snapshots/*.json')"
  if [[ -n "$untracked_il_snapshots" ]]; then
    while IFS= read -r path; do
      rm -f -- "$path"
    done <<< "$untracked_il_snapshots"
  fi
fi

echo "Status after cleanup:"
git status --short
