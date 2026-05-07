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

echo "Status after cleanup:"
git status --short
