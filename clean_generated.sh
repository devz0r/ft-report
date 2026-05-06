
#!/bin/bash

set -e

echo "Restoring generated/cache files to HEAD..."

git restore \

  engine/espn_players.json \

  engine/learned_biases.json \

  engine/predictions/*.jsonl \

  engine/tracker_snapshots/*.json \

  engine/streaming_cache/*.json \

  index.html \

  tracker_report.html 2>/dev/null || true

echo "Status after cleanup:"

git status --short

