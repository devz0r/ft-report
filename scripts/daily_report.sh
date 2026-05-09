#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

usage() {
  cat <<'EOF'
Usage: scripts/daily_report.sh [--audit] [--help]

Runs the normal daily tracker report.

Options:
  --audit   After the tracker run, rebuild warehouse mirrors and run the warehouse audit.
  --help    Show this help text.
EOF
}

run_audit=false

case "${1:-}" in
  "")
    ;;
  --audit)
    run_audit=true
    ;;
  --help|-h)
    usage
    exit 0
    ;;
  *)
    echo "Unknown option: $1" >&2
    usage >&2
    exit 2
    ;;
esac

if [[ $# -gt 1 ]]; then
  echo "Too many arguments." >&2
  usage >&2
  exit 2
fi

echo "Running daily fantasy tracker report..."
python3.11 -B engine/fantasy_tracker.py

if [[ "$run_audit" == true ]]; then
  echo
  echo "Running optional warehouse audit backfills..."
  python3.11 -B engine/fantasy_tracker.py --backfill-warehouse-features-from-archive
  python3.11 -B engine/fantasy_tracker.py --backfill-warehouse-outcomes
  python3.11 -B engine/fantasy_tracker.py --audit-warehouse
fi

echo
echo "Daily report complete."
echo "  Local report: engine/tracker_report.html"
echo "  Live site: https://devz0r.github.io/ft-report/"
echo "  Reminder: GitHub Pages may take 5-10 minutes to update."
