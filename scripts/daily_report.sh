#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

usage() {
  cat <<'EOF'
Usage: scripts/daily_report.sh [--audit] [--lineups] [--help]

Runs the normal daily tracker report.

Options:
  --audit    After the tracker run, rebuild warehouse mirrors and run the warehouse audit.
  --lineups  Refresh hitter lineup cache, then generate a local preview report.
  --help     Show this help text.
EOF
}

run_audit=false
run_lineups=false

case "${1:-}" in
  "")
    ;;
  --audit)
    run_audit=true
    ;;
  --lineups)
    run_lineups=true
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

if [[ "$run_lineups" == true ]]; then
  echo "Refreshing hitter lineups and building local preview..."
  python3.11 -B engine/fantasy_tracker.py --refresh-hitter-lineups
  python3.11 -B engine/fantasy_tracker.py --preview-local
  echo
  echo "Lineup preview complete."
  echo "  Local preview: engine/local_preview/tracker_report.html"
  echo "  Use this later in the day when MLB lineups are closer to posting."
  exit 0
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
echo
echo "Closer to first pitch, refresh hitter lineup context with:"
echo "  scripts/daily_report.sh --lineups"
echo "or:"
echo "  python3.11 -B engine/fantasy_tracker.py --refresh-hitter-lineups"
echo "  python3.11 -B engine/fantasy_tracker.py --analyze-hitter-context-coverage"
