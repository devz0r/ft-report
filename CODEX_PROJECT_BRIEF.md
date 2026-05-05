
# Fantasy Baseball SP Streaming Project

## Goal

Maintain and improve a fantasy baseball starting pitcher streaming/projection system.

## Current app

- Python 3.11

- Main file: engine/fantasy_tracker.py

- Current architecture is mostly a single-file CLI script.

- GitHub Actions runs production.

- Output is an encrypted/static HTML report published to GitHub Pages.

- Current storage is JSON/JSONL.

## Do not break

- Existing JSON/JSONL behavior

- GitHub Actions workflow

- HTML report generation

- learned_biases.json behavior

- predictions JSONL files

- predictions_outcomes.jsonl

- ESPN cookies must stay local and gitignored

## Development rules

- Make small scoped changes.

- Do not rewrite fantasy_tracker.py wholesale unless explicitly asked.

- Preserve current scoring unless explicitly asked.

- Add audits before changing behavior.

- Avoid data leakage.

- Any pregame feature must only use information available before the game/snapshot.

- Every new feature should be logged, auditable, and null-safe.

- Report changed files and commands run.

## Near-term roadmap

1. Add FEATURE_REGISTRY and --audit-features.

2. Add workload/leash features.

3. Add weather/roof features.

4. Upgrade opponent context toward projected/confirmed lineup quality.

5. Add defense/catcher context.

6. Add bullpen fatigue.

7. Add odds/market context.

8. Add DuckDB + Parquet dual-write storage later.

## Important

The existing model already works. Improve it incrementally.

