# Fantasy Baseball SP Streaming Project

## Developer Workflow

1. Let Codex edit code/docs/scripts only.
2. Run `scripts/safe_commit.sh "message"` to clean generated files, preflight, stage code/docs/scripts only, commit, rebase, and push.
3. For a local report preview before pushing, run `python3.11 -B engine/fantasy_tracker.py --preview-local`, then open `engine/local_preview/tracker_report.html`.
4. Run the normal tracker only after code is committed/pushed, so generated reports and caches do not block the code commit.
5. If you intentionally need to clean without committing, run `scripts/clean_generated.sh` to restore the common generated/cache/report files.

## Warehouse Foundation

DuckDB + Parquet warehouse support is being added in parallel under `engine/warehouse/`.
For now, the existing JSON/JSONL files remain the source of truth; the warehouse is foundation-only and does not mirror predictions or outcomes yet.
Use `python3.11 -B engine/fantasy_tracker.py --audit-warehouse` to verify the folder skeleton and DuckDB initialization.
