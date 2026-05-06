# Fantasy Baseball SP Streaming Project

## Developer Workflow

1. Let Codex edit code/docs/scripts only.
2. Run `scripts/safe_commit.sh "message"` to clean generated files, preflight, stage code/docs/scripts only, commit, rebase, and push.
3. Run the normal tracker only after code is committed/pushed, so generated reports and caches do not block the code commit.
4. If you intentionally need to clean without committing, run `scripts/clean_generated.sh` to restore the common generated/cache/report files.
