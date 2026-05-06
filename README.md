# Fantasy Baseball SP Streaming Project

## Developer Workflow

1. Let Codex edit code/docs/scripts only.
2. Run `scripts/safe_commit.sh "message"` to preflight, stage code/docs only, commit, rebase, and push.
3. Only run the normal tracker after code is pushed, so generated reports and caches are produced by the production workflow.
4. If a local tracker run dirties generated files, run `scripts/clean_generated.sh` to restore the common generated/cache/report files.
