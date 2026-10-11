# CI log — erdos708 Lean development

Workflow: `.github/workflows/lean.yml` (`erdos708-lean`), GitHub Actions, repository
chy4pro/erdos-708-explicit-upper-bounds.

| Date | Run id | Commit | Content | Result |
|---|---|---|---|---|
| 2026-10-11 | [38164592298](https://github.com/chy4pro/erdos-708-explicit-upper-bounds/actions/runs/38164592298) | f4f02b8 | baseline (lakefile roots = FinalCheck, H883.Statement) | failure: imported modules not local to the lib (`Erdos708.Statement.olean does not exist`); fixed by root module `Erdos708.lean` |
| 2026-10-11 | [38164822858](https://github.com/chy4pro/erdos-708-explicit-upper-bounds/actions/runs/38164822858) | 7c0902a | baseline with root module | cancelled after start, superseded by the build-cache workflow |
| 2026-10-11 | [38164883443](https://github.com/chy4pro/erdos-708-explicit-upper-bounds/actions/runs/38164883443) | 363bbea | baseline + build cache | running |
| 2026-10-11 | [38165010473](https://github.com/chy4pro/erdos-708-explicit-upper-bounds/actions/runs/38165010473) | 8b1ed00 | + H883/Knapsack.lean | running |
| 2026-10-11 | [38164883443](https://github.com/chy4pro/erdos-708-explicit-upper-bounds/actions/runs/38164883443) | 363bbea | baseline + build cache | failure: runner shutdown signal 7.5 min into `lake build` (likely memory, parallel elaboration of the large H97 certificates); cache not saved |
| 2026-10-11 | [38165010473](https://github.com/chy4pro/erdos-708-explicit-upper-bounds/actions/runs/38165010473) | 8b1ed00 | + H883 knapsack card | cancelled (same memory risk); superseded by swap + sequential prebuild |
