# Reunion merge campaign

Bringing the upstream mainline `qinz/reunion` into `codex/short-time-existence-align`.
Measured 2026-07-25; **not yet executed** — deferred to a dedicated branch so the
main line stays green for the `(N)` and forward-uniqueness math lanes.

## Why

`qinz/reunion` (remote `qinz` = `upstream` = `qinz1yang/differential-geometry`) is
the upstream mainline. It has done a large assumption-hygiene pass that we want:
in particular it **removed `[InnerProductSpace ℝ E]` from the model space** in
~953 of the 1539 files in our tree that mention it, and replaced ad-hoc
assumptions with `omit [A] [B] in` on the individual declarations.

An ambient inner product on the model space `E` is the wrong assumption: a
Riemannian metric is fibrewise data on `TangentSpace I x`, and the ambient
instance diamonds against it. This is a standing ruling — see `lessons.md`
(2026-07-25) for the failure mode and the correct repair pattern.

## Measured scope

Merge-base `67c9b6b2ce31c2e3b32f424a90c5d27d30995593`.

| quantity | value |
|---|---|
| reunion ahead of merge-base | 612 commits |
| ours ahead of merge-base | 148 commits |
| files differing (`DifferentialGeometry/`) | 4055 |
| files changed by us since base | 1199 |
| files changed by reunion since base | 3210 |
| **both sides changed** (conflict surface) | 352 |
| actually conflicted | 280 (125 `.lean`, 155 `.md`) |
| conflict hunks in `.lean` | 414 |
| of those, mechanically resolvable | 11 |
| **needing judgment** | **403** |
| conflicted Lean files with substantial both-side change | 111 / 125 |

After the textual merge there is a second phase: a full 10,623-module rebuild
plus the semantic fallout where reunion's 953-file assumption cleanup meets our
1199 changed files. Budget this as a multi-day campaign, not an afternoon.

## Conflict shape

The dominant pattern is *reunion removed an assumption / added `omit`* against
*we added content*. Resolution rule: **take reunion's assumption lines, keep our
content and docstrings.** Example (`RicciConnDiffPalatini.lean`): ours had
`omit [InnerProductSpace ℝ E] [NeZero …] [BoundarylessManifold I M] in` plus a
docstring; theirs had `omit [NeZero …] [BoundarylessManifold I M] in` +
`omit [SigmaCompactSpace M] [T2Space M] in` and no docstring in the hunk. Correct
result is their two `omit` lines followed by our docstring.

An automatic classifier (`scratchpad/resolve.py`, takes reunion's side when BOTH
sides of a hunk are only `omit`/`variable`/`import`/`set_option`/blank lines)
resolves 11 of 414. It is safe to run first, but do not expect it to carry the
merge.

## Execution plan

1. Branch `codex/reunion-merge` off the green ste-align head.
2. `git merge --no-commit --no-ff qinz/reunion`.
3. `.md` conflicts (155): take **ours** — our same-name notes and `PROJECT_MAP.md`
   are the live in-flight state per `CLAUDE.md`. (Done once already; redo.)
4. Run the hygiene classifier for the mechanical 11.
5. Resolve the remaining ~403 by hand, file by file, applying the rule above.
   Prioritize by build order: `Analysis/` → `Geometry/Connection` →
   `Geometry/Curvature` → `Geometry/Flow/RicciFlow` → `HCGCompactness`.
6. Full `lake build`; expect several rounds of semantic fallout.
7. Only fast-forward `codex/short-time-existence-align` once the merge branch is
   green and axiom-clean.

## Do not repeat

When a merge makes consumers fail to synthesize a newly-demanded instance, do
**not** add the instance to the consumers' variable blocks. That compensates for
a bad root and multiplies the diamond. Check whether the *producer* should be
demanding it. Twelve full-build rounds and ≈40 files were spent this way on
2026-07-25 before the direction was corrected; all of it was reverted.

## Status

- 2026-07-25 — main line verified GREEN (10623/10623, exit 0, 248 sorries unchanged, endpoints axiom-clean).
- 2026-07-25 — scope measured, merge attempted and cleanly aborted. The three-way
  target is reunion + ste-align + `codex/analytic-producers-e87b`; the e87b tail
  (3 documentation commits) is **already merged** into ste-align at `8a3ce03e8`,
  so only reunion remains outstanding.
- Root-cause fix for the model-space assumption landed separately on ste-align at
  `453900554` (canonical producer swap + three `omit`s in `RicciConnDiffPalatini`).
- Next action: create `codex/reunion-merge` and start at step 2.
