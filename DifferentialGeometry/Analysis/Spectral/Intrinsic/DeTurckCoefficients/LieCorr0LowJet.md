# LieCorr0LowJet

## Proved-source targets

- `pureTrace` and `pureTrace_split` expose the canonical moving cometric
  double trace from the curvature coefficient tower.
- `lc0Trace_fiber` identifies the reindexed field with the trace step used by
  `lieCorr0`.
- `riem_refold` writes the fixed-curvature correction as one moving trace
  applied to one fixed smooth curvature passenger.
- `trace2_grid` gives pointwise covariant-jet control of that moving trace by
  the intrinsic antidiagonal metric-jet window.

The exact first-order Leibniz factors are therefore
`trace^0 * fixed^0` at order zero and
`trace^1 * fixed^0 + trace^0 * fixed^1` at order one.  No pointwise second
metric derivative is requested.

## Verification state

2026-07-25: **RED — STOP (deep WIP, out of dedup scope).**

After the TensorRS topology dedup + the mechanical `set_option
backward.isDefEq.respectTransparency false` (added after `noncomputable section`,
same as `LieCorr0Split`), the FiberBundle/VectorBundle synthesis blocker is
GONE — no bundle-synthesis errors remain. But `lake build +LieCorr0LowJet`
still fails with ~40 pre-existing errors that are NOT mechanical hygiene:

- **Syntax errors**: `unexpected token ':='` at lines 1381, 1520; `expected
  token` at 1598 (the 1598 error breaks the `private theorem riemRest_smooth`
  defined at 1597, cascading to "unknown identifier riemRest_smooth" at 1629).
- **Embedded `sorry`s** in hypotheses (e.g. `htie : … = … + sorry`, `hbound :
  sorry`) at 91, 119, 1772, 1794, …
- **Unresolved identifiers**: `ccTensorBilinSymm` (exists in
  `MetricRealization/TensorHsRealize.lean:395` but unimported here),
  `gFibreOpBound` (exists in `MetricRealization/PosDefPerturbation.lean:70`,
  unimported), `lieCorr0IVPerm` (no definition found).
- **Genuine proof failures**: type mismatches (123, 1756), application type
  mismatches (263, 392, 418), rewrite failures (1232, 1288, 1644, 1772, 1794),
  `No goals` (312), positivity failure (1693), whnf/tactic heartbeat timeout
  (232, 234).

Bringing this file green requires fixing syntax, resolving `sorry`s, adding
imports, and repairing proofs — theorem-statement / genuine-proof work beyond
the mechanical-hygiene guardrail. The transparency `set_option` was kept (it is
a correct, necessary partial fix) but is necessary-not-sufficient. Endpoint
completion remains 0%.
