# RicciDifferenceMeanValue

## 2026-07-15: generic realized-family joint Gram

`genGram_of_family` now converts an arbitrary `MetricFamilySmoothOn D G` into
`GenJointGram (fun t => G.metric t) α D.regular`.

The proof feeds the actual trivialization frame
`(trivializationAt E (TangentSpace I) α).localFrame (chartModelBasis E)` to
`frameCompSmooth`, identifies those frame components with `chartGramMatrix`, and
then pulls them back by `(t, y) ↦ (t, (extChartAt I α).symm y)` in the Euclidean
self-model.  This avoids whole-product model normalization.  Positive determinant
is supplied directly by `chartGramMatrix_det_pos`.

Focused verification passed.  The first check found two routine statement-shape
issues: the inverse-chart composition needed an explicitly typed `MapsTo`, and a
neighborhood of `D.regular` must come from `D.regular_isOpen` rather than
`D.regular_mem_nhds` (which gives a neighborhood of `D.carrier`).  Both were fixed.

No new assumptions, `HasLocallyConstantChartAt`, or consumer wrapper were added.
No separate generic inverse/cometric theorem is needed: the existing
`gen_joint_invGram` and the rest of the generic Gram tower consume this producer
directly.

Two direct chart-source consumers are now also verified:

- `invGram_of_family` packages `genGram_of_family` through
  `gen_joint_invGram`, proving joint smoothness of
  `(x, t) ↦ chartInvGramMatrix (G.metric t) α x i j` on
  `(chartAt H α).source ×ˢ D.regular`.
- `christ_of_family` uses the same chart-time move with
  `gen_joint_christoffel`, proving joint smoothness of
  `(x, t) ↦ chartChristoffel (G.metric t) α i j k (extChartAt I α x)` on the
  same set.

Both focused checks passed.  These are concrete consumers of the generic Gram
tower, not new inverse or connection assumptions; `christ_of_family` is the
current scalar chart bridge for the connection-trace coefficient route.

Accounting: `genGram_of_family`, `invGram_of_family`, and `christ_of_family`
theorems 100%; their dedicated machinery 100%.
The all-scale moving-Laplacian time-continuity theorem remains unstated/unproved
(0%), with its dedicated machinery roughly 70%.  The Perelman noncollapsing
endpoint remains 0%; whole HCG dedicated machinery remains roughly 57%, with its
endpoint theorems still 0%.

## 2026-07-15: generic cometric operator tower

The generic family route now reaches the invariant cometric operators without
specializing back to `realizedFam`:

- `invSharp_of_family` proves joint smoothness of the inverse-metric sharp
  Hom-section on `univ ×ˢ D.regular` from `invGram_of_family`.
- `comRaise_of_family` proves joint smoothness after raising slot zero of a
  jointly smooth covariant tensor family.  Its proof evaluates the Hom-section
  on an actual smooth covector section and uses the joint interior product.
- `comTrace_of_family` composes that raise with the natural trace and the unit
  rank-zero section to obtain joint smoothness of the cometric double trace.

All three focused checks passed.  The proofs stay in applied fibre normal form:
they do not assert equality of whole Hom models, add a chart-selector hypothesis,
or introduce a consumer-side regularity assumption.  This is the reusable
producer chain needed by the connection-difference and moving-Laplacian lanes.

Accounting: all six generic family producers in this note are proved (100%),
and their dedicated joint-smoothness tower is 100%.  The all-scale
moving-Laplacian time-continuity theorem itself is still unstated/unproved (0%);
its broader dedicated machinery is now roughly 72%, with uniform intrinsic
operator-norm control still outside this file.  The Perelman noncollapsing
endpoint remains 0%.  Whole HCG dedicated machinery remains roughly 57%, and
its endpoint theorems remain 0%.
