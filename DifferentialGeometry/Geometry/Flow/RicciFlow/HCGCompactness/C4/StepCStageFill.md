# StepCStageFill

## Route

This file implements Route A's smooth two-bump safety-totalization layer.  A
fixed safety clamp globalizes the reverse transition, and a fixed activity
cutoff interpolates between that target and the source point.  No pointwise
chart selector or equality-test `activeFill` occurs in the smooth map.

## Status

- `safeFill`, `safeFill_smooth`, and `safeFill_diag` implement the generic
  smooth filler and its reindexed `C^∞` diagonal convergence.
- `activityBump` and `safetyBump` implement the fixed `6/7` and `7/8` radius
  gaps.  `stageClamp_mapsTo` is the global target-domain safety statement and
  `stageFill_eq_raw` is the exact active-region readout.
- `stageTotal` totalizes only over the fixed finite slot index, retaining the
  old `InterSlot L ... alpha`; there is no pointwise chart selector or old/new
  subtype equivalence.
- `stageWeightSub`, `stagePtsSub`, and `stageCfgSub` are the actual refined
  finite-stage configuration.  `HasSuppConvData.cfgSub_conv` proves its full
  all-reindexing `MapCInfConvOnCompacts` convergence to the diagonal
  configuration on every source patch.
- `stagePtsSub_eq_ne` proves that a nonzero actual weight at a retained
  interacting target makes the smooth filler exactly the raw two-transition
  target.
- `HasSuppConvData.pts_eq_ne` takes one finite common tail and proves that every
  arbitrary nonzero actual slot selects such an old `InterSlot`, then applies
  the exact raw-target readout.  Stable-disjoint slots are therefore vacuous on
  the same tail.
- `HasSuppConvData` now retains the all-stage two-sided transition smoothness
  already produced by the common finite-pair tail; this is producer output,
  not a new compactness input.

Focused verification passed for `StepCStageFill`, the strengthened upstream
`StepCProducers`, `StepCSupportCapstone`, and `StepB1RawProducer`; the two
explicit producer modules were refreshed successfully.

The Route-A filler/configuration subphase is checked (100%).  The first
genuinely new analytic frontier is common-domain center-equation convergence and a
moving implicit-root family with one parameter neighborhood.  The concrete
`StepB1RawInput` producer and textbook Step B1 theorem remain theorem-level
0%.  Rounded machinery estimates are about 95% for Step-B/B1, 87% for Chapter
4, and 57% for the whole HCG project.

## 2026-07-16 buffered-cover compatibility

The four direct `HasSuppConvData` decompositions now retain and ignore, where
appropriate, the new convexity, origin, and uniform closed-ball buffer fields
before reading the existing core-cover, geometry, weight, and transition
fields.  No stage-filler statement or radius was changed.  Focused verification
passed after this projection-only migration.

`StepB1RawInput` and textbook B1 remain theorem-level 0%.  Dedicated Step-B/B1
machinery is roughly 98%, Chapter-4 machinery roughly 90%, and whole-HCG
machinery roughly 60%.

## 2026-07-18 framed-radius migration

All four stage-coordinate consumers now take the direct item-3 hypothesis
`8 * lamInf <= expRadiusGp`: `stageWeight_small`, `stagePts_eq_weight`,
`stagePtsSub_eq_ne`, and `HasSuppConvData.pts_eq_ne`.  The same `hGp` witness is
passed unchanged to `weight_trans_small`; no coercivity or raw-chart radius
bridge remains in this file.

Focused verification reached `stageWeight_small` and failed only because the
imported `StepCPairTail.olean` still exports the old
`weight_trans_small` parameter `8 * lamInf <= expMapC2Radius`.  The live
`StepCPairTail.lean` source already has the required `expRadiusGp` signature,
so this is a stale exact-module artifact rather than a source error in
`StepCStageFill`.  No downstream build was run here.

## 2026-07-18 selected framed chart seam

The three Route-A finite-stage readouts now use the canonical framed chart:
`stageWeightSub_eq` evaluates the global weight at `framedChartAt.symm`, while
`HasSuppConvData.weightSub_ev` and `HasSuppConvData.pts_eq_ne` use
`framedExpDiffeo` for the represented source point.  The stabilized
`normalTransition` alias remains unchanged.

Focused verification accepts the exact weight readout and stops only at the
two uses of `hgeom`: the imported `StepCProducers.olean` still exposes the old
raw `expMapDiffeo` version of `HasSuppConvData`, whereas the live
`StepCProducers.lean` source already exposes `framedExpDiffeo`.  This is a
stale-interface blocker, not a new proof or mathematical failure in this file.
No targeted build was run.

After the ordered upstream refresh and the exact-green `StepCProducers`
rebuild, the same `StepCStageFill` source passed its focused check with zero
diagnostics.  No targeted `StepCStageFill` build was run.  The selected framed
filler/configuration layer is therefore source-checked (100%); the downstream
global comparison-map and `StepB1RawInput` producers are still not revalidated,
and textbook B1 remains theorem-level 0%.
