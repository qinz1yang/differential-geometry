# HamiltonPositiveRicciAdapter

## 2026-07-24 fixed-time trace-free decay producer

Added `tf_decay0_of_cgh`, the direct time-zero transfer theorem for
`LimitTfDecayAt L 0`.  It combines the retained smooth-CGH scalar and intrinsic
Ricci-norm pullback convergence into convergence of
`|Ric|² - R² / 3`, freezes both source and limit functions at time zero, and
uses `FunctionPullbackTendsto.le_of_bound0` with the bound from
`ham3_tf_bound0` and the vanishing scale factor from `ham3_scale_decay`.

The source comparison is geometric rather than an added transfer predicate:
`Ham3SourceRealizes.metric_eq` identifies the source metric with the
cross-model pullback of the selected rescaling, and `tfRicNormSq_cross`
identifies the fully evaluated trace-free Ricci norms.  No new consumer
assumption, desired-conclusion wrapper, or strong maximum principle input was
introduced.

Focused verification passed after normalizing the fully applied scalar source
expression before rewriting the stored metric equality.  Thus
`tf_decay0_of_cgh` and its dedicated fixed-time transfer machinery are each
100%.  This does not complete the compactness endpoint:
`ham3_cgh_limit` remains theorem-level 0%, and the whole HCG machinery remains
about 60%.

## Current state — 2026-07-09 source realization and witness binding

`Ham3SourceLink` is now data, parameterized by the actual point-selection
witness.  It records the common-time inclusion, selected basepoint map, and
equality between each source metric and the pullback of the corresponding
`ham3RescaledSol` metric, while retaining the separate base-scalar identity.
`Ham3SourceLink.realizes` converts these fields mechanically into
`Ham3SourceRealizes` for the concrete `cghToHam3` record.

`HamCGHConclusion` now binds Ricci transfer, scalar positivity, and pinching
transfer inside the existential scope of the actual `L`, subsequence, smooth-CGH
witness, and completeness proof.  `toHam3Exists` no longer asks for any of
those conclusions for every arbitrary `Ham3CGHLimitData`, and boundarylessness
is obtained from the ambient model instance rather than presented as a fake
limit-topology producer.

Focused verification and the targeted adapter refresh passed after one local
namespace qualification.  The adapter contract is 100% checked infrastructure; construction of the actual
common-window source and the Hamilton compactness producer remain 0%.  Whole
HCG machinery remains about 45%, and endpoint theorems remain 0%.

The dated material below is historical unless an individual section explicitly
says otherwise.

## 2026-07-09 noncollapse cleanup

Removed the zero-callsite `noncollapseInput_of_ham3` projection and the arbitrary
numeric `NoncollapseInput` type it targeted.  The adapter must eventually
construct or identify the actual Hamilton rescaled `PointedFlowSeq`, prove
`IsFlowBaseVolBound`, and cross the single `flowInj_of_vol` CGT frontier.  A
basepoint scalar equality alone is insufficient to identify those flow balls.

Focused adapter verification is currently blocked before elaboration because
the shared workspace lacks `Lemma45Engine.olean` while that upstream source is
claimed by another active lane.  No adapter-local error has been observed.

Source used: the current `HamiltonPositiveRicci.lean` black-box interface around `Ham3CGHLimitData`, `Ham3LimitSubseq`, `Ham3LimitWindow`, `Ham3LimitFlow`, `Ham3CGHLimitExists`, and `ham3_cgh_limit`.

Introduced definitions: `pointedFlowToHam3` and theorem `toHam3Exists`.

2026-05-26 update: added `ham3OfCompactSol`, which is the intended derivation
shape for the Hamilton `ham3_cgh_limit` black box from the MSM135 Theorem 3.10
wrapper `compactnessSol`.  It takes the rescaled pointed-flow sequence `X`,
the three compactness inputs `CompleteInput`, `CurvBoundInput`, and `InjInput`,
the explicit time-zero metric compactness inputs, the derivative-input record,
and the smooth-flow upgrade backend. It then applies `compactnessSol` and feeds
the result through `toHam3Exists`.
The remaining explicit inputs are the Hamilton-specific limit-window,
regular-window, connectedness/boundarylessness, and tensor/scalar convergence
transfer producers.

Relation to `Ham3CGHLimitExists`: the adapter forgets the new convergence fields down to the current Section 12 limit-data record. The old proposition does not yet store the source rescaling relation, so the adapter needs the new compactness conclusion plus the fixed closed time-window inclusion and open regular-window inclusion.

2026-05-26 update: `Ham3CGHLimitExists` now also records connectedness and
boundarylessness for the limit.  The generic HCG `PointedFlowData` record does
not yet store those global manifold facts, so `toHam3Exists` takes them as
explicit adapter inputs rather than hiding them in the compactness conclusion.
This keeps the adapter checked while preserving the honest frontier: a future
CGH producer should prove connectedness/boundarylessness for limits of the
closed connected source manifolds.

2026-05-26 update: `Ham3CGHLimitExists` now also records basepoint scalar
convergence, the `Ham3RicNonnegTransfer` datum used by the Section 12 Ricci
nonnegativity inheritance step, and the `Ham3PinchTransfer` datum used by the
trace-free Ricci argument.  The adapter takes these as explicit inputs from the
HCG side; it does not pretend that the generic `PointedFlowData` record alone
contains those tensor/scalar/function-pullback convergence facts.

2026-05-27 update: `ham3OfCompactSol` was adjusted after `compactnessSol`
became an honest Theorem 3.10 wrapper requiring derivative and smooth-flow
upgrade inputs; the adapter still does not edit `HamiltonPositiveRicci.lean`.

2026-05-27 review update: after the pointed Riemannian rename and removal of
public `smoothPlus` fields from generic HCG data, the adapter now derives the
old `Ham3CGHLimitData.smooth_plus` field locally from `L.smooth`. The adapter
still only forgets the generic HCG conclusion into the old Hamilton endpoint
and does not edit `HamiltonPositiveRicci.lean`.

2026-05-27 update: added the first Hamilton transfer producer from the generic
smooth CGH convergence scaffold.  `Ham3BaseScalarSeq` records only the source
realization needed here: the time-zero basepoint scalar of the generic pointed
flow sequence is the Hamilton rescaled scalar from `(P,Q)`.  Then
`baseScalarConv_of_smoothCGH` proves `Ham3LimitBaseScalarConv` from
`SmoothCGHConverges.scalar_converges` and the comparison maps'
`basepoint_map`.  Consequently `toHam3Exists` and `ham3OfCompactSol` no longer
take the broad `hbaseScalar` transfer input; they take the narrower source
realization input and derive the scalar convergence internally.

Verification: focused checking passed for this file after refreshing stale
upstream HCG and curvature artifacts.  A later targeted adapter build was
blocked by an unrelated upstream failure in `DimensionThree/RicciControlsRm`;
the adapter source itself elaborated successfully.  Remaining explicit
Hamilton-specific inputs are connectedness, boundarylessness, Ricci
nonnegativity transfer, and pinching transfer.

2026-05-27 shape cleanup: moved connectedness and boundarylessness out of the
late Hamilton adapter assumptions.  The adapter now introduces
`HamCGHConclusion`, a Hamilton-specific strengthened compactness conclusion
containing the ordinary `SmoothCGHConverges` witness plus limit connectedness
and boundarylessness.  The package `HamCGHTopology` is the honest upstream
frontier: it should be proved from the connected/boundaryless source manifold
and the CGH construction, then used to lift `solutionCompactness`'s ordinary
`CompactnessConclusion`.  Consequently `toHam3Exists` consumes
`HamCGHConclusion`, while `ham3OfCompactSol` consumes `HamCGHTopology` and no
longer asks for per-limit `hconnected`/`hboundaryless` functions.

Verification: blocked before adapter elaboration by upstream Rm04 slot
migration failures in `RicciFlow/Evolution/ImprovedPinching/Definitions.lean`.
The visible upstream errors are old output/slot order assumptions now expecting
the corrected first-two input skew and standard `Rm04` order.  Re-run this file
after `ImprovedPinching.Definitions` is repaired.

2026-05-27 noncollapse producer update: added `noncollapseInput_of_ham3`,
which turns Hamilton's geometric `Ham3Noncollapse` ball/volume package into
the legacy HCG `NoncollapseInput` volume slot.  Because the Hamilton package is
eventual in the selected index while `NoncollapseInput` is currently a numeric
all-index record, the finite prefix is saturated by the lower-bound value
itself.  This does not prove the real noncollapse-to-injectivity-radius bridge;
that remains the next compactness producer needed by Theorem 3.10.

Verification: focused checking passed for this file.

2026-05-27 injectivity update: `ham3OfCompactSol` now carries `[I.Boundaryless]`
to pass the real normal-coordinate `FlowBaseInjBound` through
`compactnessSol`.  The adapter still does not edit `HamiltonPositiveRicci.lean`
and does not bridge the legacy `InjInput` to the new injectivity-radius
predicate.

Verification: focused checking of this adapter passed after the injectivity
update.  The targeted adapter module build and umbrella import are blocked by
the unrelated upstream `RicciFlow/Evolution/ImprovedPinching/Wrappers.lean`
slot-order mismatch at line 133, where the available `hRm` statement has the
last four slots ordered differently from the wrapper theorem input.

2026-05-27 alias cleanup: removed the HCG `LimitFlowData` abbrev and rewrote
the adapter directly over `PointedFlowData`.  The old namespace helper
`LimitFlowData.toHam3` is now the standalone adapter `pointedFlowToHam3`.

## 2026-06-19 comment cleanup

Moved source-comment lessons from `HamiltonPositiveRicciAdapter.lean` into this
same-name note.  The Lean comments now describe adapter interfaces without
embedding dated implementation plans.

Lessons preserved from the source comments:

- `HamCGHTopology` is consumed by the adapter.  Its producer belongs upstream in
  the CGH construction/source-topology transfer layer; connectedness and
  boundarylessness should not be treated as scalar or tensor convergence
  consequences.
- `noncollapseInput_of_ham3` only projects Hamilton's geometric noncollapse
  package into the legacy numeric `NoncollapseInput` slot.  Because the legacy
  record is all-index numeric data while the Hamilton package is eventual in the
  selected index, the finite prefix is saturated by the lower-bound value.  The
  real geometric producer remains the noncollapse-to-injectivity-radius bridge
  used by the Theorem 3.10 compactness interface.
- `toHam3Exists` forgets the strengthened HCG conclusion down to
  `Ham3CGHLimitExists`, including the fixed time window, regularity on the open
  window, topology facts, Ricci-flow predicate, Ricci nonnegativity transfer,
  basepoint scalar convergence, and pinching transfer.
- `ham3OfCompactSol` remains the intended replacement shape for the old
  `ham3_cgh_limit` black box: construct the pointed rescaled-flow sequence,
  prove the compactness inputs and smooth-flow upgrade inputs, then supply the
  Hamilton-specific scalar/tensor transfer producers from smooth CGH
  convergence.

Verification: focused checking passed for this cleanup pass.

## 2026-07-09 convergence-data retention

The old `pointedFlowToHam3` forgetful constructor was removed.  Its replacement
`cghToHam3` stores the actual source `PointedFlowSeq`, original Hamilton index
map, both strict-monotonicity proofs, `SmoothCGHConverges` witness and comparison
maps, source-to-original-manifold diffeomorphisms, and all-time limit
completeness.

`Ham3SourceLink` now exposes the original indexing and source topology instead
of pretending that a scalar equality alone realizes the Hamilton rescalings.
The stronger `HamCGHConclusion` includes limit completeness.  The arbitrary
`HamCGHTopology.lift` desired-conclusion wrapper and zero-callsite
`ham3OfCompactSol` were deleted; the adapter stops honestly at
`toHam3Exists` until the generic smooth-CGH limit-completeness/topology producer
is available.

The adapter theorem machinery is structurally complete, but the actual
common-window Hamilton source producer is about 20% and the Hamilton compactness
endpoint remains 0%.
