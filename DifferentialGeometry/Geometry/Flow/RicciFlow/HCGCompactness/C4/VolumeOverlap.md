# VolumeOverlap.lean — A0′ producer (brick B7)

Same-name note for `VolumeOverlap.lean`.  Verification: **focused check + targeted
build both PASS**; grep-clean of `sorry`/`axiom` in the file (only the docstring
mentions the word).  `#print axioms volInput_of_bg` = `[propext, sorryAx,
Classical.choice, Quot.sound]` — no new axioms; the lone `sorryAx` is the intended
transitive frontier.

## What this file delivers

`volInput_of_bg` (a `def`, not a `theorem`: its result is the data subtype
`{ vc : VolumeComparisonInput X // vc.dist = hd.dist }`).  It wires the accepted
member-level count `segBall_card` (`Comparison/Volume/SegmentCount.lean`) into the
`ballMult` field of `VolumeComparisonInput`, for the supplied distance.

Signature (final):

```
def volInput_of_bg
    (X : PointedRiemannianSeq I) (bg : SeqBoundedGeometry X)
    (hd : InjRadiusDecayInput X) (hreal : hd.RealizesEdist)
    (hcpl : SeqMetricComplete X)
    (hconn : ∀ k, ConnectedSpace (X.obj k).M)
    (r0 : Real) (hr0 : 0 < r0) :
    { vc : VolumeComparisonInput X // vc.dist = hd.dist }
```

`hd` is consumed ONLY through `hd.dist` (the field value) and `hreal` (realization);
`hd.decay` is never touched, so A0′ is independent of the CGT input, as required.
The subtype proof is `rfl` (`vc.dist := hd.dist`), so `MetricCompactBase.dist_eq`
is dischargeable.

## Input-bundle design decision: REUSED, not new

No new per-member data bundle was introduced.  The per-member instance stack is
reused from the existing HCG layer:

* completeness — `SeqMetricComplete` (input) → `MetricComplete.complete`
  (`PointedRiemannian.lean`) gives the `CompleteSpace` instance under the member
  emetric.
* emetric / bundle — `PointedRiemannianManifold.{riemBundle, riemBundle_cont,
  emetricSpace}` (`PointedEmetric.lean`) install `RiemannianBundle`,
  `IsContinuousRiemannianBundle`, `EMetricSpace`.  The instance block mirrors the
  proven `GoodCoveringOrdered.exists_proper_realization_aux`.
* connectedness — supplied as `hconn` (segBall_card / Hopf–Rinow surjectivity needs
  `[ConnectedSpace M]`; this is an honest input, matching
  `VolumeComparisonBridge.exists_pairR_of_seqBoundedGeometry`).

Two honest inputs beyond plan §0's sketch: `hconn` (per-member connectedness) and
`hcpl` (per-member completeness).  Both are genuinely required by `segBall_card`'s
`[ConnectedSpace]`/`[CompleteSpace]` instances and by the Hopf–Rinow surjectivity
it consumes; neither hides derivable content.  This is not the "explicit `hRic`"
fallback — the Ricci bound IS derived internally (see below).

## Distance bridge: `rfl`-level

`RealizesEdist.edist_eq` speaks the member's `emetricSpace = EMetricSpace.
ofRiemannianMetric`.  Mathlib's `IsRiemannianManifold` (`…/Riemannian/Basic.lean`)
is `class … where out (x y) : edist x y = riemannianEDist I x y`, and the
`ofRiemannianMetric` instance proves it by `fun _ _ => rfl`.  So installing
`IsRiemannianManifold I M := ⟨fun _ _ => rfl⟩` and using `IsRiemannianManifold.out`
turns `hreal.edist_eq` into `riemannianEDist I x y = ofReal (hd.dist k x y)`; the
supplied separation/containment hypotheses transfer via `ENNReal.ofReal_le_ofReal`.
`riemannianEDist` is instance-independent (needs only the fibrewise ENorm), so this
is robust.  `hEnorm` reuses `tensor0SBundle_enorm_eq_riemannianBundle_enorm`
(`TangentNormDiamond.lean`) via `simpa`, exactly as `GoodCoveringOrdered` does.

## Ricci fold (the "B1 fold"), with dim-1 resolution

`segBall_card` wants `Ric ≥ -(n-1)q²`.  Choice `q := n·√(bg.C 0)` (so
`q² = n²·(bg.C 0)`).

* `n ≥ 2`: `rm04Bound_of_seq` → `ricciLower_of_rm` gives `Ric ≥ -(n²·C₀)`; the
  target `-(n-1)q² = -(n-1)·n²·C₀` is ≤ that, so `RicciBoundedBelow` transfers by
  antitonicity in the constant (inlined; needs `0 ≤ g.inner`, from `g.pos`/`v=0`).
  The antitone step is not packaged in Mathlib/the tree — inlined here.
* `n = 1`: the target constant is `0` and antitonicity fails.  Resolved by proving
  the Ricci tensor VANISHES in dimension one (`ricci_dim1_bddBelow`), giving
  `Ric ≥ 0` outright.  There is NO reusable in-tree dim-1 Ricci/Riemann vanishing
  lemma (only a `private` `dim1_riemannOp_first_two_eq_zero` in a DeTurck file), so
  a self-contained proof was written from PUBLIC API:
  - `riemannOp_dim1_zero`: `riemannOp (LeviCivita g) x u v w = 0` when
    `finrank ℝ E = 1`.  In a 1-dim tangent space `u = a•e`, `v = b•e`
    (`finrank_eq_one_iff_of_nonzero'` + `Module.nontrivial_of_finrank_pos`), and
    `R(e,e,w) = 0` from `riemannOp_swap` (antisymmetry in the first two slots) via
    `X = -X ⟹ X = 0`.  Then `map_smul` in slots 1,2 (riemannOp is a triple CLM).
  - `ricci_dim1_bddBelow`: `RicciBoundedBelow g 0`, from
    `ricciTensor_apply_basisSum` (each summand is `repr (riemannOp … ) i = 0`).

Both dim-1 helpers are placed locally in this file (surgical, one new file).  They
are reusable CURVATURE facts; **B8 candidate: relocate to the canonical curvature
layer** (`Curvature/CurvatureOperator/RicciConnection.lean` or `Comparison/
BonnetMyers/RicciBound.lean`) and register `ricci_dim1_bddBelow` there.

## Transitive-`sorry` status (binding for the lane)

The file adds ZERO `sorry`.  `volInput_of_bg` nonetheless remains **transitively
`sorry`'d** through `segBall_card` → `segBall_vol_rel`/`segBall_vol_fin` →
`SegmentPolar.lean:107`/`:159` (decl lines), the two intended A0′ frontiers.
`#print axioms` confirms exactly one `sorryAx`, tracing to those two SegmentPolar
declarations (build warnings name them).  The HopfRinow.lean `sorry`s (:779/:818/
:854) are compiled in the graph but NOT in this def's cone (segBall_card uses the
CLEAN `hopf_rinow_expMapIntrinsic_surjective_minimizing` entrypoint, per B0).

## What remains for the endpoint to go `sorry`-free

Only the two SegmentPolar frontiers (bricks B5b `L1`+`L2`, then B5c assembly): the
manifold-valued non-injective area inequality (`E → M`, `riemannianVolumeMeasure`
target) + off-zero differentiability of `expMapIntrinsic`.  Nothing in
`VolumeOverlap.lean` blocks; when those close, `volInput_of_bg` becomes sorry-free
with no edit here.  Endpoint per plan §7: **0%** until then (this brick is
assembly; its own content is done).
