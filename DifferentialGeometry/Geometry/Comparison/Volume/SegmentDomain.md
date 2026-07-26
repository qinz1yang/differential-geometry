# SegmentDomain.lean — B2 (α) segment-domain set/measurability layer

Brick B2 of the A0′ `VolumeComparisonInput` lane
(`HCGCompactness/C4/A0PRIME_VOLUME_PLAN.md` §5).  This file is the
**set/measurability layer** of the segment domain past the cut locus; the
polar-measure layer (upper bound + relative form) lives in `SegmentPolar.lean`.

## Setting

One generic complete member `(M, g, p)` with the instance set of
`hopf_rinow_expMapIntrinsic_surjective_minimizing`
(`Exponential/MinimizingGeodesic.lean:2430`):
`[ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M]
[CompleteSpace M] [IsContinuousRiemannianBundle E (TangentSpace I)]`,
`g : SmoothRiemannianMetric I M`,
`hEnorm : ∀ x w, ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))`.
σ-compact + T2, NOT compact.  Continuity of `v ↦ exp_x v` additionally needs
`[T2Space (TangentBundle I M)]`.

## Deliverables (all sorry-free target)

- `SegDom g hEnorm x : Set (TangentSpace I x)` :=
  `{ v | √(g.inner x v v) = (riemannianEDist I x (expMapIntrinsic g hEnorm x v)).toReal }`.
  The distance-realizing launch velocities. The Hopf–Rinow minimizing witness
  lands in it by construction.
- `mem_segDom` / `segDom_zero`.
- `segDom_smul` — **star-shapedness**: `v ∈ SegDom → s ∈ [0,1] → s • v ∈ SegDom`.
- `ball_sub_image_segDom` — **surjectivity onto the edist-ball**:
  `{ y | riemannianEDist I x y < ofReal R } ⊆ exp_x '' (SegDom ∩ gBall x R)`,
  where `gBall x R := { v | √(g.inner x v v) < R }` is the g-metric ball on the
  fibre (equals `Metric.ball 0 R` via `hEnorm`; g-ball avoids norm-instance churn
  and is what the `modelHaar` integral consumes).
- `isClosed_segDom` / `measurableSet_segDom`.
- `isOpen_gBall` / `measurableSet_gBall`.

## Route (what worked)

- **Star-shapedness** does NOT need `subArc_of_minimizer_is_minimizer` /
  `pathELength_eq_arcLength`.  Cleaner: `intrinsicGeodesic_riemannianEDist_le`
  (`MinimizingGeodesic.lean:553`, length bound
  `edist (γ s)(γ t) ≤ ofReal(√(g v v)·(t−s))`) + `riemannianEDist_triangle`
  (Mathlib) + `intrinsicGeodesic_smul` (`IntrinsicExp.lean:1854`,
  `exp_x(s•v)=intrinsicGeodesic x v s`).  Write `γ=intrinsicGeodesic x v`,
  `L=√(g v v)`.  `v∈SegDom ⟹ edist x (γ1)=ofReal L`.  Upper `edist(γ0)(γs)≤ofReal(Ls)`;
  lower via `ofReal L = ofReal(Ls)+ofReal(L(1−s)) ≤ edist(γ0)(γs)+ofReal(L(1−s))`
  then cancel the finite `ofReal(L(1−s))` (`ENNReal.add_le_add_iff_right`).  So
  `edist x (γs)=ofReal(Ls)`, `.toReal = Ls = √(g (s•v)(s•v))` (`sqrt_gInner_smul_self`).
- **Surjectivity**: `hopf_rinow_expMapIntrinsic_surjective_minimizing` gives `v`
  with `exp_x v = y` and `√(g v v)=(edist x y).toReal`.  Membership in SegDom by
  rewriting `y = exp_x v`; membership in gBall from `(edist x y).toReal < R`
  (`hy` + `riemannianEDist_ne_top`).
- **Measurability**: `SegDom = {v | f₁ v = f₂ v}`, `f₁ = √(g.inner x ··)` continuous
  (`continuous_gInner_self` + `Real.continuous_sqrt`), `f₂ = (edist x (exp_x ·)).toReal`
  continuous via `expMapIntrinsic_continuous` (needs `T2Space (TangentBundle I M)`) +
  `continuous_riemannianEDist_to` (same `.Exponential` instance world — avoids the
  `continuous_riemannianEDist` `letI` clash) + `riemannianEDist_comm` +
  `ENNReal.continuousOn_toReal.comp_continuous` (values finite by
  `riemannianEDist_ne_top`).  `isClosed_eq` → `IsClosed` → `MeasurableSet` (borel).

## Instance/elaboration lessons (paid for here)

- `expMapIntrinsic_continuous` forces `[RiemannianBundle (fun x ↦ TangentSpace I x)]`
  (its file's variable). WITHOUT it in scope the failure surfaces as a spurious
  `‖w‖ₑ` enorm-instance mismatch (`NormedAddCommGroup.toENormedAddCommMonoid` vs
  `SeminormedAddGroup`) plus `PseudoEMetricSpace M`/`ConnectedSpace M` synth
  failures — all one cascade. FIX: add `variable [RiemannianBundle …]` at file
  level (this is what MinimizingGeodesic/HopfRinowProper do).
- Do NOT put `[IsContinuousRiemannianBundle …]` at file level TOGETHER with the
  explicit `[RiemannianBundle …]` and the emetric block — it cascaded broadly
  (`hopf_rinow …` reported as `TangentSpace I x → M`). Keep the emetric quartet
  (`PseudoEMetricSpace/IsRiemannianManifold/CompleteSpace/IsContinuousRiemannianBundle`)
  as PER-THEOREM binders; file-level = base + `[I.Boundaryless]` + `[T2Space M]`
  + `[T2Space (TangentBundle I M)]` + `[SigmaCompactSpace M]` + `[RiemannianBundle …]`.
- `riemannianEDist_ne_top` needs `[ConnectedSpace M]`.
- `continuous_riemannianEDist_to` takes only `(q : M)` (no `g`); swap the slot with
  `Manifold.riemannianEDist_comm` (implicit args — no explicit points) via `.congr`.
- `positivity` needs `hLnn : 0 ≤ L` in context after `set L := √…` (it does not see
  through `set`); pass `mul_nonneg hLnn …` explicitly.  `add_le_add_left` orientation
  bit — use `add_le_add le_rfl h`.  `set L` then `rw [hg0] at heq` (rewrite the
  named subterm) instead of `rw [← hg0]` in the goal (which over-fires on every `x`).

## Status

- 2026-07-25: **GREEN, sorry-free, no warnings** (focused `lake env lean` pass).
  Deliverable 1 (segment-domain set layer) COMPLETE: `SegDom`, `mem_segDom`,
  `segDom_zero`, `segDom_smul` (star-shaped), `ball_sub_image_segDom`
  (Hopf–Rinow surjectivity onto the edist-ball, landing in `SegDom ∩ gBall`),
  `isClosed_segDom`/`measurableSet_segDom`, `isOpen_gBall`/`measurableSet_gBall`.
  All past the cut locus (no injectivity hypothesis).
