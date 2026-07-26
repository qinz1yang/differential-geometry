# HalfSqDistGrad.lean — one-summand distance-squared gradient (MSM135 Ch4 §6 lbl411)

## Target

Discharge the `hflat` hypothesis of `CenterOfMass.sum_expInv_of_flat`, i.e. the
one-summand first-variation covector identity:

```
(mfderiv I 𝓘(ℝ,ℝ) (halfSqDist pt) q).toLinearMap
  = metricFlatEquiv g q (-(normalChartAt g q pt))
```

`halfSqDist pt q = ½ dist q pt ^2`; `normalChartAt g q pt = exp_q⁻¹(pt)` (fixed-base,
`NormalCoordinates.normalChartAt = (expMapDiffeo g q).symm`). With this discharged,
`grad_halfSqDist_of_flat` gives `grad (½ d²(·,pt)) = -exp_q⁻¹(pt)` and
`sum_expInv_of_flat` gives the center-of-mass equation `Σ μᵢ exp_q⁻¹(ptᵢ)=0`.

## Status

- UPSTREAM UNBLOCKER DONE: `diagExpInv` (Exponential/DiagExpDerivative.lean) — the
  moving-base inverse exp section, the producer CenterOfMass.md repeatedly flagged
  as THE blocker. Verified sorry-free.
- This file: 4 FOUNDATIONAL BRICKS DONE (verified sorry-free via `lake build`, `✔`):
  1. `hasDerivAt_eq_of_le` — comparison derivative lemma (touching graphs ⟹ equal
     derivatives, via `IsLocalMin.hasDerivAt_eq_zero`). Pure ℝ analysis.
  2. `arcLength_radial` — `arcLength g (intrinsicGeodesic g q v) a b = (b-a)·√(g_q v v)`
     (constant speed via `intrinsicGeodesic_speedSq_eq`; `intervalIntegral.integral_congr`
     + `congr 1` + `exact` to dodge the Tensor0SBundle-instance/attribute-removed mismatch
     that blocks `simp_rw`).
  3. `exists_dist_eq_sqrt` — `∃ρ>0, √(g_q v v)<ρ → dist q (exp_q v) = √(g_q v v)`
     (`radial_riemannianEDist_eq_of_small'` + `HopfRinow.riemMetric_dist_eq` + `toReal_ofReal`).
  4. `exists_expMapIntrinsic_normalChart` — `∃ρ>0, pt∈normalChart.source → small →
     expMapIntrinsic q (normalChartAt g q pt) = pt` (round-trip; mirrors
     `expMapIntrinsic_local_surjective`'s middle: `normalChartAt_left_inv` +
     `normalChartAt_symm_apply` + agreement `exists_expMapIntrinsic_eq_expMap_radius`).
- REMAINING (B route, central geodesic + variation assembly): see below.

## Lean gotchas (this pass)

- Instance/attribute mismatch: `arcLength` (ArcLength.lean) is elaborated with the
  default `Tensor0SBundle.tangentSpace_normed*` instances; `intrinsicGeodesic_speedSq_eq`
  (MinimizingGeodesic) is elaborated with them REMOVED (`attribute [-instance] … in`).
  So `simp_rw [speedSq_eq]` after `unfold arcLength` fails to MATCH (syntactic), but
  `congr 1; exact speedSq_eq …` succeeds (defeq, `TangentSpace I x = E`). Every decl
  here carries the `attribute [-instance] Tensor0SBundle.tangentSpace_normed* in` prefix
  + `[T2Space (TangentBundle I M)]`, mirroring MinimizingGeodesic.
- `HopfRinow.riemMetricSpace` / `HopfRinow.riemMetric_dist_eq` need `[T3Space M]`.

## DONE — brick 5 (central geodesic): `exists_central_geodesic` (verified)

`∃ρ>0, ∀ pt ∈ normalChart.source, pt ≠ q, small → ∃ u L, 0<L ∧ L=dist q pt ∧
g_q u u=1 ∧ intrinsicGeodesic q u L=pt ∧ L•u=normalChartAt g q pt ∧ IsGeodesicOn ∧
mfderiv(intrinsicGeodesic q u) 0 1=u ∧ arcLength=L`. Built from bricks 3+4 +
`intrinsicGeodesic_smul`/`_zero`/`_speedSq_eq`/`_isGeodesic`/`_mfderiv_zero`,
`gInner_smul_self`, `IsGeodesic.isGeodesicOn`. `u := L⁻¹•v₀`, `v₀ := normalChartAt q pt`,
`L := dist q pt`; `L²=g_q v₀ v₀` from brick 3 (`Real.sq_sqrt`); unit speed from
`gInner_smul_self`+`inv_mul_cancel₀`.

## REFINED REMAINING ROUTE (better than the original — avoids parallel transport AND uniformity)

Use the **minimizing variation** built from `diagExpInv` for the comparison trick:
`f(s,t) := expMapIntrinsic g (β s) ((t/L) • W s)`, where `β s := expMapIntrinsic g q (s•w̃)`
(so `β'0 = w`, via `mfderiv_expMapIntrinsic_at_zero`) and
`W s := (diagExpInv g hEnorm q (β s, pt)).snd` (the inverse-exp field, smooth via
`diagExpInv_contMDiffAt`; `exp_{β s}(W s) = pt` via `expIntr_diagExpInv`+`diagExpInv_proj`).
Then `f 0 · = γ` (brick 5's geodesic, since `(t/L)•W 0 = (t/L)•(L•u) = t•u`), `f s L = pt`,
`f s 0 = β s` — and the **comparison trick uses arc length, so NO `hdist`/uniformity is
needed**:
6. **Variation smoothness** `IsSmoothVariation f`: from `expMapIntrinsic_variation_contMDiffAt`
   (ExpVariationSmooth.lean:925, shape `(p.1•(V₀ p.2).snd)` = scalar•field — matches with
   the `t/L` scalar and `W` field) — has phase-ball `hsmall` hypotheses to discharge.
7. **First variation of ARC LENGTH (no hdist)**: `first_variation_geodesic_fixed_end`
   (FirstVariation.lean:1006) ⟹ `HasDerivAt (s↦arcLength(f s·) 0 L) (-⟨w,γ'0⟩) 0`; chain
   to `½arcLength²`: `d/ds[½arcLength²]|0 = L·(-⟨w,γ'0⟩)` (arcLength(γ)=L by brick 2+5).
8. **Comparison** (free ≤, per-point — NO uniformity): `dist(f s 0,pt) ≤ arcLength(f s·)`
   from `Manifold.riemannianEDist_le_pathELength` + an arcLength↔pathELength bridge
   (LOCATE/ADD: `arcLength = (pathELength …).toReal`), with EQUALITY at s=0
   (`arcLength(γ)=L=dist(q,pt)`, bricks 2+3+5). brick 1 (`hasDerivAt_eq_of_le`) ⟹
   `d/ds[½dist(f s 0,pt)²]|0 = L·(-⟨w,γ'0⟩)`, i.e. `d/ds[halfSqDist pt (β s)]|0 = L·(-⟨w,γ'0⟩)`.
9. **Chain rule + metricFlat**: with `hdiff : MDifferentiableAt (halfSqDist pt) q`,
   `mfderiv(halfSqDist pt) q w = d/ds[halfSqDist pt (β s)]|0 = L·(-⟨u,w⟩) = -⟨L•u,w⟩
   = -⟨normalChartAt,w⟩ = metricFlatEquiv g q (-normalChartAt) (w)`. `∀w` + ext ⟹ done.

### Comparison brick DONE (in MaximalInterval, not here) + instance gotcha

The `dist ≤ arcLength` comparison is `Geodesic.riemannianEDist_le_arcLength`
(MaximalInterval.lean, `section ArcLengthBridge`, verified sorry-free):
`riemannianEDist I (γ a) (γ b) ≤ ENNReal.ofReal (arcLength g γ a b)` for a `C¹` curve
with the pointwise enorm identification. Combined with `HopfRinow.riemMetric_dist_eq`
(`dist = riemannianEDist.toReal`) + `ENNReal.toReal_ofReal` it gives `dist ≤ arcLength`.

**Instance gotcha (cost ~4 routes):** this comparison CANNOT be stated in HalfSqDistGrad's
`Radial` section — that section's EXTRA instances (`IsContinuousRiemannianBundle`,
`T2Space (TangentBundle I M)`, `Module.Finite`, `NeZero`) perturb instance resolution so
that `pathELength_eq_arcLength`/`speedSqrt_integrableOn_Icc_of_C1` fail with
`failed to synthesize (x : M) → InnerProductSpace ℝ (TangentSpace I x)`. With the
`attribute [-instance] Tensor0SBundle.tangentSpace_normed*` removal the `pathELength` enorm
instead MISMATCHES Mathlib's frozen `Tensor0SBundle` enorm. The fix is the **canonical
home**: prove it in `MaximalInterval.ArcLengthBridge` (RiemannianBundle but WITHOUT those
extra instances), where `pathELength_eq_arcLength` already lives and composes. Lesson:
keep length/distance/arcLength comparison lemmas in the geodesic layer, not the
center-of-mass layer.

### BLOCKER (2026-06-26): variation construction needs a missing FIELD producer

The first variation needs a smooth variation `f` with `f 0 · = γ`, `f s 0 = β s`
(`β'0 = w`), `f s L = pt`. Both packaged routes need a **global bundle-smooth field
along `γ` with prescribed value `w` at `t=0`** (and `=0` at `t=L` for the fixed
endpoint), and NO such producer exists in the project:

- `Variation.exists_expVar_fixEnd` (the packaged transverse-variation builder, gives
  `IsSmoothVariation` for free) requires `hVbundle : ContMDiff 𝓘(ℝ,ℝ) I.tangent ∞
  (fun t => ⟨γ t, V t⟩)` — a GLOBAL bundle-smooth field. The only field producer,
  `parallelTransport_section_contMDiffOn` (ParallelTransportSmooth.lean:150), is
  `ContMDiffOn` on `Icc`, NOT global. `contMDiff_smul_bundleField`
  (SecondVariationMinimiser:164, the scale-by-scalar tool for fade-out) also needs a
  GLOBAL base field. The high-level consumers (`indexForm_nonneg_of_minimising_geodesic`,
  BonnetMyers `Headlines`) all **hypothesize** the parallel/eigen frame field — none builds one.
- Direct minimizing `f(s,t)=exp_{β s}((t/L)•W s)` via `expMapIntrinsic_variation_contMDiffAt`:
  the field `W s = (diagExpInv q (β s,pt)).snd` along `β` is only LOCALLY smooth
  (`diagExpInv` is `ContMDiffAt` at `(q,q)`), and `IsSmoothVariation` (global `ContMDiff 8`)
  would need a manual `ContMDiffAt → ContMDiff` globalization (the tube/`reparam` trick that
  `exists_expVar_field` does internally).

Four routes (exists_expVar_fixEnd; direct minimizing; cutoff `ψ•W_par`; `W = X∘γ`) all
converge on the SAME gap: **no global bundle-smooth field-along-curve producer**.

**FIELD PRODUCER DONE (2026-06-26, verified sorry-free).**
`Riemannian.exists_contMDiff_vectorField_eq (q : M) (v : TangentSpace I q) :
  ∃ V : (x:M) → TangentSpace I x, ContMDiff I (I.prod 𝓘(ℝ,E)) ∞ (T% V) ∧ V q = v`
lives in `Geometry/Metric/SmoothVectorFieldExtGlobal.lean`, with the chart-constant
section helpers (`chartConstVecFiber`, `chartConstVecFiber_self`, `chartConstVec_contMDiffOn`)
in `Geometry/Metric/SmoothVectorFieldExt.lean`. `V x = f x • chartConstVecFiber q c x`,
`f : SmoothBumpFunction I q`, global via `ContMDiffOn.smul_section_of_tsupport`.
**Whnf-wall fix CONFIRMED:** the chart-constant section smoothness must be proved in a file
importing ONLY `ChartGram` (light); adding `SmoothSection`/`BumpFunction`/`PartitionOfUnity`
to that elaboration triggers an instance `whnf` timeout. The split (helper upstream, applied
downstream) dodges it. So `W := fun t => X (γ t)` (global field along γ, `W 0 = v`) and the
fade-out `(1-t/L)•W` (via `contMDiff_smul_bundleField`) are now available.

**GRADIENT VARIATION DONE (2026-06-26, verified sorry-free).**
`Riemannian.exists_gradVariation` in `Geometry/Comparison/HalfSqDistGradVar.lean`:
given the central geodesic `γ = intrinsicGeodesic g q u` with `γ L = pt` (`0 < L`) and a base
direction `w : TangentSpace I q`, produces a fixed-endpoint `IsSmoothVariation f` with
`f 0 · = γ`, `f s L = pt`, and `mfderiv (f·0) 0 1 = w`. Built from the field producer
(`exists_contMDiff_vectorField_eq` for `X q = w`), the faded field `(1-t/L)•(X∘γ)` via
`contMDiff_smul_bundleField`, and `exists_expVar_fixEnd`. Needs `attribute [-instance]
Tensor0SBundle.tangentSpace_normed*` (else `hEnorm`'s enorm fails `(x:M)→InnerProductSpace`
synth) + `[T2Space (TangentBundle I M)]`. Gotcha: `V L = 0` proof needs `show (1-L/L)•X(γL)=0;
rw [div_self hL.ne', sub_self, zero_smul]` (simp leaves an unclosable `0=0` from a TangentSpace-vs-E
zero-instance mismatch); final `mfderiv = w` step uses `simp only [zero_div, sub_zero, one_smul]; rw [hγ0]; exact hXq`.

**A-SIDE FIRST VARIATION DONE (2026-06-26, verified).** `Riemannian.halfArcLengthSq_deriv`
in `Geometry/Comparison/HalfSqDistGradMain.lean`: for the central unit-speed geodesic
`γ=intrinsicGeodesic g q u` (`g_q u u=1`, `γ L=pt`) and a fixed-endpoint variation `f` with
central curve `γ`, `HasDerivAt (fun s => ½ (arcLength (f s·) 0 L)²) (L·(-⟨mfderiv(f·0) 0 1, mfderiv γ 0 1⟩)) 0`.
Via `first_variation_geodesic_fixed_end` + `(·.pow 2).const_mul (1/2)` + `arcLength_radial`
(arcLength(γ)=L) + `intrinsicGeodesic_speedSq_eq`/`_isGeodesic`/`_zero`. Gotcha: keep the
velocity as `mfderiv γ 0 1` (NOT `u`) in the conclusion — `rw [intrinsicGeodesic_mfderiv_zero]`
fails on a coercion-ascription mismatch; defer the `mfderiv γ 0 1 = u` identification to the
covector wrapper. `hval` value step: `rw [harc0, hγ0]; norm_num; ring`.

**D-SIDE CHAIN RULE DONE (2026-06-26, verified).** `Riemannian.halfSqDist_curve_hasDerivAt`
(HalfSqDistGradMain.lean): `HasDerivAt (fun s => halfSqDist pt (f s 0)) (mfderiv(halfSqDist pt) q
(mfderiv(f·0) 0 1)) 0` given `f 0 0 = q` + `MDifferentiableAt (halfSqDist pt) q` (under
`letI := riemMetricSpace`). Via `HasMFDerivAt.comp` + `hasMFDerivAt_iff_hasFDerivAt` +
`hasFDerivAt_iff_hasDerivAt`. GOTCHA: `comp` mis-infers the inner fn as the curried `f 0`;
`set β := fun s => f s 0` makes it opaque so `comp` unifies `β` correctly.

**VALUE LEMMA + COVECTOR + GRADIENT = DONE (2026-06-26).** All in
`Geometry/Comparison/HalfSqDistGradMain.lean`:
- `halfSqDist_dir_deriv` (value lemma): A-side `halfArcLengthSq_deriv` + D-side
  `halfSqDist_curve_hasDerivAt` + comparison `½d²≤½arcLength²`, glued by `hasDerivAt_eq_of_le`.
- `halfSqDist_flat` (THE lbl411 covector identity): `∃ρ>0, ∀ pt small,
  (mfderiv (halfSqDist pt) q).toLinearMap = metricFlatEquiv g q (-(normalChartAt g q pt))`.
- `grad_halfSqDist`: `gradientFun g (halfSqDist pt) q = -(normalChartAt g q pt)` via
  `gradientFun_eq_of_flat` (instance-free; consumes only the covector identity).
- comparison helpers `arcLength_nonneg` + `dist_le_arcLength` (real form) in this file.

**ENORM-CONFLICT ROOT-CAUSE FIX (the unblock).** The blocker was NOT solvable by "opaque helpers
in MaximalInterval (no removal)" as previously planned — `riemMetric_dist_eq`/`riemMetricSpace`
themselves bake the **RiemannianBundle** enorm (they carry the `attribute [-instance]
Tensor0SBundle.*` removal in HopfRinowProper), while `riemannianEDist_le_arcLength` baked the
**Tensor0SBundle** enorm (MaximalInterval, no removal). The `hEnorm`/`riemannianEDist` instance is
FIXED in each lemma's TYPE (not resynthesized at the use site — confirmed by the exact error
`expected Tensor0SBundle… vs instNormedAddCommGroupOfRiemannianBundle…`). So no single world consumes
both. **FIX:** convert `MaximalInterval.ArcLengthBridge` to the RiemannianBundle world: add
`attribute [-instance] Tensor0SBundle.tangentSpace_normed*` to `pathELength_eq_arcLength` and
`riemannianEDist_le_arcLength`, and DROP the unused `_hEnorm` from `speedSqrt_integrableOn_Icc_of_C1`
(now enorm-free). Safe: all three were internal to the bridge (riemannianEDist_le_arcLength had NO
external uses). Then `dist_le_arcLength` (removal) composes `riemMetric_dist_eq`[R] +
`riemannianEDist_le_arcLength`[R] cleanly. `riemannianEDist` (Mathlib `irreducible_def`) takes the
bundle instance, so it's the same term once both lemmas are in the [R] world.

**Wrapper algebra gotchas (resolved):** `metricFlatEquiv_apply` is `rfl` but did NOT fire under
`simp` (coercion structure) — use `show … = g.inner q (-(show TangentSpace I q from normalChartAt)) w`
(defeq, both it and `ContinuousLinearMap.coe_coe` are rfl). Coercion `mfderiv γ 0 1 = u` (E-coerced
in `intrinsicGeodesic_mfderiv_zero`) lifts to TangentSpace via `have hu' : … = u := hmfd` (defeq
ascription works). Then `(g.inner q).map_neg` + `ContinuousLinearMap.neg_apply` + `g.symm q w u` +
`mul_neg`. `pow_le_pow_left₀ hdnn hdle 2` for `dist²≤arcLength²`. hEnorm in a `⟨g.toRiemannianMetric⟩`
consumer: discharge via `tensor0SBundle_enorm_eq_riemannianBundle_enorm` (TangentNormDiamond; pattern
at `GoodCoveringOrdered.lean:765` `by intro x v; simpa using (… g x v)`).

---
(historical) **Unblocking lemma — BUILDABLE (corrected: NOT missing-API; Mathlib has the tools):**
`exists_contMDiff_vectorField_eq : ∀ (x : M) (v : TangentSpace I x),
  ∃ X : ContMDiffSection I E ∞ (TangentSpace I), X x = v` — a smooth vector field with
prescribed value at one point. Two Mathlib routes, both present + sorry-free:
- `PartitionOfUnity.exists_contMDiffSection_forall_mem_convex_of_local` (assembles a GLOBAL
  smooth section from LOCAL ones via partition of unity; use convex sets `t x = {v}` at `x`,
  `univ` elsewhere — needs only a local smooth field with value `v` at `x`); OR
- manual: `ContMDiffOn.smul_section_of_tsupport` (PartitionOfUnity.lean:~624 — bump×section
  zero-extension to global) applied to `φ • σ`, `φ` a `SmoothBumpFunction` at `x`, `σ` a local
  smooth field with `σ x = v`.
The only remaining sub-piece is the LOCAL smooth field `σ` with `σ x = v`: via
`VectorField.Pullback.contMDiffWithinAt_mpullbackWithin_extChartAt_symm`
(Pullback.lean:617 — pulls a field through `(extChartAt I x).symm`, smooth) or a
`chartBasisVecFiber` linear combination (Operator/Gradient.lean). Then `W t := X (γ t)` is the
global bundle-smooth field along γ (`X∘γ`, `W 0 = v`), fade-out `(1-t/L)•W` via
`contMDiff_smul_bundleField`. ~60–120 lines, reusable; bundle/section layer.

So the covector identity is a LARGE but FULLY FEASIBLE assembly (no missing math, all API
present + sorry-free): field producer (above) → variation via `exists_expVar_fixEnd` →
first variation + comparison + chain + metricFlat. Realistically ~2-3 sessions.

### Then-remaining wiring (once the field producer exists)

`first_variation_geodesic_fixed_end` (no hdist) → chain to ½arcLength²;
`Geodesic.riemannianEDist_le_arcLength` (DONE) + `riemMetric_dist_eq` → `dist ≤ arcLength`,
equality at 0 (bricks 2+3+5); `hasDerivAt_eq_of_le` (brick 1) → `d/ds[½dist²]|0`;
chain rule (`MDifferentiableAt (halfSqDist pt) q` HYPOTHESIS) → mfderiv;
`metricFlatEquiv_apply` + `map_neg` (trivial) → covector identity; ext over `w`.

## Route B (comparison trick) — per-point at q, NO uniform injectivity radius

Take `MDifferentiableAt I 𝓘(ℝ,ℝ) (halfSqDist pt) q` as a HYPOTHESIS (matches the
existing `sum_expInv_of_flat` interface, which already assumes it). Then prove the
mfderiv VALUE. This avoids the smoothness sub-frontier (A) entirely.

For each tangent direction `w` at `q`:
1. **Central geodesic.** `γ(t) = expMapIntrinsic g q (t • u)`, `u` the unit initial
   velocity toward `pt`, `L = dist q pt`, so `γ 0 = q`, `γ L = pt`, `arcLength γ 0 L = L`,
   `γ` unit-speed geodesic, and `L • u = exp_q⁻¹(pt) = normalChartAt g q pt`.
   Producer: `hopf_rinow_expMapIntrinsic_surjective_minimizing` (MinimizingGeodesic.lean:2016,
   gives `v` with `exp_q v = pt`, `√(g v v) = riemannianEDist`) + intrinsic↔chart exp
   reconciliation (`exists_expMapIntrinsic_eq_expMap_radius`) to identify `v = normalChartAt`.
2. **Transverse variation + first variation.** Build a smooth variation `f` (e.g. via
   `exists_expVar_fixEnd`) with `f 0 · = γ`, `f s 0` a curve of velocity `w`, `f s L = pt`.
   `first_variation_geodesic_fixed_end` ⟹ `d/ds[arcLength (f s ·) 0 L]|0 = -⟨w, γ'0⟩`,
   hence `d/ds[½ arcLength²]|0 = L·(-⟨w, γ'0⟩)` (chain, arcLength(γ)=L).
3. **Comparison.** `dist (f s 0) pt ≤ arcLength (f s ·) 0 L` ALWAYS (free:
   `riemannianEDist_le_pathELength` + arcLength↔pathELength bridge), with EQUALITY at
   `s=0` (`γ` minimizing: `dist q pt = L = arcLength γ`). So `½dist² ≤ ½arcLength²`,
   equal at 0; both `HasDerivAt` at 0 (½dist² via `hdiff` + chain; ½arcLength² via step 2)
   ⟹ `d/ds[½dist²]|0 = L·(-⟨w,γ'0⟩)` (`IsLocalMin.hasDerivAt_eq_zero` on the difference).
4. **Chain rule.** `d/ds[½dist(f s 0,pt)²]|0 = d/ds[halfSqDist pt (f s 0)]|0
   = mfderiv (halfSqDist pt) q (mfderiv (f·0) 0 1)`, and `mfderiv (f·0) 0 1 = w`.
5. **metricFlat algebra.** `L·(-⟨w,γ'0⟩) = -⟨w, L•γ'0⟩ = -⟨w, normalChartAt⟩
   = -⟨normalChartAt, w⟩ = metricFlatEquiv g q (-normalChartAt) (w)`. ∀ w ⟹ covector eq.

## Available facts (verified, sorry-free)

- `MinimizingGeodesic.radial_riemannianEDist_eq_of_small'` (:730): `riemannianEDist q (exp_q w)
  = ofReal √(g_q w w)` for `√(g w w) < ρ_q`.
- `MinimizingGeodesic.hopf_rinow_expMapIntrinsic_surjective_minimizing` (:2016).
- `MinimizingGeodesic.intrinsicGeodesic_riemannianEDist_le` (:550), `..._le_radius` (GeodesicConvexity:256).
- `HopfRinow.riemMetric_dist_eq` (HopfRinowProper.lean:67): `dist x y = (riemannianEDist I x y).toReal`.
- `Variation.first_variation_geodesic_fixed_end` (FirstVariation.lean:1006), `dist_deriv_of_length` (:1082),
  `halfSq_deriv_length` (:1104).
- `Variation.exists_expVar_fixEnd` / `exists_sqDeriv_field` (SecondVariationMinimiser.lean:422/448).
- `Manifold.riemannianEDist_le_pathELength` (the free dist≤length).
- `IsLocalMin.hasDerivAt_eq_zero` (Mathlib LocalExtr/Basic:239).
- `DiagExpDerivative.diagExpInv` + `diagExp_diagExpInv`/`diagExpInv_proj`/`expIntr_diagExpInv`.

## Remaining sub-frontiers / risks

- Brick 1 (central geodesic velocity = normalChartAt, unit-speed, arcLength=L): geometry-heavy;
  needs intrinsic↔chart exp reconciliation + geodesic ODE velocity. Likely the hardest brick.
- arcLength (Variation) ↔ pathELength (Manifold) ↔ riemannianEDist bridge for step 3.
- The reusable smoothness sub-frontier is resolved below by the fixed-target
  producer `exists_halfSqDist_md`.  Removing the `hdiff` hypothesis from the
  current `q`-based `halfSqDist_flat` interface still requires reverse-chart
  source/smallness, which belongs to the concrete configuration-domain work.

## 2026-07-10 — fixed-target differentiability producer

- Added `exists_halfSqDist_md`, verified by focused checking and a targeted
  module build.  For fixed `pt`, it supplies a positive radius on which
  `halfSqDist pt` is manifold-differentiable at every `q` in the fixed normal
  chart of `pt` with sufficiently small normal coordinate.
- The proof avoids the unavailable moving-base radius lower bound: by distance
  symmetry it works in the fixed chart at `pt`, where `halfSqDist pt` agrees
  locally with the smooth quadratic form
  `(1 / 2) * g.inner pt (normalChartAt g pt q) (normalChartAt g pt q)`.
- This completes the reusable local differentiability producer.  It does not
  yet discharge the `hdiff` argument of `halfSqDist_flat`, whose current input
  is phrased with the opposite, `q`-based chart.  The concrete Step-C
  application must still prove the reverse-chart source and smallness facts
  for each finite-hat center/atom pair.
- Honest accounting: `exists_halfSqDist_md` itself is complete; the concrete
  finite-hat differentiability instantiation remains unstated and therefore
  0% complete.

## 2026-07-24 component-local radial length

The public `arcLength_radial` theorem now omits the section-wide
`ConnectedSpace M` assumption.  Its proof only uses the constant-speed theorem
for one complete intrinsic geodesic, which is component-local.  This
strengthening is needed by the no-connectedness Route B-prime broken-path
Calabi support.

The source change is complete and focused verification is GREEN against the
repaired, exact-current inverse-branch chain.  After restoring the
connectivity-free `DiagExpDerivative` artifact, the exact targeted refresh is
also GREEN (`3792/3792`).  This API cleanup does not prove the radial
Laplacian/Jacobi-trace bridge or the final distance barrier, both of which
remain open.
