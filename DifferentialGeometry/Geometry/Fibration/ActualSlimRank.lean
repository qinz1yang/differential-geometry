import DifferentialGeometry.Geometry.Fibration.ActualSlimGraphApprox
import DifferentialGeometry.Geometry.Fibration.ActualSlimRankTiers

/-!
# SGP05: the actual projected rank at every preimage

Blueprint `master207B.tex`, SGP05 (`lem:fibration-slim-all-preimage-rank`, B:4667–4709): with
SGP04's model `Φ_i = sgpFullGraph` and (SG), at every preimage `q` of a core point
`x = π₃𝓔⁰(p)` (`|η_i(p)| ≤ 7ℓ`) the projection of `ρ(i)⁻¹dπ₃𝓔⁰_q` onto `T_x = im DΦ_i(η_i p)` is
onto, its normal error is at most `eν` and it is bounded below by `ν/2` on the `g`-orthogonal
complement of its kernel and above by `3C_*ν` (`ν = √(ρ(i)⁻²g)`, `C_* = sgpGraphBound`).

* `sgp05_rank_form_SGP5`: the rank argument (FC06 in dimension one) for a positive semidefinite
  bilinear form `B` on the source, `ν = √(B v v)`; `sgp05_rank_metric_SGP5`: the same for
  `B = c²g_q`, with `df_q` and `c·dF_q`, in metric form.
* `fderiv_sgpFullGraph_own_SGP5`, `sgp05_model_reference` (frozen tier): `|z| ≤ ‖DΦ_i(a)z‖` (own
  block) and `‖DΦ_i(a)‖ ≤ C_*` (G3's early modulus).
* `sgp05_row`: the row on `LocalChartPacketsRVZ`, with (SG) for the SAME model passed through, so a
  consumer gets the graph, (SG) and the rank from one choice of signs and translations.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section RankKernel

/-- **SGP05's rank argument for a positive semidefinite form on the source** (FC06 in dimension
one, with the source measured by `ν(v) = √(B v v)` instead of an inner-product norm). A reference
derivative `T : ℝ → H` with identity component (`|z| ≤ ‖T z‖`) and `‖T‖ ≤ C`, a covector `dη` with a
`B`-unit vector on which it exceeds `9/10` and `|dη| ≤ 2ν`, and `D` with `‖D v − T(dη v)‖ ≤ eν(v)`
(`e < 2/5`, `e ≤ C`): the projection `P` of `D` onto `im T` is onto, the normal error is at most
`eν`, `‖P v‖ ≥ ν(v)/2` for `v` `B`-orthogonal to `ker P`, and `‖P v‖ ≤ 3Cν(v)`. -/
theorem sgp05_rank_form_SGP5 {V H : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hBs : ∀ v w, B v w = B w v) (hBp : ∀ v, 0 ≤ B v v)
    (T : ℝ →L[ℝ] H) (hT : ∀ z, ‖z‖ ≤ ‖T z‖) {C e : ℝ} (hTC : ‖T‖ ≤ C)
    (dη : V →L[ℝ] ℝ) (hlow : ∃ w, B w w = 1 ∧ 9 / 10 < dη w)
    (hup : ∀ v, |dη v| ≤ 2 * Real.sqrt (B v v)) (D : V →L[ℝ] H)
    (hD : ∀ v, ‖D v - T (dη v)‖ ≤ e * Real.sqrt (B v v)) (he : e < 2 / 5) (heC : e ≤ C) :
    let P := T.range.orthogonalProjectionOnto.comp D
    Function.Surjective P ∧ (∀ v, ‖D v - (P v : H)‖ ≤ e * Real.sqrt (B v v)) ∧
      (∀ v, (∀ k, P k = 0 → B v k = 0) → 1 / 2 * Real.sqrt (B v v) ≤ ‖P v‖) ∧
      ∀ v, ‖P v‖ ≤ 3 * C * Real.sqrt (B v v) := by
  intro P
  obtain ⟨w, hw1, hw⟩ := hlow
  have hνw : Real.sqrt (B w w) = 1 := by rw [hw1, Real.sqrt_one]
  have hPv : ∀ v, (P v : H) = T.range.starProjection (D v) := fun v => rfl
  have hprojT : ∀ z, T.range.starProjection (T z) = T z := fun z =>
    T.range.starProjection_mem_subspace_eq_self ⟨T z, ⟨z, rfl⟩⟩
  -- `P v` is within `eν` of `T(dη v)`
  have hPerr : ∀ v, ‖(P v : H) - T (dη v)‖ ≤ e * Real.sqrt (B v v) := by
    intro v
    rw [hPv, ← hprojT (dη v), ← map_sub]
    exact (T.range.norm_starProjection_apply_le _).trans (hD v)
  have he0 : 0 ≤ e := by
    have h1 := hD w
    rw [hνw, mul_one] at h1
    exact (norm_nonneg _).trans h1
  -- the image of `w`
  have hPw : 9 / 10 - e ≤ ‖P w‖ := by
    have h1 := hPerr w
    rw [hνw, mul_one] at h1
    have h2 : 9 / 10 < ‖T (dη w)‖ := by
      have := hT (dη w)
      rw [Real.norm_eq_abs, abs_of_pos (by linarith)] at this
      linarith
    have h3 := norm_sub_norm_le (T (dη w)) (T (dη w) - (P w : H))
    rw [sub_sub_cancel, norm_sub_rev] at h3
    change 9 / 10 - e ≤ ‖(P w : H)‖
    linarith
  have hPw0 : (P w : H) ≠ 0 := by
    intro h
    have : ‖P w‖ = 0 := by
      change ‖(P w : H)‖ = 0
      rw [h, norm_zero]
    linarith
  -- every value of `P` is a multiple of `P w`
  obtain ⟨zw, hzw⟩ := (P w).2
  have hzw0 : zw ≠ 0 := by
    intro h
    apply hPw0
    rw [← hzw, h, map_zero]
  have hmult : ∀ v, ∃ t : ℝ, P v = t • P w := by
    intro v
    obtain ⟨zv, hzv⟩ := (P v).2
    refine ⟨zv / zw, Subtype.ext ?_⟩
    change (P v : H) = (zv / zw) • (P w : H)
    rw [← hzv, ← hzw, ← map_smul, smul_eq_mul, div_mul_cancel₀ _ hzw0]
  refine ⟨?_, fun v => ?_, fun v hv => ?_, fun v => ?_⟩
  · -- onto
    rintro ⟨y, z, rfl⟩
    refine ⟨(z / zw) • w, Subtype.ext ?_⟩
    change ((P ((z / zw) • w) : T.range) : H) = T z
    rw [map_smul]
    change (z / zw) • (P w : H) = T z
    rw [← hzw, ← map_smul, smul_eq_mul, div_mul_cancel₀ _ hzw0]
    rfl
  · -- normal error
    rw [hPv]
    have h := Metric.infDist_le_dist_of_mem (show T (dη v) ∈ T.range from ⟨dη v, rfl⟩)
      (x := D v)
    rw [← T.range.dist_starProjection_eq_infDist, dist_eq_norm, dist_eq_norm] at h
    exact h.trans (hD v)
  · -- lower bound on the `B`-orthogonal complement of the kernel
    obtain ⟨t, ht⟩ := hmult v
    have hk : P (v - t • w) = 0 := by rw [map_sub, map_smul, ht, sub_self]
    have hBk := hv _ hk
    have hBvw : B v v = t * B v w := by
      rw [map_sub, map_smul, smul_eq_mul] at hBk
      linarith
    have hBkk := hBp (v - t • w)
    have hexp : B (v - t • w) (v - t • w) = B v v - 2 * t * B v w + t ^ 2 * B w w := by
      simp only [map_sub, map_smul, sub_apply, smul_apply,
        smul_eq_mul]
      rw [hBs w v]
      ring
    rw [hexp, hw1] at hBkk
    have hsq : B v v ≤ t ^ 2 := by nlinarith
    have hν : Real.sqrt (B v v) ≤ |t| := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hsq
    have hnorm : ‖P v‖ = |t| * ‖P w‖ := by
      rw [ht, norm_smul, Real.norm_eq_abs]
    rw [hnorm]
    have h12 : 1 / 2 ≤ ‖P w‖ := by linarith
    calc 1 / 2 * Real.sqrt (B v v) ≤ 1 / 2 * |t| :=
          mul_le_mul_of_nonneg_left hν (by norm_num)
      _ ≤ ‖P w‖ * |t| := mul_le_mul_of_nonneg_right h12 (abs_nonneg t)
      _ = |t| * ‖P w‖ := mul_comm _ _
  · -- upper bound
    have h1 : ‖P v‖ ≤ ‖D v‖ := by
      change ‖(P v : H)‖ ≤ ‖D v‖
      rw [hPv]
      exact T.range.norm_starProjection_apply_le _
    have h2 : ‖D v‖ ≤ ‖T (dη v)‖ + e * Real.sqrt (B v v) := by
      have := norm_le_insert' (D v) (T (dη v))
      linarith [hD v, norm_sub_norm_le (D v) (T (dη v))]
    have h3 : ‖T (dη v)‖ ≤ C * (2 * Real.sqrt (B v v)) := by
      refine (T.le_opNorm _).trans ?_
      rw [Real.norm_eq_abs]
      exact mul_le_mul hTC (hup v) (abs_nonneg _) ((norm_nonneg _).trans hTC)
    have hν0 := Real.sqrt_nonneg (B v v)
    nlinarith

end RankKernel

section ModelReference

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- The own component of `DΦ_i(a) z` is `(z e₀, 0)`. -/
theorem fderiv_sgpFullGraph_own_SGP5 (i : L.slim.finite_centres.toFinset)
    (sgn c zsgn zc : X → ℝ) (a z : ℝ) :
    fderiv ℝ (sgpFullGraph L Z i sgn c zsgn zc) a z (.inr (.inl i)) =
      sgpBlockEmbed (WithLp.toLp 2 (z, (0 : ℝ))) := by
  have hfd := fderiv_orthogonalBlocks_apply_SGP4 (sgpFullTag L Z i sgn c zsgn zc) (a := a)
    (fun t => (contDiff_sgpFullTag L Z i sgn c zsgn zc t).differentiable (by simp) _) z
    (.inr (.inl i))
  change fderiv ℝ (orthogonalBlocks (sgpFullTag L Z i sgn c zsgn zc)) a z (.inr (.inl i)) = _
  rw [hfd]
  have hmodel : sgpFullTag L Z i sgn c zsgn zc (.inr (.inl i)) =
      fun y => sgpBlockEmbed (WithLp.toLp 2 (y, (1 : ℝ))) := by
    funext y
    simp [sgpFullTag, sgpSlimModelBlock, sgpBlockEmbed_apply]
  have hG : DifferentiableAt ℝ (fun y : ℝ => (WithLp.toLp 2 (y, (1 : ℝ)) : WithLp 2 (ℝ × ℝ))) a :=
    ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.differentiableAt).comp a
      (differentiableAt_id.prodMk (differentiableAt_const _))
  rw [hmodel, fderiv_isometry_comp_apply_SGP4 sgpBlockEmbed hG z, fderiv_ownScalar_apply_SGP4]

/-- **SGP05, the model reference** (frozen tier): `T = DΦ_i(a)` has `|z| ≤ ‖T z‖` (its identity
component) and `‖T‖ ≤ C_*` (G3's early modulus, under G3's hypotheses). -/
theorem sgp05_model_reference (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (i : L.slim.finite_centres.toFinset) (sgn c zsgn zc : X → ℝ) (hsgn : ∀ j, |sgn j| ≤ 1)
    (hzsgn : ∀ k, |zsgn k| ≤ 1)
    (hs0 : ∀ k (hk : k ∈ Z.centres), sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k hk →
      1 ≤ (Z.zero k hk).radius / ρ i.1)
    (huniq : ∀ k₁ (hk₁ : k₁ ∈ Z.centres) k₂ (hk₂ : k₂ ∈ Z.centres),
      sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k₁ hk₁ → sgpZeroMeets Z (Δ := Δ) (ρ := ρ) i.1 k₂ hk₂ →
      k₁ = k₂) (a : ℝ) :
    (∀ z : ℝ, ‖z‖ ≤ ‖fderiv ℝ (sgpFullGraph L Z i sgn c zsgn zc) a z‖) ∧
      ‖fderiv ℝ (sgpFullGraph L Z i sgn c zsgn zc) a‖ ≤ sgpGraphBound := by
  refine ⟨fun z => ?_, (sgp04_full_model_bounds L Z hΔ hΛ hLΛ i sgn c zsgn zc hsgn hzsgn hs0
    huniq a).1⟩
  refine le_trans ?_ (PiLp.norm_apply_le _ (.inr (.inl i)))
  rw [fderiv_sgpFullGraph_own_SGP5, LinearIsometry.norm_map, WithLp.prod_norm_eq_of_L2]
  change ‖z‖ ≤ Real.sqrt (‖z‖ ^ 2 + ‖(0 : ℝ)‖ ^ 2)
  rw [norm_zero, zero_pow two_ne_zero, add_zero, Real.sqrt_sq (norm_nonneg z)]

end ModelReference

section Row

/-- The model metrics of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instMetricNRVZ_SGP5 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instChartedNRVZ_SGP5 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsRVZ`, as a named local instance. -/
local instance instMetricCRVZ_SGP5 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- The scaled metric form `ρ(i)⁻² g_q` as a continuous bilinear form. -/
theorem scaled_form_SGP5 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X) (q : X) (c : ℝ) :
    (∀ v w : TangentSpace 𝓘(ℝ, E3) q, (c ^ 2 • g.inner q) v w = c ^ 2 * g.inner q v w) ∧
    (∀ v w : TangentSpace 𝓘(ℝ, E3) q, (c ^ 2 • g.inner q) v w = (c ^ 2 • g.inner q) w v) ∧
    ∀ v : TangentSpace 𝓘(ℝ, E3) q, 0 ≤ (c ^ 2 • g.inner q) v v := by
  have happ : ∀ v w : TangentSpace 𝓘(ℝ, E3) q,
      (c ^ 2 • g.inner q) v w = c ^ 2 * g.inner q v w := by
    intro v w
    rw [smul_apply, smul_apply, smul_eq_mul]
  refine ⟨happ, fun v w => by rw [happ, happ, g.symm q v w], fun v => ?_⟩
  rw [happ]
  refine mul_nonneg (sq_nonneg c) ?_
  by_cases hv : v = 0
  · rw [hv, map_zero]
  · exact (g.pos q v hv).le

/-- **SGP05's rank form in metric terms**: `sgp05_rank_form_SGP5` for the form `c²g_q`, with the
covector `df_q` and the map `c·dF_q`, stated with `√(c²g_q(v,v))`. -/
theorem sgp05_rank_metric_SGP5 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X) (q : X) (c : ℝ)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (f : X → ℝ) (F : X → H)
    (T : ℝ →L[ℝ] H) (hT : ∀ z, ‖z‖ ≤ ‖T z‖) {C e : ℝ} (hTC : ‖T‖ ≤ C)
    (hlow : ∃ w : TangentSpace 𝓘(ℝ, E3) q,
      c ^ 2 * g.inner q w w = 1 ∧ 9 / 10 < mvfderiv 𝓘(ℝ, E3) f q w)
    (hup : ∀ v : TangentSpace 𝓘(ℝ, E3) q,
      |mvfderiv 𝓘(ℝ, E3) f q v| ≤ 2 * Real.sqrt (c ^ 2 * g.inner q v v))
    (hD : ∀ v : TangentSpace 𝓘(ℝ, E3) q,
      ‖c • mvfderiv 𝓘(ℝ, E3) F q v - T (mvfderiv 𝓘(ℝ, E3) f q v)‖ ≤
        e * Real.sqrt (c ^ 2 * g.inner q v v))
    (he : e < 2 / 5) (heC : e ≤ C) :
    let P := T.range.orthogonalProjectionOnto.comp (c • mvfderiv 𝓘(ℝ, E3) F q)
    Function.Surjective P ∧
      (∀ v, ‖c • mvfderiv 𝓘(ℝ, E3) F q v - (P v : H)‖ ≤ e * Real.sqrt (c ^ 2 * g.inner q v v)) ∧
      (∀ v, (∀ k, P k = 0 → g.inner q v k = 0) →
        1 / 2 * Real.sqrt (c ^ 2 * g.inner q v v) ≤ ‖P v‖) ∧
      ∀ v, ‖P v‖ ≤ 3 * C * Real.sqrt (c ^ 2 * g.inner q v v) := by
  intro P
  obtain ⟨hBapp, hBs, hBp⟩ := scaled_form_SGP5 g q c
  have hlow' : ∃ w, (c ^ 2 • g.inner q) w w = 1 ∧ 9 / 10 < mvfderiv 𝓘(ℝ, E3) f q w := by
    obtain ⟨w, hw1, hw⟩ := hlow
    exact ⟨w, by rw [hBapp]; exact hw1, hw⟩
  have hup' : ∀ v, |mvfderiv 𝓘(ℝ, E3) f q v| ≤ 2 * Real.sqrt ((c ^ 2 • g.inner q) v v) := by
    intro v
    rw [hBapp]
    exact hup v
  have hD' : ∀ v, ‖(c • mvfderiv 𝓘(ℝ, E3) F q) v - T (mvfderiv 𝓘(ℝ, E3) f q v)‖ ≤
      e * Real.sqrt ((c ^ 2 • g.inner q) v v) := by
    intro v
    rw [hBapp, smul_apply]
    exact hD v
  obtain ⟨k1, k2, k3, k4⟩ := sgp05_rank_form_SGP5 (c ^ 2 • g.inner q) hBs hBp T hT hTC
    (mvfderiv 𝓘(ℝ, E3) f q) hlow' hup' (c • mvfderiv 𝓘(ℝ, E3) F q) hD' he heC
  refine ⟨k1, fun v => ?_, fun v hv => ?_, fun v => ?_⟩
  · have h := k2 v
    rw [hBapp, smul_apply] at h
    exact h
  · have h := k3 v (fun k hk => by rw [hBapp, hv k hk, mul_zero])
    rw [hBapp] at h
    exact h
  · have h := k4 v
    rw [hBapp] at h
    exact h

/-- **SGP05 on the actual merged family** (with SGP04's (SG) for the SAME model): for
`0 < e < 1/100` there are `θ` (early) and thresholds such that on every actual RVZ family with
SGP03's hypotheses at `θ`, every slim reference `i` has signs and translations whose full model
`Φ_i` satisfies (SG) on `{|η_i| ≤ 8ℓ}` and, for every core witness `p` (`|η_i(p)| ≤ 7ℓ`) and EVERY
preimage `q` of `x = π₃𝓔⁰(p)`, with `T_x = DΦ_i(η_i p)` and `P_q` the projection onto `im T_x` of
`ρ(i)⁻¹dπ₃𝓔⁰_q`: `P_q` is onto, the normal error is at most `eν`, `‖P_q v‖ ≥ ν(v)/2` on the
`g`-orthogonal complement of `ker P_q` and `‖P_q v‖ ≤ 3C_*ν(v)` (`ν = √(ρ(i)⁻²g)`). -/
theorem sgp05_row {Δ β₂ eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) (heg : 0 < eg)
    (heg1 : eg < 1 / 100) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsRVZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
        0 < σs → σs < θ ^ 2 / 10 ^ 6 → vs < θ / 100 →
        0 < ζ → ζ < θ ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
        εr < θ / (100 * (1000000 * Δ)) →
        ∀ i : P.toLocalChartFamily.slim.finite_centres.toFinset, ∃ sgn c zsgn zc : X → ℝ,
          (∀ j, |sgn j| ≤ 1) ∧ (∀ k, |zsgn k| ≤ 1) ∧
          (∀ x ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1),
            |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x| ≤
              8 * 10 ^ 5 * Δ →
            ‖(ρ i.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ3Tags P.toLocalChartFamily P.zero) x -
              sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc
                ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)‖ < eg ∧
            ∀ w : TangentSpace 𝓘(ℝ, E3) x,
              ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                  (cgpQ3Tags P.toLocalChartFamily P.zero)) x w -
                fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc)
                  ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)
                  (mvfderiv 𝓘(ℝ, E3) (P.slim.centre i.1
                    ((Set.Finite.mem_toFinset _).mp i.2)).coord x w)‖ ≤
                eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner x w w)) ∧
          ∀ p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1),
            |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤
              7 * (10 ^ 5 * Δ) →
            ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
              cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) p →
            let Tx := fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc)
              ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p)
            let Pq := Tx.range.orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)) q)
            Function.Surjective Pq ∧
            (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ3Tags P.toLocalChartFamily P.zero)) q v - (Pq v : BlockSpace _)‖ ≤
              eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
            (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
              1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
            ∀ v, ‖Pq v‖ ≤ 3 * sgpGraphBound * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) := by
  obtain ⟨θ, hθ, hθ1, Lc, η₀, hLc, hη₀, hrow⟩ := sgp04_row hΔ hβ₂ hβ₂1 heg heg1
  have hΔ0 : 0 < Δ := lt_of_lt_of_le one_pos hΔ
  have hθ2 : θ ^ 2 / 10 ^ 6 < 1 / 100 := by
    have : θ ^ 2 < 1 := by nlinarith
    rw [div_lt_iff₀ (by norm_num)]
    linarith
  have hG := four_le_sgpGraphBound_SGP4
  have h78 : 7 * (10 ^ 5 * Δ) ≤ 8 * 10 ^ 5 * Δ := by
    rw [mul_assoc 8]
    exact mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg (by norm_num) hΔ0.le)
  have he25 : eg < 2 / 5 := by linarith
  have heC : eg ≤ sgpGraphBound := by linarith
  refine ⟨θ, hθ, hθ1, Lc, min η₀ (min (1 / (1000 * (1000000 * Δ))) (1 / 2 / 100)), hLc,
    lt_min hη₀ (lt_min (by positivity) (by norm_num)), ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hβ2 hβ1 hLmax hΛ hLΛ he hT hΛzT hσs hσθ hvθ hζ hζθ hζL hεr i
  have hrowP := hrow X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε
    γc βc Lmax τ γ δ εr e T V vs ζ Λz P hβ2 (hβ1.trans (min_le_left _ _)) hLmax hΛ hLΛ he hT
    hΛzT hσs hσθ hvθ hζ hζθ hζL hεr
  have hrowi := hrowP i
  obtain ⟨sgn, c, zsgn, zc, hsgn, hzsgn, hSG⟩ := hrowi
  refine ⟨sgn, c, zsgn, zc, hsgn, hzsgn, hSG, ?_⟩
  intro p hp hηp q hpq
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have hri := hρ i.1
  have hσ1 : σs < 1 / 100 := hσθ.trans hθ2
  have hβref : β 1 ≤ min (1 / (1000 * (1000000 * Δ))) (1 / 2 / 100) :=
    hβ1.trans (min_le_right _ _)
  have hηp8 : |(P.slim.centre i.1 hi).coord p| ≤ 8 * 10 ^ 5 * Δ := hηp.trans h78
  have hfm := sgp05_full_marker P.toLocalChartFamily P.zero i hp hηp8 hpq
  obtain ⟨hcut, hηq⟩ := hfm
  have hqts : q ∈ tsupport (P.slim.cutoff i.1) := by
    apply subset_tsupport
    rw [Function.mem_support, hcut]
    exact one_ne_zero
  have hfc := fc18_slim_row P.toLocalChartFamily hΔ0 hi
  obtain ⟨h1, h2, h3, -⟩ := hfc
  have hqL : q ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1) := h3 (h2 (h1 hqts))
  have hqD : q ∈ ball i.1 (95 / 100 * (1000000 * Δ) * ρ i.1) := by
    have h := h2 (h1 hqts)
    have he' : 95 / 100 * (1000000 * Δ) * ρ i.1 = 950000 * Δ * ρ i.1 := by ring
    rw [he']
    exact h
  have hηq8 : |(P.slim.centre i.1 hi).coord q| ≤ 8 * 10 ^ 5 * Δ := by rw [hηq]; exact hηp8
  have hSGq := (hSG q hqL hηq8).2
  have hrb := sgp05_reference_bounds P.slim hΔ hσs hσ1 hβref hi hqD
  obtain ⟨hlow, hup⟩ := hrb
  have hs01 := sgp01_row P.toLocalChartPacketsR hΛ hΔ hLΛ he hT hσs.le hσ1.le hi
  obtain ⟨-, -, -, huniq, hzero01, -⟩ := hs01
  have hs0 : ∀ k (hk : k ∈ P.zero.centres),
      sgpZeroMeets P.zero (Δ := Δ) (ρ := ρ) i.1 k hk → 1 ≤ (P.zero.zero k hk).radius / ρ i.1 :=
    fun k hk hm => (one_le_div_twenty_SGP4 hΔ hT).trans (hzero01 k hk hm).1
  have hmr := sgp05_model_reference P.toLocalChartFamily P.zero hΔ hΛ hLΛ i sgn c
    zsgn zc hsgn hzsgn hs0 huniq ((P.slim.centre i.1 hi).coord p)
  obtain ⟨hTlow, hTC⟩ := hmr
  have hD : ∀ v : TangentSpace 𝓘(ℝ, E3) q,
      ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ3Tags P.toLocalChartFamily P.zero)) q v -
      fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc)
        ((P.slim.centre i.1 hi).coord p) (mvfderiv 𝓘(ℝ, E3) (P.slim.centre i.1 hi).coord q v)‖ ≤
      eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) := by
    intro v
    rw [← hηq]
    exact hSGq v
  have hrk := sgp05_rank_metric_SGP5 g q (ρ i.1)⁻¹ (P.slim.centre i.1 hi).coord
    (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero))
    (fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc)
      ((P.slim.centre i.1 hi).coord p)) hTlow hTC hlow hup hD he25 heC
  exact hrk

end Row

end DifferentialGeometry.Geometry.Collapse
