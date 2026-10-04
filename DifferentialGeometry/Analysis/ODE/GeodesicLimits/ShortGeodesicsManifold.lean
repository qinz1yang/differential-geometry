import DifferentialGeometry.Analysis.ODE.GeodesicLimits.MetricChristoffelC1
import DifferentialGeometry.Analysis.ODE.GeodesicLimits.MetricChristoffel
import DifferentialGeometry.Analysis.FiniteDimensional.Coercivity
import DifferentialGeometry.Geometry.Metric.ChartLipschitz
import DifferentialGeometry.Geometry.Metric.Approximation.FiniteMetric.Smoothing

/-!
# LFR09 on manifolds: uniform short joining geodesics for `C²`-convergent metrics

Blueprint row LFR09 (A:25443): `C ⊆ W` compact, `W` open in a manifold carrying a metric `g` with
distance `d_g`; `C²` metrics `h_i → g` in `C²` on compact subsets of `W`. There are `τ, L > 0` and
a tail such that `d_g(x, y) < τ`, `x ∈ C`, gives an `h_i`-geodesic from `x` to `y` inside `W` of
`h_i`-length `≤ L d_g(x, y)`.

The metrics `h_i` enter through their coefficient fields `b i z` in the extended chart at `z`
(e.g. `pullbackMetricCoefficients (g i) (j i ∘ (extChartAt I z).symm)` for Cheeger–Gromov
comparison maps `j i`); an `h_i`-geodesic is a solution of the chart geodesic equation
`γ'' = -Γ(b i z)(γ)(γ', γ')` (the second component of the tree's `metricSpray (b i z)`), and its
`h_i`-speed is `√(b i z (γ t) (γ' t) (γ' t))`.

* `exists_short_geodesics_of_metric_C2_eventually`: the chart kernel with regularity of the `h_i`
  only for a tail, no coercivity hypothesis on the `h_i` (it follows from the convergence), the
  geodesics inside `U`, and the metric speed bound `b i (γ t) (γ' t) (γ' t) ≤ (L ‖y - x‖)²`.
* `exists_short_geodesics_in_charts`: the manifold / `d_g` form, for any metric space `N` whose
  distance is the Riemannian distance of a continuous Riemannian structure (finite chart cover,
  coordinate margin, local Lipschitz bound of the charts for `d_g`).
* `exists_short_geodesics_of_contMDiffRiemannianMetric`: **LFR09 for actual finite-order
  Riemannian manifolds** — the limit coefficients are `chartCoeff G z` of a `C^n` metric `G`,
  `2 ≤ n`, and `d_g` is the Riemannian distance of `G`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Metric Bundle
open scoped Topology NNReal Manifold ContDiff

namespace DifferentialGeometry.Analysis.ODE.GeodesicLimits

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.MetricKoszul

section Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ContinuousDualEquiv E]

/-- **LFR09, chart kernel, tail form with metric speed.** `C²` coefficient fields `b i` (for a
tail of `i`) converging in `C²` on compact subsets of the open set `U` to a coercive `C²` field
`b∞`: for `C ⊆ U` compact there are `τ, L > 0` such that eventually every `x ∈ C` and `y` with
`‖y - x‖ ≤ τ` are joined by a `b i`-geodesic `γ : [0, 1] → U` with coordinate speed
`≤ L ‖y - x‖` and metric speed `√(b i (γ t) (γ' t) (γ' t)) ≤ L ‖y - x‖`. -/
theorem exists_short_geodesics_of_metric_C2_eventually {U : Set E} (hU : IsOpen U)
    {b : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ} {bInf : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hb : ∀ᶠ i in atTop, ContDiffOn ℝ 2 (b i) U) (hbInf : ContDiffOn ℝ 2 bInf U)
    (hco : ∀ x ∈ U, IsCoercive (bInf x))
    (hconv : ∀ K, IsCompact K → K ⊆ U → MapCPConvergenceOn K 2 b bInf) {C : Set E}
    (hC : IsCompact C) (hCU : C ⊆ U) :
    ∃ τ L : ℝ, 0 < τ ∧ 0 < L ∧ ∀ᶠ i in atTop, ∀ x ∈ C, ∀ y : E,
      ‖y - x‖ ≤ τ → ∃ γ γ' : ℝ → E, γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U ∧
        HasDerivWithinAt γ (γ' t) (Icc 0 1) t ∧
        HasDerivWithinAt γ' (-(raisedKoszulOp (b i (γ t)) (fderiv ℝ (b i) (γ t)) (γ' t) (γ' t)))
          (Icc 0 1) t ∧ ‖γ' t‖ ≤ L * ‖y - x‖ ∧
        b i (γ t) (γ' t) (γ' t) ≤ (L * ‖y - x‖) ^ 2 := by
  obtain ⟨δ, hδ, hδU⟩ := hC.exists_cthickening_subset_open hU hCU
  have hQ : IsCompact (cthickening δ C) := hC.cthickening
  have hU'o : IsOpen (thickening δ C) := isOpen_thickening
  have hU'Q : thickening δ C ⊆ cthickening δ C := thickening_subset_cthickening δ C
  have hU'U : thickening δ C ⊆ U := hU'Q.trans hδU
  have hCU' : C ⊆ thickening δ C := self_subset_thickening hδ C
  -- uniform coercivity and a bound of the limit on the compact `cthickening δ C`
  obtain ⟨c, hc, hcQ⟩ := exists_uniform_coercive_of_isCompact hQ (hbInf.continuousOn.mono hδU)
    (fun x hx => hco x (hδU hx))
  obtain ⟨B₀, hB₀⟩ := hQ.exists_bound_of_continuousOn (hbInf.continuousOn.mono hδU)
  have hunif := Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_of_cPConvergence
    ((hconv _ hQ hδU).mono_order (Nat.zero_le 2)))
  have hgood : ∀ᶠ i in atTop, ContDiffOn ℝ 2 (b i) U ∧
      ∀ x ∈ cthickening δ C, ‖b i x - bInf x‖ < min (c / 2) 1 := by
    filter_upwards [hb, hunif _ (lt_min (half_pos hc) one_pos)] with i hi1 hi2
    exact ⟨hi1, fun x hx => by rw [← dist_eq_norm, dist_comm]; exact hi2 x hx⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hgood
  set B : ℝ := max B₀ 0 + 1 with hB_def
  have hB1 : 1 ≤ B := by have := le_max_right B₀ 0; linarith
  have hcoQ : ∀ i, N ≤ i → ∀ x ∈ cthickening δ C, IsCoercive (b i x) := by
    intro i hi x hx
    refine ⟨c / 2, half_pos hc, fun u => ?_⟩
    have hd := (hN i hi).2 x hx
    have h1 : |(b i x - bInf x) u u| ≤ ‖b i x - bInf x‖ * ‖u‖ * ‖u‖ := by
      rw [← Real.norm_eq_abs]
      exact (b i x - bInf x).le_opNorm₂ u u
    have h3 : (b i x - bInf x) u u = b i x u u - bInf x u u := rfl
    have h4 := mul_le_mul_of_nonneg_right ((hd.trans_le (min_le_left _ _)).le)
      (mul_nonneg (norm_nonneg u) (norm_nonneg u))
    have h5 := hcQ x hx u
    nlinarith [neg_abs_le ((b i x - bInf x) u u)]
  have hbdQ : ∀ i, N ≤ i → ∀ x ∈ cthickening δ C, ‖b i x‖ ≤ B := by
    intro i hi x hx
    have hd := ((hN i hi).2 x hx).trans_le (min_le_right _ _)
    calc ‖b i x‖ = ‖(b i x - bInf x) + bInf x‖ := by rw [sub_add_cancel]
      _ ≤ ‖b i x - bInf x‖ + ‖bInf x‖ := norm_add_le _ _
      _ ≤ 1 + max B₀ 0 := add_le_add hd.le ((hB₀ x hx).trans (le_max_left _ _))
      _ = B := by rw [hB_def]; ring
  -- the coefficient kernel for the shifted sequence on `thickening δ C`
  obtain ⟨τ, L, hτ, hL, hev⟩ := exists_short_geodesics_of_metric_C2 hU'o
    (b := fun k => b (k + N)) (bInf := bInf)
    (fun k => (hN (k + N) (Nat.le_add_left N k)).1.mono hU'U) (hbInf.mono hU'U)
    (fun k x hx => hcoQ (k + N) (Nat.le_add_left N k) x (hU'Q hx)) (fun x hx => hco x (hU'U hx))
    (fun K hK hKU' => (hconv K hK (hKU'.trans hU'U)).comp_tendsto_atTop
      (tendsto_add_atTop_nat N)) hC hCU'
  refine ⟨τ, L * B, hτ, mul_pos hL (zero_lt_one.trans_le hB1), ?_⟩
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hev
  filter_upwards [eventually_ge_atTop (k₀ + N)] with i hi x hx y hy
  have hNi : i - N + N = i := Nat.sub_add_cancel (by omega)
  have hi' := hk₀ (i - N) (by omega)
  simp only [hNi] at hi'
  obtain ⟨γ, γ', h0, h1, hγ⟩ := hi' x hx y hy
  refine ⟨γ, γ', h0, h1, fun t ht => ?_⟩
  obtain ⟨hγU, hd, hd', hsp⟩ := hγ t ht
  have hLx : 0 ≤ L * ‖y - x‖ := mul_nonneg hL.le (norm_nonneg _)
  have hsp' : ‖γ' t‖ ≤ L * B * ‖y - x‖ := hsp.trans (by
    rw [mul_right_comm]
    exact le_mul_of_one_le_right hLx hB1)
  refine ⟨hU'U hγU, hd, hd', hsp', ?_⟩
  have hbd := hbdQ i (by omega) (γ t) (hU'Q hγU)
  calc b i (γ t) (γ' t) (γ' t) ≤ ‖b i (γ t) (γ' t) (γ' t)‖ := Real.le_norm_self _
    _ ≤ ‖b i (γ t)‖ * ‖γ' t‖ * ‖γ' t‖ := (b i (γ t)).le_opNorm₂ _ _
    _ ≤ B * (L * ‖y - x‖) * (L * ‖y - x‖) := by
        gcongr
    _ ≤ B * B * (L * ‖y - x‖) * (L * ‖y - x‖) := by
        have h0' : 0 ≤ (L * ‖y - x‖) * (L * ‖y - x‖) := mul_nonneg hLx hLx
        have hBB : B ≤ B * B := le_mul_of_one_le_right (by linarith) hB1
        rw [mul_assoc B, mul_assoc (B * B)]
        exact mul_le_mul_of_nonneg_right hBB h0'
    _ = (L * B * ‖y - x‖) ^ 2 := by ring

end Chart

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ContinuousDualEquiv E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

omit [FiniteDimensional ℝ E] [ContinuousDualEquiv E] [IsManifold I ∞ N] in
theorem isOpen_extChartAt_target_inter_preimage {W : Set N} (hW : IsOpen W) (z : N) :
    IsOpen ((extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' W) :=
  (continuousOn_extChartAt_symm z).isOpen_inter_preimage (isOpen_extChartAt_target z) hW

variable [RiemannianBundle (fun x : N => TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]

/-- **LFR09, manifold / `d_g` form.** `N` a manifold whose distance is the Riemannian distance of
a continuous Riemannian structure; `W ⊆ N` open, `C ⊆ W` compact. The metrics `h_i` are given by
their coefficient fields `b i z` in the extended charts at `z`, `C²` (for a tail of `i`) on
`chart target ∩ chart⁻¹ W`, converging in `C²` on its compact subsets to coercive `C²` fields
`b∞ z`. Then there are `τ, L > 0` and a tail such that any `x ∈ C` and `y` with `d(x, y) < τ`
are joined, in the chart at some `z`, by a `b i z`-geodesic `γ : [0, 1]` running in
`chart target ∩ chart⁻¹ W` with `h_i`-speed `√(b i z (γ t) (γ' t) (γ' t)) ≤ L d(x, y)` (hence
`h_i`-length `≤ L d(x, y)`) and coordinate speed `≤ L d(x, y)`. -/
theorem exists_short_geodesics_in_charts
    (b : ℕ → N → E → E →L[ℝ] E →L[ℝ] ℝ) (bInf : N → E → E →L[ℝ] E →L[ℝ] ℝ)
    {W : Set N} (hW : IsOpen W)
    (hb : ∀ z, ∀ᶠ i in atTop,
      ContDiffOn ℝ 2 (b i z) ((extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' W))
    (hbInf : ∀ z,
      ContDiffOn ℝ 2 (bInf z) ((extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' W))
    (hco : ∀ z, ∀ u ∈ (extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' W,
      IsCoercive (bInf z u))
    (hconv : ∀ z K, IsCompact K → K ⊆ (extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' W →
      MapCPConvergenceOn K 2 (fun i => b i z) (bInf z))
    {C : Set N} (hC : IsCompact C) (hCW : C ⊆ W) :
    ∃ τ L : ℝ, 0 < τ ∧ 0 < L ∧ ∀ᶠ i in atTop, ∀ x ∈ C, ∀ y : N, dist x y < τ →
      ∃ z : N, ∃ γ γ' : ℝ → E, x ∈ (extChartAt I z).source ∧ y ∈ (extChartAt I z).source ∧
        γ 0 = extChartAt I z x ∧ γ 1 = extChartAt I z y ∧
        ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (extChartAt I z).target ∧ (extChartAt I z).symm (γ t) ∈ W ∧
          HasDerivWithinAt γ (γ' t) (Icc 0 1) t ∧
          HasDerivWithinAt γ'
            (-(raisedKoszulOp (b i z (γ t)) (fderiv ℝ (b i z) (γ t)) (γ' t) (γ' t))) (Icc 0 1) t ∧
          ‖γ' t‖ ≤ L * dist x y ∧ b i z (γ t) (γ' t) (γ' t) ≤ (L * dist x y) ^ 2 := by
  classical
  -- per centre: a Lipschitz neighbourhood of the chart, a ball, and the chart kernel
  have hloc : ∀ z ∈ C, ∃ ε K τ L : ℝ, 0 < ε ∧ 0 ≤ K ∧ 0 < τ ∧ 0 < L ∧
      ball z (2 * ε) ⊆ W ∩ (extChartAt I z).source ∧
      (∀ x ∈ ball z (2 * ε), ∀ y ∈ ball z (2 * ε),
        dist (extChartAt I z x) (extChartAt I z y) ≤ K * dist x y) ∧
      ∀ᶠ i in atTop, ∀ x ∈ C ∩ closedBall z ε, ∀ y' : E, ‖y' - extChartAt I z x‖ ≤ τ →
        ∃ γ γ' : ℝ → E, γ 0 = extChartAt I z x ∧ γ 1 = y' ∧ ∀ t ∈ Icc (0 : ℝ) 1,
          γ t ∈ (extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' W ∧
          HasDerivWithinAt γ (γ' t) (Icc 0 1) t ∧
          HasDerivWithinAt γ'
            (-(raisedKoszulOp (b i z (γ t)) (fderiv ℝ (b i z) (γ t)) (γ' t) (γ' t))) (Icc 0 1) t ∧
          ‖γ' t‖ ≤ L * ‖y' - extChartAt I z x‖ ∧
          b i z (γ t) (γ' t) (γ' t) ≤ (L * ‖y' - extChartAt I z x‖) ^ 2 := by
    intro z hz
    obtain ⟨K, s, hs, hKs⟩ :=
      DifferentialGeometry.Geometry.Riemannian.exists_lipschitzOnWith_extChartAt (I := I) z
    have hnhds : s ∩ (W ∩ (extChartAt I z).source) ∈ 𝓝 z :=
      inter_mem hs (inter_mem (hW.mem_nhds (hCW hz)) (extChartAt_source_mem_nhds z))
    obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.mp hnhds
    set ε := ε₀ / 2 with hε_def
    have hε : 0 < ε := half_pos hε₀
    have h2ε : 2 * ε = ε₀ := by rw [hε_def]; ring
    have hball' : ball z (2 * ε) ⊆ s ∩ (W ∩ (extChartAt I z).source) := by rw [h2ε]; exact hball
    set Uz := (extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' W with hUz_def
    have hUz : IsOpen Uz := isOpen_extChartAt_target_inter_preimage hW z
    have hCz_sub : C ∩ closedBall z ε ⊆ ball z (2 * ε) := fun x hx =>
      mem_ball.mpr ((mem_closedBall.mp hx.2).trans_lt (by linarith))
    have hCzc : IsCompact (extChartAt I z '' (C ∩ closedBall z ε)) :=
      (hC.inter_right isClosed_closedBall).image_of_continuousOn
        ((continuousOn_extChartAt z).mono fun x hx => (hball' (hCz_sub hx)).2.2)
    have hCzU : extChartAt I z '' (C ∩ closedBall z ε) ⊆ Uz := by
      rintro _ ⟨x, hx, rfl⟩
      have hxs : x ∈ (extChartAt I z).source := (hball' (hCz_sub hx)).2.2
      refine ⟨(extChartAt I z).map_source hxs, ?_⟩
      change (extChartAt I z).symm (extChartAt I z x) ∈ W
      rw [(extChartAt I z).left_inv hxs]
      exact hCW hx.1
    obtain ⟨τ, L, hτ, hL, hev⟩ := exists_short_geodesics_of_metric_C2_eventually hUz (hb z)
      (hbInf z) (hco z) (hconv z) hCzc hCzU
    refine ⟨ε, K, τ, L, hε, K.coe_nonneg, hτ, hL, fun x hx => (hball' hx).2,
      fun x hx y hy => ?_, ?_⟩
    · have := hKs.dist_le_mul x (hball' hx).1 y (hball' hy).1
      exact this
    · filter_upwards [hev] with i hi x hx y' hy'
      exact hi _ ⟨x, hx, rfl⟩ y' hy'
  choose! ε K τ L hε hK hτ hL hballW hlip hev using hloc
  obtain ⟨t, htC, hCt⟩ := hC.elim_nhds_subcover (fun z => ball z (ε z))
    (fun z hz => ball_mem_nhds z (hε z hz))
  -- the threshold and the length constant over the finite cover
  set τz : N → ℝ := fun z => min (ε z) (τ z / (K z + 1)) with hτz_def
  have hτzpos : ∀ z ∈ C, 0 < τz z := fun z hz =>
    lt_min (hε z hz) (div_pos (hτ z hz) (by linarith [hK z hz]))
  obtain ⟨τm, hτm, hτmle⟩ : ∃ τm : ℝ, 0 < τm ∧ ∀ z ∈ t, τm ≤ τz z := by
    by_cases ht : t.Nonempty
    · obtain ⟨z₁, hz₁, hmin⟩ := t.exists_min_image τz ht
      exact ⟨τz z₁, hτzpos z₁ (htC z₁ hz₁), hmin⟩
    · exact ⟨1, one_pos, fun z hz => absurd ⟨z, hz⟩ ht⟩
  set Lz : N → ℝ := fun z => L z * (K z + 1) with hLz_def
  set Lm : ℝ := 1 + ∑ z ∈ t, Lz z with hLm_def
  have hLzpos : ∀ z ∈ t, 0 ≤ Lz z := fun z hz =>
    mul_nonneg (hL z (htC z hz)).le (by linarith [hK z (htC z hz)])
  have hLm : 0 < Lm := by
    have := Finset.sum_nonneg hLzpos
    linarith
  have hLle : ∀ z ∈ t, Lz z ≤ Lm := fun z hz => by
    have := Finset.single_le_sum hLzpos hz
    linarith
  refine ⟨τm, Lm, hτm, hLm, ?_⟩
  filter_upwards [(Filter.eventually_all_finset t).2 fun z hz => hev z (htC z hz)] with i hi
    x hx y hxy
  obtain ⟨z, hzt, hxz⟩ := mem_iUnion₂.mp (hCt hx)
  have hzC := htC z hzt
  have hεz : dist x y < ε z := hxy.trans_le ((hτmle z hzt).trans (min_le_left _ _))
  have hx2 : x ∈ ball z (2 * ε z) :=
    mem_ball.mpr ((mem_ball.mp hxz).trans (by linarith [hε z hzC]))
  have hy2 : y ∈ ball z (2 * ε z) := by
    refine mem_ball.mpr ?_
    calc dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
      _ < ε z + ε z := add_lt_add (by rw [dist_comm]; exact hεz) (mem_ball.mp hxz)
      _ = 2 * ε z := by ring
  have hxs := (hballW z hzC hx2).2
  have hys := (hballW z hzC hy2).2
  have hKz := hK z hzC
  have hcoord : ‖extChartAt I z y - extChartAt I z x‖ ≤ (K z + 1) * dist x y := by
    rw [← dist_eq_norm, dist_comm]
    exact (hlip z hzC x hx2 y hy2).trans
      (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg)
  have hτK : (K z + 1) * dist x y ≤ τ z := by
    have h1 : dist x y < τ z / (K z + 1) := hxy.trans_le ((hτmle z hzt).trans (min_le_right _ _))
    have h2 : 0 < K z + 1 := by linarith
    rw [lt_div_iff₀ h2] at h1
    linarith
  obtain ⟨γ, γ', h0, h1, hγ⟩ := hi z hzt x ⟨hx, ball_subset_closedBall hxz⟩
    (extChartAt I z y) (hcoord.trans hτK)
  refine ⟨z, γ, γ', hxs, hys, h0, h1, fun s hs => ?_⟩
  obtain ⟨hγU, hd, hd', hsp, hmsp⟩ := hγ s hs
  have hLK : L z * ‖extChartAt I z y - extChartAt I z x‖ ≤ Lm * dist x y := by
    calc L z * ‖extChartAt I z y - extChartAt I z x‖ ≤ L z * ((K z + 1) * dist x y) :=
          mul_le_mul_of_nonneg_left hcoord (hL z hzC).le
      _ = Lz z * dist x y := by rw [hLz_def]; ring
      _ ≤ Lm * dist x y := mul_le_mul_of_nonneg_right (hLle z hzt) dist_nonneg
  have hLK0 : 0 ≤ L z * ‖extChartAt I z y - extChartAt I z x‖ :=
    mul_nonneg (hL z hzC).le (norm_nonneg _)
  refine ⟨hγU.1, hγU.2, hd, hd', hsp.trans hLK, hmsp.trans ?_⟩
  exact pow_le_pow_left₀ hLK0 hLK 2

end Manifold

section FiniteOrder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ContinuousDualEquiv E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

open DifferentialGeometry.Geometry.MetricSmoothing in
/-- **LFR09 for actual finite-order Riemannian manifolds.** `(N, G)` a manifold with a `C^n`
Riemannian metric `G`, `2 ≤ n`, whose distance is the Riemannian distance of `G`; `W ⊆ N` open,
`C ⊆ W` compact; metrics `h_i` with chart coefficients `b i z` (`C²` for a tail, on
`chart target ∩ chart⁻¹ W`) converging in `C²` on compact subsets to the chart coefficients
`chartCoeff G z` of `G`. Then there are `τ, L > 0` and a tail such that any `x ∈ C` and `y` with
`d_G(x, y) < τ` are joined by an `h_i`-geodesic (chart geodesic equation of `b i z`) inside `W`
of `h_i`-speed, hence `h_i`-length, at most `L d_G(x, y)`. -/
theorem exists_short_geodesics_of_contMDiffRiemannianMetric {n : ℕ∞ω}
    (G : ContMDiffRiemannianMetric I n E (TangentSpace I : N → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (hG : letI : RiemannianBundle (fun x : N => TangentSpace I x) := ⟨G.toRiemannianMetric⟩
      IsRiemannianManifold I N)
    (b : ℕ → N → E → E →L[ℝ] E →L[ℝ] ℝ) {W : Set N} (hW : IsOpen W)
    (hb : ∀ z, ∀ᶠ i in atTop,
      ContDiffOn ℝ 2 (b i z) ((extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' W))
    (hconv : ∀ z K, IsCompact K → K ⊆ (extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' W →
      MapCPConvergenceOn K 2 (fun i => b i z) (chartCoeff G z))
    {C : Set N} (hC : IsCompact C) (hCW : C ⊆ W) :
    ∃ τ L : ℝ, 0 < τ ∧ 0 < L ∧ ∀ᶠ i in atTop, ∀ x ∈ C, ∀ y : N, dist x y < τ →
      ∃ z : N, ∃ γ γ' : ℝ → E, x ∈ (extChartAt I z).source ∧ y ∈ (extChartAt I z).source ∧
        γ 0 = extChartAt I z x ∧ γ 1 = extChartAt I z y ∧
        ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (extChartAt I z).target ∧ (extChartAt I z).symm (γ t) ∈ W ∧
          HasDerivWithinAt γ (γ' t) (Icc 0 1) t ∧
          HasDerivWithinAt γ'
            (-(raisedKoszulOp (b i z (γ t)) (fderiv ℝ (b i z) (γ t)) (γ' t) (γ' t))) (Icc 0 1) t ∧
          ‖γ' t‖ ≤ L * dist x y ∧ b i z (γ t) (γ' t) (γ' t) ≤ (L * dist x y) ^ 2 := by
  let _ : RiemannianBundle (fun x : N => TangentSpace I x) := ⟨G.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x) :=
    ⟨⟨G.inner, G.contMDiff.continuous, by intro x v w; rfl⟩⟩
  have := hG
  exact exists_short_geodesics_in_charts b (chartCoeff G) hW hb
    (fun z => (contDiffOn_chartCoeff G hn z).mono inter_subset_left)
    (fun z u hu => ContinuousLinearMap.isCoercive_of_posDef _ fun _ hv =>
      chartCoeff_pos G z hu.1 hv)
    hconv hC hCW

end FiniteOrder

end DifferentialGeometry.Analysis.ODE.GeodesicLimits
