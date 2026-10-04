import DifferentialGeometry.Analysis.ODE.GeodesicLimits.LipschitzTube
import DifferentialGeometry.Geometry.Geodesic.Equation.MetricSprayFiniteRegularity
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic

/-!
# Geodesic limits in coefficient form: `C¹` convergence of chart metrics

The chart Christoffel operator of a coefficient field `b : F → F →L F →L ℝ` is
`MetricKoszul.raisedKoszulOp (b x) (fderiv ℝ b x)`, the second component of `MetricKoszul.metricSpray b`
(`Geometry/Geodesic/Equation/MetricSpray.lean`); CM-P's finite-metric flow satisfies this chart equation
(`Bundle.ContMDiffRiemannianMetric.hasDerivAt_geodesicFlow_chart`).

* `exists_uniform_coercive_of_isCompact`: continuous coercive forms on a compact set are uniformly
  coercive.
* `norm_raisedKoszulOp_sub_le`: quantitative continuity of `(B, D) ↦ raisedKoszulOp B D` at a coercive
  `B` (from the tree's `koszul_vec_sub_le`).
* `tendstoUniformlyOn_raisedKoszulOp_of_mapCPConvergenceOn`: `C¹` convergence of coefficients
  (`MapCPConvergenceOn K 1`) gives uniform convergence of the Christoffel operators on `K`.
* `continuousOn_raisedKoszulOp_fderiv`: the limit operator is continuous on `K`.
* `exists_C1_subseq_limit_of_metric_tendsto`: CM4.a in coefficient form (`C¹` metrics, `C¹` convergence).
* `tendstoUniformlyOn_of_metric_tendsto`: CM4.c in coefficient form (`C²` limit metric): the whole
  sequence of geodesics converges in `C¹` once the initial data converge.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology Metric
open scoped NNReal
open DifferentialGeometry.MetricKoszul DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.Analysis.ODE.GeodesicLimits

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [ContinuousDualEquiv F]

noncomputable local instance cmlDualNormedGroup : NormedAddCommGroup (F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance cmlDualNormedSpace : NormedSpace ℝ (F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
noncomputable local instance cmlBilinNormedGroup : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance cmlBilinNormedSpace : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
noncomputable local instance cmlTriNormedGroup :
    NormedAddCommGroup (F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance cmlTriNormedSpace : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

omit [FiniteDimensional ℝ F] [ContinuousDualEquiv F] in
/-- A continuous family of coercive forms on a compact set is uniformly coercive. -/
theorem exists_uniform_coercive_of_isCompact {K : Set F} (hK : IsCompact K)
    {bInf : F → F →L[ℝ] F →L[ℝ] ℝ} (hcont : ContinuousOn bInf K)
    (hco : ∀ x ∈ K, IsCoercive (bInf x)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ u : F, c * ‖u‖ * ‖u‖ ≤ bInf x u u := by
  refine hK.induction_on (p := fun s => ∃ c : ℝ, 0 < c ∧ ∀ x ∈ s, ∀ u : F,
      c * ‖u‖ * ‖u‖ ≤ bInf x u u) ⟨1, one_pos, fun x hx => absurd hx (notMem_empty x)⟩ ?_ ?_ ?_
  · rintro s t hst ⟨c, hc, h⟩
    exact ⟨c, hc, fun x hx => h x (hst hx)⟩
  · rintro s t ⟨c, hc, h⟩ ⟨c', hc', h'⟩
    refine ⟨min c c', lt_min hc hc', fun x hx u => ?_⟩
    have hu := mul_self_nonneg ‖u‖
    rcases hx with hx | hx
    · calc min c c' * ‖u‖ * ‖u‖ ≤ c * ‖u‖ * ‖u‖ := by
            rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (min_le_left c c') hu
        _ ≤ bInf x u u := h x hx u
    · calc min c c' * ‖u‖ * ‖u‖ ≤ c' * ‖u‖ * ‖u‖ := by
            rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (min_le_right c c') hu
        _ ≤ bInf x u u := h' x hx u
  · intro x₀ hx₀
    obtain ⟨c₀, hc₀, h₀⟩ := hco x₀ hx₀
    obtain ⟨δ, hδ, hδc⟩ :=
      Metric.continuousWithinAt_iff.mp (hcont x₀ hx₀) (c₀ / 2) (by positivity)
    refine ⟨K ∩ ball x₀ δ, inter_mem_nhdsWithin _ (ball_mem_nhds x₀ hδ), c₀ / 2, by positivity,
      fun y hy u => ?_⟩
    have hd : dist (bInf y) (bInf x₀) < c₀ / 2 := hδc hy.1 hy.2
    rw [dist_eq_norm (bInf y) (bInf x₀)] at hd
    have hdiff : |(bInf y - bInf x₀) u u| ≤ ‖bInf y - bInf x₀‖ * ‖u‖ * ‖u‖ := by
      rw [← Real.norm_eq_abs]
      exact (bInf y - bInf x₀).le_opNorm₂ u u
    have hsplit : bInf y u u = bInf x₀ u u + (bInf y - bInf x₀) u u := by
      simp only [FunLike.coe_sub, Pi.sub_apply]; ring
    have hu := mul_self_nonneg ‖u‖
    have h1 : ‖bInf y - bInf x₀‖ * ‖u‖ * ‖u‖ ≤ c₀ / 2 * ‖u‖ * ‖u‖ := by
      rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hd.le hu
    have h2 := h₀ u
    have h3 := neg_abs_le ((bInf y - bInf x₀) u u)
    rw [hsplit]
    nlinarith

/-- Quantitative continuity of the Christoffel operator at a coercive form. -/
theorem norm_raisedKoszulOp_sub_le {B B₀ : F →L[ℝ] F →L[ℝ] ℝ} {c : ℝ} (hc : 0 < c)
    (hB₀ : ∀ u : F, c * ‖u‖ * ‖u‖ ≤ B₀ u u) {δ M : ℝ} (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hBB : ‖B - B₀‖ ≤ δ) (hδc : δ ≤ c / 2) {D D₀ : F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ}
    (hDD : ‖D - D₀‖ ≤ δ) (hD₀ : ‖D₀‖ ≤ M) :
    ‖raisedKoszulOp B D - raisedKoszulOp B₀ D₀‖ ≤ (3 / c + 3 * M / c ^ 2) * δ := by
  have : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hc2 : 0 < c / 2 := by positivity
  have hB : ∀ u : F, c / 2 * ‖u‖ * ‖u‖ ≤ B u u := by
    intro u
    have hdiff : |(B - B₀) u u| ≤ ‖B - B₀‖ * ‖u‖ * ‖u‖ := by
      rw [← Real.norm_eq_abs]
      exact (B - B₀).le_opNorm₂ u u
    have hsplit : B u u = B₀ u u + (B - B₀) u u := by
      simp only [FunLike.coe_sub, Pi.sub_apply]; ring
    have hu := mul_self_nonneg ‖u‖
    have h1 : ‖B - B₀‖ * ‖u‖ * ‖u‖ ≤ c / 2 * ‖u‖ * ‖u‖ := by
      rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (hBB.trans hδc) hu
    have h2 := hB₀ u
    have h3 := neg_abs_le ((B - B₀) u u)
    rw [hsplit]
    nlinarith
  have hBco : IsCoercive B := ⟨c / 2, hc2, hB⟩
  have hB₀co : IsCoercive B₀ := ⟨c, hc, hB₀⟩
  have h3 : ∀ (T : F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) (u v w : F),
      ‖T u v w‖ ≤ ‖T‖ * ‖u‖ * ‖v‖ * ‖w‖ := by
    intro T u v w
    calc ‖T u v w‖ ≤ ‖T u‖ * ‖v‖ * ‖w‖ := (T u).le_opNorm₂ v w
      _ ≤ ‖T‖ * ‖u‖ * ‖v‖ * ‖w‖ := by
        gcongr
        exact T.le_opNorm u
  have hsub : ∀ u v w : F, ‖(D - D₀) u v w‖ ≤ δ * ‖u‖ * ‖v‖ * ‖w‖ := fun u v w =>
    (h3 (D - D₀) u v w).trans (by gcongr)
  have hF : ∀ u v w : F, ‖D₀ u v w‖ ≤ M * ‖u‖ * ‖v‖ * ‖w‖ := fun u v w =>
    (h3 D₀ u v w).trans (by gcongr)
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun v w => ?_
  rw [FunLike.coe_sub, Pi.sub_apply, FunLike.coe_sub, Pi.sub_apply,
    raisedKoszulOp_eq hBco, raisedKoszulOp_eq hB₀co]
  have hk := koszul_vec_sub_le hBco hB₀co hc2 hc hB hB₀ D D₀ hδ hM hsub hF v w
  have hBB' : ‖B₀ - B‖ ≤ δ := by rw [norm_sub_rev]; exact hBB
  have hv := norm_nonneg v
  have hw := norm_nonneg w
  calc ‖koszulVec hBco D v w - koszulVec hB₀co D₀ v w‖
      ≤ (c / 2)⁻¹ * (3 / 2 * δ * ‖v‖ * ‖w‖) +
          (c / 2)⁻¹ * (‖B₀ - B‖ * (c⁻¹ * (3 / 2 * M * ‖v‖ * ‖w‖))) := hk
    _ ≤ (c / 2)⁻¹ * (3 / 2 * δ * ‖v‖ * ‖w‖) +
          (c / 2)⁻¹ * (δ * (c⁻¹ * (3 / 2 * M * ‖v‖ * ‖w‖))) := by gcongr
    _ = (3 / c + 3 * M / c ^ 2) * δ * ‖v‖ * ‖w‖ := by field_simp

/-- The limit Christoffel operator of a `C¹` coefficient field is continuous on a set where the
coefficients are coercive. -/
theorem continuousOn_raisedKoszulOp_fderiv {U K : Set F} (hU : IsOpen U) (hKU : K ⊆ U)
    {bInf : F → F →L[ℝ] F →L[ℝ] ℝ} (hbInf : ContDiffOn ℝ 1 bInf U)
    (hco : ∀ x ∈ K, IsCoercive (bInf x)) :
    ContinuousOn (fun x => raisedKoszulOp (bInf x) (fderiv ℝ bInf x)) K :=
  (raisedKoszulOp_contDiffOn (n := 0) (U := K)
    (contDiffOn_zero.mpr (hbInf.continuousOn.mono hKU))
    (contDiffOn_zero.mpr ((hbInf.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU)) hco).continuousOn

/-- **Metric adapter.** `C¹` convergence of `C¹` coefficient fields on a compact `K` (coercive limit)
gives uniform convergence of the Christoffel operators on `K`. -/
theorem tendstoUniformlyOn_raisedKoszulOp_of_mapCPConvergenceOn
    {U K : Set F} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (b : ℕ → F → F →L[ℝ] F →L[ℝ] ℝ) (bInf : F → F →L[ℝ] F →L[ℝ] ℝ)
    (hb : ∀ i, ContDiffOn ℝ 1 (b i) U) (hbInf : ContDiffOn ℝ 1 bInf U)
    (hco : ∀ x ∈ K, IsCoercive (bInf x)) (hconv : MapCPConvergenceOn K 1 b bInf) :
    TendstoUniformlyOn (fun i x => raisedKoszulOp (b i x) (fderiv ℝ (b i) x))
      (fun x => raisedKoszulOp (bInf x) (fderiv ℝ bInf x)) atTop K := by
  have hdiff : ∀ i, ∀ x ∈ K, DifferentiableAt ℝ (b i) x := fun i x hx =>
    ((hb i).differentiableOn one_ne_zero x (hKU hx)).differentiableAt (hU.mem_nhds (hKU hx))
  have hdiffInf : ∀ x ∈ K, DifferentiableAt ℝ bInf x := fun x hx =>
    (hbInf.differentiableOn one_ne_zero x (hKU hx)).differentiableAt (hU.mem_nhds (hKU hx))
  obtain ⟨c, hc, hcK⟩ :=
    exists_uniform_coercive_of_isCompact hK (hbInf.continuousOn.mono hKU) hco
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn
    ((hbInf.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU)
  set M : ℝ := max M₀ 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  set C₁ : ℝ := 3 / c + 3 * M / c ^ 2 with hC₁def
  have hC₁ : 0 < C₁ := by positivity
  refine (Metric.tendstoUniformlyOn_iff
    (F := fun i x => raisedKoszulOp (b i x) (fderiv ℝ (b i) x))
    (f := fun x => raisedKoszulOp (bInf x) (fderiv ℝ bInf x)) (p := atTop) (s := K)).mpr ?_
  intro ε hε
  set δ : ℝ := min (c / 2) (ε / (2 * C₁)) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  obtain ⟨k0, hk0⟩ := hconv δ hδ
  rw [eventually_atTop]
  refine ⟨k0, fun k hk x hx => ?_⟩
  have h0b := hk0 k hk 0 (Nat.zero_le 1) x hx
  rw [mapDerivNorm, norm_iteratedFDeriv_zero] at h0b
  have h1b := hk0 k hk 1 le_rfl x hx
  rw [mapDerivNorm, norm_iteratedFDeriv_one, fderiv_fun_sub (hdiff k x hx) (hdiffInf x hx)] at h1b
  have hest := norm_raisedKoszulOp_sub_le hc (hcK x hx) hδ.le hM h0b (min_le_left _ _) h1b
    ((hM₀ x hx).trans (le_max_left _ _))
  rw [dist_comm (raisedKoszulOp (bInf x) (fderiv ℝ bInf x))
    (raisedKoszulOp (b k x) (fderiv ℝ (b k) x)), dist_eq_norm (raisedKoszulOp (b k x)
    (fderiv ℝ (b k) x)) (raisedKoszulOp (bInf x) (fderiv ℝ bInf x))]
  calc ‖raisedKoszulOp (b k x) (fderiv ℝ (b k) x) - raisedKoszulOp (bInf x) (fderiv ℝ bInf x)‖
      ≤ C₁ * δ := hest
    _ ≤ C₁ * (ε / (2 * C₁)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hC₁.le
    _ = ε / 2 := by field_simp
    _ < ε := half_lt_self hε

/-- **CM4.a, coefficient form.** Geodesics of `C¹` chart metrics `b i` converging in `C¹` on a compact
`K` (coercive limit), with values in `K` and bounded speed, have a `C¹`-convergent subsequence whose
limit solves the geodesic equation of `bInf`. -/
theorem exists_C1_subseq_limit_of_metric_tendsto
    {U K : Set F} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (b : ℕ → F → F →L[ℝ] F →L[ℝ] ℝ) (bInf : F → F →L[ℝ] F →L[ℝ] ℝ)
    (hb : ∀ i, ContDiffOn ℝ 1 (b i) U) (hbInf : ContDiffOn ℝ 1 bInf U)
    (hco : ∀ x ∈ K, IsCoercive (bInf x)) (hconv : MapCPConvergenceOn K 1 b bInf)
    {T L : ℝ} (γ γ' : ℕ → ℝ → F)
    (hmaps : ∀ i, ∀ t ∈ Icc 0 T, γ i t ∈ K)
    (hvel : ∀ i, ∀ t ∈ Icc 0 T, HasDerivWithinAt (γ i) (γ' i t) (Icc 0 T) t)
    (hacc : ∀ i, ∀ t ∈ Icc 0 T, HasDerivWithinAt (γ' i)
      (-(raisedKoszulOp (b i (γ i t)) (fderiv ℝ (b i) (γ i t)) (γ' i t) (γ' i t))) (Icc 0 T) t)
    (hbound : ∀ i, ∀ t ∈ Icc 0 T, ‖γ' i t‖ ≤ L) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c c' : ℝ → F,
      TendstoUniformlyOn (fun i => γ (φ i)) c atTop (Icc 0 T) ∧
      TendstoUniformlyOn (fun i => γ' (φ i)) c' atTop (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, c t ∈ K ∧ HasDerivWithinAt c (c' t) (Icc 0 T) t ∧
        HasDerivWithinAt c'
          (-(raisedKoszulOp (bInf (c t)) (fderiv ℝ bInf (c t)) (c' t) (c' t))) (Icc 0 T) t :=
  exists_C1_subseq_limit_of_christoffel_tendsto hK
    (fun i x => raisedKoszulOp (b i x) (fderiv ℝ (b i) x))
    (fun x => raisedKoszulOp (bInf x) (fderiv ℝ bInf x))
    (continuousOn_raisedKoszulOp_fderiv hU hKU hbInf hco)
    (tendstoUniformlyOn_raisedKoszulOp_of_mapCPConvergenceOn hU hK hKU b bInf hb hbInf hco hconv)
    γ γ' hmaps hvel hacc hbound

/-- **CM4.c, coefficient form.** Let `C¹` chart metrics `b i` converge in `C¹` on compact subsets of
an open `U` to a `C²` coefficient field `bInf`, coercive on `U`. A geodesic `(c, c')` of `bInf` on
`[t₀, t₁]` inside `U` is the uniform limit, with velocities, of every sequence of `b i`-geodesics whose
initial data converge to its own. -/
theorem tendstoUniformlyOn_of_metric_tendsto
    {U : Set F} (hU : IsOpen U)
    (b : ℕ → F → F →L[ℝ] F →L[ℝ] ℝ) (bInf : F → F →L[ℝ] F →L[ℝ] ℝ)
    (hb : ∀ i, ContDiffOn ℝ 1 (b i) U) (hbInf : ContDiffOn ℝ 2 bInf U)
    (hco : ∀ x ∈ U, IsCoercive (bInf x))
    (hconv : ∀ C : Set F, IsCompact C → C ⊆ U → MapCPConvergenceOn C 1 b bInf)
    {t₀ t₁ : ℝ} (c c' : ℝ → F) (hcU : ∀ t ∈ Icc t₀ t₁, c t ∈ U)
    (hc : ∀ t ∈ Icc t₀ t₁, HasDerivWithinAt c (c' t) (Icc t₀ t₁) t)
    (hc' : ∀ t ∈ Icc t₀ t₁, HasDerivWithinAt c'
      (-(raisedKoszulOp (bInf (c t)) (fderiv ℝ bInf (c t)) (c' t) (c' t))) (Icc t₀ t₁) t)
    (γ γ' : ℕ → ℝ → F)
    (hvel : ∀ i, ∀ t ∈ Icc t₀ t₁, HasDerivWithinAt (γ i) (γ' i t) (Icc t₀ t₁) t)
    (hacc : ∀ i, ∀ t ∈ Icc t₀ t₁, HasDerivWithinAt (γ' i)
      (-(raisedKoszulOp (b i (γ i t)) (fderiv ℝ (b i) (γ i t)) (γ' i t) (γ' i t))) (Icc t₀ t₁) t)
    (h0 : Tendsto (fun i => γ i t₀) atTop (𝓝 (c t₀)))
    (h0' : Tendsto (fun i => γ' i t₀) atTop (𝓝 (c' t₀))) :
    TendstoUniformlyOn γ c atTop (Icc t₀ t₁) ∧ TendstoUniformlyOn γ' c' atTop (Icc t₀ t₁) := by
  have hbInf1 : ContDiffOn ℝ 1 bInf U := hbInf.of_le (by norm_num)
  have hΓ : ContDiffOn ℝ 1 (fun x => raisedKoszulOp (bInf x) (fderiv ℝ bInf x)) U :=
    raisedOp_contDiffOn_succ hU (hbInf.of_le (by norm_num)) hco
  exact tendstoUniformlyOn_of_christoffel_tendsto hU
    (fun i x => raisedKoszulOp (b i x) (fderiv ℝ (b i) x))
    (fun x => raisedKoszulOp (bInf x) (fderiv ℝ bInf x)) hΓ
    (fun C hC hCU => tendstoUniformlyOn_raisedKoszulOp_of_mapCPConvergenceOn hU hC hCU b bInf hb
      hbInf1 (fun x hx => hco x (hCU hx)) (hconv C hC hCU))
    c c' hcU hc hc' γ γ' hvel hacc h0 h0'

end DifferentialGeometry.Analysis.ODE.GeodesicLimits
