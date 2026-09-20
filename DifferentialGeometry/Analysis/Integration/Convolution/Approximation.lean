import DifferentialGeometry.Analysis.Calculus.Taylor
import DifferentialGeometry.Analysis.Integration.Convolution.Derivatives
import DifferentialGeometry.Analysis.Integration.Integral.Asymptotics
import DifferentialGeometry.Analysis.Integration.Integral.LocalIntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology Convolution

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure V} [μ.IsAddHaarMeasure]

theorem ContDiffBump.tendstoUniformly_normed_convolution {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : V)}
    (hr : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    {u : V → F} (hu : UniformContinuous u) :
    TendstoUniformly (fun i => (φ i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) u l := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuous_iff.mp hu (ε / 2) (half_pos hε)
  filter_upwards [hr.eventually (gt_mem_nhds hδ)] with n hn
  intro x
  have hh : dist (((φ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) x) (u x) ≤ ε / 2 := by
    apply (φ n).dist_normed_convolution_le hu.continuous.aestronglyMeasurable
    intro y hy
    exact (hδu (lt_trans hy hn)).le
  rw [dist_comm]
  exact hh.trans_lt (half_lt_self hε)

private theorem fderiv_fderiv_convolution_rescale
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {κ u : E → ℝ} (hκ : ContDiff ℝ 2 κ) (hc : HasCompactSupport κ)
    (hu : LocallyIntegrable u μ) {r : ℝ} (hr : 0 < r) (x v w : E) :
    fderiv ℝ (fderiv ℝ ((fun z => (r ^ Module.finrank ℝ E)⁻¹ * κ (r⁻¹ • z)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u)) x v w =
      (r ^ 2)⁻¹ * ∫ z, fderiv ℝ (fderiv ℝ κ) z v w * u (x - r • z) ∂μ := by
  let A : E →L[ℝ] E := r⁻¹ • ContinuousLinearMap.id ℝ E
  let k : E → ℝ := fun z => κ (r⁻¹ • z)
  have hk : ContDiff ℝ 2 k := hκ.comp A.contDiff
  have hkc : HasCompactSupport k :=
    hc.comp_homeomorph (Homeomorph.smul (isUnit_iff_ne_zero.mpr (inv_ne_zero hr.ne')).unit)
  have hq : ContDiff ℝ 2 (fun z => (r ^ Module.finrank ℝ E)⁻¹ * k z) :=
    contDiff_const.mul hk
  have hqc : HasCompactSupport (fun z => (r ^ Module.finrank ℝ E)⁻¹ * k z) := hkc.mul_left
  rw [MeasureTheory.fderiv_fderiv_convolution_left_apply _ hqc hq hu]
  have hDD (z : E) :
      fderiv ℝ (fderiv ℝ (fun z => (r ^ Module.finrank ℝ E)⁻¹ * k z)) z v w =
        (r ^ Module.finrank ℝ E)⁻¹ * (r ^ 2)⁻¹ * fderiv ℝ (fderiv ℝ κ) (r⁻¹ • z) v w := by
    change fderiv ℝ (fderiv ℝ ((r ^ Module.finrank ℝ E)⁻¹ • k)) z v w = _
    rw [fderiv_const_smul_field, fderiv_const_smul_field]
    change (r ^ Module.finrank ℝ E)⁻¹ * fderiv ℝ (fderiv ℝ k) z v w = _
    have hh := DifferentialGeometry.Analysis.fderiv_fderiv_comp_affine A (0 : E) z v w
      (hκ.contDiffAt (x := 0 + A z))
    simp only [zero_add] at hh
    change fderiv ℝ (fderiv ℝ k) z v w = _ at hh
    rw [hh]
    simp only [A, smul_apply, ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
    ring
  simp_rw [hDD]
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hscale := μ.integral_comp_smul_of_nonneg
    (fun y => fderiv ℝ (fderiv ℝ κ) (r⁻¹ • y) v w * u (x - y)) r (hR := hr.le)
  simp only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul, smul_eq_mul] at hscale
  calc
    _ = ((r ^ Module.finrank ℝ E)⁻¹ * (r ^ 2)⁻¹) *
        ∫ y, fderiv ℝ (fderiv ℝ κ) (r⁻¹ • y) v w * u (x - y) ∂μ := by
      rw [← integral_const_mul]
      congr 1
      funext y
      ring
    _ = (r ^ 2)⁻¹ * ∫ z, fderiv ℝ (fderiv ℝ κ) z v w * u (x - r • z) ∂μ := by
      rw [hscale]
      ring


private theorem tendsto_fderiv_fderiv_convolution_rescale_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {κ u : E → ℝ} (hκ : ContDiff ℝ 2 κ) (hc : HasCompactSupport κ)
    (hu : LocallyIntegrable u μ) {x : E}
    (hR : (fun z => u (x - z)) =o[𝓝 (0 : E)] (fun z => ‖z‖ ^ 2)) (v w : E) :
    Tendsto (fun r : ℝ => fderiv ℝ (fderiv ℝ
      ((fun z => (r ^ Module.finrank ℝ E)⁻¹ * κ (r⁻¹ • z)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u)) x v w)
      (𝓝[>] 0) (𝓝 0) := by
  let K : E → ℝ := fun z => fderiv ℝ (fderiv ℝ κ) z v w
  have hKc : Continuous K :=
    (((hκ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).clm_apply continuous_const
  have hKs : HasCompactSupport K :=
    ((hc.fderiv ℝ).fderiv_apply ℝ v).comp_left (g := fun A : E →L[ℝ] ℝ => A w) rfl
  have hi : Integrable (fun z => ‖K z‖ * ‖z‖ ^ 2) μ :=
    (hKc.norm.mul (continuous_norm.pow 2)).integrable_of_hasCompactSupport hKs.norm.mul_right
  have h := hR.integral_smul_comp_smul
    (hKs.isCompact.isBounded.subset (subset_tsupport K)) hi
  have ht := h.tendsto_inv_smul_nhds_zero.mono_left
    (show 𝓝[>] 0 ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  change 0 < r at hr
  rw [fderiv_fderiv_convolution_rescale hκ hc hu hr]
  rfl


private theorem integral_hessian_mul_quadratic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {κ : E → ℝ} (hκ : ContDiff ℝ 2 κ) (hc : HasCompactSupport κ)
    (c : ℝ) (p : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : B.flip = B) (v w : E) :
    (∫ z, fderiv ℝ (fderiv ℝ κ) z v w * (c + p z + (1 / 2 : ℝ) * B z z) ∂μ) =
      B v w * ∫ z, κ z ∂μ := by
  let P : E → ℝ := fun z => c + p z + (1 / 2 : ℝ) * B z z
  obtain ⟨hP, hP0, hd⟩ := DifferentialGeometry.Analysis.second_order_polynomial_derivatives
    (0 : E) c p B hB
  simp only [sub_zero, smul_eq_mul] at hP hd
  change ContDiff ℝ (⊤ : ℕ∞) P at hP
  have hD : ContDiff ℝ 1 (fderiv ℝ P) := hP.fderiv_right
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have h := DifferentialGeometry.Analysis.integral_fderiv_fderiv_mul_eq_of_locallyLipschitzOn_fderiv
    (μ := μ) isOpen_univ (hP.differentiable (by simp)).differentiableOn
    hD.locallyLipschitz.locallyLipschitzOn hκ hc (subset_univ _) w v
  have hDD (z : E) : fderiv ℝ (fderiv ℝ P) z = B := (hd z).2
  simp_rw [Measure.restrict_univ, hDD, integral_const_mul] at h
  have hsym : B w v = B v w := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w) hB
  rw [hsym] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards with z
  exact mul_comm _ _


private theorem integrable_mul_comp_const_sub_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {K f : E → ℝ} (hK : Continuous K) (hc : HasCompactSupport K)
    (hf : LocallyIntegrable f μ) {r : ℝ} (hr : r ≠ 0) (x : E) :
    Integrable (fun z => K z * f (x - r • z)) μ := by
  have hkc : HasCompactSupport (fun y : E => K (r⁻¹ • y)) :=
    hc.comp_homeomorph (Homeomorph.smul (isUnit_iff_ne_zero.mpr (inv_ne_zero hr)).unit)
  have hkt : Continuous (fun y : E => K (r⁻¹ • y)) :=
    hK.comp (continuous_const.smul continuous_id)
  have h := (hkc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hkt hf x).comp_smul hr
  change Integrable (fun z => K (r⁻¹ • (r • z)) * f (x - r • z)) μ at h
  simpa only [smul_smul, inv_mul_cancel₀ hr, one_smul] using h

private theorem tendsto_fderiv_fderiv_convolution_rescale_apply_of_isLittleO
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {κ u : E → ℝ} (hκ : ContDiff ℝ 2 κ) (hc : HasCompactSupport κ)
    (hmass : ∫ z, κ z ∂μ = 1) (hu : LocallyIntegrable u μ) {x : E}
    {p : E →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : B.flip = B)
    (htaylor : (fun y => u y - u x - p (y - x) - (1 / 2 : ℝ) * B (y - x) (y - x))
      =o[𝓝 x] (fun y => ‖y - x‖ ^ 2)) (v w : E) :
    Tendsto (fun r : ℝ => fderiv ℝ (fderiv ℝ
      ((fun z => (r ^ Module.finrank ℝ E)⁻¹ * κ (r⁻¹ • z)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u)) x v w)
      (𝓝[>] 0) (𝓝 (B v w)) := by
  let P : E → ℝ := fun y => u x + p (y - x) + (1 / 2 : ℝ) * B (y - x) (y - x)
  have hP : ContDiff ℝ 2 P := by
    exact (contDiff_const.add (p.contDiff.comp (contDiff_id.sub contDiff_const))).add
      (contDiff_const.mul ((B.contDiff.comp (contDiff_id.sub contDiff_const)).clm_apply
        (contDiff_id.sub contDiff_const)))
  have hq : LocallyIntegrable (u - P) μ := hu.sub hP.continuous.locallyIntegrable
  have hR : (fun z => (u - P) (x - z)) =o[𝓝 (0 : E)] (fun z => ‖z‖ ^ 2) := by
    have htrans : Tendsto (fun z : E => x - z) (𝓝 0) (𝓝 x) := by
      have h : Continuous (fun z : E => x - z) := continuous_const.sub continuous_id
      simpa only [sub_zero] using h.tendsto (0 : E)
    convert htaylor.comp_tendsto htrans using 1
    · funext z
      simp only [Function.comp_apply, Pi.sub_apply, P]
      ring
    · funext z
      simp only [Function.comp_apply, show x - z - x = -z by abel, norm_neg]
  have hlim := (tendsto_fderiv_fderiv_convolution_rescale_zero hκ hc hq hR v w).add_const (B v w)
  simp only [zero_add] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  change 0 < r at hr
  rw [fderiv_fderiv_convolution_rescale hκ hc hq hr,
    fderiv_fderiv_convolution_rescale hκ hc hu hr]
  let K : E → ℝ := fun z => fderiv ℝ (fderiv ℝ κ) z v w
  have hKc : Continuous K :=
    (((hκ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).clm_apply continuous_const
  have hKs : HasCompactSupport K :=
    ((hc.fderiv ℝ).fderiv_apply ℝ v).comp_left (g := fun A : E →L[ℝ] ℝ => A w) rfl
  have hint (f : E → ℝ) (hf : LocallyIntegrable f μ) :
      Integrable (fun z => K z * f (x - r • z)) μ :=
    integrable_mul_comp_const_sub_smul hKc hKs hf hr.ne' x
  have hquad (z : E) : P (x - r • z) =
      u x + (-r • p) z + (1 / 2 : ℝ) * (r ^ 2 • B) z z := by
    simp only [P, show x - r • z - x = -(r • z) by abel,
      map_neg, map_smul, neg_apply, smul_apply, smul_eq_mul]
    ring
  have hBr : (r ^ 2 • B).flip = r ^ 2 • B := by
    rw [ContinuousLinearMap.flip_smul, hB]
  have hm := integral_hessian_mul_quadratic (μ := μ) hκ hc (u x) (-r • p) (r ^ 2 • B) hBr v w
  rw [hmass, mul_one] at hm
  simp only [smul_apply, smul_eq_mul] at hm
  have hPint : (∫ z, K z * P (x - r • z) ∂μ) = r ^ 2 * B v w := by
    simp_rw [hquad]
    exact hm
  change (r ^ 2)⁻¹ * (∫ z, K z * (u (x - r • z) - P (x - r • z)) ∂μ) + B v w =
    (r ^ 2)⁻¹ * ∫ z, K z * u (x - r • z) ∂μ
  simp_rw [mul_sub]
  rw [integral_sub (hint u hu) (hint P hP.continuous.locallyIntegrable), hPint]
  field_simp [hr.ne']
  ring


theorem DifferentialGeometry.Analysis.tendsto_fderiv_fderiv_convolution_rescale_of_isLittleO
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {κ u : E → ℝ} (hκ : ContDiff ℝ 2 κ) (hc : HasCompactSupport κ)
    (hmass : ∫ z, κ z ∂μ = 1) (hu : LocallyIntegrable u μ) {x : E}
    {p : E →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : B.flip = B)
    (htaylor : (fun y => u y - u x - p (y - x) - (1 / 2 : ℝ) * B (y - x) (y - x))
      =o[𝓝 x] (fun y => ‖y - x‖ ^ 2)) :
    Tendsto (fun r : ℝ => fderiv ℝ (fderiv ℝ
      ((fun z => (r ^ Module.finrank ℝ E)⁻¹ * κ (r⁻¹ • z)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u)) x)
      (𝓝[>] 0) (𝓝 B) := by
  let ev : (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] (E → E → ℝ) :=
    { toFun := fun A v w => A v w
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    intro A B h
    ext v w
    exact congrFun (congrFun h v) w
  apply (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hinj)).tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro v
  apply tendsto_pi_nhds.mpr
  intro w
  exact tendsto_fderiv_fderiv_convolution_rescale_apply_of_isLittleO hκ hc hmass hu hB htaylor v w
