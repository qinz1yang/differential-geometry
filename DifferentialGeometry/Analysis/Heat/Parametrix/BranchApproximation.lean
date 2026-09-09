import DifferentialGeometry.Analysis.Heat.Parametrix.BranchCutoff
import DifferentialGeometry.Analysis.Heat.Parametrix.Approximation
import DifferentialGeometry.Analysis.Calculus.ExponentialAsymptotics
import DifferentialGeometry.Geometry.Exponential.BranchEnergyBounds

noncomputable section

open Bundle Set MeasureTheory Filter
open scoped Manifold ContDiff Topology BigOperators

private theorem tendsto_integral_gaussian_mul_zero
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (e F : α → ℝ) (a : ℝ)
    (hF : Integrable F μ) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ y, F y ≠ 0 → c ≤ e y) :
    Tendsto (fun t : ℝ => ∫ y, t ^ a * Real.exp (-e y / t) * F y ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  have hlim := (Real.tendsto_rpow_mul_exp_neg_div_nhdsGT_zero a hc).mul_const
    (∫ y, ‖F y‖ ∂μ)
  simp only [zero_mul] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  have hbound : ∀ y, ‖t ^ a * Real.exp (-e y / t) * F y‖ ≤
      (t ^ a * Real.exp (-c / t)) * ‖F y‖ := by
    intro y
    by_cases hy : F y = 0
    · simp only [hy, mul_zero, norm_zero, le_refl]
    · rw [norm_mul, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg htpos.le _),
        Real.norm_of_nonneg (Real.exp_pos _).le]
      gcongr
      exact hgap y hy
  have h := norm_integral_le_of_norm_le (hF.norm.const_mul (t ^ a * Real.exp (-c / t)))
    (Eventually.of_forall hbound)
  rwa [integral_const_mul] at h

namespace DifferentialGeometry.Geometry.Riemannian.Exponential.ExpInvBranch

open DifferentialGeometry.Analysis.HeatEquation
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [T2Space (TangentBundle I M)] in
private theorem continuous_cutoff_coefficient_mul
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {χ f : M → ℝ} (hχ : Continuous χ) (hf : Continuous f)
    (hs : ∀ q ∈ tsupport χ, ∃ U : Set E, IsOpen U ∧ StarConvex ℝ 0 U ∧
      U ⊆ B.hom.source ∧ q ∈ B.dom ∩ B.inv ⁻¹' U) (k : ℕ) :
    Continuous (fun y => χ y * heatParametrixCoefficientInCoordinates g B.hom B.inv
      (fun v => paramDensity g B.hom v / paramDensity g B.hom 0) k y * f y) := by
  apply continuous_of_tsupport
  intro q hq
  have hqχ : q ∈ tsupport χ := tsupport_mul_subset_left (tsupport_mul_subset_left hq)
  obtain ⟨U, hU, hstar, hsub, hqU⟩ := hs q hqχ
  have hV : IsOpen (B.dom ∩ B.inv ⁻¹' U) :=
    B.inv_inf.continuousOn.isOpen_inter_preimage B.hom.open_target hU
  exact (hχ.continuousAt.mul
    (((B.contMDiffOn_heatParametrixCoefficientInCoordinates hU hstar hsub k q hqU).contMDiffAt
      (hV.mem_nhds hqU)).continuousAt)).mul hf.continuousAt

omit [T2Space (TangentBundle I M)] in
private theorem integrable_gaussian_mul
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {F : M → ℝ} (hF : Continuous F)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ B.dom) (t : ℝ) :
    Integrable (fun y => Real.exp (-branchEnergy g B y / (2 * t)) * F y)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hcont : Continuous (fun y => Real.exp (-branchEnergy g B y / (2 * t)) * F y) := by
    apply continuous_of_tsupport
    intro q hq
    have hqF : q ∈ tsupport F := tsupport_mul_subset_right hq
    have he := (contMDiffOn_branchEnergy B).continuousOn.continuousAt
      (B.hom.open_target.mem_nhds (hs hqF))
    exact (Real.continuous_exp.continuousAt.comp (he.neg.div_const (2 * t))).mul hF.continuousAt
  exact Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure (I := I) (M := M) g hcont hc.mul_left

omit [T2Space (TangentBundle I M)] in
private theorem tendsto_integral_norm_cutoff_zero
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) (N : ℕ) {χ f : M → ℝ}
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (hf : Continuous f)
    (hs : ∀ q ∈ tsupport χ, ∃ U : Set E, IsOpen U ∧ StarConvex ℝ 0 U ∧
      U ⊆ B.hom.source ∧ q ∈ B.dom ∩ B.inv ⁻¹' U) (hp : p ∉ tsupport χ) :
    Tendsto (fun t : ℝ => ∫ y, ‖B.cutoffHeatParametrix χ N t y * f y‖
      ∂riemannianVolumeMeasure (I := I) (M := M) g) (𝓝[>] 0) (𝓝 0) := by
  let a := heatParametrixCoefficientInCoordinates g B.hom B.inv
    (fun v => paramDensity g B.hom v / paramDensity g B.hom 0)
  let F : ℕ → M → ℝ := fun k y => χ y * a k y * f y
  have hcont (k : ℕ) : Continuous (F k) := continuous_cutoff_coefficient_mul B hχ hf hs k
  have hcF (k : ℕ) : HasCompactSupport (F k) := hc.mul_right.mul_right
  have hFB (k : ℕ) : tsupport (F k) ⊆ B.dom := by
    intro y hy
    obtain ⟨U, _, _, _, hyU⟩ := hs y (tsupport_mul_subset_left (tsupport_mul_subset_left hy))
    exact hyU.1
  obtain ⟨c, hcpos, hgap⟩ := exists_pos_le_branchEnergy_of_isCompact B hc
    (fun y hy => by obtain ⟨U, _, _, _, hyU⟩ := hs y hy; exact hyU.1) hp
  have hterm (k : ℕ) : Tendsto (fun t : ℝ => ∫ y,
      (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-branchEnergy g B y / (2 * t)) * t ^ k * ‖F k y‖
      ∂riemannianVolumeMeasure (I := I) (M := M) g) (𝓝[>] 0) (𝓝 0) := by
    have hi := Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure (I := I) (M := M) g (hcont k).norm (hcF k).norm
    have hh := tendsto_integral_gaussian_mul_zero (riemannianVolumeMeasure (I := I) (M := M) g)
      (fun y => branchEnergy g B y / 2) (fun y => ‖F k y‖) ((k : ℝ) - (Module.finrank ℝ E : ℝ) / 2)
      hi (half_pos hcpos) (fun y hy => by
        have hyχ : y ∈ tsupport χ := tsupport_mul_subset_left
          (tsupport_mul_subset_left (subset_closure (norm_ne_zero_iff.mp hy)))
        exact div_le_div_of_nonneg_right (hgap y hyχ) (by norm_num))
    have h := hh.const_mul ((4 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2))
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    rw [Real.mul_rpow (by positivity) (le_of_lt ht), Real.rpow_sub ht,
      Real.rpow_natCast]
    rw [show - (branchEnergy g B y / 2) / t = -branchEnergy g B y / (2 * t) by ring,
      neg_div, Real.rpow_neg (le_of_lt ht)]
    ring
  have hlim := tendsto_finsetSum (Finset.range (N + 1)) (fun k _ => hterm k)
  simp only [Finset.sum_const_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => norm_nonneg _) _ hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  have hi (k : ℕ) : Integrable (fun y =>
      (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-branchEnergy g B y / (2 * t)) * t ^ k * ‖F k y‖)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hi := (integrable_gaussian_mul B (hcont k).norm (hcF k).norm
      (by
        have heq : tsupport (fun y => ‖F k y‖) = tsupport (F k) := by
          apply congrArg closure
          ext y
          exact not_congr norm_eq_zero
        rw [heq]
        exact hFB k) t).const_mul
      ((4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) * t ^ k)
    convert hi using 1
    funext y
    ring
  rw [← integral_finsetSum _ (fun k _ => hi k)]
  apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
    (integrable_finsetSum _ (fun k _ => hi k))
  filter_upwards with y
  have heq : B.cutoffHeatParametrix χ N t y * f y =
      ∑ k ∈ Finset.range (N + 1),
        (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
          Real.exp (-branchEnergy g B y / (2 * t)) * t ^ k * F k y := by
    simp only [cutoffHeatParametrix, heatParametrix, Finset.mul_sum, Finset.sum_mul, F, a]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [heq]
  have hnonneg (k : ℕ) : 0 ≤
      (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-branchEnergy g B y / (2 * t)) * t ^ k := by
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le)
      (pow_nonneg (le_of_lt ht) _)
  simpa only [norm_mul, Real.norm_of_nonneg (hnonneg _)] using
    norm_sum_le (Finset.range (N + 1)) (fun k =>
      (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-branchEnergy g B y / (2 * t)) * t ^ k * F k y)

omit [T2Space (TangentBundle I M)] in
private theorem integrable_cutoff_mul
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {χ f : M → ℝ} (hχ : Continuous χ)
    (hc : HasCompactSupport χ) (hf : Continuous f)
    (hs : ∀ q ∈ tsupport χ, ∃ U : Set E, IsOpen U ∧ StarConvex ℝ 0 U ∧
      U ⊆ B.hom.source ∧ q ∈ B.dom ∩ B.inv ⁻¹' U) (N : ℕ) (t : ℝ) :
    Integrable (fun y => B.cutoffHeatParametrix χ N t y * f y)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hcont : Continuous (fun y => B.cutoffHeatParametrix χ N t y * f y) := by
    apply continuous_of_tsupport
    intro q hq
    have hqχ : q ∈ tsupport χ := tsupport_mul_subset_left (tsupport_mul_subset_left hq)
    obtain ⟨U, hU, hstar, hsub, hqU⟩ := hs q hqχ
    have hV : IsOpen (B.dom ∩ B.inv ⁻¹' U) :=
      B.inv_inf.continuousOn.isOpen_inter_preimage B.hom.open_target hU
    exact (hχ.continuousAt.mul
      (((B.contMDiffOn_heatParametrix hU hstar hsub N t q hqU).contMDiffAt
        (hV.mem_nhds hqU)).continuousAt)).mul hf.continuousAt
  exact Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure g hcont hc.mul_right.mul_right

private theorem tendsto_integral_cutoffHeatParametrix_mul_and_bound
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) (N : ℕ) (χ f : M → ℝ)
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (hχp : χ p = 1)
    (hs : ∀ q ∈ tsupport χ, ∃ U : Set E, IsOpen U ∧ StarConvex ℝ 0 U ∧
      U ⊆ B.hom.source ∧ q ∈ B.dom ∩ B.inv ⁻¹' U) (hf : Continuous f) :
    Tendsto (fun t : ℝ => ∫ y, B.cutoffHeatParametrix χ N t y * f y
      ∂riemannianVolumeMeasure (I := I) (M := M) g) (𝓝[>] 0) (𝓝 (f p)) ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ), ∫ y, ‖B.cutoffHeatParametrix χ N t y‖
        ∂riemannianVolumeMeasure (I := I) (M := M) g ≤ 3 := by
  let a := heatParametrixCoefficientInCoordinates g B.hom B.inv
    (fun v => paramDensity g B.hom v / paramDensity g B.hom 0)
  have hpχ : p ∈ tsupport χ := subset_closure (by simp [Function.mem_support, hχp])
  obtain ⟨U, _, hstar, hsub, hpU⟩ := hs p hpχ
  have hB0 : (0 : E) ∈ B.hom.source := hsub (by
    simpa only [zero_smul] using hstar.smul_mem hpU.2 (le_refl (0 : ℝ)) zero_le_one)
  have hinv : B.inv p = 0 := by
    have h := B.left_inv hB0
    simpa only [map_zero, expMapIntrinsic_zero] using h
  have hsmall : ∀ᶠ q in 𝓝 p, ‖B.inv q‖ < expMapC2Radius g p := by
    have hi := B.inv_inf.continuousOn.continuousAt (B.hom.open_target.mem_nhds hpU.1)
    have hball := hi (Metric.ball_mem_nhds (B.inv p) (expMapC2Radius_pos g p))
    have hball' : ∀ᶠ q in 𝓝 p, B.inv q ∈ Metric.ball (B.inv p) (expMapC2Radius g p) := hball
    simpa only [hinv, Metric.mem_ball, dist_zero_right] using hball'
  have heq : ∀ᶠ q in 𝓝 p, ∀ k ∈ Finset.range (N + 1), a k q = heatParametrixCoefficient g p k q :=
    (eventually_all_finset _).mpr (fun k _ => B.heatParametrixCoefficientInCoordinates_eventuallyEq hB0 k)
  have hnear : ∀ᶠ q in 𝓝 p, q ∈ B.dom ∧ ‖B.inv q‖ < expMapC2Radius g p ∧
      ∀ k ∈ Finset.range (N + 1), a k q = heatParametrixCoefficient g p k q := by
    filter_upwards [B.hom.open_target.mem_nhds hpU.1, hsmall, heq] with q hq hsm he
    exact ⟨hq, hsm, he⟩
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp hnear
  obtain ⟨ρ, hρ, hcρ, hρone, hsρ, _⟩ := DifferentialGeometry.Analysis.exists_mfd_bump
    (I := I) isCompact_singleton hV (singleton_subset_iff.mpr hpV)
  have hρp : ρ =ᶠ[𝓝 p] fun _ => 1 := by
    have h : ρ =ᶠ[𝓝 p] 1 := by simpa only [nhdsSet_singleton] using hρone
    filter_upwards [h] with y hy
    exact hy
  let χ₀ : M → ℝ := fun y => ρ y * χ y
  let χ₁ : M → ℝ := fun y => (1 - ρ y) * χ y
  have hs₀ : tsupport χ₀ ⊆ tsupport χ := tsupport_mul_subset_right
  have hs₁ : tsupport χ₁ ⊆ tsupport χ := tsupport_mul_subset_right
  have hχ₀ : Continuous χ₀ := hρ.continuous.mul hχ
  have hχ₁ : Continuous χ₁ := (continuous_const.sub hρ.continuous).mul hχ
  have hc₀ : HasCompactSupport χ₀ := hc.mul_left
  have hc₁ : HasCompactSupport χ₁ := hc.mul_left
  have h₀s : ∀ q ∈ tsupport χ₀, q ∈ V := fun q hq => hsρ (tsupport_mul_subset_left hq)
  have hlim₀ := DifferentialGeometry.Analysis.HeatEquation.tendsto_integral_cutoffHeatParametrix_mul
    B N χ₀ f hχ₀ hc₀ (by dsimp only [χ₀]; rw [hρp.eq_of_nhds, hχp, one_mul])
    (fun q hq => (hVsub (h₀s q hq)).1)
    (fun q hq => (hVsub (h₀s q hq)).2.1) hf
  have hcore (t : ℝ) (f : M → ℝ) : (fun y => B.cutoffHeatParametrix χ₀ N t y * f y) =
      fun y => DifferentialGeometry.Analysis.HeatEquation.cutoffHeatParametrix g B χ₀ N t y * f y := by
    funext y
    by_cases hy : y ∈ tsupport χ₀
    · have hcoef := (hVsub (h₀s y hy)).2.2
      have hsum : (∑ k ∈ Finset.range (N + 1), t ^ k * a k y) =
          ∑ k ∈ Finset.range (N + 1), t ^ k * heatParametrixCoefficient g p k y := by
        exact Finset.sum_congr rfl (fun k hk => congrArg (fun z => t ^ k * z) (hcoef k hk))
      change χ₀ y * ((_ * _) * (∑ k ∈ Finset.range (N + 1), t ^ k * a k y)) * f y = _
      rw [hsum]
      rfl
    · simp only [cutoffHeatParametrix, DifferentialGeometry.Analysis.HeatEquation.cutoffHeatParametrix,
        image_eq_zero_of_notMem_tsupport hy, zero_mul]
  have hlim₀' : Tendsto (fun t : ℝ => ∫ y, B.cutoffHeatParametrix χ₀ N t y * f y
      ∂riemannianVolumeMeasure (I := I) (M := M) g) (𝓝[>] 0) (𝓝 (f p)) := by
    simpa only [hcore] using hlim₀
  have hχ₁p : χ₁ =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [hρp] with y hy
    simp only [χ₁, hy, sub_self, zero_mul]
  have htail_norm := tendsto_integral_norm_cutoff_zero B N hχ₁ hc₁ hf
    (fun q hq => hs q (hs₁ hq)) (notMem_tsupport_iff_eventuallyEq.mpr hχ₁p)
  have htail : Tendsto (fun t : ℝ => ∫ y, B.cutoffHeatParametrix χ₁ N t y * f y
      ∂riemannianVolumeMeasure (I := I) (M := M) g) (𝓝[>] 0) (𝓝 0) :=
    squeeze_zero_norm' (Eventually.of_forall fun _ => norm_integral_le_integral_norm _) htail_norm
  constructor
  · have hlim := hlim₀'.add htail
    simp only [add_zero] at hlim
    apply hlim.congr'
    filter_upwards with t
    rw [← integral_add (integrable_cutoff_mul B hχ₀ hc₀ hf (fun q hq => hs q (hs₀ hq)) N t)
      (integrable_cutoff_mul B hχ₁ hc₁ hf (fun q hq => hs q (hs₁ hq)) N t)]
    apply integral_congr_ae
    filter_upwards with y
    dsimp only [cutoffHeatParametrix, χ₀, χ₁]
    ring
  · have hbound₀ := DifferentialGeometry.Analysis.HeatEquation.eventually_integral_norm_cutoffHeatParametrix_le_two
      B N χ₀ hχ₀ hc₀ (by dsimp only [χ₀]; rw [hρp.eq_of_nhds, hχp, one_mul])
      (fun q hq => (hVsub (h₀s q hq)).1)
      (fun q hq => (hVsub (h₀s q hq)).2.1)
    have htail₁ := tendsto_integral_norm_cutoff_zero B N hχ₁ hc₁ continuous_const
      (fun q hq => hs q (hs₁ hq)) (notMem_tsupport_iff_eventuallyEq.mpr hχ₁p)
        (f := fun _ => 1)
    simp only [mul_one] at htail₁
    have hbound₁ := htail₁.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hbound₀, hbound₁] with t ht₀ ht₁
    have heq₀ := hcore t (fun _ => 1)
    simp only [mul_one] at heq₀
    have hi₀ := (integrable_cutoff_mul B hχ₀ hc₀ continuous_const
      (fun q hq => hs q (hs₀ hq)) N t (f := fun _ => 1)).norm
    have hi₁ := (integrable_cutoff_mul B hχ₁ hc₁ continuous_const
      (fun q hq => hs q (hs₁ hq)) N t (f := fun _ => 1)).norm
    simp only [mul_one] at hi₀ hi₁
    have hle : (∫ y, ‖B.cutoffHeatParametrix χ N t y‖
        ∂riemannianVolumeMeasure (I := I) (M := M) g) ≤
        (∫ y, ‖B.cutoffHeatParametrix χ₀ N t y‖
          ∂riemannianVolumeMeasure (I := I) (M := M) g) +
        ∫ y, ‖B.cutoffHeatParametrix χ₁ N t y‖
          ∂riemannianVolumeMeasure (I := I) (M := M) g := by
      rw [← integral_add hi₀ hi₁]
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (hi₀.add hi₁)
      filter_upwards with y
      have heq : B.cutoffHeatParametrix χ N t y =
          B.cutoffHeatParametrix χ₀ N t y + B.cutoffHeatParametrix χ₁ N t y := by
        dsimp only [cutoffHeatParametrix, χ₀, χ₁]
        ring
      rw [heq]
      exact norm_add_le _ _
    have hbound : (∫ y, ‖B.cutoffHeatParametrix χ₀ N t y‖
        ∂riemannianVolumeMeasure (I := I) (M := M) g) ≤ 2 := by
      simpa only [heq₀] using ht₀
    linarith

theorem tendsto_integral_cutoffHeatParametrix_mul
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) (N : ℕ) (χ f : M → ℝ)
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (hχp : χ p = 1)
    (hs : ∀ q ∈ tsupport χ, ∃ U : Set E, IsOpen U ∧ StarConvex ℝ 0 U ∧
      U ⊆ B.hom.source ∧ q ∈ B.dom ∩ B.inv ⁻¹' U) (hf : Continuous f) :
    Tendsto (fun t : ℝ => ∫ y, B.cutoffHeatParametrix χ N t y * f y
      ∂riemannianVolumeMeasure (I := I) (M := M) g) (𝓝[>] 0) (𝓝 (f p)) :=
  (tendsto_integral_cutoffHeatParametrix_mul_and_bound B N χ f hχ hc hχp hs hf).1

theorem eventually_integral_norm_cutoffHeatParametrix_le_three
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) (N : ℕ) (χ : M → ℝ)
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (hχp : χ p = 1)
    (hs : ∀ q ∈ tsupport χ, ∃ U : Set E, IsOpen U ∧ StarConvex ℝ 0 U ∧
      U ⊆ B.hom.source ∧ q ∈ B.dom ∩ B.inv ⁻¹' U) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∫ y, ‖B.cutoffHeatParametrix χ N t y‖
      ∂riemannianVolumeMeasure (I := I) (M := M) g ≤ 3 :=
  (tendsto_integral_cutoffHeatParametrix_mul_and_bound B N χ (fun _ => 1)
    hχ hc hχp hs continuous_const).2

end DifferentialGeometry.Geometry.Riemannian.Exponential.ExpInvBranch
