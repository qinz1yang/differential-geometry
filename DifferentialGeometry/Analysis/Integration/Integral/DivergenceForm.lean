import DifferentialGeometry.Analysis.Calculus.LipschitzConvolution
import DifferentialGeometry.Analysis.Integration.Integral.LocalIntegrationByParts

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

theorem integral_mul_add_fderiv_nonneg_of_contDiff_test
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {Ω : Set E} (hΩ : IsOpen Ω) {b : E → ℝ} {V : E → E}
    (hb : LocallyIntegrableOn b Ω μ) (hV : LocallyIntegrableOn V Ω μ)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∀ x, 0 ≤ ψ x) → 0 ≤ ∫ x, b x * ψ x + fderiv ℝ ψ x (V x) ∂μ)
    {φ : E → ℝ} (hφ : LocallyLipschitzOn Ω φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) (hφ0 : ∀ x, 0 ≤ φ x) :
    0 ≤ ∫ x, b x * φ x + fderiv ℝ φ x (V x) ∂μ := by
  obtain ⟨C, hφL⟩ := hφ.exists_lipschitzWith_of_hasCompactSupport hΩ hφc hφs
  obtain ⟨K, hK, hKΩ, hφK, g, hgs, hgL, hgK, hg0, hgu, hgd⟩ :=
    hφL.exists_contDiff_nonneg_tsupport_subset_tendstoUniformly_fderiv (μ := μ) hφ0 hφc hΩ hφs
  have hbK := hb.integrableOn_compact_subset hKΩ hK
  have hVK := hV.integrableOn_compact_subset hKΩ hK
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hφL.continuous.continuousOn
  have hgnorm : ∀ᶠ n in atTop, ∀ x ∈ K, ‖g n x‖ ≤ max B 0 + 1 := by
    filter_upwards [(Metric.tendstoUniformly_iff.mp hgu) 1 zero_lt_one] with n hn x hx
    calc
      ‖g n x‖ ≤ ‖g n x - φ x‖ + ‖φ x‖ := norm_le_norm_sub_add _ _
      _ ≤ 1 + B := add_le_add (by simpa only [dist_eq_norm, norm_sub_rev] using (hn x).le) (hB x hx)
      _ ≤ max B 0 + 1 := by linarith [le_max_left B 0]
  have hzero {ψ : E → ℝ} (hψ : tsupport ψ ⊆ K) :
      (∫ x in K, b x * ψ x + fderiv ℝ ψ x (V x) ∂μ) =
        ∫ x, b x * ψ x + fderiv ℝ ψ x (V x) ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hψ h)),
      fderiv_of_notMem_tsupport ℝ (fun h => hx (hψ h))]
    simp
  have hconv : Tendsto (fun n => ∫ x in K, b x * g n x + fderiv ℝ (g n) x (V x) ∂μ)
      atTop (𝓝 (∫ x in K, b x * φ x + fderiv ℝ φ x (V x) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun x => ‖b x‖ * (max B 0 + 1) + (C : ℝ) * ‖V x‖)
    · filter_upwards [] with n
      exact (hbK.aestronglyMeasurable.mul (hgs n).continuous.aestronglyMeasurable).add
        ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
          ((measurable_fderiv ℝ (g n)).aestronglyMeasurable.prodMk hVK.aestronglyMeasurable))
    · filter_upwards [hgnorm] with n hn
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      calc
        ‖b x * g n x + fderiv ℝ (g n) x (V x)‖ ≤
            ‖b x * g n x‖ + ‖fderiv ℝ (g n) x (V x)‖ := norm_add_le _ _
        _ ≤ ‖b x‖ * (max B 0 + 1) + (C : ℝ) * ‖V x‖ := by
          rw [norm_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left (hn x hx) (norm_nonneg _))
            (((fderiv ℝ (g n) x).le_opNorm (V x)).trans
              (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hgL n)) (norm_nonneg _)))
    · exact (hbK.norm.mul_const _).add (hVK.norm.const_mul _)
    · filter_upwards [ae_restrict_of_ae hgd] with x hx
      exact ((hgu.tendsto_at x).const_mul (b x)).add
        (((ContinuousLinearMap.apply ℝ ℝ (V x)).continuous.tendsto _).comp hx)
  rw [← hzero hφK]
  apply ge_of_tendsto hconv
  filter_upwards [] with n
  rw [hzero (hgK n)]
  exact hweak (g n) (hgs n) (hK.of_isClosed_subset (isClosed_tsupport (g n)) (hgK n))
    ((hgK n).trans hKΩ) (hg0 n)

theorem sum_integral_mul_fderiv_nonneg_of_contDiff_test
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] [Fintype ι]
    {Ω : Set E} (hΩ : IsOpen Ω) {b : ι → E → ℝ}
    (hb : ∀ i, LocallyIntegrableOn (b i) Ω μ) (v : ι → E)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → (∀ x, 0 ≤ ψ x) → 0 ≤ ∑ i, ∫ x, b i x * fderiv ℝ ψ x (v i) ∂μ)
    {φ : E → ℝ} (hφ : LocallyLipschitzOn Ω φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) (hφ0 : ∀ x, 0 ≤ φ x) :
    0 ≤ ∑ i, ∫ x, b i x * fderiv ℝ φ x (v i) ∂μ := by
  let V : E → E := fun x => ∑ i, b i x • v i
  have hV : LocallyIntegrableOn V Ω μ := by
    apply (locallyIntegrableOn_iff hΩ.isLocallyClosed).mpr
    intro K hKΩ hK
    exact integrable_finsetSum Finset.univ fun i _ =>
      ((hb i).integrableOn_compact_subset hKΩ hK).smul_const (v i)
  have heq {ψ : E → ℝ} (hψ : LocallyLipschitzOn Ω ψ)
      (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) :
      (∫ x, fderiv ℝ ψ x (V x) ∂μ) = ∑ i, ∫ x, b i x * fderiv ℝ ψ x (v i) ∂μ := by
    simp only [V, map_sum, map_smul, smul_eq_mul]
    exact integral_finsetSum Finset.univ fun i _ =>
      (hb i).integrable_mul_fderiv_of_hasCompactSupport hΩ hψ hψc hψs (v i)
  have h := integral_mul_add_fderiv_nonneg_of_contDiff_test hΩ
    (b := fun _ => 0) (continuousOn_const.locallyIntegrableOn hΩ.measurableSet) hV
    (fun ψ hψ hψc hψs hψ0 => by
      simp only [zero_mul, zero_add]
      rw [heq (hψ.of_le (by norm_num)).locallyLipschitz.locallyLipschitzOn hψc hψs]
      exact hweak ψ hψ hψc hψs hψ0) hφ hφc hφs hφ0
  simpa only [zero_mul, zero_add, heq hφ hφc hφs] using h

private theorem integral_mul_fderiv_eq_neg_lineDeriv_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {u ψ : E → ℝ} {Ω : Set E} (hu : LocallyLipschitzOn Ω u)
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) (v : E) :
    (∫ x, u x * fderiv ℝ ψ x v ∂μ) = -∫ x, lineDeriv ℝ u x v * ψ x ∂μ := by
  have h := integral_mul_fderiv_eq_neg_lineDeriv_mul_of_locallyLipschitzOn (μ := μ) hu hψ hψc hψs v
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero] at h
  · exact h
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (f := ψ) (fun h => hx (hψs h)), mul_zero]
  · intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hψs h)), zero_apply, mul_zero]

theorem integral_second_order_adjoint_eq_divergence
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    [Fintype ι] [Fintype κ] {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu : LocallyLipschitzOn Ω u)
    {A : ι → κ → E → ℝ} {b : κ → E → ℝ}
    (hA : ∀ i j, ContDiffOn ℝ 2 (A i j) Ω)
    (v : ι → E) (w : κ → E)
    (hdiv : ∀ x ∈ Ω, ∀ j, (∑ i, fderiv ℝ (A i j) x (v i)) + b j x = 0)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) :
    -(∑ i, ∑ j, ∫ x, u x * fderiv ℝ (fderiv ℝ (fun y => A i j y * φ y))
      x (w j) (v i) ∂μ) -
      (∑ j, ∫ x, u x * fderiv ℝ (fun y => b j y * φ y) x (w j) ∂μ) =
        ∑ i, ∑ j, ∫ x, A i j x * lineDeriv ℝ u x (w j) * fderiv ℝ φ x (v i) ∂μ := by
  have htestA (i : ι) (j : κ) : ContDiff ℝ 2 (fun x => A i j x * φ x) :=
    ((hA i j).mul hφ.contDiffOn).contDiff_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hφs)
  let ψ : ι → κ → E → ℝ := fun i j x => fderiv ℝ (fun y => A i j y * φ y) x (v i)
  have hψ (i : ι) (j : κ) : ContDiff ℝ 1 (ψ i j) :=
    ((htestA i j).fderiv_right (by norm_num)).clm_apply contDiff_const
  have hψc (i : ι) (j : κ) : HasCompactSupport (ψ i j) := hφc.mul_left.fderiv_apply ℝ (v i)
  have hψs (i : ι) (j : κ) : tsupport (ψ i j) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ (v i)).trans (tsupport_mul_subset_right.trans hφs)
  have hb (j : κ) : ContDiffOn ℝ 1 (b j) Ω := by
    have h : ContDiffOn ℝ 1 (fun x => -(∑ i, fderiv ℝ (A i j) x (v i))) Ω :=
      (ContDiffOn.sum fun i _ => ((hA i j).fderiv_of_isOpen hΩ (by norm_num)).clm_apply
        contDiffOn_const).neg
    apply h.congr
    intro x hx
    linarith only [hdiv x hx j]
  have htestb (j : κ) : ContDiff ℝ 1 (fun x => b j x * φ x) :=
    ((hb j).mul (hφ.of_le (by norm_num)).contDiffOn).contDiff_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hφs)
  have hsecond (i : ι) (j : κ) :
      (∫ x, u x * fderiv ℝ (fderiv ℝ (fun y => A i j y * φ y)) x (w j) (v i) ∂μ) =
        -∫ x, lineDeriv ℝ u x (w j) * ψ i j x ∂μ := by
    have h := integral_mul_fderiv_eq_neg_lineDeriv_mul (μ := μ) hu (hψ i j) (hψc i j) (hψs i j) (w j)
    have hd (x : E) : fderiv ℝ (ψ i j) x (w j) =
        fderiv ℝ (fderiv ℝ (fun y => A i j y * φ y)) x (w j) (v i) := by
      rw [fderiv_clm_apply (((htestA i j).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x)
        (differentiableAt_const (v i))]
      simp
    simpa only [hd] using h
  have hfirst (j : κ) : (∫ x, u x * fderiv ℝ (fun y => b j y * φ y) x (w j) ∂μ) =
      -∫ x, lineDeriv ℝ u x (w j) * (b j x * φ x) ∂μ :=
    integral_mul_fderiv_eq_neg_lineDeriv_mul hu (htestb j) hφc.mul_left
      (tsupport_mul_subset_right.trans hφs) (w j)
  have hψint (i : ι) (j : κ) : Integrable (fun x => lineDeriv ℝ u x (w j) * ψ i j x) μ :=
    hu.integrable_lineDeriv_mul_of_hasCompactSupport (hψ i j).continuous (hψc i j) (hψs i j) (w j)
  have hbint (j : κ) : Integrable (fun x => lineDeriv ℝ u x (w j) * (b j x * φ x)) μ :=
    hu.integrable_lineDeriv_mul_of_hasCompactSupport (htestb j).continuous hφc.mul_left
      (tsupport_mul_subset_right.trans hφs) (w j)
  have hfluxc (i : ι) (j : κ) : Continuous (fun x => A i j x * fderiv ℝ φ x (v i)) :=
    ((hA i j).continuousOn.mul ((hφ.continuous_fderiv (by norm_num)).clm_apply
      continuous_const).continuousOn).continuous_of_tsupport_subset hΩ
        (tsupport_mul_subset_right.trans ((tsupport_fderiv_apply_subset ℝ (v i)).trans hφs))
  have hfluxint (i : ι) (j : κ) :
      Integrable (fun x => lineDeriv ℝ u x (w j) * (A i j x * fderiv ℝ φ x (v i))) μ :=
    hu.integrable_lineDeriv_mul_of_hasCompactSupport (hfluxc i j)
      (hφc.fderiv_apply ℝ (v i)).mul_left
      (tsupport_mul_subset_right.trans ((tsupport_fderiv_apply_subset ℝ (v i)).trans hφs)) (w j)
  have hcancel (x : E) (j : κ) :
      (∑ i, ψ i j x) + b j x * φ x = ∑ i, A i j x * fderiv ℝ φ x (v i) := by
    by_cases hx : x ∈ Ω
    · have hexp (i : ι) : ψ i j x = fderiv ℝ (A i j) x (v i) * φ x +
          A i j x * fderiv ℝ φ x (v i) := by
        dsimp only [ψ]
        rw [fderiv_fun_mul (((hA i j).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by norm_num))
          (hφ.differentiable (by norm_num) x)]
        simp only [add_apply, smul_apply, smul_eq_mul]
        ring
      simp_rw [hexp, Finset.sum_add_distrib, ← Finset.sum_mul]
      have h := hdiv x hx j
      linear_combination φ x * h
    · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hφs h))
      have hdz : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ (fun h => hx (hφs h))
      have hψz (i : ι) : ψ i j x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hψs i j h))
      simp only [hψz, Finset.sum_const_zero, hz, hdz, zero_apply, mul_zero, add_zero]
  simp_rw [hsecond, hfirst, Finset.sum_neg_distrib, neg_neg, sub_neg_eq_add]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib, Finset.sum_comm (f := fun i j =>
    ∫ x, A i j x * lineDeriv ℝ u x (w j) * fderiv ℝ φ x (v i) ∂μ)]
  apply Finset.sum_congr rfl
  intro j _
  rw [← integral_finsetSum Finset.univ (fun i _ => hψint i j),
    ← integral_add (integrable_finsetSum Finset.univ (fun i _ => hψint i j)) (hbint j)]
  calc
    _ = ∫ x, ∑ i, lineDeriv ℝ u x (w j) * (A i j x * fderiv ℝ φ x (v i)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [← Finset.mul_sum, ← mul_add, hcancel]
    _ = ∑ i, ∫ x, lineDeriv ℝ u x (w j) * (A i j x * fderiv ℝ φ x (v i)) ∂μ :=
      integral_finsetSum Finset.univ (fun i _ => hfluxint i j)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      ext x
      ring

theorem integral_weighted_parabolic_adjoint_eq_divergence
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    [Fintype ι] [Fintype κ] {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu : LocallyLipschitzOn Ω u)
    {A : ι → κ → E → ℝ} {b : κ → E → ℝ} {ρ c : E → ℝ}
    (hA : ∀ i j, ContDiffOn ℝ 2 (fun x => A i j x * ρ x) Ω)
    (hρ : ContDiffOn ℝ 1 ρ Ω) (v : ι → E) (w : κ → E) (t : E)
    (hdiv : ∀ x ∈ Ω, ∀ j, (∑ i, fderiv ℝ (fun y => A i j y * ρ y) x (v i)) + b j x * ρ x = 0)
    (ht : ∀ x ∈ Ω, fderiv ℝ ρ x t = c x * ρ x)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) :
    -(∑ i, ∑ j, ∫ x, u x * fderiv ℝ (fderiv ℝ (fun y => A i j y * (ρ y * φ y)))
      x (w j) (v i) ∂μ) - (∫ x, u x * fderiv ℝ (fun y => ρ y * φ y) x t ∂μ) -
      (∑ j, ∫ x, u x * fderiv ℝ (fun y => b j y * (ρ y * φ y)) x (w j) ∂μ) +
      (∫ x, c x * u x * (ρ x * φ x) ∂μ) =
        (∑ i, ∑ j, ∫ x, (A i j x * ρ x) * lineDeriv ℝ u x (w j) * fderiv ℝ φ x (v i) ∂μ) -
          ∫ x, ρ x * u x * fderiv ℝ φ x t ∂μ := by
  have hs := integral_second_order_adjoint_eq_divergence (μ := μ) hΩ hu hA v w hdiv hφ hφc hφs
  simp only [mul_assoc] at hs
  have hdρ : ContinuousOn (fun x => fderiv ℝ ρ x t) Ω :=
    (hρ.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const
  have hi₁ : Integrable (fun x => ρ x * u x * fderiv ℝ φ x t) μ :=
    (((hρ.continuousOn.mul hu.continuousOn).mul
      ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).continuousOn).continuous_of_tsupport_subset
      hΩ (tsupport_mul_subset_right.trans ((tsupport_fderiv_apply_subset ℝ t).trans hφs))).integrable_of_hasCompactSupport
        (hφc.fderiv_apply ℝ t).mul_left
  have hi₂ : Integrable (fun x => u x * fderiv ℝ ρ x t * φ x) μ :=
    (((hu.continuousOn.mul hdρ).mul hφ.continuous.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hφs)).integrable_of_hasCompactSupport hφc.mul_left
  have hpotential (x : E) : c x * u x * (ρ x * φ x) = u x * fderiv ℝ ρ x t * φ x := by
    by_cases hx : x ∈ Ω
    · rw [ht x hx]
      ring
    · rw [image_eq_zero_of_notMem_tsupport (f := φ) (fun h => hx (hφs h))]
      ring
  have hproduct (x : E) : u x * fderiv ℝ (fun y => ρ y * φ y) x t =
      ρ x * u x * fderiv ℝ φ x t + u x * fderiv ℝ ρ x t * φ x := by
    by_cases hx : x ∈ Ω
    · rw [fderiv_fun_mul ((hρ.contDiffAt (hΩ.mem_nhds hx)).differentiableAt one_ne_zero)
        (hφ.differentiable (by norm_num) x)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    · rw [fderiv_of_notMem_tsupport ℝ (fun h => hx ((tsupport_mul_subset_right.trans hφs) h)),
        fderiv_of_notMem_tsupport ℝ (fun h => hx (hφs h)),
        image_eq_zero_of_notMem_tsupport (f := φ) (fun h => hx (hφs h))]
      simp
  have htime : (∫ x, u x * fderiv ℝ (fun y => ρ y * φ y) x t ∂μ) =
      (∫ x, ρ x * u x * fderiv ℝ φ x t ∂μ) + ∫ x, c x * u x * (ρ x * φ x) ∂μ := by
    simp_rw [hproduct, hpotential]
    exact integral_add hi₁ hi₂
  have hs' :
      -(∑ i, ∑ j, ∫ x, u x * fderiv ℝ (fderiv ℝ (fun y => A i j y * (ρ y * φ y)))
        x (w j) (v i) ∂μ) -
        (∑ j, ∫ x, u x * fderiv ℝ (fun y => b j y * (ρ y * φ y)) x (w j) ∂μ) =
          ∑ i, ∑ j, ∫ x, (A i j x * ρ x) * lineDeriv ℝ u x (w j) * fderiv ℝ φ x (v i) ∂μ := by
    simpa only [mul_assoc] using hs
  linarith only [hs', htime]

end DifferentialGeometry.Analysis
