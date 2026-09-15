import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Rademacher

open MeasureTheory Filter Metric ContinuousLinearMap
open scoped Topology ContDiff Convolution NNReal

namespace ContDiffBump

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem lipschitz_normed_convolution (φ : ContDiffBump (0 : E)) {f : E → F} {C : ℝ≥0}
    (hf : LipschitzWith C f) : LipschitzWith C (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) := by
  have hi (x : E) : Integrable (fun t => φ.normed μ t • f (x - t)) μ :=
    φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right (lsmul ℝ ℝ)
      φ.integrable_normed.locallyIntegrable hf.continuous x
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [convolution_def, lsmul_apply, dist_eq_norm]
  rw [← integral_sub (hi x) (hi y)]
  calc
    ‖∫ t, φ.normed μ t • f (x - t) - φ.normed μ t • f (y - t) ∂μ‖ ≤
        ∫ t, φ.normed μ t * ((C : ℝ) * ‖x - y‖) ∂μ := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _)
      filter_upwards [] with t
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed t)]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed t)
      simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hf.dist_le_mul (x - t) (y - t)
    _ = (C : ℝ) * ‖x - y‖ := by rw [integral_mul_const, φ.integral_normed, one_mul]

theorem dist_normed_convolution_le_mul [CompleteSpace F] (φ : ContDiffBump (0 : E))
    {f : E → F} {C : ℝ≥0} (hf : LipschitzWith C f) (x : E) :
    dist ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x) (f x) ≤ (C : ℝ) * φ.rOut := by
  apply φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
  intro y hy
  exact (hf.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left (mem_ball.mp hy).le C.coe_nonneg)

theorem convolution_tendstoUniformly_of_lipschitz [CompleteSpace F]
    {ι : Type*} {φ : ι → ContDiffBump (0 : E)} {l : Filter ι} {f : E → F} {C : ℝ≥0}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) (hf : LipschitzWith C f) :
    TendstoUniformly (fun i => (φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f) f l := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have h : Tendsto (fun i => (C : ℝ) * (φ i).rOut) l (𝓝 0) := by
    simpa using hφ.const_mul (C : ℝ)
  filter_upwards [h.eventually (gt_mem_nhds hε)] with i hi x
  exact (dist_comm _ _).trans_le ((φ i).dist_normed_convolution_le_mul hf x) |>.trans_lt hi

end ContDiffBump

namespace LipschitzWith

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_contDiff_lipschitz_tendstoUniformly {f : E → F} {C : ℝ≥0}
    (hf : LipschitzWith C f) :
    ∃ g : ℕ → E → F, (∀ n, ContDiff ℝ ∞ (g n)) ∧
      (∀ n, LipschitzWith C (g n)) ∧ TendstoUniformly g f atTop := by
  borelize E
  let φ (n : ℕ) : ContDiffBump (0 : E) :=
    ⟨(1 / ((n : ℝ) + 1)) / 2, 1 / ((n : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  let μ : Measure E := Measure.addHaar
  refine ⟨fun n => (φ n).normed μ ⋆[lsmul ℝ ℝ, μ] f, ?_, ?_, ?_⟩
  · intro n
    exact (φ n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (φ n).contDiff_normed hf.continuous.locallyIntegrable
  · exact fun n => (φ n).lipschitz_normed_convolution hf
  · exact ContDiffBump.convolution_tendstoUniformly_of_lipschitz
      tendsto_one_div_add_atTop_nhds_zero_nat hf

end LipschitzWith

namespace ContDiffBump

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem hasFDerivAt_normed_convolution_of_lipschitz
    (φ : ContDiffBump (0 : E)) {f : E → F} {C : ℝ≥0}
    (hf : LipschitzWith C f) (x : E) :
    HasFDerivAt (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f)
      ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] fderiv ℝ f) x) x := by
  have hi (y : E) : Integrable (fun t => φ.normed μ t • f (y - t)) μ :=
    φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right (lsmul ℝ ℝ)
      φ.integrable_normed.locallyIntegrable hf.continuous y
  have hm : AEStronglyMeasurable (fun t => φ.normed μ t • fderiv ℝ f (x - t)) μ := by
    exact φ.continuous_normed.aestronglyMeasurable.smul
      ((measurable_fderiv ℝ f).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hd : ∀ᵐ t ∂μ, DifferentiableAt ℝ f (x - t) := by
    exact (μ.measurePreserving_sub_left x).quasiMeasurePreserving.ae (hf.ae_differentiableAt (μ := μ))
  have h := hasFDerivAt_integral_of_dominated_loc_of_lip'
    (F := fun y t => φ.normed μ t • f (y - t))
    (F' := fun t => φ.normed μ t • fderiv ℝ f (x - t))
    (bound := fun t => φ.normed μ t * (C : ℝ))
    (s := Set.univ) Filter.univ_mem (fun y _ => (hi y).aestronglyMeasurable) (hi x) hm
    (by
      filter_upwards [] with t y _
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed t)]
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed t)
      simpa only [sub_sub_sub_cancel_right] using hf.norm_sub_le (y - t) (x - t))
    (φ.integrable_normed.mul_const (C : ℝ))
    (by
      filter_upwards [hd] with t ht
      simpa [Function.comp_def, Pi.smul_def, Pi.sub_def] using (ht.hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub (hasFDerivAt_const t x))).const_smul (φ.normed μ t))
  exact h.2

end ContDiffBump

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {μ : Measure E}

omit [FiniteDimensional ℝ F] in
theorem LipschitzWith.locallyIntegrable_fderiv [CompleteSpace F] [SecondCountableTopology F]
    [IsLocallyFiniteMeasure μ]
    {f : E → F} {C : ℝ≥0} (hf : LipschitzWith C f) :
    LocallyIntegrable (fderiv ℝ f) μ := by
  apply locallyIntegrable_iff.mpr
  intro k hk
  exact (integrableOn_const (C := (C : ℝ)) hk.measure_ne_top).mono'
    (measurable_fderiv ℝ f).aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => norm_fderiv_le_of_lipschitz ℝ hf)

namespace ContDiffBump

variable [μ.IsAddHaarMeasure]

theorem ae_fderiv_normed_convolution_tendsto_of_lipschitz
    {ι : Type*} {φ : ι → ContDiffBump (0 : E)} {l : Filter ι} {K : ℝ}
    {f : E → F} {C : ℝ≥0}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hφ_ratio : ∀ᶠ i in l, (φ i).rOut ≤ K * (φ i).rIn)
    (hf : LipschitzWith C f) :
    ∀ᵐ x ∂μ, Tendsto (fun i => fderiv ℝ ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f) x)
      l (𝓝 (fderiv ℝ f x)) := by
  filter_upwards [ae_convolution_tendsto_right_of_locallyIntegrable hφ hφ_ratio
    (hf.locallyIntegrable_fderiv (μ := μ))] with x hx
  exact hx.congr (fun i => ((φ i).hasFDerivAt_normed_convolution_of_lipschitz hf x).fderiv.symm)

theorem integral_norm_sub_fderiv_normed_convolution_sq_tendsto_of_lipschitz
    {ι : Type*} {φ : ι → ContDiffBump (0 : E)} {l : Filter ι} [l.IsCountablyGenerated]
    {K : ℝ} {f : E → F} {C : ℝ≥0} {s : Set E}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hφ_ratio : ∀ᶠ i in l, (φ i).rOut ≤ K * (φ i).rIn)
    (hf : LipschitzWith C f) (hs : μ s ≠ ⊤) :
    Tendsto (fun i => ∫ x in s,
      ‖fderiv ℝ ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f) x - fderiv ℝ f x‖ ^ 2 ∂μ)
      l (𝓝 0) := by
  have hlim := ae_fderiv_normed_convolution_tendsto_of_lipschitz (μ := μ) hφ hφ_ratio hf
  have hbound (i : ι) (x : E) :
      ‖fderiv ℝ ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f) x - fderiv ℝ f x‖ ≤ 2 * C := by
    calc
      ‖fderiv ℝ ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f) x - fderiv ℝ f x‖ ≤
          ‖fderiv ℝ ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f) x‖ + ‖fderiv ℝ f x‖ := norm_sub_le _ _
      _ ≤ (C : ℝ) + C := add_le_add
        (norm_fderiv_le_of_lipschitz ℝ ((φ i).lipschitz_normed_convolution hf))
        (norm_fderiv_le_of_lipschitz ℝ hf)
      _ = 2 * C := by ring
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := μ.restrict s) (f := fun _ : E => (0 : ℝ)) (fun _ : E => (2 * (C : ℝ)) ^ 2)
    (Filter.Eventually.of_forall fun i =>
      (((measurable_fderiv ℝ ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f)).sub
        (measurable_fderiv ℝ f)).norm.pow_const 2).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun i => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound i x) 2)
    (integrableOn_const hs)
    (by
      filter_upwards [ae_restrict_of_ae hlim] with x hx
      simpa using ((hx.sub_const (fderiv ℝ f x)).norm.pow 2))
  simpa using h

end ContDiffBump

end

namespace LipschitzWith

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem exists_contDiff_lipschitz_tendstoUniformly_fderiv
    {f : E → F} {C : ℝ≥0} (hf : LipschitzWith C f) :
    ∃ g : ℕ → E → F, (∀ n, ContDiff ℝ ∞ (g n)) ∧
      (∀ n, LipschitzWith C (g n)) ∧ TendstoUniformly g f atTop ∧
      (∀ n x, ‖g n x - f x‖ ≤ (C : ℝ) / ((n : ℝ) + 1)) ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => fderiv ℝ (g n) x) atTop (𝓝 (fderiv ℝ f x))) ∧
      ∀ s : Set E, μ s ≠ ⊤ →
        Tendsto (fun n => ∫ x in s, ‖fderiv ℝ (g n) x - fderiv ℝ f x‖ ^ 2 ∂μ)
          atTop (𝓝 0) := by
  let φ (n : ℕ) : ContDiffBump (0 : E) :=
    ⟨(1 / ((n : ℝ) + 1)) / 2, 1 / ((n : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hφ_ratio : ∀ᶠ n in atTop, (φ n).rOut ≤ 2 * (φ n).rIn := by
    filter_upwards [] with n
    dsimp [φ]
    linarith
  refine ⟨fun n => (φ n).normed μ ⋆[lsmul ℝ ℝ, μ] f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (φ n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (φ n).contDiff_normed hf.continuous.locallyIntegrable
  · exact fun n => (φ n).lipschitz_normed_convolution hf
  · exact ContDiffBump.convolution_tendstoUniformly_of_lipschitz hφ hf
  · intro n x
    have hrad : (φ n).rOut = 1 / ((n : ℝ) + 1) := rfl
    simpa only [dist_eq_norm, hrad, mul_one_div] using
      (φ n).dist_normed_convolution_le_mul (μ := μ) hf x
  · exact ContDiffBump.ae_fderiv_normed_convolution_tendsto_of_lipschitz hφ hφ_ratio hf
  · intro s hs
    exact ContDiffBump.integral_norm_sub_fderiv_normed_convolution_sq_tendsto_of_lipschitz
      hφ hφ_ratio hf hs

end LipschitzWith
