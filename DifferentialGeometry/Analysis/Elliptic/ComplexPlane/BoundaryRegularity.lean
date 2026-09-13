import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.OddReflection
import DifferentialGeometry.Analysis.Elliptic.Euclidean.WeakLaplacianRegularity
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.BoundaryGradient

noncomputable section
open Set Filter MeasureTheory Metric InnerProductSpace
open scoped Topology ContDiff NNReal
namespace DifferentialGeometry.Analysis

theorem exists_holder_fderiv_oddReflection
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℂ → F} {K B : ℝ} (hc : HasCompactSupport f)
    (hf : ∀ z : ℂ, 0 < z.im → ContDiffAt ℝ 2 f z)
    (hg : ∀ z : ℂ, 0 < z.im → ‖f z‖ ≤ K * z.im)
    (hB : ∀ z : ℂ, 0 < z.im → ‖Laplacian.laplacian f z‖ ≤ B)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ≥0, ContDiff ℝ 1 (oddReflection f) ∧
      HolderWith C α (fderiv ℝ (oddReflection f)) := by
  have hfc : ContinuousOn f {z : ℂ | 0 < z.im} :=
    fun z hz => (hf z hz).continuousAt.continuousWithinAt
  have hΔ : ContinuousOn (Laplacian.laplacian f) {z : ℂ | 0 < z.im} :=
    fun z hz => (hf z hz).continuousAt_laplacian.continuousWithinAt
  apply exists_holder_fderiv_of_bounded_weak_laplacian
    (continuous_oddReflection_of_norm_le_mul_im hfc hg)
    (hasCompactSupport_oddReflection hc) (aestronglyMeasurable_oddReflection hΔ)
    (oddReflection_norm_le_of_bound hB) ?_ hα hα1
  intro φ hφ hcφ
  exact integral_laplacian_smul_oddReflection hφ hcφ hf hg hB



theorem exists_contDiff_one_extension_of_norm_laplacian_le
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : ℂ → F} {R β : ℝ} (hR : 0 < R) (hβ : 0 ≤ β)
    (hf : ContinuousOn f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hd : ∀ z : ℂ, ‖z‖ < R → 0 < z.im → ContDiffAt ℝ 2 f z)
    (hΔ : ∀ z : ℂ, ‖z‖ < R → 0 < z.im → ‖Laplacian.laplacian f z‖ ≤
      β * (fderiv ℝ f z).hilbertSchmidtInner (fderiv ℝ f z))
    (hzero : ∀ z : ℂ, ‖z‖ ≤ R → z.im = 0 → f z = 0)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ ρ > (0 : ℝ), ρ < R ∧ ∃ u : ℂ → F, ∃ C : ℝ≥0,
      ContDiff ℝ 1 u ∧ HolderWith C α (fderiv ℝ u) ∧
        EqOn u f {z : ℂ | ‖z‖ ≤ ρ ∧ 0 ≤ z.im} := by
  obtain ⟨r, hr, hrR, K, hLip⟩ :=
    exists_lipschitzOnWith_near_zero_of_norm_laplacian_le hR hβ hf hd hΔ hzero
  have hgrowth (z : ℂ) (hz : ‖z‖ ≤ r) (hi : 0 ≤ z.im) : ‖f z‖ ≤ K * z.im := by
    have hqn : ‖(z.re : ℂ)‖ ≤ ‖z‖ := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using Complex.abs_re_le_norm z
    have he : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    have hdist : ‖z - (z.re : ℂ)‖ = z.im := by
      rw [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hi]
    have hh := hLip.norm_sub_le ⟨hz, hi⟩ ⟨hqn.trans hz, by simp⟩
    rw [hzero (z.re : ℂ) (hqn.trans (hz.trans hrR.le)) (by simp), sub_zero, hdist] at hh
    exact hh
  have hDf (z : ℂ) (hz : ‖z‖ < r) (hi : 0 < z.im) : ‖fderiv ℝ f z‖ ≤ K := by
    apply norm_fderiv_le_of_lipschitzOn ℝ _ hLip
    have hopen : IsOpen {z : ℂ | ‖z‖ < r ∧ 0 < z.im} :=
      (isOpen_lt continuous_norm continuous_const).inter
        (isOpen_lt continuous_const Complex.continuous_im)
    exact mem_of_superset (hopen.mem_nhds ⟨hz, hi⟩) (fun w hw => ⟨hw.1.le, hw.2.le⟩)
  let χ : ℂ → ℝ := ballCutoff 0 (r / 4) (r / 2)
  have hχ : ContDiff ℝ 2 χ := (ballCutoff_contDiff _ _ _).of_le
    (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hcχ : HasCompactSupport χ := ballCutoff_hasCompactSupport (by positivity) (by linarith)
  have hsχ {z : ℂ} (hz : z ∈ tsupport χ) : ‖z‖ ≤ r / 2 := by
    simpa only [mem_closedBall, dist_zero_right] using
      ballCutoff_tsupport_subset_closedBall (by positivity : 0 ≤ r / 4)
        (by linarith : r / 4 < r / 2) hz
  have hnχ (z : ℂ) : ‖χ z‖ ≤ 1 := by
    have hh := ballCutoff_mem_Icc (0 : ℂ) (r / 4) (r / 2) z
    change 0 ≤ χ z ∧ χ z ≤ 1 at hh
    simpa only [Real.norm_eq_abs, abs_of_nonneg hh.1] using hh.2
  obtain ⟨D, hD⟩ := (hcχ.fderiv ℝ).exists_bound_of_continuous
    (hχ.continuous_fderiv (by norm_num))
  have hD0 : 0 ≤ D := (norm_nonneg (fderiv ℝ χ 0)).trans (hD 0)
  have hcχΔ : HasCompactSupport (Laplacian.laplacian χ) :=
    hcχ.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset χ)
  have hχΔ : Continuous (Laplacian.laplacian χ) :=
    continuous_iff_continuousAt.mpr (fun _ => hχ.contDiffAt.continuousAt_laplacian)
  obtain ⟨A, hA⟩ := hcχΔ.exists_bound_of_continuous hχΔ
  have hA0 : 0 ≤ A := (norm_nonneg (Laplacian.laplacian χ 0)).trans (hA 0)
  let g : ℂ → F := χ • f
  have hgc : HasCompactSupport g := hcχ.smul_right
  have hgz (z : ℂ) (hz : z ∉ tsupport χ) : g =ᶠ[𝓝 z] 0 := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with w hw
    change χ w • f w = 0
    rw [hw, Pi.zero_apply, zero_smul]
  have hgd (z : ℂ) (hi : 0 < z.im) : ContDiffAt ℝ 2 g z := by
    by_cases hz : z ∈ tsupport χ
    · exact hχ.contDiffAt.smul (hd z ((hsχ hz).trans_lt (by linarith)) hi)
    · exact contDiffAt_const.congr_of_eventuallyEq (hgz z hz)
  have hgg (z : ℂ) (hi : 0 < z.im) : ‖g z‖ ≤ K * z.im := by
    by_cases hz : z ∈ tsupport χ
    · change ‖χ z • f z‖ ≤ _
      rw [norm_smul]
      exact (mul_le_mul (hnχ z) (hgrowth z ((hsχ hz).trans (by linarith)) hi.le)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    · rw [(hgz z hz).eq_of_nhds]
      change ‖(0 : F)‖ ≤ _
      simp only [norm_zero]
      positivity
  let B : ℝ := 2 * β * (K : ℝ) ^ 2 + 2 * D * K + A * (K * r)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hgΔ (z : ℂ) (hi : 0 < z.im) : ‖Laplacian.laplacian g z‖ ≤ B := by
    by_cases hz : z ∈ tsupport χ
    · have hzr : ‖z‖ < r := (hsχ hz).trans_lt (by linarith)
      have hzd := hd z (hzr.trans hrR) hi
      have hfΔ : ‖Laplacian.laplacian f z‖ ≤ 2 * β * (K : ℝ) ^ 2 := by
        have hh := (fderiv ℝ f z).hilbertSchmidtInner_self_le_finrank_mul_norm_sq
        norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat] at hh
        have hsq := sq_le_sq₀ (norm_nonneg (fderiv ℝ f z)) K.coe_nonneg
        have hm := mul_le_mul_of_nonneg_left (hh.trans
          (mul_le_mul_of_nonneg_left (hsq.mpr (hDf z hzr hi)) (by norm_num))) hβ
        exact (hΔ z (hzr.trans hrR) hi).trans (by nlinarith only [hm])
      have hfv : ‖f z‖ ≤ K * r := (hgrowth z hzr.le hi.le).trans
        (mul_le_mul_of_nonneg_left ((Complex.im_le_norm z).trans hzr.le) K.coe_nonneg)
      have hp := hχ.contDiffAt.norm_laplacian_fun_smul_le hzd
      change ‖Laplacian.laplacian g z‖ ≤ _ at hp
      apply hp.trans
      calc
        _ ≤ 1 * (2 * β * (K : ℝ) ^ 2) + 2 * D * K + A * (K * r) := by
          gcongr
          · exact hnχ z
          · exact hD z
          · exact hDf z hzr hi
          · exact hA z
        _ = B := by simp only [one_mul, B]
    · rw [(laplacian_congr_nhds (hgz z hz)).eq_of_nhds]
      change ‖Laplacian.laplacian (fun _ : ℂ => (0 : F)) z‖ ≤ B
      simpa only [laplacian_const, Pi.zero_apply, norm_zero] using hB0
  obtain ⟨C, hC1, hCh⟩ := exists_holder_fderiv_oddReflection hgc hgd hgg hgΔ hα hα1
  refine ⟨r / 4, by positivity, by linarith, oddReflection g, C, hC1, hCh, ?_⟩
  intro z hz
  have hg0 (w : ℂ) (hw : w.im = 0) : g w = 0 := by
    by_cases hws : w ∈ tsupport χ
    · change χ w • f w = 0
      rw [hzero w ((hsχ hws).trans (by linarith)) hw, smul_zero]
    · exact (hgz w hws).eq_of_nhds
  rw [oddReflection_eq_of_im_nonneg g hg0 hz.2]
  change χ z • f z = f z
  rw [show χ z = 1 from ballCutoff_eq_one_of_mem_closedBall (by positivity) (by linarith)
    (by simpa only [mem_closedBall, dist_zero_right] using hz.1), one_smul]

end DifferentialGeometry.Analysis
