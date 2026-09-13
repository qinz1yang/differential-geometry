import Mathlib.Analysis.InnerProductSpace.PiL2
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Reflection
import DifferentialGeometry.Analysis.Elliptic.Euclidean.WeakLaplacianRegularity
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.BoundaryGradient
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.BoundaryLifting

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

private theorem hasCompactSupport_evenReflection_of_laplacian_eq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : ℂ → F} (hc : HasCompactSupport f)
    (hg : ContinuousOn g {z : ℂ | 0 ≤ z.im})
    (hfg : ∀ z : ℂ, 0 < z.im → Laplacian.laplacian f z = g z) :
    HasCompactSupport (evenReflection g) := by
  have hcΔ : HasCompactSupport (Laplacian.laplacian f) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset f)
  have hcR := hasCompactSupport_evenReflection hcΔ
  have hzero : EqOn (evenReflection g) (fun _ => 0) (tsupport (evenReflection (Laplacian.laplacian f)))ᶜ := by
    apply Measure.eqOn_open_of_ae_eq (μ := volume) (hU := hcR.isClosed.isOpen_compl)
      (hf := (continuous_evenReflection hg).continuousOn) (hg := continuousOn_const)
    filter_upwards [ae_restrict_of_ae (evenReflection_congr_ae hfg),
      ae_restrict_mem hcR.isClosed.measurableSet.compl] with z hz hzK
    rw [← hz, image_eq_zero_of_notMem_tsupport hzK]
  exact HasCompactSupport.intro hcR (fun z hz => hzero hz)

theorem exists_holder_iteratedFDeriv_two_evenReflection
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f g : ℂ → F} (hc : HasCompactSupport f)
    (hf : ContDiffOn ℝ 1 f {z : ℂ | 0 ≤ z.im})
    (hf2 : ContDiffOn ℝ 2 f {z : ℂ | 0 < z.im})
    (hN : ∀ x : ℝ, fderivWithin ℝ f {z : ℂ | 0 ≤ z.im} x Complex.I = 0)
    (hfg : ∀ z : ℂ, 0 < z.im → Laplacian.laplacian f z = g z)
    {α K : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) (hg : HolderOnWith K α g {z : ℂ | 0 ≤ z.im}) :
    ∃ C : ℝ≥0, ContDiff ℝ 2 (evenReflection f) ∧
      HolderWith C α (iteratedFDeriv ℝ 2 (evenReflection f)) := by
  have hgc := hg.continuousOn hα
  have hgext := continuous_evenReflection hgc
  have hcg := hasCompactSupport_evenReflection_of_laplacian_eq hc hgc hfg
  obtain ⟨B, hB⟩ := hcg.exists_bound_of_continuous hgext
  have hL : LocallyIntegrable (Laplacian.laplacian f) (volume.restrict {z : ℂ | 0 < z.im}) := by
    apply (hgext.locallyIntegrable.mono_measure (Measure.restrict_le_self)).congr
    filter_upwards [ae_restrict_mem (isOpen_lt continuous_const Complex.continuous_im).measurableSet] with z hz
    rw [evenReflection_of_im_nonneg g (show 0 < z.im from hz).le, hfg z hz]
  apply exists_holder_iteratedFDeriv_two_of_holder_weak_laplacian
    (continuous_evenReflection hf.continuousOn) (hasCompactSupport_evenReflection hc)
    hB ?_ hα hα1 (holderWith_evenReflection hg)
  intro φ hφ hcφ
  rw [integral_laplacian_smul_evenReflection hφ hcφ hf hf2 hN hL]
  apply integral_congr_ae
  filter_upwards [evenReflection_congr_ae hfg] with z hz
  rw [hz]

private theorem upper_unique_diff : UniqueDiffOn ℝ {z : ℂ | 0 ≤ z.im} := by
  apply uniqueDiffOn_convex (convex_halfSpace_im_ge 0)
  refine ⟨Complex.I, mem_interior_iff_mem_nhds.mpr ?_⟩
  have hH : {z : ℂ | 0 < z.im} ∈ 𝓝 Complex.I :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by simp)
  exact mem_of_superset hH (fun z hz => (show 0 ≤ z.im from hz.le))

private theorem laplacianWithin_eq_at_of_contDiffAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℂ → F} {z : ℂ} (hz : 0 ≤ z.im) (hf : ContDiffAt ℝ 2 f z) :
    laplacianWithin f {w : ℂ | 0 ≤ w.im} z = Laplacian.laplacian f z := by
  rw [laplacianWithin_eq_iteratedFDerivWithin_complexPlane _ upper_unique_diff hz,
    laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDerivWithin_eq_iteratedFDeriv upper_unique_diff hf hz]

private theorem neumann_from_boundary_lifting
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {L : ℂ → F} (hc : HasCompactSupport L)
    (hC2 : ContDiffOn ℝ 2 L {z : ℂ | 0 ≤ z.im})
    (hN : ∀ s : ℝ, HasFDerivWithinAt L (0 : ℂ →L[ℝ] F)
      {z : ℂ | 0 ≤ z.im} (s : ℂ))
    {K α : ℝ≥0} (hH : HolderOnWith K α
      (laplacianWithin L {z : ℂ | 0 ≤ z.im}) {z : ℂ | 0 ≤ z.im})
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ≥0, ContDiff ℝ 2 (evenReflection L) ∧
      HolderWith C α (iteratedFDeriv ℝ 2 (evenReflection L)) ∧
      EqOn (evenReflection L) L {z : ℂ | 0 ≤ z.im} := by
  have hC1 : ContDiffOn ℝ 1 L {z : ℂ | 0 ≤ z.im} := hC2.of_le (by norm_num)
  have hC2o : ContDiffOn ℝ 2 L {z : ℂ | 0 < z.im} :=
    hC2.mono (fun z hz => (show 0 ≤ z.im from hz.le))
  have hnormal (s : ℝ) : fderivWithin ℝ L {z : ℂ | 0 ≤ z.im} (s : ℂ) Complex.I = 0 := by
    rw [(hN s).fderivWithin (upper_unique_diff _ (by simp))]
    rfl
  have hLap (z : ℂ) (hz : 0 < z.im) : Laplacian.laplacian L z =
      laplacianWithin L {w : ℂ | 0 ≤ w.im} z := by
    exact (laplacianWithin_eq_at_of_contDiffAt hz.le ((hC2o z hz).contDiffAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz))).symm
  obtain ⟨C, hC, hHC⟩ := exists_holder_iteratedFDeriv_two_evenReflection hc hC1 hC2o
    hnormal hLap hα hα1 hH
  exact ⟨C, hC, hHC, fun z hz => evenReflection_of_im_nonneg L hz⟩

theorem exists_holder_iteratedFDeriv_two_laplacian_trace_lifting
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {b : ℝ → F} (hc : HasCompactSupport b)
    {K α : ℝ≥0} (hH : HolderWith K α b) (hα : 0 < α) (hα1 : α < 1) :
    ∃ G : ℂ → F, HasCompactSupport G ∧ ContDiff ℝ 2 G ∧
      ContDiffOn ℝ ∞ G {z : ℂ | 0 < z.im} ∧
      (∀ s : ℝ, G (s : ℂ) = 0 ∧ fderiv ℝ G (s : ℂ) = 0 ∧
        Laplacian.laplacian G (s : ℂ) = b s) ∧
      ∃ C : ℝ≥0, HolderWith C α (iteratedFDeriv ℝ 2 G) := by
  obtain ⟨L, hLc, hL2, hLi, hjet, B, hB⟩ :=
    exists_holderOnWith_laplacianWithin_lifting (hH.continuous hα) hc hH hα1.le
  have hN := fun s => (hjet s).2.1
  obtain ⟨C, hG2, hGC, heq⟩ := neumann_from_boundary_lifting hLc hL2 hN hB hα hα1
  refine ⟨evenReflection L, hasCompactSupport_evenReflection hLc, hG2,
    hLi.congr (fun z hz => heq (show 0 ≤ z.im from hz.le)), ?_, C, hGC⟩
  intro s
  have hs : (s : ℂ) ∈ {z : ℂ | 0 ≤ z.im} := by simp
  refine ⟨(heq hs).trans (hjet s).1, ?_, ?_⟩
  · rw [← fderivWithin_eq_fderiv (upper_unique_diff _ hs)
      (hG2.differentiable (by norm_num) (s : ℂ)),
      fderivWithin_congr' heq hs, (hN s).fderivWithin (upper_unique_diff _ hs)]
  · have he : evenReflection L =ᶠ[𝓝[{z : ℂ | 0 ≤ z.im}] (s : ℂ)] L :=
      heq.eventuallyEq_of_mem self_mem_nhdsWithin
    rw [← laplacianWithin_eq_at_of_contDiffAt hs hG2.contDiffAt,
      (laplacianWithin_congr_nhdsWithin he upper_unique_diff).eq_of_nhdsWithin hs,
      (hjet s).2.2]

private theorem exists_lipschitzOnWith_of_contDiffOn_compactSupport
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (hs : IsClosed s) (hconv : Convex ℝ s) (hu : UniqueDiffOn ℝ s)
    {f : E → F} (hf : ContDiffOn ℝ 1 f s) (hc : HasCompactSupport f) :
    ∃ L : ℝ≥0, LipschitzOnWith L f s := by
  have hd := hf.continuousOn_fderivWithin hu (by norm_num)
  have hk := (hc.inter_right hs).image_of_continuousOn (hd.mono inter_subset_right)
  obtain ⟨R, hR, hbound⟩ := hk.isBounded.exists_pos_norm_le
  refine ⟨⟨R, hR.le⟩, hconv.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun z hz => (hf.differentiableOn (by norm_num) z hz).hasFDerivWithinAt) ?_⟩
  intro z hz
  apply NNReal.coe_le_coe.mp
  change ‖fderivWithin ℝ f s z‖ ≤ R
  by_cases hzs : z ∈ tsupport f
  · exact hbound _ ⟨z, ⟨hzs, hz⟩, rfl⟩
  · have he := (notMem_tsupport_iff_eventuallyEq.mp hzs).fderivWithin_eq_of_nhds
      (𝕜 := ℝ) (s := s)
    rw [he]
    simpa using hR.le

theorem exists_holder_iteratedFDeriv_two_oddReflection
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f g : ℂ → F} (hc : HasCompactSupport f)
    (hf : ContDiffOn ℝ 1 f {z : ℂ | 0 ≤ z.im})
    (hf2 : ContDiffOn ℝ 2 f {z : ℂ | 0 < z.im})
    (hzero : ∀ s : ℝ, f (s : ℂ) = 0)
    (hfg : ∀ z : ℂ, 0 < z.im → Laplacian.laplacian f z = g z)
    {K α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hg : HolderOnWith K α g {z : ℂ | 0 ≤ z.im})
    (hgzero : ∀ s : ℝ, g (s : ℂ) = 0) :
    ∃ C : ℝ≥0, ContDiff ℝ 2 (oddReflection f) ∧
      HolderWith C α (iteratedFDeriv ℝ 2 (oddReflection f)) := by
  obtain ⟨L, hL⟩ := exists_lipschitzOnWith_of_contDiffOn_compactSupport
    (isClosed_le continuous_const Complex.continuous_im) (convex_halfSpace_im_ge 0)
    upper_unique_diff hf hc
  have hgrowth (z : ℂ) (hz : 0 < z.im) : ‖f z‖ ≤ L * z.im := by
    have hh := hL.norm_sub_le hz.le (show (z.re : ℂ) ∈ {w : ℂ | 0 ≤ w.im} from by simp)
    rw [hzero z.re, sub_zero] at hh
    have he : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    simpa only [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hz] using hh
  have hg0 (z : ℂ) (hz : z.im = 0) : g z = 0 := by
    have he : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hz]
    rw [← he, hgzero]
  have hGH := holderWith_oddReflection hg hg0
  have hcΔ : HasCompactSupport (Laplacian.laplacian f) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset f)
  have hcg : HasCompactSupport (oddReflection g) := by
    rw [← oddReflection_congr hfg]
    exact hasCompactSupport_oddReflection hcΔ
  obtain ⟨B, hB⟩ := hcg.exists_bound_of_continuous (hGH.continuous hα)
  have hDelta (z : ℂ) (hz : 0 < z.im) : ‖Laplacian.laplacian f z‖ ≤ B := by
    rw [hfg z hz, ← oddReflection_of_im_pos g hz]
    exact hB z
  have hfc : ContinuousOn f {z : ℂ | 0 < z.im} := hf2.continuousOn
  apply exists_holder_iteratedFDeriv_two_of_holder_weak_laplacian
    (continuous_oddReflection_of_norm_le_mul_im hfc hgrowth)
    (hasCompactSupport_oddReflection hc) hB ?_ hα hα1 hGH
  intro φ hφ hcφ
  rw [integral_laplacian_smul_oddReflection hφ hcφ
    (fun z hz => (hf2 z hz).contDiffAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)) hgrowth hDelta,
    oddReflection_congr hfg]

private theorem holderWith_laplacian_of_iteratedFDeriv_two
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℂ → F} {K α : ℝ≥0} (hf : HolderWith K α (iteratedFDeriv ℝ 2 f)) :
    HolderWith (2 * K) α (Laplacian.laplacian f) := by
  have heval (v : Fin 2 → ℂ) (hv : ‖v‖ ≤ 1) :
      HolderWith K α (fun z => iteratedFDeriv ℝ 2 f z v) := by
    have hl : LipschitzWith 1
        (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℂ) F => A v) := by
      apply LipschitzWith.mk_one
      intro A B
      rw [dist_eq_norm, dist_eq_norm]
      exact (A - B).unit_le_opNorm hv
    simpa only [Function.comp_def, one_mul, mul_one, NNReal.coe_one, NNReal.rpow_one] using hl.holderWith.comp hf
  have h1 : ‖(![1, 1] : Fin 2 → ℂ)‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).2
    intro i
    fin_cases i <;> norm_num
  have hI : ‖(![Complex.I, Complex.I] : Fin 2 → ℂ)‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).2
    intro i
    fin_cases i <;> norm_num
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  intro x y
  simpa only [two_mul, Pi.add_apply] using
    ((heval ![1, 1] h1).add (heval ![Complex.I, Complex.I] hI)) x y

theorem exists_contDiff_two_extension_of_holder_laplacian
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f g : ℂ → F} (hc : HasCompactSupport f)
    (hf : ContDiffOn ℝ 1 f {z : ℂ | 0 ≤ z.im})
    (hf2 : ContDiffOn ℝ 2 f {z : ℂ | 0 < z.im})
    (hzero : ∀ s : ℝ, f (s : ℂ) = 0)
    (hfg : ∀ z : ℂ, 0 < z.im → Laplacian.laplacian f z = g z)
    {K α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hg : HolderOnWith K α g {z : ℂ | 0 ≤ z.im}) :
    ∃ u : ℂ → F, HasCompactSupport u ∧ ContDiff ℝ 2 u ∧
      (∃ C : ℝ≥0, HolderWith C α (iteratedFDeriv ℝ 2 u)) ∧
      EqOn u f {z : ℂ | 0 ≤ z.im} := by
  let b : ℝ → F := fun x => g (x : ℂ)
  have hbH : HolderWith K α b := by
    intro x y
    simpa only [b, Complex.isometry_ofReal.edist_eq] using
      hg (x : ℂ) (by simp) (y : ℂ) (by simp)
  have hcg := hasCompactSupport_evenReflection_of_laplacian_eq hc (hg.continuousOn hα) hfg
  have hbc : HasCompactSupport b := by
    have he : b = evenReflection g ∘ ((↑) : ℝ → ℂ) := by
      funext x
      exact (evenReflection_of_im_nonneg g (by simp : (0 : ℝ) ≤ (x : ℂ).im)).symm
    rw [he]
    exact hcg.comp_isClosedEmbedding Complex.isometry_ofReal.isClosedEmbedding
  obtain ⟨G, hcG, hG2, _, hGjet, C, hGH⟩ :=
    exists_holder_iteratedFDeriv_two_laplacian_trace_lifting hbc hbH hα hα1
  let w : ℂ → F := fun z => f z - G z
  let q : ℂ → F := fun z => g z - Laplacian.laplacian G z
  have hwc : HasCompactSupport w := hc.sub hcG
  have hw1 : ContDiffOn ℝ 1 w {z : ℂ | 0 ≤ z.im} :=
    hf.sub ((hG2.of_le (by norm_num)).contDiffOn)
  have hw2 : ContDiffOn ℝ 2 w {z : ℂ | 0 < z.im} := hf2.sub hG2.contDiffOn
  have hw0 (s : ℝ) : w (s : ℂ) = 0 := by
    simp only [w, hzero s, (hGjet s).1, sub_self]
  have hwq (z : ℂ) (hz : 0 < z.im) : Laplacian.laplacian w z = q z := by
    change Laplacian.laplacian (f - G) z = _
    rw [((hf2 z hz).contDiffAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)).laplacian_sub hG2.contDiffAt]
    rw [hfg z hz]
  have hqH : HolderOnWith (K + 2 * C) α q {z : ℂ | 0 ≤ z.im} :=
    HolderWith.restrict_iff.mp (Schauder.holderWith_sub hg.holderWith
      ((holderWith_laplacian_of_iteratedFDeriv_two hGH).holderOnWith _).holderWith)
  have hq0 (s : ℝ) : q (s : ℂ) = 0 := by
    change g (s : ℂ) - Laplacian.laplacian G (s : ℂ) = 0
    rw [(hGjet s).2.2]
    exact sub_self _
  obtain ⟨A, hU2, hUH⟩ := exists_holder_iteratedFDeriv_two_oddReflection
    hwc hw1 hw2 hw0 hwq hα hα1 hqH hq0
  refine ⟨fun z => oddReflection w z + G z,
    (hasCompactSupport_oddReflection hwc).add hcG, hU2.add hG2, ?_, ?_⟩
  · refine ⟨A + C, ?_⟩
    rw [fun_iteratedFDeriv_add hU2 hG2]
    exact hUH.add hGH
  · intro z hz
    have hwaxis (y : ℂ) (hy : y.im = 0) : w y = 0 := by
      have he : (y.re : ℂ) = y := by apply Complex.ext <;> simp [hy]
      rw [← he]
      exact hw0 y.re
    change oddReflection w z + G z = f z
    rw [oddReflection_eq_of_im_nonneg w hwaxis hz]
    exact sub_add_cancel _ _

private theorem norm_sq_le_basisEquiv_mul_hilbertSchmidt
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : E →L[ℝ] F) :
    ‖A‖ ^ 2 ≤ ‖((stdOrthonormalBasis ℝ E).continuousLinearMapEquiv (V := F)).symm.toContinuousLinearMap‖ ^ 2 *
      A.hilbertSchmidtInner A := by
  let L := (stdOrthonormalBasis ℝ E).continuousLinearMapEquiv (V := F)
  have h := L.symm.toContinuousLinearMap.le_opNorm (L A)
  change ‖L.symm (L A)‖ ≤ ‖L.symm.toContinuousLinearMap‖ * ‖L A‖ at h
  rw [L.symm_apply_apply] at h
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  rw [mul_pow] at hs
  have he : ‖L A‖ ^ 2 = A.hilbertSchmidtInner A := by
    rw [ContinuousLinearMap.hilbertSchmidtInner_eq_inner (stdOrthonormalBasis ℝ E)]
    exact (real_inner_self_eq_norm_sq _).symm
  rw [he] at hs
  exact hs

private theorem exists_contDiff_one_extension_of_quadratic_growth_equiv
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : F ≃L[ℝ] E)
    {f : ℂ → F} {R β : ℝ} (hR : 0 < R) (hβ : 0 ≤ β)
    (hf : ContinuousOn f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hd : ∀ z : ℂ, ‖z‖ < R → 0 < z.im → ContDiffAt ℝ 2 f z)
    (hΔ : ∀ z : ℂ, ‖z‖ < R → 0 < z.im → ‖Laplacian.laplacian f z‖ ≤
      β * ‖fderiv ℝ f z‖ ^ 2)
    (hzero : ∀ z : ℂ, ‖z‖ ≤ R → z.im = 0 → f z = 0)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ ρ > (0 : ℝ), ρ < R ∧ ∃ u : ℂ → F, ∃ C : ℝ≥0,
      ContDiff ℝ 1 u ∧ HolderWith C α (fderiv ℝ u) ∧
        EqOn u f {z : ℂ | ‖z‖ ≤ ρ ∧ 0 ≤ z.im} := by
  let w := e ∘ f
  let L := (stdOrthonormalBasis ℝ ℂ).continuousLinearMapEquiv (V := E)
  let B : ℝ := ‖e.toContinuousLinearMap‖ * β * ‖e.symm.toContinuousLinearMap‖ ^ 2 *
    ‖L.symm.toContinuousLinearMap‖ ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hwd (z : ℂ) (hz : ‖z‖ < R) (hi : 0 < z.im) : ContDiffAt ℝ 2 w z :=
    e.contDiff.contDiffAt.comp z (hd z hz hi)
  have hwΔ (z : ℂ) (hz : ‖z‖ < R) (hi : 0 < z.im) :
      ‖Laplacian.laplacian w z‖ ≤ B * (fderiv ℝ w z).hilbertSchmidtInner (fderiv ℝ w z) := by
    have hde : fderiv ℝ f z = e.symm.toContinuousLinearMap.comp (fderiv ℝ w z) := by
      have h := e.symm.hasFDerivAt.comp z ((hwd z hz hi).differentiableAt (by norm_num)).hasFDerivAt
      have he : e.symm ∘ w = f := by funext x; exact e.symm_apply_apply (f x)
      rw [he] at h
      exact h.fderiv
    have hn : ‖fderiv ℝ f z‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖fderiv ℝ w z‖ := by
      rw [hde]
      exact ContinuousLinearMap.opNorm_comp_le _ _
    have hns := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
    rw [mul_pow] at hns
    have hhs := norm_sq_le_basisEquiv_mul_hilbertSchmidt (fderiv ℝ w z)
    have hla : Laplacian.laplacian w z = e (Laplacian.laplacian f z) := by
      exact (hd z hz hi).laplacian_CLM_comp_left (l := e.toContinuousLinearMap)
    rw [hla]
    calc
      ‖e (Laplacian.laplacian f z)‖ ≤ ‖e.toContinuousLinearMap‖ * ‖Laplacian.laplacian f z‖ :=
        e.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖e.toContinuousLinearMap‖ * (β * ‖fderiv ℝ f z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hΔ z hz hi) (norm_nonneg _)
      _ ≤ ‖e.toContinuousLinearMap‖ * (β * (‖e.symm.toContinuousLinearMap‖ ^ 2 *
          (‖L.symm.toContinuousLinearMap‖ ^ 2 *
            (fderiv ℝ w z).hilbertSchmidtInner (fderiv ℝ w z)))) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply mul_le_mul_of_nonneg_left _ hβ
        exact hns.trans (mul_le_mul_of_nonneg_left hhs (sq_nonneg _))
      _ = B * (fderiv ℝ w z).hilbertSchmidtInner (fderiv ℝ w z) := by dsimp [B]; ring
  obtain ⟨ρ, hρ, hρR, u, C, hu, hDu, hue⟩ :=
    exists_contDiff_one_extension_of_norm_laplacian_le hR hB
      (e.continuous.comp_continuousOn hf) hwd hwΔ
      (fun z hz hi => by dsimp [w]; rw [hzero z hz hi, map_zero]) hα hα1
  let A := ContinuousLinearMap.compL ℝ ℂ E F e.symm.toContinuousLinearMap
  have he (z : ℂ) : fderiv ℝ (e.symm ∘ u) z = A (fderiv ℝ u z) :=
    (e.symm.hasFDerivAt.comp z (hu.differentiable (by norm_num) z).hasFDerivAt).fderiv
  refine ⟨ρ, hρ, hρR, e.symm ∘ u, ‖A‖₊ * C,
    e.symm.contDiff.comp hu, ?_, ?_⟩
  · have h := A.lipschitz.holderWith.comp hDu
    intro x y
    rw [he x, he y]
    simpa only [Function.comp_def, one_mul, NNReal.coe_one, NNReal.rpow_one] using! h x y
  · intro z hz
    change e.symm (u z) = f z
    rw [hue hz]
    exact e.symm_apply_apply (f z)

theorem exists_contDiff_one_extension_of_norm_laplacian_le_mul_norm_fderiv_sq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : ℂ → F} {R β : ℝ} (hR : 0 < R) (hβ : 0 ≤ β)
    (hf : ContinuousOn f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hd : ∀ z : ℂ, ‖z‖ < R → 0 < z.im → ContDiffAt ℝ 2 f z)
    (hΔ : ∀ z : ℂ, ‖z‖ < R → 0 < z.im → ‖Laplacian.laplacian f z‖ ≤
      β * ‖fderiv ℝ f z‖ ^ 2)
    (hzero : ∀ z : ℂ, ‖z‖ ≤ R → z.im = 0 → f z = 0)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ ρ > (0 : ℝ), ρ < R ∧ ∃ u : ℂ → F, ∃ C : ℝ≥0,
      ContDiff ℝ 1 u ∧ HolderWith C α (fderiv ℝ u) ∧
        EqOn u f {z : ℂ | ‖z‖ ≤ ρ ∧ 0 ≤ z.im} := by
  let E := EuclideanSpace ℝ (Fin (Module.finrank ℝ F))
  let e : F ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  exact exists_contDiff_one_extension_of_quadratic_growth_equiv e hR hβ hf hd hΔ hzero hα hα1

end DifferentialGeometry.Analysis
