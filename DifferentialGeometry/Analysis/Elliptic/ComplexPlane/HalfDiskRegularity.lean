import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.BoundaryRegularity
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Gradient
import DifferentialGeometry.Analysis.Schauder.Holder.CompactRegularity
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section
open Set Filter MeasureTheory Metric InnerProductSpace
open scoped Topology ContDiff NNReal
namespace DifferentialGeometry.Analysis

private theorem exists_holderOnWith_smul_of_compactSupport_subset
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Q U : Set E} (hQU : IsCompact (Q ∩ U))
    {χ : E → ℝ} (hχ : ContDiff ℝ 1 χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ U) {f : E → F} {K α : ℝ≥0}
    (hf : HolderOnWith K α f (Q ∩ U)) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ≥0, HolderOnWith C α (fun x => χ x • f x) Q := by
  obtain ⟨M, A, hM, hA⟩ := Schauder.exists_norm_bound_and_holderWith_of_contDiff_hasCompactSupport hχ hcχ hα1
  obtain ⟨N, hN⟩ := Schauder.exists_norm_bound_of_continuousOn_isCompact
    hQU (hf.continuousOn hα)
  refine ⟨M * K + N * A, HolderWith.restrict_iff.mp ?_⟩
  apply Schauder.holderWith_smul_of_eq_zero_outside χ f (hA.holderOnWith Q).holderWith
    hf.holderWith (fun x _ _ => hM x) (fun x hQ hU => hN x ⟨hQ, hU⟩)
  intro x _ hx
  exact image_eq_zero_of_notMem_tsupport (fun hs => hx (hsχ hs))

private theorem holderOnWith_apply_clm
    {E F V : Type*} [PseudoEMetricSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Q : Set E} {f : E → V →L[ℝ] F} {K α : ℝ≥0}
    (hf : HolderOnWith K α f Q) (v : V) :
    ∃ C : ℝ≥0, HolderOnWith C α (fun x => f x v) Q := by
  have h := (ContinuousLinearMap.apply ℝ F v).lipschitz.holderWith.comp_holderOnWith hf
  refine ⟨‖ContinuousLinearMap.apply ℝ F v‖₊ * K, ?_⟩
  intro x hx y hy
  simpa only [Function.comp_def, one_mul, NNReal.coe_one, NNReal.rpow_one] using! h x hx y hy

private theorem exists_holderOnWith_cutoff_laplacian_field
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Q U : Set ℂ} (hQU : IsCompact (Q ∩ U))
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ 3 χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ U) {f g : ℂ → F} {D : ℂ → ℂ →L[ℝ] F}
    {Kf Kg KD α : ℝ≥0}
    (hf : HolderOnWith Kf α f (Q ∩ U))
    (hg : HolderOnWith Kg α g (Q ∩ U))
    (hD : HolderOnWith KD α D (Q ∩ U))
    (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ≥0, HolderOnWith C α
      (fun z => χ z • g z +
        (2 : ℝ) • ((fderiv ℝ χ z 1) • (D z 1) +
          (fderiv ℝ χ z Complex.I) • (D z Complex.I)) +
        Laplacian.laplacian χ z • f z) Q := by
  have hdχ : ContDiff ℝ 2 (fderiv ℝ χ) := hχ.fderiv_right (by norm_num)
  have hddχ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ χ)) := hdχ.fderiv_right (by norm_num)
  have hχL : ContDiff ℝ 1 (Laplacian.laplacian χ) := by
    rw [laplacian_eq_iteratedFDeriv_complexPlane]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ((hddχ.clm_apply contDiff_const).clm_apply contDiff_const).add
      ((hddχ.clm_apply contDiff_const).clm_apply contDiff_const)
  obtain ⟨A, hA⟩ := exists_holderOnWith_smul_of_compactSupport_subset hQU
    (hχ.of_le (by norm_num)) hcχ hsχ hg hα hα1
  obtain ⟨B, hB⟩ := exists_holderOnWith_smul_of_compactSupport_subset hQU hχL
    (hcχ.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset χ))
    ((tsupport_laplacian_subset χ).trans hsχ) hf hα hα1
  have heval (v : ℂ) : ∃ C : ℝ≥0, HolderOnWith C α
      (fun z => fderiv ℝ χ z v • D z v) Q := by
    obtain ⟨C, hC⟩ := holderOnWith_apply_clm hD v
    exact exists_holderOnWith_smul_of_compactSupport_subset hQU
      ((hdχ.clm_apply contDiff_const).of_le (by norm_num))
      (hcχ.of_isClosed_subset (isClosed_tsupport _) (tsupport_fderiv_apply_subset ℝ v))
      ((tsupport_fderiv_apply_subset ℝ v).trans hsχ) hC hα hα1
  obtain ⟨C, hC⟩ := heval 1
  obtain ⟨D, hD⟩ := heval Complex.I
  refine ⟨A + (C + D) * ‖(2 : ℝ)‖₊ + B, HolderWith.restrict_iff.mp ?_⟩
  exact (hA.holderWith.add ((hC.holderWith.add hD.holderWith).smul (2 : ℝ))).add hB.holderWith

private theorem laplacian_smul_complex
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {χ : ℂ → ℝ} {f : ℂ → F} {z : ℂ}
    (hχ : ContDiffAt ℝ 2 χ z) (hf : ContDiffAt ℝ 2 f z) :
    Laplacian.laplacian (fun w => χ w • f w) z = χ z • Laplacian.laplacian f z +
      (2 : ℝ) • ((fderiv ℝ χ z 1) • (fderiv ℝ f z 1) +
        (fderiv ℝ χ z Complex.I) • (fderiv ℝ f z Complex.I)) +
      Laplacian.laplacian χ z • f z := by
  rw [hχ.laplacian_fun_smul hf]
  have he : gradient χ z =
      (fderiv ℝ χ z 1) • (1 : ℂ) + (fderiv ℝ χ z Complex.I) • Complex.I := by
    apply Complex.ext <;> simp [gradient_complex_re, gradient_complex_im, Complex.real_smul]
  rw [he, map_add, map_smul, map_smul]

private theorem halfDisk_cutoff_of_holder_laplacian
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : ℂ → F} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hf : ContDiffOn ℝ 1 f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hf2 : ContDiffOn ℝ 2 f {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (hfg : ∀ z : ℂ, ‖z‖ < R → 0 < z.im → Laplacian.laplacian f z = g z)
    {K KD α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hg : HolderOnWith K α g {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hD : HolderOnWith KD α (fderivWithin ℝ f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
      {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) :
    ∃ G : ℂ → F,
      ContDiffOn ℝ 1 (fun z => ballCutoff 0 r ((r + R) / 2) z • f z) {z : ℂ | 0 ≤ z.im} ∧
      ContDiffOn ℝ 2 (fun z => ballCutoff 0 r ((r + R) / 2) z • f z) {z : ℂ | 0 < z.im} ∧
      (∀ z : ℂ, 0 < z.im → Laplacian.laplacian
        (fun w => ballCutoff 0 r ((r + R) / 2) w • f w) z = G z) ∧
      ∃ C : ℝ≥0, HolderOnWith C α G {z : ℂ | 0 ≤ z.im} := by
  let S : Set ℂ := {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}
  let Q : Set ℂ := {z : ℂ | 0 ≤ z.im}
  let χ : ℂ → ℝ := ballCutoff 0 r ((r + R) / 2)
  have hχ : ContDiff ℝ 3 χ := (ballCutoff_contDiff _ _ _).of_le
    (WithTop.coe_le_coe.mpr (le_top : (3 : ℕ∞) ≤ ⊤))
  have hcχ : HasCompactSupport χ := ballCutoff_hasCompactSupport hr.le (by linarith)
  have hsχ {z : ℂ} (hz : z ∈ tsupport χ) : ‖z‖ ≤ (r + R) / 2 := by
    simpa only [mem_closedBall, dist_zero_right] using
      ballCutoff_tsupport_subset_closedBall hr.le (by linarith : r < (r + R) / 2) hz
  have hsχR {z : ℂ} (hz : z ∈ tsupport χ) : ‖z‖ < R := (hsχ hz).trans_lt (by linarith)
  have hSeq : S = closedBall (0 : ℂ) R ∩ Q := by
    ext z
    simp only [S, Q, mem_inter_iff, mem_ofPred_eq, mem_closedBall, dist_zero_right]
  have hSc : IsCompact S := by
    rw [hSeq]
    exact (isCompact_closedBall (0 : ℂ) R).inter_right
      (isClosed_le (continuous_const (y := (0 : ℝ))) Complex.continuous_im)
  have hSconv : Convex ℝ S := by
    rw [hSeq]
    exact (convex_closedBall (0 : ℂ) R).inter (convex_halfSpace_im_ge 0)
  have hSopen : IsOpen {z : ℂ | ‖z‖ < R ∧ 0 < z.im} :=
    (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const Complex.continuous_im)
  have hSn {z : ℂ} (hz : ‖z‖ < R) (hi : 0 < z.im) : S ∈ 𝓝 z :=
    mem_of_superset (hSopen.mem_nhds ⟨hz, hi⟩) (fun w hw => ⟨hw.1.le, hw.2.le⟩)
  have hSnw {z : ℂ} (hz : ‖z‖ < R) : S ∈ 𝓝[Q] z := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds
      ((isOpen_lt continuous_norm continuous_const).mem_nhds hz), self_mem_nhdsWithin] with w hw hi
    exact ⟨hw.le, hi⟩
  let v : ℂ → F := fun z => χ z • f z
  have hvzero {z : ℂ} (hz : z ∉ tsupport χ) : v =ᶠ[𝓝 z] 0 := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with w hw
    change χ w • f w = 0
    rw [hw, Pi.zero_apply, zero_smul]
  have hv1 : ContDiffOn ℝ 1 v Q := by
    intro z hz
    by_cases hs : z ∈ tsupport χ
    · exact ((hχ.of_le (by norm_num)).contDiffAt.contDiffWithinAt).smul
        ((hf z ⟨(hsχR hs).le, hz⟩).mono_of_mem_nhdsWithin (hSnw (hsχR hs)))
    · exact (contDiffAt_const.congr_of_eventuallyEq (hvzero hs)).contDiffWithinAt
  have hv2 : ContDiffOn ℝ 2 v {z : ℂ | 0 < z.im} := by
    intro z hz
    by_cases hs : z ∈ tsupport χ
    · exact (((hχ.of_le (by norm_num)).contDiffAt).smul
        ((hf2 z ⟨hsχR hs, hz⟩).contDiffAt (hSopen.mem_nhds ⟨hsχR hs, hz⟩))).contDiffWithinAt
    · exact (contDiffAt_const.congr_of_eventuallyEq (hvzero hs)).contDiffWithinAt
  let G : ℂ → F := fun z => χ z • g z +
    (2 : ℝ) • ((fderiv ℝ χ z 1) • (fderivWithin ℝ f S z 1) +
      (fderiv ℝ χ z Complex.I) • (fderivWithin ℝ f S z Complex.I)) +
    Laplacian.laplacian χ z • f z
  have hvG (z : ℂ) (hz : 0 < z.im) : Laplacian.laplacian v z = G z := by
    by_cases hs : z ∈ tsupport χ
    · have hfd := (hf2 z ⟨hsχR hs, hz⟩).contDiffAt (hSopen.mem_nhds ⟨hsχR hs, hz⟩)
      dsimp only [v, G]
      rw [laplacian_smul_complex ((hχ.of_le (by norm_num)).contDiffAt) hfd,
        hfg z (hsχR hs) hz, fderivWithin_of_mem_nhds (hSn (hsχR hs) hz)]
    · have ha : χ z = 0 := image_eq_zero_of_notMem_tsupport hs
      have hd : fderiv ℝ χ z = 0 := fderiv_of_notMem_tsupport ℝ hs
      have hL : Laplacian.laplacian χ z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hs (tsupport_laplacian_subset χ h))
      rw [(laplacian_congr_nhds (hvzero hs)).eq_of_nhds]
      simp only [G, ha, hd, hL, _root_.zero_apply, zero_smul,
        add_zero, smul_zero]
      change Laplacian.laplacian (fun _ : ℂ => (0 : F)) z = 0
      simp only [laplacian_const, Pi.zero_apply]
  have hKQ : Q ∩ closedBall (0 : ℂ) R = S := by
    ext z
    simp only [Q, S, mem_inter_iff, mem_ofPred_eq, mem_closedBall, dist_zero_right, and_comm]
  obtain ⟨A, hA⟩ := Schauder.exists_holderWith_restrict_of_contDiffOn_isCompact hSc hSconv hf hα1.le
  have hfH : HolderOnWith A α f S := HolderWith.restrict_iff.mp hA
  obtain ⟨B, hB⟩ := exists_holderOnWith_cutoff_laplacian_field
    (Q := Q) (U := closedBall (0 : ℂ) R) (by simpa only [hKQ] using hSc)
    hχ hcχ (fun z hz => by simpa only [mem_closedBall, dist_zero_right] using (hsχR hz).le)
    (by simpa only [hKQ] using hfH) (by simpa only [hKQ] using hg)
    (by simpa only [hKQ] using hD) hα hα1.le
  exact ⟨G, hv1, hv2, hvG, B, hB⟩

theorem exists_contDiff_two_extension_halfDisk_of_dirichlet
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f g : ℂ → F} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hf : ContDiffOn ℝ 1 f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hf2 : ContDiffOn ℝ 2 f {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (hzero : ∀ x : ℝ, ‖(x : ℂ)‖ ≤ R → f (x : ℂ) = 0)
    (hfg : ∀ z : ℂ, ‖z‖ < R → 0 < z.im → Laplacian.laplacian f z = g z)
    {K KD α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hg : HolderOnWith K α g {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hD : HolderOnWith KD α (fderivWithin ℝ f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
      {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) :
    ∃ u : ℂ → F, HasCompactSupport u ∧ ContDiff ℝ 2 u ∧
      (∃ C : ℝ≥0, HolderWith C α (iteratedFDeriv ℝ 2 u)) ∧
      EqOn u f {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} := by
  obtain ⟨G, hv1, hv2, hvG, B, hB⟩ :=
    halfDisk_cutoff_of_holder_laplacian hr hrR hf hf2 hfg hα hα1 hg hD
  let χ : ℂ → ℝ := ballCutoff 0 r ((r + R) / 2)
  let v : ℂ → F := fun z => χ z • f z
  have hcχ : HasCompactSupport χ := ballCutoff_hasCompactSupport hr.le (by linarith)
  have hvc : HasCompactSupport v := hcχ.smul_right
  have hsχR {z : ℂ} (hz : z ∈ tsupport χ) : ‖z‖ < R := by
    have hh := ballCutoff_tsupport_subset_closedBall hr.le (by linarith : r < (r + R) / 2) hz
    simp only [mem_closedBall, dist_zero_right] at hh
    linarith
  have hv0 (x : ℝ) : v (x : ℂ) = 0 := by
    change χ (x : ℂ) • f (x : ℂ) = 0
    by_cases hs : (x : ℂ) ∈ tsupport χ
    · rw [hzero x (hsχR hs).le, smul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hs, zero_smul]
  obtain ⟨u, huc, hu2, huH, heq⟩ := exists_contDiff_two_extension_of_holder_laplacian
    hvc hv1 hv2 hv0 hvG hα hα1 hB
  refine ⟨u, huc, hu2, huH, ?_⟩
  intro z hz
  rw [heq hz.2]
  change χ z • f z = f z
  rw [show χ z = 1 from ballCutoff_eq_one_of_mem_closedBall hr.le (by linarith)
    (by simpa only [mem_closedBall, dist_zero_right] using hz.1), one_smul]

private theorem upper_unique_diff : UniqueDiffOn ℝ {z : ℂ | 0 ≤ z.im} := by
  apply uniqueDiffOn_convex (convex_halfSpace_im_ge 0)
  refine ⟨Complex.I, mem_interior_iff_mem_nhds.mpr ?_⟩
  exact mem_of_superset ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds
    (by simp : (0 : ℝ) < Complex.I.im)) (fun z hz => (show 0 < z.im from hz).le)

private theorem fderivWithin_normal_ballCutoff_smul_eq_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℂ → F} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hf : ContDiffOn ℝ 1 f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hN : ∀ x : ℝ, ‖(x : ℂ)‖ ≤ R →
      fderivWithin ℝ f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} (x : ℂ) Complex.I = 0)
    (x : ℝ) :
    fderivWithin ℝ (fun z => ballCutoff 0 r ((r + R) / 2) z • f z)
      {z : ℂ | 0 ≤ z.im} (x : ℂ) Complex.I = 0 := by
  let S : Set ℂ := {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}
  let Q : Set ℂ := {z : ℂ | 0 ≤ z.im}
  let χ : ℂ → ℝ := ballCutoff 0 r ((r + R) / 2)
  by_cases hs : (x : ℂ) ∈ tsupport χ
  · have hxr : ‖(x : ℂ)‖ < R := by
      have hh := ballCutoff_tsupport_subset_closedBall hr.le (by linarith : r < (r + R) / 2) hs
      simp only [mem_closedBall, dist_zero_right] at hh
      linarith
    have hSnw : S ∈ 𝓝[Q] (x : ℂ) := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds
        ((isOpen_lt continuous_norm continuous_const).mem_nhds hxr), self_mem_nhdsWithin] with w hw hi
      exact ⟨hw.le, hi⟩
    have hfd : HasFDerivWithinAt f (fderivWithin ℝ f S (x : ℂ)) Q (x : ℂ) :=
      ((hf.differentiableOn (by norm_num) (x : ℂ) ⟨hxr.le, by simp⟩).hasFDerivWithinAt).mono_of_mem_nhdsWithin hSnw
    have hχd := hasFDerivAt_ballCutoff (0 : ℂ) r ((r + R) / 2) (x : ℂ)
    have hh := hχd.hasFDerivWithinAt.smul hfd
    change fderivWithin ℝ (ballCutoff (0 : ℂ) r ((r + R) / 2) • f) Q (x : ℂ) Complex.I = 0
    rw [hh.fderivWithin (upper_unique_diff _ (by simp))]
    have hn : ballCutoffFDeriv (0 : ℂ) r ((r + R) / 2) (x : ℂ) Complex.I = 0 := by
      simp [ballCutoffFDeriv, ballCutoffArgumentFDeriv_apply, Complex.inner]
    have hnf : fderivWithin ℝ f S (x : ℂ) Complex.I = 0 := hN x hxr.le
    simp only [_root_.add_apply, _root_.smul_apply,
      ContinuousLinearMap.smulRight_apply, hn, hnf, smul_zero, zero_smul, add_zero]
  · have he : (fun z => χ z • f z) =ᶠ[𝓝 (x : ℂ)] (fun _ => (0 : F)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hs] with z hz
      rw [hz, Pi.zero_apply, zero_smul]
    rw [he.fderivWithin_eq_of_nhds (𝕜 := ℝ)]
    simp

theorem exists_contDiff_two_extension_halfDisk_of_neumann
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f g : ℂ → F} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hf : ContDiffOn ℝ 1 f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hf2 : ContDiffOn ℝ 2 f {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (hN : ∀ x : ℝ, ‖(x : ℂ)‖ ≤ R →
      fderivWithin ℝ f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} (x : ℂ) Complex.I = 0)
    (hfg : ∀ z : ℂ, ‖z‖ < R → 0 < z.im → Laplacian.laplacian f z = g z)
    {K KD α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hg : HolderOnWith K α g {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hD : HolderOnWith KD α (fderivWithin ℝ f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
      {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) :
    ∃ u : ℂ → F, HasCompactSupport u ∧ ContDiff ℝ 2 u ∧
      (∃ C : ℝ≥0, HolderWith C α (iteratedFDeriv ℝ 2 u)) ∧
      EqOn u f {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} := by
  obtain ⟨G, hv1, hv2, hvG, B, hB⟩ :=
    halfDisk_cutoff_of_holder_laplacian hr hrR hf hf2 hfg hα hα1 hg hD
  let χ : ℂ → ℝ := ballCutoff 0 r ((r + R) / 2)
  let v : ℂ → F := fun z => χ z • f z
  have hcχ : HasCompactSupport χ := ballCutoff_hasCompactSupport hr.le (by linarith)
  have hvc : HasCompactSupport v := hcχ.smul_right
  obtain ⟨C, hC2, hCH⟩ := exists_holder_iteratedFDeriv_two_evenReflection hvc hv1 hv2
    (fderivWithin_normal_ballCutoff_smul_eq_zero hr hrR hf hN) hvG hα hα1 hB
  refine ⟨evenReflection v, hasCompactSupport_evenReflection hvc, hC2, ⟨C, hCH⟩, ?_⟩
  intro z hz
  rw [evenReflection_of_im_nonneg v hz.2]
  change χ z • f z = f z
  rw [show χ z = 1 from ballCutoff_eq_one_of_mem_closedBall hr.le (by linarith)
    (by simpa only [mem_closedBall, dist_zero_right] using hz.1), one_smul]

end DifferentialGeometry.Analysis
