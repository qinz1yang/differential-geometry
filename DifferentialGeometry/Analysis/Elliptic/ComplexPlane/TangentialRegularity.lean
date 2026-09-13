import DifferentialGeometry.Analysis.Schauder.Holder.HigherOrderComposition
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.DerivativeRecovery
import DifferentialGeometry.Analysis.Schauder.Holder.DerivativeExtension
import DifferentialGeometry.Analysis.Complex.BoundaryTrace
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.HalfDiskRegularity

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff NNReal

namespace DifferentialGeometry.Analysis

private theorem exists_holderOnWith_fderivWithin_iteratedFDerivWithin_apply
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {s : Set E} (hs : UniqueDiffOn 𝕜 s) {f : E → F} {n : ℕ}
    (hf : ContDiffOn 𝕜 (n + 1) f s) {K α : ℝ≥0}
    (hD : HolderOnWith K α (iteratedFDerivWithin 𝕜 (n + 1) f s) s)
    (v : Fin n → E) :
    ∃ C : ℝ≥0, HolderOnWith C α
      (fderivWithin 𝕜 (fun x => iteratedFDerivWithin 𝕜 n f s x v) s) s := by
  let e := continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F
  let L : (E [×(n + 1)]→L[𝕜] F) →L[𝕜] (E →L[𝕜] F) :=
    (ContinuousLinearMap.compL 𝕜 E (E [×n]→L[𝕜] F) F
      (ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin n => E) F v)).comp
        e.toContinuousLinearEquiv.toContinuousLinearMap
  have he (x : E) (hx : x ∈ s) :
      fderivWithin 𝕜 (fun y => iteratedFDerivWithin 𝕜 n f s y v) s x =
        L (iteratedFDerivWithin 𝕜 (n + 1) f s x) := by
    have hC : ContDiffWithinAt 𝕜 1 (iteratedFDerivWithin 𝕜 n f s) s x :=
      (hf x hx).iteratedFDerivWithin_right hs (by norm_cast; omega) hx
    rw [fderivWithin_continuousMultilinear_apply_const (hs x hx)
      (hC.differentiableWithinAt (by norm_num))]
    rfl
  have h := L.lipschitz.holderWith.comp_holderOnWith hD
  refine ⟨‖L‖₊ * K, ?_⟩
  intro x hx y hy
  rw [he x hx, he y hy]
  simpa only [Function.comp_def, one_mul, NNReal.coe_one, NNReal.rpow_one] using! h x hx y hy

private theorem halfDisk_geometry {R : ℝ} (hR : 0 < R) :
    Convex ℝ {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} ∧
      UniqueDiffOn ℝ {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} ∧
      closure {z : ℂ | ‖z‖ < R ∧ 0 < z.im} = {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} := by
  let K : Set ℂ := {z | ‖z‖ ≤ R ∧ 0 ≤ z.im}
  have hKeq : K = closedBall (0 : ℂ) R ∩ {z : ℂ | 0 ≤ z.im} := by
    ext z
    simp [K]
  have hc : Convex ℝ K := by
    rw [hKeq]
    exact (convex_closedBall (0 : ℂ) R).inter (convex_halfSpace_im_ge 0)
  have hclosed : IsClosed K := (isClosed_le continuous_norm continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_im)
  have hi : interior K = {z : ℂ | ‖z‖ < R ∧ 0 < z.im} := by
    rw [hKeq, interior_inter, interior_closedBall _ hR.ne', Complex.interior_setOfPred_le_im]
    ext z
    simp
  have hne : (interior K).Nonempty := by
    rw [hi]
    refine ⟨((R / 2 : ℝ) : ℂ) * Complex.I, ?_⟩
    simp only [mem_ofPred_eq, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos (by positivity : 0 < R / 2), Complex.mul_I_im,
      Complex.ofReal_re]
    constructor <;> linarith
  refine ⟨hc, uniqueDiffOn_convex hc hne, ?_⟩
  rw [← hi, hc.closure_interior_eq_closure_of_nonempty_interior hne, hclosed.closure_eq]

private theorem contDiffOn_iteratedFDerivWithin_apply
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {s : Set E} (hs : UniqueDiffOn 𝕜 s) {f : E → F} {n k : ℕ}
    (hf : ContDiffOn 𝕜 (n + k) f s) (v : Fin n → E) :
    ContDiffOn 𝕜 k (fun x => iteratedFDerivWithin 𝕜 n f s x v) s := by
  apply (ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin n => E) F v).contDiff.comp_contDiffOn
  intro x hx
  exact (hf x hx).iteratedFDerivWithin_right hs (by norm_cast; omega) hx

private theorem iteratedFDerivWithin_tangent_eq_zero_on_halfDisk
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} (hR : 0 < R) {f : ℂ → F} {n : ℕ}
    (hf : ContDiffOn ℝ n f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hzero : ∀ r : ℝ, |r| ≤ R → f (r : ℂ) = 0) :
    ∀ r : ℝ, |r| ≤ R →
      iteratedFDerivWithin ℝ n f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} (r : ℂ)
        (fun _ : Fin n => (1 : ℂ)) = 0 := by
  let K : Set ℂ := {z | ‖z‖ ≤ R ∧ 0 ≤ z.im}
  let S := K ∩ ball (0 : ℂ) R
  have hKD : UniqueDiffOn ℝ K := (halfDisk_geometry hR).2.1
  have hSD : UniqueDiffOn ℝ S := hKD.inter isOpen_ball
  have hSeq : S = ball (0 : ℂ) R ∩ {z : ℂ | 0 ≤ z.im} := by
    ext z
    simp only [S, K, mem_inter_iff, mem_ofPred_eq, mem_ball, dist_zero_right]
    constructor
    · rintro ⟨⟨_, hi⟩, hn⟩
      exact ⟨hn, hi⟩
    · rintro ⟨hn, hi⟩
      exact ⟨⟨hn.le, hi⟩, hn⟩
  have htrace (r : ℝ) (hr : |r| < R) :
      iteratedFDerivWithin ℝ n f K (r : ℂ) (fun _ : Fin n => (1 : ℂ)) = 0 := by
    have hrS : (r : ℂ) ∈ S := by
      rw [hSeq]
      simpa using hr
    rw [← iteratedFDerivWithin_subset (s := S) inter_subset_left hSD hKD hf hrS, hSeq]
    apply iteratedFDerivWithin_tangent_eq_zero_of_real_trace isOpen_ball
      (by rw [← hSeq]; exact hf.mono inter_subset_left)
    · intro t ht
      apply hzero t
      simpa using (le_of_lt (show ‖(t : ℂ)‖ < R by simpa using ht))
    · simpa using hr
  have hJ : ContinuousOn
      (fun r : ℝ => iteratedFDerivWithin ℝ n f K (r : ℂ) (fun _ : Fin n => (1 : ℂ)))
      (Icc (-R) R) := by
    have hA := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℂ) F
      (fun _ => (1 : ℂ))).continuous.comp_continuousOn
        (hf.continuousOn_iteratedFDerivWithin le_rfl hKD)
    apply hA.comp Complex.continuous_ofReal.continuousOn
    intro r hr
    have ha : |r| ≤ R := abs_le.mpr hr
    simpa [K] using ha
  have hEq : EqOn
      (fun r : ℝ => iteratedFDerivWithin ℝ n f K (r : ℂ) (fun _ : Fin n => (1 : ℂ)))
      (fun _ => 0) (Ioo (-R) R) := by
    intro r hr
    exact htrace r (abs_lt.mpr hr)
  have hcl : closure (Ioo (-R) R) = Icc (-R) R := closure_Ioo (by linarith)
  have he := hEq.of_subset_closure hJ continuousOn_const
    Ioo_subset_Icc_self (by rw [hcl])
  intro r hr
  exact he (abs_le.mp hr)

private theorem fderivWithin_tangent_eq_zero_on_halfDisk
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} (hR : 0 < R) {f : ℂ → F} {n : ℕ}
    (hf : ContDiffOn ℝ (n + 1) f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hzero : ∀ r : ℝ, |r| ≤ R →
      fderivWithin ℝ f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} (r : ℂ) Complex.I = 0) :
    ∀ r : ℝ, |r| ≤ R → fderivWithin ℝ
      (fun z => iteratedFDerivWithin ℝ n f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} z
        (fun _ : Fin n => (1 : ℂ))) {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} (r : ℂ) Complex.I = 0 := by
  let K : Set ℂ := {z | ‖z‖ ≤ R ∧ 0 ≤ z.im}
  let S : Set ℂ := {z | ‖z‖ < R ∧ 0 < z.im}
  obtain ⟨_, hKD, hcl⟩ := halfDisk_geometry hR
  change closure S = K at hcl
  have hcl' : K ⊆ closure (interior K) := by
    have hSO : IsOpen S := (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im)
    have hSI : S ⊆ interior K := interior_maximal (fun _ hz => ⟨hz.1.le, hz.2.le⟩) hSO
    have hh := closure_mono hSI
    rw [hcl] at hh
    exact hh
  have hg : ContDiffOn ℝ n
      (fun z => fderivWithin ℝ f K z Complex.I) K :=
    (hf.fderivWithin hKD (by simp)).clm_apply contDiffOn_const
  intro r hr
  have hrK : (r : ℂ) ∈ K := by simpa [K] using hr
  have hC : ContDiffWithinAt ℝ 1 (iteratedFDerivWithin ℝ n f K) K (r : ℂ) :=
    (hf _ hrK).iteratedFDerivWithin_right hKD (by norm_cast; omega) hrK
  rw [fderivWithin_continuousMultilinear_apply_const_apply (hKD _ hrK)
    (hC.differentiableWithinAt (by simp))]
  rw [fderivWithin_iteratedFDerivWithin_apply_eq hKD hcl' n hf Complex.I _ hrK]
  exact iteratedFDerivWithin_tangent_eq_zero_on_halfDisk hR hg hzero r hr

private theorem laplacian_iteratedFDerivWithin_apply_on_open
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s K : Set E} (hs : IsOpen s) (hK : UniqueDiffOn ℝ K) (hsK : s ⊆ K)
    {f g : E → F} {n : ℕ} (hf : ContDiffOn ℝ (n + 2) f s)
    (hfg : EqOn (Laplacian.laplacian f) g s) (v : Fin n → E) :
    ContDiffOn ℝ 2 (fun x => iteratedFDerivWithin ℝ n f K x v) s ∧
      EqOn (Laplacian.laplacian (fun x => iteratedFDerivWithin ℝ n f K x v))
        (fun x => iteratedFDeriv ℝ n g x v) s := by
  let A := ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F v
  have hnear (x : E) (hx : x ∈ s) :
      (fun y => iteratedFDerivWithin ℝ n f K y v) =ᶠ[𝓝 x]
        (fun y => iteratedFDeriv ℝ n f y v) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hK
      ((hf y hy).contDiffAt (hs.mem_nhds hy) |>.of_le (by norm_cast; omega)) (hsK hy)]
  have hiter (x : E) (hx : x ∈ s) : ContDiffAt ℝ 2 (iteratedFDeriv ℝ n f) x :=
    ((hf x hx).contDiffAt (hs.mem_nhds hx)).iteratedFDeriv_right (by norm_cast; omega)
  constructor
  · intro x hx
    exact ((A.contDiff.contDiffAt.comp x (hiter x hx)).congr_of_eventuallyEq
      (hnear x hx)).contDiffWithinAt
  · intro x hx
    rw [(InnerProductSpace.laplacian_congr_nhds (hnear x hx)).eq_of_nhds]
    change Laplacian.laplacian (A ∘ iteratedFDeriv ℝ n f) x = _
    rw [(hiter x hx).laplacian_CLM_comp_left (l := A)]
    change A (Laplacian.laplacian (iteratedFDeriv ℝ n f) x) = _
    rw [((hf x hx).contDiffAt (hs.mem_nhds hx)).laplacian_iteratedFDeriv]
    have hg : Laplacian.laplacian f =ᶠ[𝓝 x] g := by
      filter_upwards [hs.mem_nhds hx] with y hy
      exact hfg hy
    rw [(hg.iteratedFDeriv ℝ n).eq_of_nhds]
    rfl

private theorem halfDisk_tangential_data
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} (hR : 0 < R) {f g : ℂ → F} {n : ℕ}
    (hf : ContDiffOn ℝ (n + 1) f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hfi : ContDiffOn ℝ (n + 2) f {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (hg : ContDiffOn ℝ n g {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hfg : EqOn (Laplacian.laplacian f) g {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    {Kf Kg α : ℝ≥0}
    (hDf : HolderOnWith Kf α (iteratedFDerivWithin ℝ (n + 1) f
      {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hDg : HolderOnWith Kg α (iteratedFDerivWithin ℝ n g
      {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) :
    let K : Set ℂ := {z | ‖z‖ ≤ R ∧ 0 ≤ z.im}
    let v := fun z => iteratedFDerivWithin ℝ n f K z (fun _ => (1 : ℂ))
    let q := fun z => iteratedFDerivWithin ℝ n g K z (fun _ => (1 : ℂ))
    ContDiffOn ℝ 1 v K ∧
      ContDiffOn ℝ 2 v {z : ℂ | ‖z‖ < R ∧ 0 < z.im} ∧
      EqOn (Laplacian.laplacian v) q {z : ℂ | ‖z‖ < R ∧ 0 < z.im} ∧
      (∃ C : ℝ≥0, HolderOnWith C α q K) ∧
      ∃ C : ℝ≥0, HolderOnWith C α (fderivWithin ℝ v K) K := by
  dsimp only
  let K : Set ℂ := {z | ‖z‖ ≤ R ∧ 0 ≤ z.im}
  let S : Set ℂ := {z | ‖z‖ < R ∧ 0 < z.im}
  have hK : UniqueDiffOn ℝ K := (halfDisk_geometry hR).2.1
  have hSO : IsOpen S := (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hSK : S ⊆ K := fun _ hz => ⟨hz.1.le, hz.2.le⟩
  obtain ⟨hv2, hvΔ⟩ := laplacian_iteratedFDerivWithin_apply_on_open hSO hK hSK hfi hfg
    (fun _ => (1 : ℂ))
  refine ⟨contDiffOn_iteratedFDerivWithin_apply hK (by simpa using hf) _, hv2, ?_, ?_,
    exists_holderOnWith_fderivWithin_iteratedFDerivWithin_apply hK hf hDf _⟩
  · intro z hz
    rw [hvΔ hz]
    change iteratedFDeriv ℝ n g z (fun _ => (1 : ℂ)) =
      iteratedFDerivWithin ℝ n g K z (fun _ => (1 : ℂ))
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hK
      (hg.contDiffAt (mem_of_superset (hSO.mem_nhds hz) hSK)) (hSK hz)]
  · let A := ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℂ) F (fun _ => (1 : ℂ))
    have hh := A.lipschitz.holderWith.comp_holderOnWith hDg
    refine ⟨‖A‖₊ * Kg, ?_⟩
    intro x hx y hy
    simpa only [Function.comp_def, one_mul, NNReal.coe_one, NNReal.rpow_one] using! hh x hx y hy

theorem exists_contDiff_two_extension_halfDisk_of_tangent_dirichlet
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) {f g : ℂ → F} {n : ℕ}
    (hf : ContDiffOn ℝ (n + 1) f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hfi : ContDiffOn ℝ (n + 2) f {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (hg : ContDiffOn ℝ n g {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hfg : EqOn (Laplacian.laplacian f) g {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (hzero : ∀ x : ℝ, |x| ≤ R → f (x : ℂ) = 0)
    {Kf Kg α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hDf : HolderOnWith Kf α (iteratedFDerivWithin ℝ (n + 1) f
      {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hDg : HolderOnWith Kg α (iteratedFDerivWithin ℝ n g
      {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) :
    ∃ u : ℂ → F, HasCompactSupport u ∧ ContDiff ℝ 2 u ∧
      (∃ C : ℝ≥0, HolderWith C α (iteratedFDeriv ℝ 2 u)) ∧
      EqOn u (fun z => iteratedFDerivWithin ℝ n f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} z
        (fun _ => (1 : ℂ))) {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} := by
  obtain ⟨hv1, hv2, hvq, ⟨C, hC⟩, ⟨D, hD⟩⟩ :=
    halfDisk_tangential_data (hr.trans hrR) hf hfi hg hfg hDf hDg
  apply exists_contDiff_two_extension_halfDisk_of_dirichlet hr hrR hv1 hv2 ?_
    (fun z hz hi => hvq ⟨hz, hi⟩) hα hα1 hC hD
  intro x hx
  exact iteratedFDerivWithin_tangent_eq_zero_on_halfDisk (hr.trans hrR) (hf.of_le (by simp)) hzero x (by simpa using hx)

theorem exists_contDiff_two_extension_halfDisk_of_tangent_neumann
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) {f g : ℂ → F} {n : ℕ}
    (hf : ContDiffOn ℝ (n + 1) f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hfi : ContDiffOn ℝ (n + 2) f {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (hg : ContDiffOn ℝ n g {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hfg : EqOn (Laplacian.laplacian f) g {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (hzero : ∀ x : ℝ, |x| ≤ R → fderivWithin ℝ f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} (x : ℂ) Complex.I = 0)
    {Kf Kg α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hDf : HolderOnWith Kf α (iteratedFDerivWithin ℝ (n + 1) f
      {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hDg : HolderOnWith Kg α (iteratedFDerivWithin ℝ n g
      {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) :
    ∃ u : ℂ → F, HasCompactSupport u ∧ ContDiff ℝ 2 u ∧
      (∃ C : ℝ≥0, HolderWith C α (iteratedFDeriv ℝ 2 u)) ∧
      EqOn u (fun z => iteratedFDerivWithin ℝ n f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} z
        (fun _ => (1 : ℂ))) {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} := by
  obtain ⟨hv1, hv2, hvq, ⟨C, hC⟩, ⟨D, hD⟩⟩ :=
    halfDisk_tangential_data (hr.trans hrR) hf hfi hg hfg hDf hDg
  apply exists_contDiff_two_extension_halfDisk_of_neumann hr hrR hv1 hv2 ?_
    (fun z hz hi => hvq ⟨hz, hi⟩) hα hα1 hC hD
  intro x hx
  exact fderivWithin_tangent_eq_zero_on_halfDisk (hr.trans hrR) hf hzero x (by simpa using hx)

private theorem contDiffOn_succ_halfDisk_of_tangent_extension
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {r R : ℝ} (hrR : r < R) {f g u : ℂ → F} {n : ℕ}
    (hKD : UniqueDiffOn ℝ {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hcl : closure {z : ℂ | ‖z‖ < r ∧ 0 < z.im} = {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im})
    (hf : ContDiffOn ℝ (n + 1) f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hfi : ContDiffOn ℝ (n + 2) f {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (hg : ContDiffOn ℝ n g {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hfg : EqOn (Laplacian.laplacian f) g {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    {Kg L α : ℝ≥0} (hα : 0 < α)
    (hDg : HolderOnWith Kg α (iteratedFDerivWithin ℝ n g
      {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hu : HolderWith L α (iteratedFDeriv ℝ 2 u))
    (hue : EqOn u (fun z => iteratedFDerivWithin ℝ n f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} z
      (fun _ => (1 : ℂ))) {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im}) :
    ContDiffOn ℝ (n + 2) f {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} ∧
      ∃ C : ℝ≥0, HolderOnWith C α (iteratedFDerivWithin ℝ (n + 2) f
        {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im}) {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} := by
  let K : Set ℂ := {z | ‖z‖ ≤ R ∧ 0 ≤ z.im}
  let S : Set ℂ := {z | ‖z‖ < r ∧ 0 < z.im}
  let T : Set ℂ := {z | ‖z‖ ≤ r ∧ 0 ≤ z.im}
  have hSO : IsOpen S := (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hSi : S ⊆ {z : ℂ | ‖z‖ < R ∧ 0 < z.im} := fun z hz => ⟨hz.1.trans hrR, hz.2⟩
  have hSK : S ⊆ K := fun z hz => ⟨(hz.1.trans hrR).le, hz.2.le⟩
  have hST : S ⊆ T := fun z hz => ⟨hz.1.le, hz.2.le⟩
  have hTK : T ⊆ K := fun z hz => ⟨hz.1.trans hrR.le, hz.2⟩
  change UniqueDiffOn ℝ K at hKD
  change closure S = T at hcl
  have hSC : Convex ℝ S := by
    have he : S = ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im} := by
      ext z
      simp [S]
    rw [he]
    exact (convex_ball (0 : ℂ) r).inter (convex_halfSpace_im_gt 0)
  have hG : HolderOnWith Kg α (iteratedFDeriv ℝ n g) S := by
    intro x hx y hy
    have hj (z : ℂ) (hz : z ∈ S) :
        iteratedFDerivWithin ℝ n g K z = iteratedFDeriv ℝ n g z :=
      iteratedFDerivWithin_eq_iteratedFDeriv hKD
        (hg.contDiffAt (mem_of_superset (hSO.mem_nhds hz) hSK)) (hSK hz)
    rw [← hj x hx, ← hj y hy]
    exact hDg x (hSK hx) y (hSK hy)
  have hV : HolderOnWith L α
      (iteratedFDeriv ℝ 2 (fun z => iteratedFDeriv ℝ n f z (fun _ => (1 : ℂ)))) S := by
    have he (z : ℂ) (hz : z ∈ S) :
        u =ᶠ[𝓝 z] (fun w => iteratedFDeriv ℝ n f w (fun _ => (1 : ℂ))) := by
      filter_upwards [hSO.mem_nhds hz] with w hw
      rw [hue (hST hw)]
      change iteratedFDerivWithin ℝ n f K w (fun _ => (1 : ℂ)) = _
      rw [iteratedFDerivWithin_eq_iteratedFDeriv hKD
        (((hfi w (hSi hw)).contDiffAt
          (mem_of_superset (hSO.mem_nhds hw) hSi)).of_le (by norm_cast; omega)) (hSK hw)]
    intro x hx y hy
    rw [← ((he x hx).iteratedFDeriv ℝ 2).eq_of_nhds,
      ← ((he y hy).iteratedFDeriv ℝ 2).eq_of_nhds]
    exact hu x y
  obtain ⟨C, hC⟩ := Elliptic.exists_holderOnWith_iteratedFDeriv_of_laplacian_tangent
    hSO (hfi.mono hSi) (hfg.mono hSi) hG hV
  have hfc : ContDiffOn ℝ (n + 1) f (closure S) := by
    rw [hcl]
    exact hf.mono hTK
  obtain ⟨hnew, hnewD⟩ := contDiffOn_succ_closure_of_holderOnWith_iteratedFDeriv
    (n := n + 1) hSC hSO ((hfi.mono hSi).of_le (by norm_cast)) hfc hα
    (by simpa [Nat.add_assoc] using hC)
  rw [hcl] at hnew hnewD
  exact ⟨hnew.of_le (by norm_cast), C, by simpa [Nat.add_assoc] using hnewD⟩


theorem contDiffOn_succ_halfDisk_of_dirichlet
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) {f g : ℂ → F} {n : ℕ}
    (hf : ContDiffOn ℝ (n + 1) f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hfi : ContDiffOn ℝ (n + 2) f {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (hg : ContDiffOn ℝ n g {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hfg : EqOn (Laplacian.laplacian f) g {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (hzero : ∀ x : ℝ, |x| ≤ R → f (x : ℂ) = 0)
    {Kf Kg α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hDf : HolderOnWith Kf α (iteratedFDerivWithin ℝ (n + 1) f
      {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hDg : HolderOnWith Kg α (iteratedFDerivWithin ℝ n g
      {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) :
    ContDiffOn ℝ (n + 2) f {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} ∧
      ∃ C : ℝ≥0, HolderOnWith C α (iteratedFDerivWithin ℝ (n + 2) f
        {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im}) {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} := by
  obtain ⟨u, _, _, ⟨L, hL⟩, hue⟩ :=
    exists_contDiff_two_extension_halfDisk_of_tangent_dirichlet hr hrR hf hfi hg hfg hzero
      hα hα1 hDf hDg
  exact contDiffOn_succ_halfDisk_of_tangent_extension hrR
    (halfDisk_geometry (hr.trans hrR)).2.1 (halfDisk_geometry hr).2.2
    hf hfi hg hfg hα hDg hL hue

theorem contDiffOn_succ_halfDisk_of_neumann
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) {f g : ℂ → F} {n : ℕ}
    (hf : ContDiffOn ℝ (n + 1) f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hfi : ContDiffOn ℝ (n + 2) f {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (hg : ContDiffOn ℝ n g {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hfg : EqOn (Laplacian.laplacian f) g {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (hzero : ∀ x : ℝ, |x| ≤ R → fderivWithin ℝ f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} (x : ℂ) Complex.I = 0)
    {Kf Kg α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hDf : HolderOnWith Kf α (iteratedFDerivWithin ℝ (n + 1) f
      {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hDg : HolderOnWith Kg α (iteratedFDerivWithin ℝ n g
      {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) :
    ContDiffOn ℝ (n + 2) f {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} ∧
      ∃ C : ℝ≥0, HolderOnWith C α (iteratedFDerivWithin ℝ (n + 2) f
        {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im}) {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} := by
  obtain ⟨u, _, _, ⟨L, hL⟩, hue⟩ :=
    exists_contDiff_two_extension_halfDisk_of_tangent_neumann hr hrR hf hfi hg hfg hzero
      hα hα1 hDf hDg
  exact contDiffOn_succ_halfDisk_of_tangent_extension hrR
    (halfDisk_geometry (hr.trans hrR)).2.1 (halfDisk_geometry hr).2.2
    hf hfi hg hfg hα hDg hL hue

private theorem exists_holderOnWith_iteratedFDerivWithin_clm_comp
    {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {s : Set E} (hs : UniqueDiffOn 𝕜 s) {f : E → F} {n : ℕ}
    (hf : ContDiffOn 𝕜 n f s) {K α : ℝ≥0}
    (hD : HolderOnWith K α (iteratedFDerivWithin 𝕜 n f s) s) (L : F →L[𝕜] G) :
    ∃ C : ℝ≥0, HolderOnWith C α (iteratedFDerivWithin 𝕜 n (L ∘ f) s) s := by
  let A := ContinuousLinearMap.compContinuousMultilinearMapL 𝕜 (fun _ : Fin n => E) F G L
  have h := A.lipschitz.holderWith.comp_holderOnWith hD
  refine ⟨‖A‖₊ * K, ?_⟩
  intro x hx y hy
  rw [L.iteratedFDerivWithin_comp_left (hf x hx) hs hx le_rfl,
    L.iteratedFDerivWithin_comp_left (hf y hy) hs hy le_rfl]
  simpa only [Function.comp_def, one_mul, NNReal.coe_one, NNReal.rpow_one] using! h x hx y hy

theorem contDiffOn_succ_halfDisk_of_mixed_linear_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P Q : E →L[ℝ] E) (hPQ : P + Q = ContinuousLinearMap.id ℝ E)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) {f g : ℂ → E} {n : ℕ}
    (hf : ContDiffOn ℝ (n + 1) f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hfi : ContDiffOn ℝ (n + 2) f {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (hg : ContDiffOn ℝ n g {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hfg : EqOn (Laplacian.laplacian f) g {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (hdir : ∀ x : ℝ, |x| ≤ R → P (f (x : ℂ)) = 0)
    (hneu : ∀ x : ℝ, |x| ≤ R →
      Q (fderivWithin ℝ f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} (x : ℂ) Complex.I) = 0)
    {Kf Kg α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hDf : HolderOnWith Kf α (iteratedFDerivWithin ℝ (n + 1) f
      {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hDg : HolderOnWith Kg α (iteratedFDerivWithin ℝ n g
      {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) :
    ContDiffOn ℝ (n + 2) f {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} ∧
      ∃ C : ℝ≥0, HolderOnWith C α (iteratedFDerivWithin ℝ (n + 2) f
        {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im}) {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} := by
  let K : Set ℂ := {z | ‖z‖ ≤ R ∧ 0 ≤ z.im}
  let S : Set ℂ := {z | ‖z‖ < R ∧ 0 < z.im}
  let T : Set ℂ := {z | ‖z‖ ≤ r ∧ 0 ≤ z.im}
  have hKD : UniqueDiffOn ℝ K := (halfDisk_geometry (hr.trans hrR)).2.1
  have hTD : UniqueDiffOn ℝ T := (halfDisk_geometry hr).2.1
  have hSO : IsOpen S := (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hPDE (L : E →L[ℝ] E) : EqOn (Laplacian.laplacian (L ∘ f)) (L ∘ g) S := by
    intro z hz
    rw [((hfi z hz).contDiffAt (hSO.mem_nhds hz) |>.of_le
      (by norm_cast; omega)).laplacian_CLM_comp_left]
    exact congrArg L (hfg hz)
  obtain ⟨AP, hAP⟩ := exists_holderOnWith_iteratedFDerivWithin_clm_comp hKD hf hDf P
  obtain ⟨BP, hBP⟩ := exists_holderOnWith_iteratedFDerivWithin_clm_comp hKD hg hDg P
  obtain ⟨AQ, hAQ⟩ := exists_holderOnWith_iteratedFDerivWithin_clm_comp hKD hf hDf Q
  obtain ⟨BQ, hBQ⟩ := exists_holderOnWith_iteratedFDerivWithin_clm_comp hKD hg hDg Q
  obtain ⟨hP, CP, hDP⟩ := contDiffOn_succ_halfDisk_of_dirichlet
    hr hrR (hf.continuousLinearMap_comp P) (hfi.continuousLinearMap_comp P)
    (hg.continuousLinearMap_comp P) (hPDE P) hdir hα hα1 hAP hBP
  have hQnormal : ∀ x : ℝ, |x| ≤ R → fderivWithin ℝ (Q ∘ f) K (x : ℂ) Complex.I = 0 := by
    intro x hx
    have hxK : (x : ℂ) ∈ K := by simpa [K] using hx
    have hd : DifferentiableWithinAt ℝ f K (x : ℂ) := (hf _ hxK).differentiableWithinAt (by simp)
    have he := (Q.hasFDerivAt.comp_hasFDerivWithinAt _ hd.hasFDerivWithinAt).fderivWithin (hKD _ hxK)
    rw [he]
    exact hneu x hx
  obtain ⟨hQ, CQ, hDQ⟩ := contDiffOn_succ_halfDisk_of_neumann
    hr hrR (hf.continuousLinearMap_comp Q) (hfi.continuousLinearMap_comp Q)
    (hg.continuousLinearMap_comp Q) (hPDE Q) hQnormal hα hα1 hAQ hBQ
  have heq : (P ∘ f) + (Q ∘ f) = f := by
    funext x
    exact congrArg (fun L : E →L[ℝ] E => L (f x)) hPQ
  refine ⟨?_, CP + CQ, ?_⟩
  · rw [← heq]
    exact hP.add hQ
  have hsum := hDP.holderWith.add hDQ.holderWith
  intro x hx y hy
  rw [← heq, iteratedFDerivWithin_add_apply (hP x hx) (hQ x hx) hTD hx,
    iteratedFDerivWithin_add_apply (hP y hy) (hQ y hy) hTD hy]
  exact hsum ⟨x, hx⟩ ⟨y, hy⟩


private theorem firstJet_forcing_data
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {s t : Set E} (hs : IsCompact s) (hc : Convex ℝ s) (hsD : UniqueDiffOn ℝ s)
    (hst : s ⊆ t) {u : E → F} {n : ℕ}
    (hu : ContDiffOn ℝ (n + 1) u s) (hut : ContDiffOn ℝ 1 u t)
    {K α : ℝ≥0} (hα : 0 < α) (hα1 : α ≤ 1)
    (hjet : HolderOnWith K α (iteratedFDerivWithin ℝ (n + 1) u s) s)
    {Ω : Set (E × F × (E →L[ℝ] F))} (hΩ : IsOpen Ω)
    (huΩ : MapsTo (fun x => (x, u x, fderivWithin ℝ u t x)) t Ω)
    {A : (E × F × (E →L[ℝ] F)) → G} (hA : ContDiffOn ℝ (n + 1) A Ω) :
    let g := fun x => A (x, u x, fderivWithin ℝ u s x)
    ContDiffOn ℝ n g s ∧
      ∃ C : ℝ≥0, HolderOnWith C α (iteratedFDerivWithin ℝ n g s) s := by
  have hmap : MapsTo (fun x => (x, u x, fderivWithin ℝ u s x)) s Ω := by
    intro x hx
    change (x, u x, fderivWithin ℝ u s x) ∈ Ω
    rw [fderivWithin_subset hst (hsD x hx)
      ((hut x (hst hx)).differentiableWithinAt (by norm_num))]
    exact huΩ (hst hx)
  refine ⟨?_, Schauder.exists_holderOnWith_iteratedFDerivWithin_firstJet_comp
    hs hc hsD hu hα hα1 hjet hΩ hmap hA⟩
  apply (hA.of_le (by simp)).comp _ hmap
  exact contDiffOn_id.prodMk ((hu.of_le (by simp)).prodMk (hu.fderivWithin hsD le_rfl))


theorem contDiffOn_halfDisk_of_semilinear_mixed_boundary
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (P Q : F →L[ℝ] F) (hPQ : P + Q = ContinuousLinearMap.id ℝ F)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) {f : ℂ → F}
    (hf : ContDiffOn ℝ 1 f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hfi : ContDiffOn ℝ ∞ f {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    {K α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hDf : HolderOnWith K α (iteratedFDerivWithin ℝ 1 f
      {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    {Ω : Set (ℂ × F × (ℂ →L[ℝ] F))} (hΩ : IsOpen Ω)
    (hfΩ : MapsTo (fun x => (x, f x, fderivWithin ℝ f
      {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} x)) {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} Ω)
    {A : (ℂ × F × (ℂ →L[ℝ] F)) → F} (hA : ContDiffOn ℝ ∞ A Ω)
    (hfg : EqOn (Laplacian.laplacian f) (fun z => A (z, f z, fderiv ℝ f z))
      {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (hdir : ∀ x : ℝ, |x| ≤ R → P (f (x : ℂ)) = 0)
    (hneu : ∀ x : ℝ, |x| ≤ R →
      Q (fderivWithin ℝ f {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} (x : ℂ) Complex.I) = 0) :
    ContDiffOn ℝ ∞ f {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} ∧
      ∀ n : ℕ, ∃ C : ℝ≥0, HolderOnWith C α (iteratedFDerivWithin ℝ (n + 1) f
        {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im}) {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} := by
  let T : Set ℂ := {z | ‖z‖ ≤ R ∧ 0 ≤ z.im}
  have hTD : UniqueDiffOn ℝ T := (halfDisk_geometry (hr.trans hrR)).2.1
  have hreg (n : ℕ) : ∀ ρ : ℝ, 0 < ρ → ρ < R →
      ContDiffOn ℝ (n + 1) f {z : ℂ | ‖z‖ ≤ ρ ∧ 0 ≤ z.im} ∧
        ∃ C : ℝ≥0, HolderOnWith C α (iteratedFDerivWithin ℝ (n + 1) f
          {z : ℂ | ‖z‖ ≤ ρ ∧ 0 ≤ z.im}) {z : ℂ | ‖z‖ ≤ ρ ∧ 0 ≤ z.im} := by
    induction n with
    | zero =>
      intro ρ hρ hρR
      have hsub : {z : ℂ | ‖z‖ ≤ ρ ∧ 0 ≤ z.im} ⊆ T :=
        fun z hz => ⟨hz.1.trans hρR.le, hz.2⟩
      have hρD := (halfDisk_geometry hρ).2.1
      refine ⟨by simpa using hf.mono hsub, K, ?_⟩
      intro x hx y hy
      change edist (iteratedFDerivWithin ℝ 1 f _ x) (iteratedFDerivWithin ℝ 1 f _ y) ≤ _
      rw [iteratedFDerivWithin_subset hsub hρD hTD hf hx,
        iteratedFDerivWithin_subset hsub hρD hTD hf hy]
      exact hDf x (hsub hx) y (hsub hy)
    | succ n ih =>
      intro ρ hρ hρR
      let σ : ℝ := (ρ + R) / 2
      have hρσ : ρ < σ := by dsimp [σ]; linarith
      have hσR : σ < R := by dsimp [σ]; linarith
      have hσ : 0 < σ := hρ.trans hρσ
      obtain ⟨hfσ, C, hC⟩ := ih σ hσ hσR
      let S : Set ℂ := {z | ‖z‖ ≤ σ ∧ 0 ≤ z.im}
      have hsub : S ⊆ T := fun z hz => ⟨hz.1.trans hσR.le, hz.2⟩
      have hSC : Convex ℝ S := (halfDisk_geometry hσ).1
      have hSD : UniqueDiffOn ℝ S := (halfDisk_geometry hσ).2.1
      have hSK : IsCompact S := by
        apply (isCompact_closedBall (0 : ℂ) σ).of_isClosed_subset
          ((isClosed_le continuous_norm continuous_const).inter
            (isClosed_le continuous_const Complex.continuous_im))
        intro z hz
        simpa using hz.1
      let g := fun z => A (z, f z, fderivWithin ℝ f S z)
      obtain ⟨hg, D, hD⟩ := firstJet_forcing_data hSK hSC hSD hsub hfσ hf
        hα hα1.le hC hΩ hfΩ (hA.of_le (by norm_cast; exact le_top))
      have hSO : IsOpen {z : ℂ | ‖z‖ < σ ∧ 0 < z.im} :=
        (isOpen_lt continuous_norm continuous_const).inter
          (isOpen_lt continuous_const Complex.continuous_im)
      have hSi : {z : ℂ | ‖z‖ < σ ∧ 0 < z.im} ⊆
          {z : ℂ | ‖z‖ < R ∧ 0 < z.im} := fun z hz => ⟨hz.1.trans hσR, hz.2⟩
      have hIS : {z : ℂ | ‖z‖ < σ ∧ 0 < z.im} ⊆ S :=
        fun z hz => ⟨hz.1.le, hz.2.le⟩
      have hΔ : EqOn (Laplacian.laplacian f) g {z : ℂ | ‖z‖ < σ ∧ 0 < z.im} := by
        intro z hz
        dsimp only [g]
        rw [hfg (hSi hz), fderivWithin_eq_fderiv (hSD z (hIS hz))
          ((hfi z (hSi hz)).contDiffAt (mem_of_superset (hSO.mem_nhds hz) hSi)
            |>.differentiableAt (by simp))]
      have hN : ∀ x : ℝ, |x| ≤ σ → Q (fderivWithin ℝ f S (x : ℂ) Complex.I) = 0 := by
        intro x hx
        have hxS : (x : ℂ) ∈ S := by simpa [S] using hx
        rw [fderivWithin_subset hsub (hSD _ hxS)
          ((hf _ (hsub hxS)).differentiableWithinAt (by norm_num))]
        exact hneu x (hx.trans hσR.le)
      obtain ⟨hn, Dn, hDn⟩ := contDiffOn_succ_halfDisk_of_mixed_linear_boundary P Q hPQ hρ hρσ hfσ
        (by simpa only [Nat.cast_add, Nat.cast_ofNat] using
          (contDiffOn_infty.mp hfi (n + 2)).mono hSi) hg hΔ
        (fun x hx => hdir x (hx.trans hσR.le)) hN hα hα1 hC hD
      refine ⟨hn.of_le (by norm_cast), Dn, ?_⟩
      simpa [Nat.add_assoc] using hDn
  refine ⟨contDiffOn_infty.mpr (fun n => (hreg n r hr hrR).1.of_le (by simp)),
    fun n => (hreg n r hr hrR).2⟩

end DifferentialGeometry.Analysis
