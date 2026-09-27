import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.TangentialRegularity
import DifferentialGeometry.Analysis.Complex.ConformalGradientHolder
import DifferentialGeometry.Analysis.Complex.ConformalBoundary

noncomputable section
open Set Filter Metric InnerProductSpace
open scoped Topology ContDiff NNReal
namespace DifferentialGeometry.Analysis

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

private theorem contDiffOn_one_and_holder_halfDisk_of_conformal_transverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : ℂ → E} (l : E →L[ℝ] ℝ) (t : E) {R β : ℝ} (hR : 0 < R) (hβ : 0 ≤ β)
    (hX : ContinuousOn X {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hXi : ContDiffOn ℝ ∞ X {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (htrace : ∀ z : ℂ, ‖z‖ ≤ R → z.im = 0 → X z - l (X z) • t = 0)
    (hΔ : ∀ z : ℂ, ‖z‖ < R → 0 < z.im →
      ‖Laplacian.laplacian (fun w => X w - l (X w) • t) z‖ ≤
        β * ‖fderiv ℝ (fun w => X w - l (X w) • t) z‖ ^ 2)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {Ω : Set E} (hΩ : IsOpen Ω)
    (hB : ContDiffOn ℝ 1 B Ω) (hXs : MapsTo X {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} Ω)
    (hBs : ∀ x ∈ Ω, (B x).toBilinForm.IsSymm)
    (hBt : ∀ z ∈ {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}, 0 < B (X z) t t)
    (ho : ∀ z ∈ {z : ℂ | ‖z‖ < R ∧ 0 < z.im},
      B (X z) (fderiv ℝ X z 1) (fderiv ℝ X z Complex.I) = 0)
    (he : ∀ z ∈ {z : ℂ | ‖z‖ < R ∧ 0 < z.im},
      B (X z) (fderiv ℝ X z 1) (fderiv ℝ X z 1) =
        B (X z) (fderiv ℝ X z Complex.I) (fderiv ℝ X z Complex.I)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < R ∧
      ContDiffOn ℝ 1 X {z : ℂ | ‖z‖ ≤ ρ ∧ 0 ≤ z.im} ∧
      ∃ C : ℝ≥0, HolderOnWith C (1 / 4) (fderivWithin ℝ X
        {z : ℂ | ‖z‖ ≤ ρ ∧ 0 ≤ z.im}) {z : ℂ | ‖z‖ ≤ ρ ∧ 0 ≤ z.im} := by
  let Y := fun z => X z - l (X z) • t
  let K : Set ℂ := {z | ‖z‖ ≤ R ∧ 0 ≤ z.im}
  let S : Set ℂ := {z | ‖z‖ < R ∧ 0 < z.im}
  have hSO : IsOpen S := (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hYi : ∀ z : ℂ, ‖z‖ < R → 0 < z.im → ContDiffAt ℝ 2 Y z := by
    intro z hz hi
    have hd : ContDiffAt ℝ 2 X z :=
      ((contDiffOn_infty.mp hXi 2).contDiffAt (hSO.mem_nhds ⟨hz, hi⟩))
    exact hd.sub ((l.contDiff.contDiffAt.comp z hd).smul contDiffAt_const)
  obtain ⟨ρ, hρ, hρR, u, C, hu, hDu, hue⟩ :=
    exists_contDiff_one_extension_of_norm_laplacian_le_mul_norm_fderiv_sq hR hβ
      (hX.sub ((l.continuous.comp_continuousOn hX).smul continuousOn_const)) hYi hΔ htrace
      (α := 1 / 2) (by norm_num) (by norm_num)
  let Kρ : Set ℂ := {z | ‖z‖ ≤ ρ ∧ 0 ≤ z.im}
  let Sρ : Set ℂ := {z | ‖z‖ < ρ ∧ 0 < z.im}
  have hKD : UniqueDiffOn ℝ Kρ := (halfDisk_geometry hρ).2.1
  have hcl : closure Sρ = Kρ := (halfDisk_geometry hρ).2.2
  have hKsub : Kρ ⊆ K := fun z hz => ⟨hz.1.trans hρR.le, hz.2⟩
  have hSsub : Sρ ⊆ S := fun z hz => ⟨hz.1.trans hρR, hz.2⟩
  have hSρO : IsOpen Sρ := (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hSρC : Convex ℝ Sρ := by
    have hs : Sρ = ball (0 : ℂ) ρ ∩ {z : ℂ | 0 < z.im} := by ext z; simp [Sρ]
    rw [hs]
    exact (convex_ball (0 : ℂ) ρ).inter (convex_halfSpace_im_gt 0)
  have hKcompact : IsCompact Kρ := by
    apply (isCompact_closedBall (0 : ℂ) ρ).of_isClosed_subset
      ((isClosed_le continuous_norm continuous_const).inter
        (isClosed_le continuous_const Complex.continuous_im))
    intro z hz
    simpa using hz.1
  change EqOn u Y Kρ at hue
  have hY : ContDiffOn ℝ 1 Y Kρ := hu.contDiffOn.congr hue.symm
  have hYH : HolderOnWith C (1 / 2) (fderivWithin ℝ Y Kρ) Kρ := by
    have hder (z : ℂ) (hz : z ∈ Kρ) : fderivWithin ℝ Y Kρ z = fderiv ℝ u z := by
      rw [fderivWithin_congr hue.symm (hue hz).symm]
      exact (hu.differentiable (by norm_num) z).fderivWithin (hKD z hz)
    intro x hx y hy
    rw [hder x hx, hder y hy]
    exact hDu x y
  have hrec := contDiffOn_one_closure_and_holderOnWith_of_conformal_transverse
    hSρC hSρO (by rwa [hcl])
    (f := fun z => l (X z)) (t := t)
    (by rw [hcl]; exact l.continuous.comp_continuousOn (hX.mono hKsub))
    (l.contDiff.comp_contDiffOn ((contDiffOn_infty.mp hXi 1).mono hSsub))
    (by rwa [hcl]) hΩ hB (by rw [hcl]; exact hXs.mono hKsub (Subset.refl _)) hBs
    (by rw [hcl]; exact fun z hz => hBt z (hKsub hz))
    (by norm_num : (0 : ℝ≥0) < 1 / 2) (by norm_num) (by rwa [hcl])
    (fun z hz => ho z (hSsub hz)) (fun z hz => he z (hSsub hz))
  rw [hcl] at hrec
  obtain ⟨_, hXC, D, hD⟩ := hrec
  refine ⟨ρ, hρ, hρR, hXC, D, ?_⟩
  norm_num at hD ⊢
  exact hD

theorem exists_contDiffOn_halfDisk_of_conformal_transverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : ℂ → E} (l : E →L[ℝ] ℝ) (t : E) {R β : ℝ} (hR : 0 < R) (hβ : 0 ≤ β)
    (hX : ContinuousOn X {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im})
    (hXi : ContDiffOn ℝ ∞ X {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (htrace : ∀ z : ℂ, ‖z‖ ≤ R → z.im = 0 → X z - l (X z) • t = 0)
    (hΔ : ∀ z : ℂ, ‖z‖ < R → 0 < z.im →
      ‖Laplacian.laplacian (fun w => X w - l (X w) • t) z‖ ≤
        β * ‖fderiv ℝ (fun w => X w - l (X w) • t) z‖ ^ 2)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {Ω : Set E} (hΩ : IsOpen Ω)
    (hB : ContDiffOn ℝ 1 B Ω) (hXs : MapsTo X {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} Ω)
    (hBp : ∀ x ∈ Ω, LinearMap.IsPosSemidef (B x).toBilinForm)
    (hBt : ∀ z ∈ {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}, 0 < B (X z) t t)
    (hBa : ∀ x : ℝ, |x| ≤ R → ∀ v : E,
      B (X (x : ℂ)) t v = B (X (x : ℂ)) t t * l v)
    (ho : ∀ z ∈ {z : ℂ | ‖z‖ < R ∧ 0 < z.im},
      B (X z) (fderiv ℝ X z 1) (fderiv ℝ X z Complex.I) = 0)
    (he : ∀ z ∈ {z : ℂ | ‖z‖ < R ∧ 0 < z.im},
      B (X z) (fderiv ℝ X z 1) (fderiv ℝ X z 1) =
        B (X z) (fderiv ℝ X z Complex.I) (fderiv ℝ X z Complex.I))
    {F : (E × (ℂ →L[ℝ] E)) → E} (hF : ContDiffOn ℝ ∞ F (Ω ×ˢ univ))
    (hPDE : EqOn (Laplacian.laplacian X) (fun z => F (X z, fderiv ℝ X z))
      {z : ℂ | ‖z‖ < R ∧ 0 < z.im}) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < R ∧
      ContDiffOn ℝ ∞ X {z : ℂ | ‖z‖ ≤ ρ ∧ 0 ≤ z.im} := by
  obtain ⟨ρ, hρ, hρR, hXC, C, hDC⟩ :=
    contDiffOn_one_and_holder_halfDisk_of_conformal_transverse l t hR hβ hX hXi htrace hΔ
      hΩ hB hXs (fun x hx => LinearMap.BilinForm.isSymm_iff.mpr (hBp x hx).1) hBt ho he
  let K : Set ℂ := {z | ‖z‖ ≤ ρ ∧ 0 ≤ z.im}
  let S : Set ℂ := {z | ‖z‖ < ρ ∧ 0 < z.im}
  let T : Set ℂ := {z | ‖z‖ ≤ ρ / 2 ∧ 0 ≤ z.im}
  have hhalf : 0 < ρ / 2 := half_pos hρ
  have hquarter : 0 < ρ / 4 := by positivity
  have hqr : ρ / 4 < ρ / 2 := by linarith
  have hSO : IsOpen S := (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hKD : UniqueDiffOn ℝ K := (halfDisk_geometry hρ).2.1
  have hTD : UniqueDiffOn ℝ T := (halfDisk_geometry hhalf).2.1
  have hcl : closure S = K := (halfDisk_geometry hρ).2.2
  have hTK : T ⊆ K := fun z hz => ⟨hz.1.trans (by linarith), hz.2⟩
  have hKR : K ⊆ {z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im} :=
    fun z hz => ⟨hz.1.trans hρR.le, hz.2⟩
  have hTR := hTK.trans hKR
  let Q : E →L[ℝ] E := l.smulRight t
  let P : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - Q
  have hPQ : P + Q = ContinuousLinearMap.id ℝ E := sub_add_cancel _ _
  have hN : ∀ x : ℝ, |x| ≤ ρ / 2 → Q (fderivWithin ℝ X T (x : ℂ) Complex.I) = 0 := by
    intro x hx
    have hxT : (x : ℂ) ∈ T := by simpa [T] using hx
    have hxK := hTK hxT
    have hxi : x ∈ Ioo (-ρ) ρ := by
      have hle := abs_le.mp hx
      constructor <;> linarith
    have hseg : ∀ r ∈ Ioo (-ρ) ρ, (r : ℂ) ∈ closure S := by
      intro r hr
      rw [hcl]
      change ‖(r : ℂ)‖ ≤ ρ ∧ 0 ≤ (r : ℂ).im
      have har : |r| ≤ ρ := abs_le.mpr ⟨hr.1.le, hr.2.le⟩
      simpa using har
    have hscalar := fderivWithin_normal_eq_zero_of_conformal_interior hSO
      (by rwa [hcl]) (by rwa [hcl]) hxi hseg
      (l := l) (t := t) (fun r hr => htrace (r : ℂ)
        (by have hrK := hseg r hr; rw [hcl] at hrK; exact (hKR hrK).1) (by simp))
      (hB.continuousOn.mono (by
        rintro y ⟨z, hz, rfl⟩
        rw [hcl] at hz
        exact hXs (hKR hz)))
      (hBp _ (hXs (hKR hxK))) (hBt _ (hKR hxK)).ne'
      (hBa x ((hx.trans (by linarith : ρ / 2 ≤ ρ)).trans hρR.le))
      (fun z hz => ho z ⟨hz.1.trans hρR, hz.2⟩)
      (fun z hz => he z ⟨hz.1.trans hρR, hz.2⟩)
    rw [hcl] at hscalar
    have hL : fderivWithin ℝ (fun z => l (X z)) K (x : ℂ) =
        l.comp (fderivWithin ℝ X K (x : ℂ)) :=
      (l.hasFDerivAt.comp_hasFDerivWithinAt _
        ((hXC _ hxK).differentiableWithinAt (by norm_num)).hasFDerivWithinAt).fderivWithin
        (hKD _ hxK)
    rw [hL] at hscalar
    change l (fderivWithin ℝ X K (x : ℂ) Complex.I) = 0 at hscalar
    rw [fderivWithin_subset hTK (hTD _ hxT)
      ((hXC _ hxK).differentiableWithinAt (by norm_num))]
    change l (fderivWithin ℝ X K (x : ℂ) Complex.I) • t = 0
    rw [hscalar, zero_smul]
  have hDT : HolderOnWith C (1 / 4) (iteratedFDerivWithin ℝ 1 X T) T := by
    have hD (z : ℂ) (hz : z ∈ T) : fderivWithin ℝ X T z = fderivWithin ℝ X K z :=
      fderivWithin_subset hTK (hTD z hz) ((hXC z (hTK hz)).differentiableWithinAt (by norm_num))
    intro x hx y hy
    simpa only [edist_dist, dist_iteratedFDerivWithin_one X X (hTD x hx) (hTD y hy), hD x hx, hD y hy]
      using hDC x (hTK hx) y (hTK hy)
  let U : Set (ℂ × E × (ℂ →L[ℝ] E)) := univ ×ˢ (Ω ×ˢ univ)
  have hU : IsOpen U := isOpen_univ.prod (hΩ.prod isOpen_univ)
  have hFU : ContDiffOn ℝ ∞ (fun p : ℂ × E × (ℂ →L[ℝ] E) => F p.2) U :=
    hF.comp contDiffOn_snd (fun p hp => hp.2)
  have hTI : {z : ℂ | ‖z‖ < ρ / 2 ∧ 0 < z.im} ⊆
      {z : ℂ | ‖z‖ < R ∧ 0 < z.im} :=
    fun z hz => ⟨hz.1.trans (by linarith), hz.2⟩
  obtain ⟨hnew, _⟩ := contDiffOn_halfDisk_of_semilinear_mixed_boundary P Q hPQ hquarter hqr
    (hXC.mono hTK) (hXi.mono hTI) (by norm_num : (0 : ℝ≥0) < 1 / 4) (by norm_num) hDT
    hU (fun z hz => ⟨mem_univ _, hXs (hTR hz), mem_univ _⟩) hFU (hPDE.mono hTI)
    (fun x hx => by
      change X (x : ℂ) - l (X (x : ℂ)) • t = 0
      exact htrace (x : ℂ) (by simpa using hx.trans (by linarith : ρ / 2 ≤ R)) (by simp)) hN
  exact ⟨ρ / 4, hquarter, by linarith, hnew⟩

end DifferentialGeometry.Analysis
