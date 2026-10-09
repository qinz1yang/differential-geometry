import DifferentialGeometry.Analysis.Elliptic.Planar.CoordinateChange
import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.LocalCoordinates
import DifferentialGeometry.Analysis.Complex.Beltrami.Conformality

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

/-- The scalar factor of the pushed principal matrix in determinant-one
isothermal coordinates; it depends on the coefficient and chart alone. -/
def planarIsothermalFactor (A : Matrix (Fin 2) (Fin 2) ℝ) (L : ℂ →L[ℝ] ℂ) : ℝ :=
  Complex.normSq (L 1) / A 1 1

/-- The Beltrami law for determinant-one conductivity gives the full bilinear
principal contraction. Symmetry of the test Hessian is unnecessary. -/
theorem planar_principal_contraction_of_beltrami
    (A : Matrix (Fin 2) (Fin 2) ℝ) (L : ℂ →L[ℝ] ℂ)
    (hA : A.PosDef) (hdet : A.det = 1)
    (hBel : complexAntilinearPart L =
      beltramiCoefficient (A 1 1) (A 0 0) (-A 0 1) * complexLinearPart L)
    (H : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) :
    (∑ i : Fin 2, ∑ j : Fin 2, A i j *
      H (L ((![1, Complex.I] : Fin 2 → ℂ) i))
        (L ((![1, Complex.I] : Fin 2 → ℂ) j))) =
      planarIsothermalFactor A L * (H 1 1 + H Complex.I Complex.I) := by
  have hcross : A 1 0 = A 0 1 :=
    (Matrix.isHermitian_iff_isSymm.mp hA.isHermitian).apply 0 1
  have hb : 0 < A 1 1 := hA.diag_pos
  have hd : A 1 1 * A 0 0 - (-A 0 1) ^ 2 = 1 := by
    rw [Matrix.det_fin_two, hcross] at hdet
    nlinarith only [hdet]
  have hcols : L 1 + Complex.I * L Complex.I =
      beltramiCoefficient (A 1 1) (A 0 0) (-A 0 1) *
        (L 1 - Complex.I * L Complex.I) := by
    rw [complexAntilinearPart, complexLinearPart, ← mul_div_assoc] at hBel
    exact (div_left_inj' (by norm_num : (2 : ℂ) ≠ 0)).mp hBel
  have hLI : L Complex.I = (((-A 0 1 : ℝ) : ℂ) + Complex.I) / (A 1 1 : ℝ) * L 1 := by
    have hh := (beltrami_eq_iff_metric_columns hb (by rw [hd]; norm_num)
      (L 1) (L Complex.I)).mp hcols
    simpa only [hd, Real.sqrt_one, Complex.ofReal_one, one_mul] using hh
  have hreal : (L Complex.I).re = (-A 0 1 * (L 1).re - (L 1).im) / A 1 1 := by
    rw [hLI]
    simp only [Complex.mul_re, Complex.div_ofReal_re, Complex.div_ofReal_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, add_zero, zero_add]
    ring
  have himag : (L Complex.I).im = ((L 1).re - A 0 1 * (L 1).im) / A 1 1 := by
    rw [hLI]
    simp only [Complex.mul_im, Complex.div_ofReal_re, Complex.div_ofReal_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, add_zero, zero_add]
    ring
  have haa : A 0 0 = (1 + (A 0 1) ^ 2) / A 1 1 :=
    (eq_div_iff hb.ne').mpr (by nlinarith only [hd])
  have hdecomp (z : ℂ) : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  have hH (z t : ℂ) : H z t =
      z.re * t.re * H 1 1 + z.re * t.im * H 1 Complex.I +
        z.im * t.re * H Complex.I 1 + z.im * t.im * H Complex.I Complex.I := by
    calc
      H z t = H (z.re • (1 : ℂ) + z.im • Complex.I)
          (t.re • (1 : ℂ) + t.im • Complex.I) := by rw [← hdecomp z, ← hdecomp t]
      _ = _ := by simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]; ring
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [hH (L 1) (L 1), hH (L 1) (L Complex.I),
    hH (L Complex.I) (L 1), hH (L Complex.I) (L Complex.I)]
  simp only [hcross, haa, hreal, himag, planarIsothermalFactor, Complex.normSq_apply]
  field_simp [hb.ne']
  ring

theorem planarIsothermalFactor_pos
    {A : Matrix (Fin 2) (Fin 2) ℝ} {L : ℂ →L[ℝ] ℂ}
    (hA : A.PosDef) (hL : Function.Injective L) : 0 < planarIsothermalFactor A L := by
  have hne : L 1 ≠ 0 := by
    intro hh
    apply one_ne_zero (α := ℂ)
    exact hL (by simpa only [map_zero] using hh)
  exact div_pos (Complex.normSq_pos.mpr hne) hA.diag_pos

/-- Existing smooth determinant-one coordinates supply the exact principal
contraction required by the full scalar coordinate-change theorem. -/
theorem exists_local_scalar_principal_coordinates
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) Ω)
    (hpos : ∀ x ∈ Ω, (A x).PosDef) (hdet : ∀ x ∈ Ω, (A x).det = 1)
    {p : ℂ} (hp : p ∈ Ω) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, p ∈ e.source ∧ e.source ⊆ Ω ∧ e p = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      let lam : ℂ → ℝ := fun x => planarIsothermalFactor (A x) (fderiv ℝ e x)
      (∀ x ∈ e.source, 0 < lam x) ∧
      ∀ x ∈ e.source, ∀ H : ℂ →L[ℝ] ℂ →L[ℝ] ℝ,
        (∑ i : Fin 2, ∑ j : Fin 2, A x i j *
          H (fderiv ℝ e x ((![1, Complex.I] : Fin 2 → ℂ) i))
            (fderiv ℝ e x ((![1, Complex.I] : Fin 2 → ℂ) j))) =
          lam x * (H 1 1 + H Complex.I Complex.I) := by
  obtain ⟨e, hep, heΩ, he0, he, hei, hedet, heBel⟩ :=
    exists_local_isothermal_coordinates hΩ A hA hpos hdet hp
  refine ⟨e, hep, heΩ, he0, he, hei, ?_, ?_⟩
  · intro x hx
    apply planarIsothermalFactor_pos (hpos x (heΩ hx))
    simpa only [Function.Injective, LinearMap.equivOfIsUnitDet_apply] using!
      ((fderiv ℝ e x).toLinearMap.equivOfIsUnitDet
        (isUnit_iff_ne_zero.mpr (hedet x hx).ne')).injective
  · intro x hx H
    exact planar_principal_contraction_of_beltrami (A x) (fderiv ℝ e x)
      (hpos x (heΩ hx)) (hdet x (heΩ hx)) (heBel x hx) H

/-- Smoothness of the explicit principal factor wherever the denominator is positive. -/
theorem contDiffOn_planarIsothermalFactor
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {A : ℂ → Matrix (Fin 2) (Fin 2) ℝ} {e : ℂ → ℂ}
    (hA : ContDiffOn ℝ ∞ (fun x => A x 1 1) Ω)
    (he : ContDiffOn ℝ ∞ e Ω) (hpos : ∀ x ∈ Ω, 0 < A x 1 1) :
    ContDiffOn ℝ ∞ (fun x => planarIsothermalFactor (A x) (fderiv ℝ e x)) Ω := by
  have hd := (he.fderiv_of_isOpen (m := ∞) hΩ (by simp)).clm_apply
    (contDiffOn_const (c := (1 : ℂ)))
  have hr := Complex.reCLM.contDiff.comp_contDiffOn hd
  have hi := Complex.imCLM.contDiff.comp_contDiffOn hd
  simpa only [planarIsothermalFactor, Complex.normSq_apply, pow_two] using!
    ((hr.mul hr).add (hi.mul hi)).div hA (fun x hx => (hpos x hx).ne')

/-- Normalizing a smooth positive definite planar matrix and reusing the existing
isothermal coordinate theorem gives a smooth positive scalar principal factor. -/
theorem exists_local_scalar_principal_coordinates_of_posDef
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) Ω)
    (hpos : ∀ x ∈ Ω, (A x).PosDef) {p : ℂ} (hp : p ∈ Ω) :
    ∃ (e : OpenPartialHomeomorph ℂ ℂ) (lam : ℂ → ℝ),
      p ∈ e.source ∧ e.source ⊆ Ω ∧ e p = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ContDiffOn ℝ ∞ lam e.source ∧ (∀ x ∈ e.source, 0 < lam x) ∧
      ∀ x ∈ e.source, ∀ H : ℂ →L[ℝ] ℂ →L[ℝ] ℝ,
        (∑ i : Fin 2, ∑ j : Fin 2, A x i j *
          H (fderiv ℝ e x ((![1, Complex.I] : Fin 2 → ℂ) i))
            (fderiv ℝ e x ((![1, Complex.I] : Fin 2 → ℂ) j))) =
          lam x * (H 1 1 + H Complex.I Complex.I) := by
  let B : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun x =>
    planarConductivity (A x 1 1) (A x 0 0) (-A x 0 1)
  let d : ℂ → ℝ := fun x => Real.sqrt (A x 1 1 * A x 0 0 - (-A x 0 1) ^ 2)
  have hcross (x : ℂ) (hx : x ∈ Ω) : A x 1 0 = A x 0 1 :=
    (Matrix.isHermitian_iff_isSymm.mp (hpos x hx).isHermitian).apply 0 1
  have hdet (x : ℂ) (hx : x ∈ Ω) : 0 < A x 1 1 * A x 0 0 - (-A x 0 1) ^ 2 := by
    have hh := (hpos x hx).det_pos
    rw [Matrix.det_fin_two, hcross x hx] at hh
    nlinarith only [hh]
  have hdpos (x : ℂ) (hx : x ∈ Ω) : 0 < d x := Real.sqrt_pos.mpr (hdet x hx)
  have hd : ContDiffOn ℝ ∞ d Ω :=
    (((hA 1 1).mul (hA 0 0)).sub ((hA 0 1).neg.pow 2)).sqrt
      (fun x hx => (hdet x hx).ne')
  have hB (i j : Fin 2) : ContDiffOn ℝ ∞ (fun x => B x i j) Ω :=
    contDiffOn_planarConductivity (hA 1 1) (hA 0 0) (hA 0 1).neg hdet i j
  have hBp (x : ℂ) (hx : x ∈ Ω) : (B x).PosDef :=
    planarConductivity_posDef (hpos x hx).diag_pos (hdet x hx)
  have hBd (x : ℂ) (hx : x ∈ Ω) : (B x).det = 1 :=
    det_planarConductivity (hdet x hx)
  have hAB (x : ℂ) (hx : x ∈ Ω) (i j : Fin 2) : A x i j = d x * B x i j := by
    have hn := (hdpos x hx).ne'
    have hs : Real.sqrt (A x 1 1 * A x 0 0 - (A x 0 1) ^ 2) ≠ 0 := by
      simpa only [d, neg_sq] using hn
    fin_cases i <;> fin_cases j <;>
      simp [B, planarConductivity, d, hcross x hx, hs]
  obtain ⟨e, hep, heΩ, he0, he, hei, hfactor, hprincipal⟩ :=
    exists_local_scalar_principal_coordinates hΩ B hB hBp hBd hp
  let lam : ℂ → ℝ := fun x => d x * planarIsothermalFactor (B x) (fderiv ℝ e x)
  refine ⟨e, lam, hep, heΩ, he0, he, hei, ?_, ?_, ?_⟩
  · exact (hd.mono heΩ).mul
      (contDiffOn_planarIsothermalFactor e.open_source ((hB 1 1).mono heΩ) he
        (fun x hx => (hBp x (heΩ hx)).diag_pos))
  · intro x hx
    exact mul_pos (hdpos x (heΩ hx)) (hfactor x hx)
  · intro x hx H
    simp_rw [hAB x (heΩ hx), mul_assoc, ← Finset.mul_sum]
    rw [hprincipal x hx H]
    exact (mul_assoc _ _ _).symm

/-- Every smooth positive planar scalar equation has local smooth isothermal
coordinates for its full equation. Drift and potential remain explicit and smooth,
and the original scalar map and zero set are carried by this very coordinate map. -/
theorem exists_local_isothermal_scalar_equation
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (beta : ℂ → Fin 2 → ℝ) (c w : ℂ → ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) Ω)
    (hbeta : ∀ i, ContDiffOn ℝ ∞ (fun x => beta x i) Ω)
    (hc : ContDiffOn ℝ ∞ c Ω) (hw : ContDiffOn ℝ ∞ w Ω)
    (hpos : ∀ x ∈ Ω, (A x).PosDef)
    (hpde : ∀ x ∈ Ω, planarScalarOperator A beta c w x = 0)
    {p : ℂ} (hp : p ∈ Ω) :
    ∃ (e : OpenPartialHomeomorph ℂ ℂ) (lam : ℂ → ℝ),
      p ∈ e.source ∧ e.source ⊆ Ω ∧ e p = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ContDiffOn ℝ ∞ lam e.source ∧ (∀ x ∈ e.source, 0 < lam x) ∧
      let v : ℂ → ℝ := fun y => w (e.symm y)
      let drift : ℂ → ℂ := fun y => (lam (e.symm y))⁻¹ •
        planarCoordinateDrift A beta e (e.symm y)
      let potential : ℂ → ℝ := fun y => c (e.symm y) / lam (e.symm y)
      ContDiffOn ℝ ∞ v e.target ∧ ContDiffOn ℝ ∞ drift e.target ∧
      ContDiffOn ℝ ∞ potential e.target ∧
      (∀ y ∈ e.target,
        Laplacian.laplacian v y + fderiv ℝ v y (drift y) + potential y * v y = 0) ∧
      (∀ x ∈ e.source, v (e x) = w x) ∧
      e.target ∩ v ⁻¹' ({0} : Set ℝ) = e '' (e.source ∩ w ⁻¹' ({0} : Set ℝ)) := by
  obtain ⟨e, lam, hep, heΩ, he0, he, hei, hlam, hlampos, hprincipal⟩ :=
    exists_local_scalar_principal_coordinates_of_posDef hΩ A hA hpos hp
  have hresult := planarScalarOperator_eq_zero_in_isothermal_coordinates
    A beta c w e lam ((hw.mono heΩ).of_le (by simp)) (he.of_le (by simp))
    (hei.of_le (by simp)) hlampos hprincipal (fun x hx => hpde x (heΩ hx))
  have hB : ContDiffOn ℝ ∞ (planarCoordinateDrift A beta e) e.source :=
    contDiffOn_planarCoordinateDrift e.open_source
      (fun i j => (hA i j).mono heΩ) (fun i => (hbeta i).mono heΩ) he
  refine ⟨e, lam, hep, heΩ, he0, he, hei, hlam, hlampos, ?_, ?_, ?_, hresult.2⟩
  · exact (hw.mono heΩ).comp hei (fun y hy => e.map_target hy)
  · exact ((hlam.inv (fun x hx => (hlampos x hx).ne')).smul hB).comp hei
      (fun y hy => e.map_target hy)
  · exact ((hc.mono heΩ).div hlam (fun x hx => (hlampos x hx).ne')).comp hei
      (fun y hy => e.map_target hy)

end DifferentialGeometry.Analysis
