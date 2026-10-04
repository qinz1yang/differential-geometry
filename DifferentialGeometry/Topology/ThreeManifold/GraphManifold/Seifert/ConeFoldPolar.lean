import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldShapeBridges
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsCornerMaps
import DifferentialGeometry.Compat.Ch567.Tensor.LinearAlgebra.ComplexDeterminant

/-!
# Half-angle arguments and Jacobians of polar maps

Lane A4, tier 2 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §5).
For a point `R + iI` of modulus `S > 0`, `halfArg S R I = 2 arctan (I/(S + R))` is its argument
in `(-π, π)` (off the negative axis, `halfArg_polar`), and `negHalfArg S R I = π - 2 arctan
(I/(S - R))` its argument in `(0, 2π)` (off the positive axis). Both are explicit smooth
functions of `(R, I)`, and along a curve of constant modulus their derivative is `-R'/I` off the
real axis and `I'/S`, resp. `-I'/S`, on it (`halfArg_deriv_off`, `halfArg_deriv_on`,
`negHalfArg_deriv_off`, `negHalfArg_deriv_on`); this replaces K16f's `arctan (I/R)`, which needs
`R > 0`.

`det_mul_cross` is the multiplicativity of the real determinant of an `ℝ`-linear map of `ℂ` on two
vectors; `det_fderiv_polar` computes the Jacobian of `c + S(ρ) e^{iΘ}` from a curve along which
`ρ` is constant: it is `S S' a b / (N × V)` with `a` the derivative of `Θ` along the curve
(velocity `V`) and `b` the derivative of `ρ` in a transversal direction `N`. In particular the
Jacobian is nonzero when `S'`, `a`, `b` are (the triangular blends of design §5).
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped ComplexConjugate ContDiff

namespace GC.Seifert

def halfArg (S R J : ℝ) : ℝ := 2 * Real.arctan (J / (S + R))

def negHalfArg (S R J : ℝ) : ℝ := Real.pi - 2 * Real.arctan (J / (S - R))

theorem cos_two_arctan (t : ℝ) : Real.cos (2 * Real.arctan t) = (1 - t ^ 2) / (1 + t ^ 2) := by
  rw [Real.cos_two_mul, Real.cos_arctan]
  have h : 0 < 1 + t ^ 2 := by positivity
  rw [div_pow, Real.sq_sqrt h.le]
  field_simp
  ring

theorem sin_two_arctan (t : ℝ) : Real.sin (2 * Real.arctan t) = 2 * t / (1 + t ^ 2) := by
  rw [Real.sin_two_mul, Real.cos_arctan, Real.sin_arctan]
  have h : 0 < 1 + t ^ 2 := by positivity
  have hs := Real.sq_sqrt h.le
  have hs0 : Real.sqrt (1 + t ^ 2) ≠ 0 := (Real.sqrt_pos.2 h).ne'
  field_simp
  rw [hs]

theorem halfArg_cos {S R J : ℝ} (hS : 0 < S) (hSR : 0 < S + R) (h : R ^ 2 + J ^ 2 = S ^ 2) :
    Real.cos (halfArg S R J) = R / S := by
  rw [halfArg, cos_two_arctan]
  have hI : J ^ 2 = (S - R) * (S + R) := by linarith
  field_simp
  linear_combination (-(S + R)) * hI

theorem halfArg_sin {S R J : ℝ} (hS : 0 < S) (hSR : 0 < S + R) (h : R ^ 2 + J ^ 2 = S ^ 2) :
    Real.sin (halfArg S R J) = J / S := by
  rw [halfArg, sin_two_arctan]
  have hI : J ^ 2 = (S - R) * (S + R) := by linarith
  field_simp
  linear_combination (-J) * hI

theorem negHalfArg_cos {S R J : ℝ} (hS : 0 < S) (hSR : 0 < S - R) (h : R ^ 2 + J ^ 2 = S ^ 2) :
    Real.cos (negHalfArg S R J) = R / S := by
  rw [negHalfArg, Real.cos_pi_sub, cos_two_arctan]
  have hI : J ^ 2 = (S - R) * (S + R) := by linarith
  field_simp
  linear_combination (S - R) * hI

theorem negHalfArg_sin {S R J : ℝ} (hS : 0 < S) (hSR : 0 < S - R) (h : R ^ 2 + J ^ 2 = S ^ 2) :
    Real.sin (negHalfArg S R J) = J / S := by
  rw [negHalfArg, Real.sin_pi_sub, sin_two_arctan]
  have hI : J ^ 2 = (S - R) * (S + R) := by linarith
  field_simp
  linear_combination (-J) * hI

theorem polar_of_cos_sin {S R J θ : ℝ} (hS : 0 < S) (hc : Real.cos θ = R / S)
    (hs : Real.sin θ = J / S) : (⟨R, J⟩ : ℂ) = (S : ℂ) * exp ((θ : ℂ) * I) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  apply Complex.ext
  · simp only [mul_re, ofReal_re, ofReal_im, add_re, I_re, I_im]
    rw [hc]
    field_simp
    ring
  · simp only [mul_im, ofReal_re, ofReal_im, add_im, I_re, I_im]
    rw [hs]
    field_simp
    ring

theorem halfArg_polar {S R J : ℝ} (hS : 0 < S) (hSR : 0 < S + R) (h : R ^ 2 + J ^ 2 = S ^ 2) :
    (⟨R, J⟩ : ℂ) = (S : ℂ) * exp ((halfArg S R J : ℂ) * I) :=
  polar_of_cos_sin hS (halfArg_cos hS hSR h) (halfArg_sin hS hSR h)

theorem negHalfArg_polar {S R J : ℝ} (hS : 0 < S) (hSR : 0 < S - R)
    (h : R ^ 2 + J ^ 2 = S ^ 2) :
    (⟨R, J⟩ : ℂ) = (S : ℂ) * exp ((negHalfArg S R J : ℂ) * I) :=
  polar_of_cos_sin hS (negHalfArg_cos hS hSR h) (negHalfArg_sin hS hSR h)

theorem halfArg_mem (S R J : ℝ) : halfArg S R J ∈ Set.Ioo (-Real.pi) Real.pi := by
  have h1 := Real.neg_pi_div_two_lt_arctan (J / (S + R))
  have h2 := Real.arctan_lt_pi_div_two (J / (S + R))
  constructor <;> unfold halfArg <;> linarith

theorem negHalfArg_mem {S R J : ℝ} : negHalfArg S R J ∈ Set.Ioo 0 (2 * Real.pi) := by
  have h1 := Real.neg_pi_div_two_lt_arctan (J / (S - R))
  have h2 := Real.arctan_lt_pi_div_two (J / (S - R))
  constructor <;> unfold negHalfArg <;> linarith

theorem halfArg_neg (S R J : ℝ) : halfArg S R (-J) = -halfArg S R J := by
  simp [halfArg, neg_div, Real.arctan_neg]

theorem negHalfArg_neg (S R J : ℝ) :
    negHalfArg S R (-J) = 2 * Real.pi - negHalfArg S R J := by
  simp only [negHalfArg, neg_div, Real.arctan_neg]
  ring

theorem halfArg_zero (S R : ℝ) : halfArg S R 0 = 0 := by
  simp [halfArg]

theorem negHalfArg_zero (S R : ℝ) : negHalfArg S R 0 = Real.pi := by
  simp [negHalfArg]

theorem halfArg_pos {S R J : ℝ} (hSR : 0 < S + R) (hI : 0 < J) : 0 < halfArg S R J := by
  have : 0 < Real.arctan (J / (S + R)) := Real.arctan_pos.2 (div_pos hI hSR)
  unfold halfArg
  linarith

theorem negHalfArg_lt_pi {S R J : ℝ} (hSR : 0 < S - R) (hI : 0 < J) :
    negHalfArg S R J < Real.pi := by
  have : 0 < Real.arctan (J / (S - R)) := Real.arctan_pos.2 (div_pos hI hSR)
  unfold negHalfArg
  linarith

theorem hasDerivAt_halfArg {R J : ℝ → ℝ} {S R' I' t : ℝ} (hR : HasDerivAt R R' t)
    (hI : HasDerivAt J I' t) (hSR : 0 < S + R t) :
    HasDerivAt (fun s => halfArg S (R s) (J s))
      (2 * ((S + R t) * I' - J t * R') / ((S + R t) ^ 2 + J t ^ 2)) t := by
  have hd : HasDerivAt (fun s => S + R s) R' t := hR.const_add S
  have h := ((hI.div hd hSR.ne').arctan).const_mul 2
  refine h.congr_deriv ?_
  simp only [Pi.div_apply]
  field_simp

theorem hasDerivAt_negHalfArg {R J : ℝ → ℝ} {S R' I' t : ℝ} (hR : HasDerivAt R R' t)
    (hI : HasDerivAt J I' t) (hSR : 0 < S - R t) :
    HasDerivAt (fun s => negHalfArg S (R s) (J s))
      (-(2 * ((S - R t) * I' + J t * R') / ((S - R t) ^ 2 + J t ^ 2))) t := by
  have hd : HasDerivAt (fun s => S - R s) (-R') t := hR.const_sub S
  have h := (((hI.div hd hSR.ne').arctan).const_mul 2).const_sub Real.pi
  refine h.congr_deriv ?_
  simp only [Pi.div_apply]
  field_simp
  ring

theorem halfArg_deriv_off {S R J R' I' : ℝ} (hS : 0 < S) (hSR : 0 < S + R)
    (h : R ^ 2 + J ^ 2 = S ^ 2) (hd : R * R' + J * I' = 0) (hI : J ≠ 0) :
    2 * ((S + R) * I' - J * R') / ((S + R) ^ 2 + J ^ 2) = -R' / J := by
  have hden : (S + R) ^ 2 + J ^ 2 = 2 * S * (S + R) := by nlinarith
  rw [hden, div_eq_div_iff (by positivity) hI]
  linear_combination (2 * (S + R)) * hd - (2 * R') * h

theorem halfArg_deriv_on {S R J R' I' : ℝ} (hS : 0 < S) (hI : J = 0) (hR : R = S) :
    2 * ((S + R) * I' - J * R') / ((S + R) ^ 2 + J ^ 2) = I' / S := by
  subst hI hR
  field_simp
  ring

theorem negHalfArg_deriv_off {S R J R' I' : ℝ} (hS : 0 < S) (hSR : 0 < S - R)
    (h : R ^ 2 + J ^ 2 = S ^ 2) (hd : R * R' + J * I' = 0) (hI : J ≠ 0) :
    -(2 * ((S - R) * I' + J * R') / ((S - R) ^ 2 + J ^ 2)) = -R' / J := by
  have hden : (S - R) ^ 2 + J ^ 2 = 2 * S * (S - R) := by nlinarith
  rw [hden, neg_div J R', neg_inj, div_eq_div_iff (by positivity) hI]
  linear_combination (2 * (S - R)) * hd + (2 * R') * h

theorem negHalfArg_deriv_on {S R J R' I' : ℝ} (hS : 0 < S) (hI : J = 0) (hR : R = -S) :
    -(2 * ((S - R) * I' + J * R') / ((S - R) ^ 2 + J ^ 2)) = -I' / S := by
  subst hI hR
  field_simp
  ring

theorem det_mul_cross (A : ℂ →ₗ[ℝ] ℂ) (N V : ℂ) :
    (A N).re * (A V).im - (A V).re * (A N).im = A.det * (N.re * V.im - V.re * N.im) := by
  rw [LinearMap.det_complex]
  have hN : A N = N.re • A 1 + N.im • A I := by
    conv_lhs => rw [← Complex.re_add_im N]
    rw [map_add, show (N.im : ℂ) * I = N.im • I by simp [Complex.real_smul],
      show (N.re : ℂ) = N.re • (1 : ℂ) by simp [Complex.real_smul], map_smul, map_smul]
  have hV : A V = V.re • A 1 + V.im • A I := by
    conv_lhs => rw [← Complex.re_add_im V]
    rw [map_add, show (V.im : ℂ) * I = V.im • I by simp [Complex.real_smul],
      show (V.re : ℂ) = V.re • (1 : ℂ) by simp [Complex.real_smul], map_smul, map_smul]
  rw [hN, hV]
  simp only [add_re, add_im, smul_re, smul_im, smul_eq_mul]
  ring

theorem polar_cross (S S' a b e Θ : ℝ) :
    ((((S' * b : ℝ) : ℂ) + (S : ℂ) * e * I) * exp ((Θ : ℂ) * I)).re *
        (((S * a : ℝ) : ℂ) * I * exp ((Θ : ℂ) * I)).im -
      (((S * a : ℝ) : ℂ) * I * exp ((Θ : ℂ) * I)).re *
        ((((S' * b : ℝ) : ℂ) + (S : ℂ) * e * I) * exp ((Θ : ℂ) * I)).im =
      S * S' * a * b := by
  rw [Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, mul_re, mul_im, add_re, add_im,
    ofReal_re, ofReal_im, I_re, I_im]
  have hcs := Real.cos_sq_add_sin_sq Θ
  linear_combination (S * S' * a * b) * hcs

theorem hasDerivAt_line_of_differentiableAt {F : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℝ F z)
    (N : ℂ) : HasDerivAt (fun t : ℝ => F (z + t * N)) (fderiv ℝ F z N) 0 := by
  have hl : HasDerivAt (fun t : ℝ => z + (t : ℂ) * N) N 0 := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const N).const_add z
  have hF' : HasFDerivAt F (fderiv ℝ F z) (z + ((0 : ℝ) : ℂ) * N) := by
    simpa using hF.hasFDerivAt
  exact hF'.comp_hasDerivAt 0 hl

theorem hasDerivAt_curve_of_differentiableAt {F : ℂ → ℂ} {γ : ℝ → ℂ} {V : ℂ}
    (hF : DifferentiableAt ℝ F (γ 0)) (hγ : HasDerivAt γ V 0) :
    HasDerivAt (fun t => F (γ t)) (fderiv ℝ F (γ 0) V) 0 :=
  hF.hasFDerivAt.comp_hasDerivAt 0 hγ

theorem det_fderiv_polar {c : ℂ} {S : ℝ → ℝ} {ρ Θ : ℂ → ℝ} {z V N : ℂ} {γ : ℝ → ℂ}
    {S' a b e : ℝ} (hS : HasDerivAt S S' (ρ z)) (hρ : DifferentiableAt ℝ ρ z)
    (hΘ : DifferentiableAt ℝ Θ z) (hγ : HasDerivAt γ V 0) (hγ0 : γ 0 = z)
    (hργ : ∀ᶠ t in nhds 0, ρ (γ t) = ρ z) (hΘγ : HasDerivAt (fun t => Θ (γ t)) a 0)
    (hρN : HasDerivAt (fun t : ℝ => ρ (z + t * N)) b 0)
    (hΘN : HasDerivAt (fun t : ℝ => Θ (z + t * N)) e 0) :
    (fderiv ℝ (fun u => c + (S (ρ u) : ℂ) * exp ((Θ u : ℂ) * I)) z).det *
        (N.re * V.im - V.re * N.im) =
      S (ρ z) * S' * a * b := by
  have hSd : DifferentiableAt ℝ S (ρ z) := hS.differentiableAt
  have hFd : DifferentiableAt ℝ (fun u => c + (S (ρ u) : ℂ) * exp ((Θ u : ℂ) * I)) z := by
    have h1 : DifferentiableAt ℝ (fun u => (S (ρ u) : ℂ)) z :=
      Complex.ofRealCLM.differentiableAt.comp z (hSd.comp z hρ)
    have h2 : DifferentiableAt ℝ (fun u => exp ((Θ u : ℂ) * I)) z :=
      ((Complex.ofRealCLM.differentiableAt.comp z hΘ).mul_const I).cexp
    exact (differentiableAt_const c).add (h1.mul h2)
  have hFV := hasDerivAt_curve_of_differentiableAt (hγ0 ▸ hFd) hγ
  rw [hγ0] at hFV
  have hFV' : HasDerivAt (fun t => c + (S (ρ (γ t)) : ℂ) * exp ((Θ (γ t) : ℂ) * I))
      (((S (ρ z) * a : ℝ) : ℂ) * I * exp ((Θ z : ℂ) * I)) 0 := by
    have hc : (fun t => c + (S (ρ (γ t)) : ℂ) * exp ((Θ (γ t) : ℂ) * I)) =ᶠ[nhds 0]
        fun t => c + (S (ρ z) : ℂ) * exp ((Θ (γ t) : ℂ) * I) := by
      filter_upwards [hργ] with t ht
      rw [ht]
    have h := (((hΘγ.ofReal_comp.mul_const I).cexp).const_mul (S (ρ z) : ℂ)).const_add c
    rw [hγ0] at h
    refine (h.congr_of_eventuallyEq hc).congr_deriv ?_
    push_cast
    ring
  have hFN := hasDerivAt_line_of_differentiableAt hFd N
  have hFN' : HasDerivAt (fun t : ℝ => c + (S (ρ (z + t * N)) : ℂ) *
      exp ((Θ (z + t * N) : ℂ) * I))
      ((((S' * b : ℝ) : ℂ) + (S (ρ z) : ℂ) * e * I) * exp ((Θ z : ℂ) * I)) 0 := by
    have hSρ : HasDerivAt (fun t : ℝ => S (ρ (z + t * N))) (S' * b) 0 := by
      have h0 : ρ (z + ((0 : ℝ) : ℂ) * N) = ρ z := by simp
      exact (h0 ▸ hS).comp 0 hρN
    have h := (hSρ.ofReal_comp.mul ((hΘN.ofReal_comp.mul_const I).cexp)).const_add c
    refine h.congr_deriv ?_
    simp only [zero_mul, add_zero, ofReal_zero]
    push_cast
    ring
  have e1 := hFV.unique hFV'
  have e2 := hFN.unique hFN'
  have hdet := det_mul_cross
    (fderiv ℝ (fun u => c + (S (ρ u) : ℂ) * exp ((Θ u : ℂ) * I)) z : ℂ →ₗ[ℝ] ℂ) N V
  simp only [ContinuousLinearMap.coe_coe] at hdet
  rw [e1, e2, polar_cross] at hdet
  rw [← hdet]

end GC.Seifert
