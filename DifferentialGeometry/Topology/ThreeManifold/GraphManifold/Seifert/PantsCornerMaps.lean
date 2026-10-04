import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsBridgeZero
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsBridgeTwo
import DifferentialGeometry.Tensor.LinearAlgebra.ComplexDeterminant
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import DifferentialGeometry.Compat.Ch567.Tensor.LinearAlgebra.ComplexDeterminant

/-!
# The corner maps of the K16f fold

Packet K16f, tier 2 (definitions). The fold `foldMap` of the ideal triangle onto the upper half
of the round-hole pants, outside a small core disc, is assembled from four explicit maps
(design `docs/geometrization/handoffs/20261004-design-k16f-fold.md`, §4):

* `cornerInf z = foldRho y · e^{i angleInf x y}`, where `foldRho` is `bridgeRho` for `y ≤ 12/25`
  bent smoothly below `3`, and `angleInf` blends `angleZero x y` and `π - angleZero (1/2 - x) y`
  with the weight `foldNu x` (a smooth step on `[23/100, 27/100]`);
* `cornerZero z = 3/2 + bridgeSigma (heightOne x y) · e^{i angleHole x y}`, where `angleHole`
  blends `angleZeroHole` and `angleTwoHole` with the weight `foldMu (holeX x y)` (a smooth step,
  `1` for `holeX ≤ -35/100` and `0` for `holeX ≥ -31/100`);
* `cornerHalf z = -conj (cornerZero (1/2 - z̄))`, the mirror image;
* `bridgeTwo` on the lens `foldLens`.

`foldMap` uses `cornerZero` on the horoball `3/5 < heightOne x y` of the cusp `0`, `cornerHalf`
on the horoball of the cusp `1/2`, `bridgeTwo` on the lens and `cornerInf` elsewhere. The core
disc is centred at `foldCenter = 1/4 + (37/100) i` with radius `1/10` and collar half-width
`1/250`. Two generic lemmas compute real Jacobians: `det_fderiv_eq_of_partials` (the determinant
of `fderiv ℝ F z` from the partial derivatives along `1` and `i`) and `polar_partials_det`
(for a map `R e^{iA}` it is `-(R R' ∂A)`).
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace GC.Seifert

def foldTau (y : ℝ) : ℝ := Real.smoothTransition ((y - 12 / 25) / (1 / 100))

def foldRho (y : ℝ) : ℝ :=
  (1 - foldTau y) * bridgeRho y + foldTau y * (3 - 1 / (50 * (1 + 4 * y ^ 2)))

def foldNu (x : ℝ) : ℝ := Real.smoothTransition ((x - 23 / 100) / (1 / 25))

def foldMu (t : ℝ) : ℝ := Real.smoothTransition ((-(31 / 100) - t) / (1 / 25))

def angleInf (x y : ℝ) : ℝ :=
  (1 - foldNu x) * angleZero x y + foldNu x * (Real.pi - angleZero (1 / 2 - x) y)

def angleHole (x y : ℝ) : ℝ :=
  (1 - foldMu (holeX x y)) * angleZeroHole x y + foldMu (holeX x y) * angleTwoHole x y

def cornerInf (z : ℂ) : ℂ :=
  (foldRho z.im : ℂ) * Complex.exp (Complex.I * (angleInf z.re z.im : ℂ))

def cornerZero (z : ℂ) : ℂ :=
  3 / 2 + (bridgeSigma (heightOne z.re z.im) : ℂ) *
    Complex.exp (Complex.I * (angleHole z.re z.im : ℂ))

def foldMirror (z : ℂ) : ℂ := 1 / 2 - (starRingEnd ℂ) z

def cornerHalf (z : ℂ) : ℂ := -(starRingEnd ℂ) (cornerZero (foldMirror z))

def foldLens (z : ℂ) : Prop :=
  wallTwo z.re z.im < 1 / 25 ∧ Complex.normSq z < 1 / 4 ∧ Complex.normSq (z - 1 / 2) < 1 / 4

open Classical in
def foldMap (z : ℂ) : ℂ :=
  if 3 / 5 < heightOne z.re z.im then cornerZero z
  else if 3 / 5 < heightOne (1 / 2 - z.re) z.im then cornerHalf z
  else if foldLens z then bridgeTwo z
  else cornerInf z

def foldCenter : ℂ := ⟨1 / 4, 37 / 100⟩

theorem foldMirror_re (z : ℂ) : (foldMirror z).re = 1 / 2 - z.re := by
  simp [foldMirror]

theorem foldMirror_im (z : ℂ) : (foldMirror z).im = z.im := by
  simp [foldMirror]

theorem foldMirror_foldMirror (z : ℂ) : foldMirror (foldMirror z) = z := by
  apply Complex.ext <;> simp [foldMirror_re, foldMirror_im]

theorem foldMap_of_heightOne {z : ℂ} (h : 3 / 5 < heightOne z.re z.im) :
    foldMap z = cornerZero z := by
  simp only [foldMap, h, ↓reduceIte]

theorem foldMap_of_heightHalf {z : ℂ} (h0 : ¬ 3 / 5 < heightOne z.re z.im)
    (h : 3 / 5 < heightOne (1 / 2 - z.re) z.im) : foldMap z = cornerHalf z := by
  simp only [foldMap, h0, h, ↓reduceIte]

theorem foldMap_of_lens {z : ℂ} (h0 : ¬ 3 / 5 < heightOne z.re z.im)
    (h1 : ¬ 3 / 5 < heightOne (1 / 2 - z.re) z.im) (h : foldLens z) :
    foldMap z = bridgeTwo z := by
  simp only [foldMap, h0, h1, h, ↓reduceIte]

theorem foldMap_of_not_lens {z : ℂ} (h0 : ¬ 3 / 5 < heightOne z.re z.im)
    (h1 : ¬ 3 / 5 < heightOne (1 / 2 - z.re) z.im) (h : ¬ foldLens z) :
    foldMap z = cornerInf z := by
  simp only [foldMap, h0, h1, h, ↓reduceIte]

theorem fderiv_apply_one_of_hasDerivAt {F : ℂ → ℂ} {z Dx : ℂ} (hF : DifferentiableAt ℝ F z)
    (h : HasDerivAt (fun t : ℝ => F (z + t)) Dx 0) : fderiv ℝ F z 1 = Dx := by
  have hl : HasDerivAt (fun t : ℝ => z + (t : ℂ)) 1 0 := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_add z)
  have hF' : HasFDerivAt F (fderiv ℝ F z) (z + ((0 : ℝ) : ℂ)) := by simpa using hF.hasFDerivAt
  have hc := hF'.comp_hasDerivAt (0 : ℝ) hl
  simpa using hc.unique h

theorem fderiv_apply_I_of_hasDerivAt {F : ℂ → ℂ} {z Dy : ℂ} (hF : DifferentiableAt ℝ F z)
    (h : HasDerivAt (fun t : ℝ => F (z + t * Complex.I)) Dy 0) :
    fderiv ℝ F z Complex.I = Dy := by
  have hl : HasDerivAt (fun t : ℝ => z + (t : ℂ) * Complex.I) Complex.I 0 := by
    simpa using (((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const Complex.I).const_add z)
  have hF' : HasFDerivAt F (fderiv ℝ F z) (z + ((0 : ℝ) : ℂ) * Complex.I) := by
    simpa using hF.hasFDerivAt
  have hc := hF'.comp_hasDerivAt (0 : ℝ) hl
  simpa using hc.unique h

theorem det_fderiv_eq_of_partials {F : ℂ → ℂ} {z Dx Dy : ℂ} (hF : DifferentiableAt ℝ F z)
    (hx : HasDerivAt (fun t : ℝ => F (z + t)) Dx 0)
    (hy : HasDerivAt (fun t : ℝ => F (z + t * Complex.I)) Dy 0) :
    (fderiv ℝ F z).det = Dx.re * Dy.im - Dy.re * Dx.im := by
  rw [ContinuousLinearMap.det, LinearMap.det_complex]
  change (fderiv ℝ F z 1).re * (fderiv ℝ F z Complex.I).im -
    (fderiv ℝ F z Complex.I).re * (fderiv ℝ F z 1).im = _
  rw [fderiv_apply_one_of_hasDerivAt hF hx, fderiv_apply_I_of_hasDerivAt hF hy]

theorem polar_partials_det (ρ ρ' a b A : ℝ) :
    ((ρ : ℂ) * a * Complex.I * Complex.exp (Complex.I * A)).re *
        ((((ρ' : ℂ) + Complex.I * ρ * b) * Complex.exp (Complex.I * A))).im -
      ((((ρ' : ℂ) + Complex.I * ρ * b) * Complex.exp (Complex.I * A))).re *
        ((ρ : ℂ) * a * Complex.I * Complex.exp (Complex.I * A)).im = -(ρ * ρ' * a) := by
  have he : Complex.exp (Complex.I * A) = ⟨Real.cos A, Real.sin A⟩ := by
    rw [mul_comm, Complex.exp_mul_I]
    apply Complex.ext <;> simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [he]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hcs := Real.cos_sq_add_sin_sq A
  linear_combination (-(ρ * ρ' * a)) * hcs

end GC.Seifert
