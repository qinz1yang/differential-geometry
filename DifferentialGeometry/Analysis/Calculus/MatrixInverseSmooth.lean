import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Smoothness of matrix determinant, adjugate and inverse (from smooth entries)

The standalone-operator foundation for the Ricci-flow time-jet match (`hglue` corollary (a)'s `Φ`).
The coordinate Ricci-flow RHS is a smooth function of the metric `2`-jet; its only non-polynomial
ingredient is the inverse Gram matrix, which is `C∞` at any invertible matrix by Cramer's rule
`M⁻¹ = (det M)⁻¹ • adjugate M`: the determinant and adjugate entries are POLYNOMIALS in the matrix
entries (hence `C∞` whenever the entries are), and the scalar reciprocal `(det M)⁻¹` is `C∞` where
`det M ≠ 0`.

Stated over an arbitrary normed domain `X` with the matrix entries given as smooth `ℝ`-valued
functions of `x`, so no norm on `Matrix` is needed (the matrix is only an intermediate; every output
is `ℝ`-valued). These are the abstract analogues of the time-curve-specialised `matrixDet_contDiffOn`
/ `matrixAdjugate_contDiffOn` in `Evolution/ExtendedSolutionRegularity.lean`; the domain-general form
lets Faà-di-Bruno (the jet-match core) be applied to `Φ ∘ (time curve of the Gram 2-jet)`. No Mathlib
lemma states these directly.
-/

noncomputable section

open scoped ContDiff

namespace DifferentialGeometry
namespace Analysis

variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The determinant `x ↦ det (N x)` is `C∞` when every entry `x ↦ N x a b` is `C∞`
(`Matrix.det_apply`: a finite sum of signed products of entries). -/
theorem contDiff_det_of_entries (N : X → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ a b : Fin n, ContDiff ℝ ∞ (fun x => N x a b)) :
    ContDiff ℝ ∞ (fun x => (N x).det) := by
  classical
  simp_rw [Matrix.det_apply]
  exact ContDiff.sum (fun σ _ => ContDiff.const_smul (Equiv.Perm.sign σ)
    (contDiff_prod (fun i _ => hN (σ i) i)))

/-- An adjugate entry `x ↦ (adjugate (N x)) k l` is `C∞` when every entry of `N` is `C∞`
(`Matrix.adjugate_apply`: a determinant of a row-updated matrix whose entries are constants or
entries of `N`). -/
theorem contDiff_adjugate_of_entries (N : X → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ a b : Fin n, ContDiff ℝ ∞ (fun x => N x a b)) (k l : Fin n) :
    ContDiff ℝ ∞ (fun x => (N x).adjugate k l) := by
  classical
  simp_rw [Matrix.adjugate_apply]
  refine contDiff_det_of_entries (fun x => (N x).updateRow l (Pi.single k 1)) (fun a b => ?_)
  rcases eq_or_ne a l with h | h
  · subst h
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simp only [Matrix.updateRow_ne h]
    exact hN a b

/-- An inverse-matrix entry `x ↦ (N x)⁻¹ k l` is `C∞` at any `x₀` with `det (N x₀) ≠ 0`, by Cramer's
rule `M⁻¹ = (det M)⁻¹ • adjugate M`: the reciprocal of the (`C∞`, non-vanishing here) determinant
times the (`C∞`) adjugate entry. -/
theorem contDiffAt_inv_of_entries (N : X → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ a b : Fin n, ContDiff ℝ ∞ (fun x => N x a b)) {x₀ : X} (hx₀ : (N x₀).det ≠ 0)
    (k l : Fin n) :
    ContDiffAt ℝ ∞ (fun x => (N x)⁻¹ k l) x₀ := by
  have hcongr : (fun x => (N x)⁻¹ k l) = fun x => ((N x).det)⁻¹ * (N x).adjugate k l := by
    funext x
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  rw [hcongr]
  exact ((contDiff_det_of_entries N hN).contDiffAt.inv hx₀).mul
    (contDiff_adjugate_of_entries N hN k l).contDiffAt

end Analysis
end DifferentialGeometry

end
