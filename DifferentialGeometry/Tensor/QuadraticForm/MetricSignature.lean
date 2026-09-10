import DifferentialGeometry.Tensor.QuadraticForm.SignatureDeterminant
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false
noncomputable section
open InnerProductSpace
open scoped BigOperators
namespace Poincare.QuadraticForm
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]


def rieszFlat (B : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E :=
  (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L B


theorem inner_rieszFlat (B : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    inner ℝ (rieszFlat B v) w = B v w := by
  change inner ℝ ((toDual ℝ E).symm (B v)) w = _
  rw [← toDual_apply_apply (𝕜 := ℝ), (toDual ℝ E).apply_symm_apply]


theorem isSymmetric_rieszFlat (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) : (rieszFlat B).toLinearMap.IsSymmetric := by
  intro v w
  change inner ℝ (rieszFlat B v) w = inner ℝ v (rieszFlat B w)
  rw [inner_rieszFlat, real_inner_comm, inner_rieszFlat, hB]


theorem det_rieszFlat_pos (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) :
    0 < LinearMap.det (rieszFlat B).toLinearMap := by
  let hs := isSymmetric_rieszFlat B hB
  rw [hs.det_eq_prod_eigenvalues rfl]
  apply Finset.prod_pos
  intro i _
  have hh := hpos (hs.eigenvectorBasis rfl i) ((hs.eigenvectorBasis rfl).toBasis.ne_zero i)
  rw [← inner_rieszFlat] at hh
  change 0 < inner ℝ ((rieszFlat B).toLinearMap (hs.eigenvectorBasis rfl i))
    (hs.eigenvectorBasis rfl i) at hh
  rw [hs.apply_eigenvectorBasis] at hh
  simpa only [real_inner_smul_left, real_inner_self_eq_norm_sq,
    (hs.eigenvectorBasis rfl).orthonormal.1 i, one_pow, mul_one] using hh


theorem sign_det_rieszFlat_comp (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
    (L : E →L[ℝ] E) :
    (SignType.sign (LinearMap.det ((rieszFlat B) ∘L L).toLinearMap) : ℤ) =
      (SignType.sign (LinearMap.det L.toLinearMap) : ℤ) := by
  change (SignType.sign (LinearMap.det ((rieszFlat B).toLinearMap.comp L.toLinearMap)) : ℤ) = _
  rw [LinearMap.det_comp, _root_.sign_mul, SignType.coe_mul]
  simp [det_rieszFlat_pos B hB hpos]

end Poincare.QuadraticForm
