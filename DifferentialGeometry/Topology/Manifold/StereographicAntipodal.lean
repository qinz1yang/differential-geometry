import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff InnerProductSpace
namespace DifferentialGeometry.Topology.Manifold
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

def sphereAntipodalDiffeomorph :
    Metric.sphere (0 : E) 1 ≃ₘ⟮𝓡 n, 𝓡 n⟯ Metric.sphere (0 : E) 1 where
  toFun := fun p => -p
  invFun := fun p => -p
  left_inv := neg_neg
  right_inv := neg_neg
  contMDiff_toFun := contMDiff_neg_sphere
  contMDiff_invFun := contMDiff_neg_sphere

theorem stereographicInverse_antipodal (north : Metric.sphere (0 : E) 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    (stereographic' n north).symm ((-4 / ‖x‖ ^ 2) • x) =
      -(stereographic' n north).symm x := by
  let U : (ℝ ∙ (north : E))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere north)).repr
  have hn (y : EuclideanSpace ℝ (Fin n)) : ‖(U.symm y : E)‖ = ‖y‖ := U.symm.norm_map y
  have hr : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hd : ‖x‖ ^ 2 + 4 ≠ 0 := by positivity
  have hlarge : 16 / ‖x‖ ^ 2 + 4 ≠ 0 := by positivity
  have hnorm : ‖(-4 / ‖x‖ ^ 2) • x‖ ^ 2 = 16 / ‖x‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp
    ring
  have hlin : (U.symm ((-4 / ‖x‖ ^ 2) • x) : E) =
      (-4 / ‖x‖ ^ 2) • (U.symm x : E) := by simp only [map_smul, Submodule.coe_smul]
  have hfirst : ((16 / ‖x‖ ^ 2 + 4)⁻¹ * 4) * (-4 / ‖x‖ ^ 2) =
      -((‖x‖ ^ 2 + 4)⁻¹ * 4) := by
    field_simp
    ring
  have hsecond : (16 / ‖x‖ ^ 2 + 4)⁻¹ * (16 / ‖x‖ ^ 2 - 4) =
      -((‖x‖ ^ 2 + 4)⁻¹ * (‖x‖ ^ 2 - 4)) := by
    field_simp
    ring
  apply Subtype.ext
  change ((stereographic' n north).symm ((-4 / ‖x‖ ^ 2) • x) : E) =
    -((stereographic' n north).symm x : E)
  simp only [stereographic'_symm_apply]
  change (‖(U.symm ((-4 / ‖x‖ ^ 2) • x) : E)‖ ^ 2 + 4)⁻¹ • (4 : ℝ) •
      (U.symm ((-4 / ‖x‖ ^ 2) • x) : E) +
      (‖(U.symm ((-4 / ‖x‖ ^ 2) • x) : E)‖ ^ 2 + 4)⁻¹ •
        (‖(U.symm ((-4 / ‖x‖ ^ 2) • x) : E)‖ ^ 2 - 4) • (north : E) =
    -((‖(U.symm x : E)‖ ^ 2 + 4)⁻¹ • (4 : ℝ) • (U.symm x : E) +
      (‖(U.symm x : E)‖ ^ 2 + 4)⁻¹ • (‖(U.symm x : E)‖ ^ 2 - 4) • (north : E))
  simp only [hn]
  rw [hnorm]
  simp only [hlin, smul_smul, ← mul_assoc]
  rw [hfirst, hsecond]
  module

theorem stereographic_antipodal_coordinates (north : Metric.sphere (0 : E) 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    stereographic' n north (sphereAntipodalDiffeomorph (n := n) ((stereographic' n north).symm x)) =
      (-4 / ‖x‖ ^ 2) • x := by
  change stereographic' n north (-(stereographic' n north).symm x) = _
  rw [← stereographicInverse_antipodal north x hx]
  exact (stereographic' n north).right_inv (by simp)
end DifferentialGeometry.Topology.Manifold
