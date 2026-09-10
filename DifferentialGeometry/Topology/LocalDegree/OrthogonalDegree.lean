import DifferentialGeometry.Topology.LocalDegree.ReflectionDegree
import Mathlib.Data.Sign.Basic

set_option autoImplicit false
open Metric Submodule
noncomputable section
namespace DifferentialGeometry.LocalDegree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem linearSphereMap_linearIsometryEquiv_mul (A B : E ≃ₗᵢ[ℝ] E) :
    linearSphereMap (A * B).toContinuousLinearEquiv =
      (linearSphereMap A.toContinuousLinearEquiv).comp
        (linearSphereMap B.toContinuousLinearEquiv) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  simp only [ContinuousMap.comp_apply, linearSphereMap_linearIsometryEquiv_apply]
  rfl


theorem linearSphereMap_linearIsometryEquiv_one :
    linearSphereMap (1 : E ≃ₗᵢ[ℝ] E).toContinuousLinearEquiv =
      ContinuousMap.id (sphere (0 : E) 1) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rw [linearSphereMap_linearIsometryEquiv_apply]
  rfl

variable {d : ℕ}

private theorem reflection_degree_eq_det_sign
    (v : EuclideanSpace ℝ (Fin (d + 1))) :
    euclideanSphereDegree (unitSphereReflection v) =
      (SignType.sign (LinearMap.det (ℝ ∙ v)ᗮ.reflection.toLinearMap) : ℤ) := by
  rw [Submodule.det_reflection, orthogonal_orthogonal]
  by_cases hv : v = 0
  · subst v
    rw [show ℝ ∙ (0 : EuclideanSpace ℝ (Fin (d + 1))) = ⊥ from
      span_singleton_eq_bot.mpr rfl]
    simp
  · rw [finrank_span_singleton hv, pow_one, euclideanSphereDegree_reflection v hv]
    norm_num

private theorem orthogonal_det_mul
    (A B : EuclideanSpace ℝ (Fin (d + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    LinearMap.det (A * B).toLinearMap =
      LinearMap.det A.toLinearMap * LinearMap.det B.toLinearMap := by
  change LinearMap.det (A.toLinearMap * B.toLinearMap) = _
  exact map_mul LinearMap.det _ _

theorem euclideanSphereDegree_linearIsometryEquiv
    (A : EuclideanSpace ℝ (Fin (d + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    euclideanSphereDegree (linearSphereMap A.toContinuousLinearEquiv) =
      (SignType.sign (LinearMap.det A.toLinearMap) : ℤ) := by
  obtain ⟨l, hlength, rfl⟩ := A.reflections_generate_dim
  clear hlength
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, linearSphereMap_linearIsometryEquiv_one,
      euclideanSphereDegree_id]
    change (1 : ℤ) = (SignType.sign (LinearMap.det (1 : _ →ₗ[ℝ] _)) : ℤ)
    simp
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, linearSphereMap_linearIsometryEquiv_mul,
      euclideanSphereDegree_comp, orthogonal_det_mul, sign_mul, SignType.coe_mul]
    change euclideanSphereDegree (unitSphereReflection v) * _ = _
    rw [reflection_degree_eq_det_sign, ih]

end DifferentialGeometry.LocalDegree
