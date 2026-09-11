import DifferentialGeometry.Topology.LocalDegree.Euclidean
import DifferentialGeometry.Topology.LocalDegree.LinearSphere

set_option autoImplicit false
open Metric Set
noncomputable section
namespace DifferentialGeometry.LocalDegree

theorem IsolatingRadius.linear_postcomp {E F G : Type*} [PseudoMetricSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : F ≃L[ℝ] G) {f : E → F} {x : E} {R : ℝ} (h : IsolatingRadius f x R) :
    IsolatingRadius (fun y => A (f y)) x R where
  pos := h.pos
  continuousOn := A.continuous.comp_continuousOn h.continuousOn
  zero_iff y hy := A.map_eq_zero_iff.trans (h.zero_iff y hy)


theorem isolatedZero_linear_postcomp {E F G : Type*} [PseudoMetricSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : F ≃L[ℝ] G) {f : E → F} {x : E} (h : isolatedZero f x) :
    isolatedZero (fun y => A (f y)) x :=
  ⟨h.choose, h.choose_spec.linear_postcomp A⟩

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem normalize_pos_smul (z : G) {a : ℝ} (ha : 0 < a) :
    ‖a • z‖⁻¹ • (a • z) = ‖z‖⁻¹ • z := by
  rw [norm_smul, Real.norm_of_nonneg ha.le, mul_inv_rev, smul_smul,
    mul_assoc, inv_mul_cancel₀ ha.ne', mul_one]

theorem sphereMap_linear_postcomp (A : F ≃L[ℝ] G)
    {f : E → F} {x : E} {R : ℝ} (h : IsolatingRadius f x R) (r : Ioc (0 : ℝ) R) :
    sphereMap (fun y => A (f y)) x R (h.linear_postcomp A).continuousOn
        (h.linear_postcomp A).nonzero r =
      (linearSphereMap A).comp (sphereMap f x R h.continuousOn h.nonzero r) := by
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  have hn : ‖(r : ℝ) • (v : E)‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg r.property.1.le, norm_eq_of_mem_sphere v, mul_one]
  have hm : x + (r : ℝ) • (v : E) ∈ closedBall x R := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, hn]
    exact r.property.2
  have he : x + (r : ℝ) • (v : E) ≠ x := by
    intro hh
    have hh' := add_eq_left.mp hh
    rw [hh', norm_zero] at hn
    exact r.property.1.ne hn
  have hp : 0 < ‖f (x + (r : ℝ) • (v : E))‖⁻¹ :=
    inv_pos.mpr (norm_pos_iff.mpr (h.nonzero _ hm he))
  rw [sphereMap_apply, ContinuousMap.comp_apply, linearSphereMap_apply, sphereMap_apply, map_smul]
  exact (normalize_pos_smul _ hp).symm

theorem euclideanLocalDegree_linear_postcomp {d : ℕ}
    (A : EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} (h : isolatedZero f x) :
    euclideanLocalDegree (fun y => A (f y)) x (isolatedZero_linear_postcomp A h) =
      euclideanSphereDegree (linearSphereMap A) * euclideanLocalDegree f x h := by
  let r : Ioc (0 : ℝ) h.choose := ⟨h.choose, h.choose_spec.pos, le_rfl⟩
  erw [euclideanLocalDegree_eq_sphereDegree _ (h.choose_spec.linear_postcomp A) r,
    euclideanLocalDegree_eq_sphereDegree _ h.choose_spec r]
  rw [sphereMap_linear_postcomp A h.choose_spec r, euclideanSphereDegree_comp]

end DifferentialGeometry.LocalDegree
