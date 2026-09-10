import DifferentialGeometry.Topology.LocalDegree.BallBoundaryHomotopy
import DifferentialGeometry.Topology.Homotopy.NonzeroPerturbation

set_option autoImplicit false
noncomputable section
open Set Metric
namespace Poincare.LocalDegree
variable {d : ℕ} {a : EuclideanSpace ℝ (Fin (d + 1))} {r : ℝ}
  (hr : 0 < r) (f : C(closedBall a r, EuclideanSpace ℝ (Fin (d + 1))))
  (hf : ∀ y : closedBall a r, y.val ∈ sphere a r → f y ≠ 0)

private def boundaryRestriction
    (g : C(closedBall a r, EuclideanSpace ℝ (Fin (d + 1)))) :
    C(sphere a r, EuclideanSpace ℝ (Fin (d + 1))) :=
  ⟨fun y => g ⟨y.val,sphere_subset_closedBall y.property⟩,by fun_prop⟩

theorem euclideanBallDegree_eq_of_norm_sub_lt
    (g : C(closedBall a r, EuclideanSpace ℝ (Fin (d + 1))))
    (hclose : ∀ y : closedBall a r, y.val ∈ sphere a r → ‖g y - f y‖ < ‖f y‖) :
    ∃ hg : ∀ y : closedBall a r, y.val ∈ sphere a r → g y ≠ 0,
      euclideanBallDegree hr f hf = euclideanBallDegree hr g hg := by
  have hg : ∀ y : closedBall a r, y.val ∈ sphere a r → g y ≠ 0 := by
    intro y hy hz
    have hh := hclose y hy
    rw [hz,zero_sub,norm_neg] at hh
    exact (lt_irrefl _) hh
  let F := boundaryRestriction f
  let G := boundaryRestriction g
  let K := ContinuousMap.Homotopy.affine F G
  refine ⟨hg,euclideanBallDegree_eq_of_boundaryHomotopy hr hf hg K.toContinuousMap ?_
    K.map_zero_left K.map_one_left⟩
  exact Poincare.Topology.affineHomotopy_ne_zero_of_norm_sub_lt F G
    (fun y => hclose ⟨y.val,sphere_subset_closedBall y.property⟩ y.property)

theorem exists_pos_euclideanBallDegree_eq_of_boundary_norm_lt :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : C(closedBall a r, EuclideanSpace ℝ (Fin (d + 1))),
      (∀ y : closedBall a r, y.val ∈ sphere a r → ‖g y - f y‖ < δ) →
      ∃ hg : ∀ y : closedBall a r, y.val ∈ sphere a r → g y ≠ 0,
        euclideanBallDegree hr f hf = euclideanBallDegree hr g hg := by
  have hK : IsCompact {y : closedBall a r | y.val ∈ sphere a r} :=
    isClosed_sphere.preimage continuous_subtype_val |>.isCompact
  obtain ⟨δ,hδ,hbound⟩ := Poincare.Topology.exists_pos_lt_norm_of_isCompact hK
    f.continuous.continuousOn hf
  exact ⟨δ,hδ,fun g hg => euclideanBallDegree_eq_of_norm_sub_lt hr f hf g
    (fun y hy => (hg y hy).trans (hbound y hy))⟩

end Poincare.LocalDegree
