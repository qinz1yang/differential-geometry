import DifferentialGeometry.Topology.LocalDegree.Euclidean
import DifferentialGeometry.Topology.LocalDegree.LinearSphere
import DifferentialGeometry.Topology.LocalDegree.LinearizationHomotopy
import Mathlib.Algebra.Group.Int.Units

set_option autoImplicit false
open Metric Set
open scoped Topology
noncomputable section
namespace DifferentialGeometry.LocalDegree

theorem isolatedZero_of_hasFDerivAt_equiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} {s : Set E}
    (A : E ≃L[ℝ] F) (hs : s ∈ 𝓝 x) (hf : ContinuousOn f s)
    (hz : f x = 0) (hd : HasFDerivAt f A.toContinuousLinearMap x) : isolatedZero f x := by
  obtain ⟨R, hR, hc, hn, _⟩ := exists_sphereMap_linearization_homotopy A hs hf hz hd
  refine ⟨R, hR, hc, fun y hy => ⟨?_, ?_⟩⟩
  · intro hfy
    by_contra hne
    exact hn y hy hne hfy
  · intro hyx
    exact hyx ▸ hz

variable {d : ℕ}
  {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
  {x : EuclideanSpace ℝ (Fin (d + 1))} {s : Set (EuclideanSpace ℝ (Fin (d + 1)))}

theorem euclideanLocalDegree_eq_linear_of_hasFDerivAt
    (A : EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    (hs : s ∈ 𝓝 x) (hf : ContinuousOn f s) (hz : f x = 0)
    (hd : HasFDerivAt f A.toContinuousLinearMap x) (h : isolatedZero f x) :
    euclideanLocalDegree f x h = euclideanSphereDegree (linearSphereMap A) := by
  obtain ⟨R, hR, hc, hn, hH⟩ := exists_sphereMap_linearization_homotopy A hs hf hz hd
  have hi : IsolatingRadius f x R := ⟨hR, hc, fun y hy => ⟨fun hfy => by
    by_contra hne
    exact hn y hy hne hfy, fun hyx => hyx ▸ hz⟩⟩
  rw [euclideanLocalDegree_eq_sphereDegree h hi ⟨R, hR, le_rfl⟩]
  obtain ⟨H, _⟩ := hH ⟨R, hR, le_rfl⟩
  exact (euclideanSphereDegree_eq_of_homotopy H).trans
    (congrArg euclideanSphereDegree (sphereMap_linear_eq A R ⟨R, hR, le_rfl⟩))


theorem euclideanLocalDegree_isUnit_of_hasFDerivAt
    (A : EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    (hs : s ∈ 𝓝 x) (hf : ContinuousOn f s) (hz : f x = 0)
    (hd : HasFDerivAt f A.toContinuousLinearMap x) (h : isolatedZero f x) :
    IsUnit (euclideanLocalDegree f x h) := by
  rw [euclideanLocalDegree_eq_linear_of_hasFDerivAt A hs hf hz hd h]
  exact euclideanSphereDegree_isUnit (linearSphereHomeomorph A).toHomotopyEquiv


theorem euclideanLocalDegree_eq_one_or_neg_one_of_hasFDerivAt
    (A : EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    (hs : s ∈ 𝓝 x) (hf : ContinuousOn f s) (hz : f x = 0)
    (hd : HasFDerivAt f A.toContinuousLinearMap x) (h : isolatedZero f x) :
    euclideanLocalDegree f x h = 1 ∨ euclideanLocalDegree f x h = -1 :=
  Int.isUnit_iff.mp (euclideanLocalDegree_isUnit_of_hasFDerivAt A hs hf hz hd h)

end DifferentialGeometry.LocalDegree
