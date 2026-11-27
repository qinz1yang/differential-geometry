import DifferentialGeometry.Topology.Homology.Spheres.HomotopySphereCompactness
import DifferentialGeometry.Topology.Sphere.SphereSimplyConnected
import DifferentialGeometry.Topology.ThreeManifold.Poincare

/-!
# Poincaré conjecture for homotopy three-spheres

The homotopy equivalence supplies compactness and simple connectivity, so the
compact simply connected form of the Poincaré conjecture applies.
-/

set_option autoImplicit false

open scoped ContinuousMap

namespace DifferentialGeometry.Topology

universe u

/-- A Hausdorff topological three-manifold homotopy equivalent to the unit
sphere in Euclidean four-space is homeomorphic to that sphere. -/
theorem poincare_conjecture_of_homotopyEquiv
    (M : Type u) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [T2Space M] (h : M ≃ₕ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
  let : CompactSpace M := compactSpace_of_homotopyEquiv_sphere h
  let : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
    simplyConnectedSpace_sphere_of_two_le (by decide : 2 ≤ 3)
  let : SimplyConnectedSpace M := h.simplyConnectedSpace
  exact poincare_conjecture M

end DifferentialGeometry.Topology
