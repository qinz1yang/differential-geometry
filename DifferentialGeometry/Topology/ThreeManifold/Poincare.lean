import DifferentialGeometry.Topology.PiecewiseLinear.Moise352Producer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Skeleton.PoincareEndgame

set_option autoImplicit false

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem poincare_conjecture
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] :
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
  obtain ⟨C, hC⟩ := PiecewiseLinear.exists_isManifold_three (M := M)
  let := C
  let : IsManifold (𝓡 3) ∞ M := hC
  obtain ⟨f⟩ := PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_holds M
  exact ⟨f.toHomeomorph⟩

end DifferentialGeometry.Topology
