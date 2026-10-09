import DifferentialGeometry.Topology.PiecewiseLinear.Moise352Producer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Extinction.Existence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ExtinctionReconstruction
import DifferentialGeometry.Geometry.Metric.Construction.Existence
import DifferentialGeometry.Topology.Manifold.Orientation

set_option autoImplicit false

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem smooth_poincare_conjecture
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] :
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
  obtain ⟨g⟩ := Geometry.nonempty_smoothRiemannianMetric (I := 𝓡 3) (M := M)
  obtain ⟨o⟩ := Manifold.exists_manifoldOrientation_of_simply_connected
    (E := EuclideanSpace ℝ (Fin 3)) (M := M) (n := 3) (by simp)
  obtain ⟨W⟩ := PDE.RicciFlow.Surgery.exists_poincare_controlled_extinction
    { Carrier := M, orientation := o } g
  exact W.nonempty_diffeomorph_sphere

theorem poincare_conjecture
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] :
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
  obtain ⟨C, hC⟩ := PiecewiseLinear.exists_isManifold_three (M := M)
  let := C
  let : IsManifold (𝓡 3) ∞ M := hC
  obtain ⟨f⟩ := smooth_poincare_conjecture M
  exact ⟨f.toHomeomorph⟩

end DifferentialGeometry.Topology
