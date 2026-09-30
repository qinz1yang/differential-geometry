import DifferentialGeometry.Topology.HighDimensional.PoincareHighDim
import DifferentialGeometry.Topology.Manifold.SmoothStructureTransport

namespace DifferentialGeometry.Topology

open scoped _root_.Manifold ContDiff ContinuousMap
open Metric

theorem exists_smooth_structure_of_homotopyEquiv_sphere {n : ℕ} (h5 : 5 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin n)) M,
      @IsManifold ℝ _ (EuclideanSpace ℝ (Fin n)) _ _ (EuclideanSpace ℝ (Fin n)) _ (𝓡 n) ∞ M _
        cs := by
  obtain ⟨h⟩ := poincare_high_dim_topological h5 e
  exact exists_smooth_structure_of_homeomorph_sphere h

end DifferentialGeometry.Topology
