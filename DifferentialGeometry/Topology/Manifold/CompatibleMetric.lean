import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Metrizable.Uniformity

namespace DifferentialGeometry.Topology

open TopologicalSpace

theorem metrizableSpace_of_compact_charted {n : ℕ} {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] : MetrizableSpace M := by
  let : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M
  infer_instance

end DifferentialGeometry.Topology
