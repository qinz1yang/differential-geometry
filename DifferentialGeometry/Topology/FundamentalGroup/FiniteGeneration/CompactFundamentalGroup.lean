import DifferentialGeometry.Topology.FundamentalGroup.FiniteGeneration.CoverConnectors
import Mathlib.Geometry.Manifold.Metrizable
set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry.Topology
open scoped Manifold
namespace GC.Topology
universe u v

theorem compact_metric_fundamentalGroup_fg (X : Type u) [MetricSpace X]
    [CompactSpace X] [StronglyLocallyContractibleSpace X] [PathConnectedSpace X] (x : X) :
    Group.FG (FundamentalGroup X x) := by
  obtain ⟨ι, hι, V, hV, hcover, hpair⟩ := exists_finite_pairwise_simplyConnected_cover X
  let : Fintype ι := hι
  let : ∀ i, PathConnectedSpace (V i) := fun i =>
    isPathConnected_iff_pathConnectedSpace.mp (hV i).2
  exact groupFG_of_finite_pairwise_cover V x hpair (fun i => (hV i).1) hcover

theorem compact_normed_charts_fundamentalGroup_fg
    (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Type u) [TopologicalSpace X] [ChartedSpace E X] [CompactSpace X]
    [T2Space X] [PathConnectedSpace X] (x : X) : Group.FG (FundamentalGroup X x) := by
  let : StronglyLocallyContractibleSpace E := normed_stronglyLocallyContractible E
  let : StronglyLocallyContractibleSpace X := charted_stronglyLocallyContractible E X
  let : TopologicalSpace.MetrizableSpace X := Manifold.metrizableSpace 𝓘(ℝ, E) X
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  exact compact_metric_fundamentalGroup_fg X x

end GC.Topology
