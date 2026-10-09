import DifferentialGeometry.Topology.PiecewiseLinear.ChartGluingCh5Port
import DifferentialGeometry.Topology.Manifold.PartialAtlas.Compact
open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

open DifferentialGeometry.Topology.Manifold (AtlasOn)

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]

theorem exists_atlasOn_univ_three :
    Nonempty (AtlasOn (plGroupoid 3) (univ : Set X)) := by
  have hsc : SecondCountableTopology X :=
    ChartedSpace.secondCountable_of_sigmaCompact (H := EuclideanSpace ℝ (Fin 3)) (M := X)
  have hlc : LocallyCompactSpace X :=
    ChartedSpace.locallyCompactSpace (H := EuclideanSpace ℝ (Fin 3)) (M := X)
  exact AtlasOn.nonempty_univ_of_chart_union (plGroupoid 3) (fun s x A => by
    have hU : IsOpen (⋃ y ∈ s, (chartAt (EuclideanSpace ℝ (Fin 3)) y).source) :=
      isOpen_biUnion fun y _ => (chartAt _ y).open_source
    exact exists_atlasOn_union_three_of_metrizable hU
      (chartAt (EuclideanSpace ℝ (Fin 3)) x).open_source A
      (AtlasOn.ofOpenPartialHomeomorph (chartAt (EuclideanSpace ℝ (Fin 3)) x)))

theorem exists_chartedSpace_hasGroupoid_plGroupoid_three :
    ∃ C : ChartedSpace (EuclideanSpace ℝ (Fin 3)) X,
      letI := C
      HasGroupoid X (plGroupoid 3) := by
  obtain ⟨A⟩ := exists_atlasOn_univ_three (X := X)
  exact ⟨A.chartedSpace, A.hasGroupoid⟩

end DifferentialGeometry.Topology.PiecewiseLinear
