import DifferentialGeometry.Topology.PiecewiseLinear.ChartGluing
import DifferentialGeometry.Topology.PiecewiseLinear.Moise352Producer

/-!
Ch5 port (P0-PORT): the dimension-three, hypothesis-free chart-gluing step that the
ch5 workbench (`Atlas/Gluing.lean`, baseline b0f2c40) states directly. Here it is
obtained from the dg-ch15 hypothesis-parametrised version and `plApproximation_three`.
-/

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

open DifferentialGeometry.Topology.Manifold (AtlasOn)

theorem exists_atlasOn_union_three_of_metrizable
    {Y : Type u} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    [SecondCountableTopology Y] {U V : Set Y} (hU : IsOpen U) (hV : IsOpen V)
    (A : AtlasOn (plGroupoid 3) U) (B : AtlasOn (plGroupoid 3) V) :
    Nonempty (AtlasOn (plGroupoid 3) (U ∪ V)) :=
  exists_atlasOn_union_of_plApproximation_of_metrizable plApproximation_three hU hV A B

end DifferentialGeometry.Topology.PiecewiseLinear
