import Mathlib.Geometry.Manifold.Metrizable

noncomputable section

open Manifold
open scoped Manifold

namespace DifferentialGeometry.Topology.Manifold

section ChartedSpaceInstances

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M]

theorem regularSpace_of_chartedSpace
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [T2Space M] : RegularSpace M := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : WeaklyLocallyCompactSpace M := inferInstance
  have : R1Space M := T2Space.r1Space
  infer_instance

theorem sigmaCompactSpace_of_chartedSpace
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M]
    [SecondCountableTopology M] : SigmaCompactSpace M := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  infer_instance

end ChartedSpaceInstances


end DifferentialGeometry.Topology.Manifold
