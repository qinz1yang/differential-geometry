import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Open subsets of σ-compact manifolds are σ-compact

For a charted space `M` over a model `ModelWithCorners ℝ E H` with `E`
finite-dimensional, every open subset of a σ-compact `M` is a σ-compact set.

The finite-dimensional model makes `H`, hence `M`, locally compact, and a
σ-compact charted space over a second-countable model is second-countable; an
open subspace inherits both, so it is σ-compact by
`sigmaCompactSpace_of_locallyCompact_secondCountable`.  No Hausdorff hypothesis
is needed.

This is the producer for the σ-compactness inputs of the flow-limit upgrade
(`FlowLimitData.hσsrc`/`hσtgt` and
`SourceDomainMetricData.ofRestrictPullback` in
`DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness`): the comparison
map source/target domains are open subsets of σ-compact manifolds.
-/

noncomputable section

open TopologicalSpace

namespace DifferentialGeometry
namespace Geometry

/-- Every open subset of a σ-compact charted space over a finite-dimensional
model with corners is σ-compact.  No Hausdorff hypothesis is required. -/
theorem isSigmaCompact_of_isOpen
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [SigmaCompactSpace M]
    {U : Set M} (hU : IsOpen U) : IsSigmaCompact U := by
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : SecondCountableTopology H := I.secondCountableTopology
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  haveI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance

end Geometry
end DifferentialGeometry
