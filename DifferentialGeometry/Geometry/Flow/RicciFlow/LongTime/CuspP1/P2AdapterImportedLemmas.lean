import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterImportedDefs
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Existence
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.HomogeneousRegularity
import DifferentialGeometry.Geometry.Metric.Completeness.PseudoEMetric

/-!
# P2A-24 (imported, EXPLICIT SORRY): mirrors of IMS03 declarations already proved on the other branch

User exception (BRIEF-CP1.md, 2026-10-06): every `sorry` in this file is a verbatim signature mirror
of a declaration of branch `gc/juihuichung/ims03-astra-20261005` (scanned tip `981d9a8cd`,
descendant of `dcf465959`).  Status of all three: **proved on the IMS03 branch** (no `sorry` token in
the source file; transitive closure not audited by us).  Replacement plan for all: after the IMS03
branch is merged, delete the mirror and refer to the original declaration directly.
Register: `docs/geometrization/chapter15/p2-adapter-sorries.md`.  Nothing outside
`CuspP1/P2AdapterImported*.lean` may import this file.
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

universe u


section PositiveDomain
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SecondCountableTopology M]


end PositiveDomain

section ProfileConfinement
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]


end ProfileConfinement

end GC.LongTime.CuspP1
