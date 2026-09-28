import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chart

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def extChartAtPartialDiffeomorph (n : ℕ∞ω) [IsManifold I n M] (x : M) :
    PartialDiffeomorph I 𝓘(𝕜, E) M E n :=
  DifferentialGeometry.PartialDiffeomorph.extChartAt I n x
