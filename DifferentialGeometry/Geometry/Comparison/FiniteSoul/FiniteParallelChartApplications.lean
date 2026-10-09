import DifferentialGeometry.Geometry.Comparison.FiniteSoul.FiniteParallelChart
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Completeness

/-!
# Consumers of the finite parallel-transport chart toolkit (lane CMS3-PT, group G1)

In the frozen setting of CM-S-three (complete `M`, metric of class `C^{r+1}`, `1 ≤ r`, `hnorm`):
the velocity of a geodesic is a parallel field along it (`IsParallelAlongFinite` along `univ`), and on a
degenerate interval every field is parallel.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] {r : ℕ∞}

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

/-- **The velocity of a geodesic is parallel** (`C²` metric, complete `M`). -/
theorem isParallelAlongFinite_geodesicFlow_velocity
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : TangentBundle I M) :
    IsParallelAlongFinite g (fun t => (g.geodesicFlow p t).proj)
      (fun t => ((g.geodesicFlow p t).snd : E)) univ := by
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ_of_one_le g hr hnorm
  have hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain := fun t => by rw [hD]; exact mem_univ _
  refine (isParallelAlongFinite_geodesicFlow_iff hr (fun t _ => hdom t)
    (fun t _ => uniqueDiffWithinAt_univ)).2 fun t _ q hq => ?_
  exact (hasDerivAt_extChartAt_tangent_geodesicFlow hr g (hdom t) hq).hasDerivWithinAt

omit [I.Boundaryless] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M] in
/-- On a degenerate interval `Icc a a` every field along every curve is parallel. -/
theorem isParallelAlongFinite_Icc_self
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (c : ℝ → M) (V : ℝ → E) (a : ℝ) : IsParallelAlongFinite g c V (Icc a a) := by
  rw [Icc_self]
  exact isParallelAlongFinite_of_subsingleton g c V subsingleton_singleton

end DifferentialGeometry.Geometry.FiniteSoul
