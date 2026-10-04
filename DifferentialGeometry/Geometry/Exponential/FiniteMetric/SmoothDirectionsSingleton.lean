import DifferentialGeometry.Geometry.Exponential.FiniteMetric.SmoothDirections
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.MinimizingDirections

/-!
# `𝒰_n(q)` is the finite-metric direction set to `{n}` (B5)

For a complete smooth metric `g` carrying the distance, the chapter-13 set of inward unit
minimizing directions `inwardMinimizingDirections g hEnorm n q` (the blueprint's `𝒰_n(q)`) is the
finite-order set `finiteMinimizingDirectionsTo g {n} q` (CM3) for the singleton target. This is the
bridge between the LC50′ outputs (stated with `finiteMinimizingDirectionsTo`) and the smooth
consumers LC48/LC49/LC51 (stated with `inwardMinimizingDirections`). Lane F8-NEW2, task 4.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace Bundle.ContMDiffRiemannianMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **B5.** `𝒰_n(q)` equals the finite-metric set of minimizing unit directions to `{n}`. -/
theorem inwardMinimizingDirections_eq_finiteMinimizingDirectionsTo
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g) (n q : M) :
    DifferentialGeometry.Geometry.Collapse.inwardMinimizingDirections g hEnorm n q =
      finiteMinimizingDirectionsTo g {n} q := by
  ext v
  rw [mem_inwardMinimizingDirections_iff_expMap]
  change _ ↔ (g.inner q v v = 1 ∧
    g.expMap (⟨q, Metric.infDist q {n} • v⟩ : TangentBundle I M) ∈ ({n} : Set M))
  rw [Metric.infDist_singleton, mem_singleton_iff, dist_comm]

end Bundle.ContMDiffRiemannianMetric
