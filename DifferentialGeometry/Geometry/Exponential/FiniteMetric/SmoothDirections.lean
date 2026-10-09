import DifferentialGeometry.Geometry.Exponential.FiniteMetric.SmoothAgreement
import DifferentialGeometry.Geometry.Collapse.SublevelCore.Defs
import DifferentialGeometry.Geometry.Comparison.Soul.NoncriticalDistance

/-!
# Minimizing-direction sets of a complete smooth metric through the ported exponential map

The chapter-13 direction sets `inwardMinimizingDirections` (the blueprint's `𝒰_n(q)`) and
`minimizingDirectionsTo` are defined with the smooth API's `intrinsicGeodesic`. Through
`expMap_smul_eq_intrinsicGeodesic` they are the corresponding sets written with the ported
finite-order exponential map `g.expMap`, which is the form in which the finite-metric results
(packages CM1–CM4) are stated. Lane CM-H (package CM, row 3), 2026-10-04.
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

/-- `𝒰_n(q)` in terms of the ported exponential map. -/
theorem mem_inwardMinimizingDirections_iff_expMap
    {g : DifferentialGeometry.SmoothRiemannianMetric I M}
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g) {n q : M}
    {v : TangentSpace I q} :
    v ∈ DifferentialGeometry.Geometry.Collapse.inwardMinimizingDirections g hEnorm n q ↔
      g.inner q v v = 1 ∧ g.expMap (⟨q, dist n q • v⟩ : TangentBundle I M) = n := by
  rw [DifferentialGeometry.Geometry.Collapse.mem_inwardMinimizingDirections,
    expMap_smul_eq_intrinsicGeodesic g hEnorm q v (dist n q)]

/-- The minimizing unit directions to a set, in terms of the ported exponential map. -/
theorem minimizingDirectionsTo_eq_setOf_expMap
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g) (S : Set M) (q : M) :
    DifferentialGeometry.Geometry.Topology.minimizingDirectionsTo g hEnorm S q =
      {u | g.inner q u u = 1 ∧
        g.expMap (⟨q, Metric.infDist q S • u⟩ : TangentBundle I M) ∈ S} := by
  ext u
  change (g.inner q u u = 1 ∧ _ ∈ S) ↔ _
  rw [Set.mem_ofPred_eq, expMap_smul_eq_intrinsicGeodesic g hEnorm q u (Metric.infDist q S)]

end Bundle.ContMDiffRiemannianMetric
