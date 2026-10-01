import DifferentialGeometry.Geometry.Neck.Normalized.Basic
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity
import DifferentialGeometry.Geometry.Metric.Convergence.Time.Lipschitz

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section MetricMonotonicity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem metricDerivNormSupOn_mono {K : Set M} (hK : IsCompact K) {j k : ℕ} (hjk : j ≤ k)
    (gk gInf gRef : SmoothRiemannianMetric I M) :
    metricDerivNormSupOn (I := I) K j gk gInf gRef ≤
      metricDerivNormSupOn (I := I) K k gk gInf gRef := by
  refine metricDerivNormSupOn_le_of_forall (I := I) K j gk gInf gRef
    (metricDerivNormSupOn (I := I) K k gk gInf gRef)
    (metricDerivNormSupOn_nonneg K k gk gInf gRef) ?_
  intro a ha x hx
  exact derivNorm_le_sup (I := I) hK (ha.trans hjk) gk gInf gRef hx

end MetricMonotonicity

section NeckDatum

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

def NormalizedNeck.lowerOrder {g : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k j : ℕ}
    (N : NormalizedNeck g δ k) (hjk : j ≤ k) : NormalizedNeck g δ j :=
  { N with
    closeness := lt_of_le_of_lt
      (metricDerivNormSupOn_mono (isCompact_neckClosedTest δ) hjk
        N.normalizedMetric (roundCylinderMetric.restrictOpen (neckBuffer δ))
        (roundCylinderMetric.restrictOpen (neckBuffer δ)))
      N.closeness }

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.scale_eq_inv_sq_of_scalar {g : SmoothRiemannianMetric ThreeModel M}
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck g δ k) {h : ℝ}
    (hcenter : metricScalarAt g N.center = (h ^ 2)⁻¹) :
    N.scale = (h ^ 2)⁻¹ :=
  N.scale_scalar.trans hcenter

end NeckDatum

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
