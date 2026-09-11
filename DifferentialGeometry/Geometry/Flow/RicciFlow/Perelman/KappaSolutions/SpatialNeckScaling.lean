import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyBasic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance spatialNeckScalingC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

namespace SpatialNeckWitness

def ofScaleMetric {h : SmoothRiemannianMetric I M}
    {yStar : SpatialNeckSphere} {p : M} {epsilon : ℝ}
    (c : ℝ) (hc : 0 < c)
    (W : SpatialNeckWitness (scaleMetric c hc h) yStar p epsilon) :
    SpatialNeckWitness h yStar p epsilon := by
  have hR : 0 < metricScalarAt (I := I) h p := by
    have hpos := W.scalar_pos
    rw [metricScalarAt_scaleMetric] at hpos
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr hc)).mp hpos
  have hcomplete : RiemannianMetricComplete (I := I) h :=
    W.complete.of_lower (inv_pos.mpr hc) (fun x v => by
      rw [scaleMetric_inner, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul])
  refine {
    dimension_three := W.dimension_three
    complete := hcomplete
    epsilon_pos := W.epsilon_pos
    scalar_pos := hR
    embedding := W.embedding
    smooth_embedding := W.smooth_embedding
    marked := W.marked
    normalizedMetric := W.normalizedMetric
    normalized_inner := ?_
    closeness := W.closeness }
  intro x V Z
  rw [W.normalized_inner, spatialNeckScale_inv_sq _ _ W.scalar_pos,
    spatialNeckScale_inv_sq _ _ hR, scaleMetric_inner, metricScalarAt_scaleMetric]
  field_simp [hc.ne']

theorem ofScaleMetric_embedding {h : SmoothRiemannianMetric I M}
    {yStar : SpatialNeckSphere} {p : M} {epsilon : ℝ}
    (c : ℝ) (hc : 0 < c)
    (W : SpatialNeckWitness (scaleMetric c hc h) yStar p epsilon) :
    (W.ofScaleMetric c hc).embedding = W.embedding := rfl

end SpatialNeckWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
