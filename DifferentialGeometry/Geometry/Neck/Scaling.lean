import DifferentialGeometry.Geometry.Neck.InsertionInput
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Neck.normalizedDatum
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
private local instance : NeZero (Module.finrank ℝ E) := ⟨by rw [show Module.finrank ℝ E = 3 from Fact.out]; decide⟩

private theorem rescaled_scalar_pos (d : normalizedDatum g x₀ δ k) (c : ℝ) (hc : 0 < c) :
    0 < metricScalarAt (scaleMetric c hc g) x₀ := by
  rw [metricScalarAt_scaleMetric]
  exact mul_pos (inv_pos.mpr hc) d.scalar_pos

private theorem rescaled_center_metric (d : normalizedDatum g x₀ δ k) (c : ℝ) (hc : 0 < c) :
    scaleMetric (metricScalarAt (scaleMetric c hc g) x₀) (rescaled_scalar_pos d c hc)
        (scaleMetric c hc g) = scaleMetric (metricScalarAt g x₀) d.scalar_pos g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x u v
  rw [scaleMetric_inner, scaleMetric_inner, scaleMetric_inner, metricScalarAt_scaleMetric]
  field_simp [hc.ne']

def rescaled (d : normalizedDatum g x₀ δ k) (c : ℝ) (hc : 0 < c) :
    normalizedDatum (scaleMetric c hc g) x₀ δ k := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = Module.finrank ℝ E := by
    rw [show Module.finrank ℝ E = 3 from Fact.out]
    simp
  let hloc := isLocalDiffeomorph_of_injective_mfderiv d.map d.smooth d.immersion hdim
  refine
    { precision_pos := d.precision_pos
      precision_lt_one := d.precision_lt_one
      map := d.map
      smooth := d.smooth
      injective := d.injective
      immersion := d.immersion
      center_eq := d.center_eq
      scalar_pos := rescaled_scalar_pos d c hc
      retainedSide := d.retainedSide
      error_lt := ?_ }
  change metricDerivENormSupOn (controlledCylinder δ) k
    (pullbackMetricOfInjectiveLocalDiffeomorph
      (scaleMetric (metricScalarAt (scaleMetric c hc g) x₀) (rescaled_scalar_pos d c hc)
        (scaleMetric c hc g)) d.map hloc d.injective)
      (referenceMetric δ) (referenceMetric δ) < ENNReal.ofReal δ
  rw [rescaled_center_metric d c hc]
  exact d.error_lt

theorem rescaled_map (d : normalizedDatum g x₀ δ k) (c : ℝ) (hc : 0 < c) :
    (d.rescaled c hc).map = d.map := rfl

theorem rescaled_retainedSide (d : normalizedDatum g x₀ δ k) (c : ℝ) (hc : 0 < c) :
    (d.rescaled c hc).retainedSide = d.retainedSide := rfl

theorem rescaled_normalizedMetric (d : normalizedDatum g x₀ δ k) (c : ℝ) (hc : 0 < c) :
    (d.rescaled c hc).normalizedMetric = d.normalizedMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro x u v
  rw [normalizedMetric_inner, normalizedMetric_inner, rescaled_map,
    scaleMetric_inner, metricScalarAt_scaleMetric]
  field_simp [hc.ne']

theorem rescaled_controlledMetric (d : normalizedDatum g x₀ δ k) (c : ℝ) (hc : 0 < c) :
    (d.rescaled c hc).controlledMetric = d.controlledMetric := by
  change (d.rescaled c hc).normalizedMetric.restrictOpenOfSubset _ = d.normalizedMetric.restrictOpenOfSubset _
  rw [rescaled_normalizedMetric]

end DifferentialGeometry.Geometry.Neck.normalizedDatum
