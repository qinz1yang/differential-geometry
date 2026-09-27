import DifferentialGeometry.Geometry.Neck.Scaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ModelWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.QuotientCollapse

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.PDE.RicciFlow.StandardCap
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Neck.normalizedDatum
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) := radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) := radialCapAttachment_isManifold transitionEnd_pos hB
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) := radialCapAttachment_t2Space transitionEnd_pos hB
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
private local instance : NeZero (Module.finrank ℝ E) := ⟨by rw [show Module.finrank ℝ E = 3 from Fact.out]; decide⟩

theorem rescaled_positiveRetainedMap (d : normalizedDatum g x₀ δ k) (c : ℝ) (hc : 0 < c) :
    (d.rescaled c hc).positiveRetainedMap = d.positiveRetainedMap := rfl

theorem rescaled_positiveSideInsertionMetric (d : normalizedDatum g x₀ δ k) (c : ℝ) (hc : 0 < c)
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    (d.rescaled c hc).positiveSideInsertionMetric hA hAB =
      scaleMetric c hc (d.positiveSideInsertionMetric hA hAB) := by
  have he : insertedQuotientMetric hA hAB (d.rescaled c hc).controlledMetric_cylinder_lower.1
      (d.rescaled c hc).controlledMetric =
      insertedQuotientMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric := by
    exact congrArg (fun h => insertedQuotientMetric hA hAB d.controlledMetric_cylinder_lower.1 h)
      (d.rescaled_controlledMetric c hc)
  apply SmoothRiemannianMetric.ext_inner
  intro p u v
  change (metricScalarAt (scaleMetric c hc g) x₀)⁻¹ *
    (insertedQuotientMetric hA hAB (d.rescaled c hc).controlledMetric_cylinder_lower.1
      (d.rescaled c hc).controlledMetric).inner p u v =
      c * ((metricScalarAt g x₀)⁻¹ *
        (insertedQuotientMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric).inner p u v)
  rw [he, metricScalarAt_scaleMetric]
  field_simp [hc.ne', d.scalar_pos.ne']

theorem rescaled_positiveSideQuotientCollapseMap (d : normalizedDatum g x₀ δ k)
    (c : ℝ) (hc : 0 < c) {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹)
    (x : d.controlledImage) :
    (d.rescaled c hc).positiveSideQuotientCollapseMap hA hAB x =
      d.positiveSideQuotientCollapseMap hA hAB x := rfl

theorem rescaled_modelWindowPullback (d : normalizedDatum g x₀ δ k) (c : ℝ) (hc : 0 < c)
    {A R : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (hfit : R ≤ transitionEnd + δ⁻¹) :
    modelWindowPullback (inv_pos.mpr d.precision_pos) hfit
      (scaleMetric (metricScalarAt (scaleMetric c hc g) x₀) (d.rescaled c hc).scalar_pos
        ((d.rescaled c hc).positiveSideInsertionMetric hA hAB)) =
    modelWindowPullback (inv_pos.mpr d.precision_pos) hfit
      (scaleMetric (metricScalarAt g x₀) d.scalar_pos (d.positiveSideInsertionMetric hA hAB)) := by
  rw [normalizedDatum_modelWindowPullback, normalizedDatum_modelWindowPullback]
  exact congrArg (fun h => (insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 h).restrictOpenOfSubset
    (modelWindow_le_insertionBall hfit)) (d.rescaled_controlledMetric c hc)

end DifferentialGeometry.Geometry.Neck.normalizedDatum
