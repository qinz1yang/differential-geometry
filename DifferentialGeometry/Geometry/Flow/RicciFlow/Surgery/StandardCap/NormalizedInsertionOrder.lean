import DifferentialGeometry.Geometry.Neck.OrderReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.QuotientCollapse

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.StandardCap DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Neck.normalizedDatum
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace E3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k j : ℕ}

theorem lowerOrder_controlledMetric (d : normalizedDatum g x₀ δ k) (hjk : j ≤ k) :
    (d.lowerOrder hjk).controlledMetric = d.controlledMetric := rfl

theorem lowerOrder_positiveRetainedMap (d : normalizedDatum g x₀ δ k) (hjk : j ≤ k) :
    (d.lowerOrder hjk).positiveRetainedMap = d.positiveRetainedMap := rfl

theorem lowerOrder_positiveSideInsertionMetric (d : normalizedDatum g x₀ δ k) (hjk : j ≤ k)
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    (d.lowerOrder hjk).positiveSideInsertionMetric hA hAB = d.positiveSideInsertionMetric hA hAB := rfl

theorem lowerOrder_positiveSideCollapseMetric (d : normalizedDatum g x₀ δ k) (hjk : j ≤ k)
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    (d.lowerOrder hjk).positiveSideCollapseMetric hA hAB = d.positiveSideCollapseMetric hA hAB := rfl

theorem lowerOrder_positiveSideCollapseMap (d : normalizedDatum g x₀ δ k) (hjk : j ≤ k)
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    (d.lowerOrder hjk).positiveSideCollapseMap hA hAB = d.positiveSideCollapseMap hA hAB := rfl

theorem lowerOrder_positiveSideQuotientCollapseMap (d : normalizedDatum g x₀ δ k) (hjk : j ≤ k)
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    (d.lowerOrder hjk).positiveSideQuotientCollapseMap hA hAB =
      d.positiveSideQuotientCollapseMap hA hAB := rfl
end DifferentialGeometry.Geometry.Neck.normalizedDatum
