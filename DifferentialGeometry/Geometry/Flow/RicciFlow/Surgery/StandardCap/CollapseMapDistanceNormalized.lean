import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CollapseMapDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.QuotientCollapse

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold TopologicalSpace DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Neck.normalizedDatum

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) := radialCapAttachment_t2Space transitionEnd_pos hB

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

theorem controlledImage_controlledChart_symm_edist (d : normalizedDatum g x₀ δ k)
    (p q : d.controlledImage) :
    riemannianEDistOf d.controlledMetric (d.controlledChart.symm p) (d.controlledChart.symm q) =
      ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀)) *
        riemannianEDistOf (g.restrictOpen d.controlledImage) p q := by
  rw [← edistOf_pullbackMetricCross d.controlledMetric d.controlledChart.symm p q,
    pullback_controlledMetric_controlledChart_symm,
    DifferentialGeometry.edistOf_scale (metricScalarAt g x₀) d.scalar_pos
      (g.restrictOpen d.controlledImage) p q]

theorem positiveSideCollapseMap_riemannianEDistOf_le (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (p q : d.controlledImage) :
    riemannianEDistOf (d.positiveSideCollapseMetric hA hAB)
        (d.positiveSideCollapseMap hA hAB p) (d.positiveSideCollapseMap hA hAB q) ≤
      riemannianEDistOf (g.restrictOpen d.controlledImage) p q := by
  have hmodel :=
    DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_riemannianEDistOf_le_of_cylinder_lower
      hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric
      d.controlledMetric_cylinder_lower.2 (d.controlledChart.symm p) (d.controlledChart.symm q)
  have hscale : ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀)⁻¹) *
      ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      ← Real.sqrt_mul (inv_nonneg.mpr d.scalar_pos.le), inv_mul_cancel₀ d.scalar_pos.ne',
      Real.sqrt_one, ENNReal.ofReal_one]
  calc riemannianEDistOf (d.positiveSideCollapseMetric hA hAB)
        (d.positiveSideCollapseMap hA hAB p) (d.positiveSideCollapseMap hA hAB q)
      = ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀)⁻¹) *
          riemannianEDistOf
            (insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric)
            (collapseMap hA hAB (d.controlledChart.symm p))
            (collapseMap hA hAB (d.controlledChart.symm q)) := by
        rw [positiveSideCollapseMap, positiveSideCollapseMetric, Function.comp_apply]
        exact DifferentialGeometry.edistOf_scale (metricScalarAt g x₀)⁻¹
          (inv_pos.mpr d.scalar_pos)
          (insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric)
          (collapseMap hA hAB (d.controlledChart.symm p))
          (collapseMap hA hAB (d.controlledChart.symm q))
    _ ≤ ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀)⁻¹) *
          riemannianEDistOf d.controlledMetric
            (d.controlledChart.symm p) (d.controlledChart.symm q) :=
        mul_le_mul_right hmodel _
    _ = ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀)⁻¹) *
          (ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀)) *
            riemannianEDistOf (g.restrictOpen d.controlledImage) p q) := by
        rw [controlledImage_controlledChart_symm_edist]
    _ = riemannianEDistOf (g.restrictOpen d.controlledImage) p q := by
        rw [← mul_assoc, hscale, one_mul]

theorem positiveSideQuotientCollapseMap_riemannianEDistOf_le (d : normalizedDatum g x₀ δ k)
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (p q : d.controlledImage) :
    letI := radialCapAttachmentChartedSpace transitionEnd_pos (inv_pos.mpr d.precision_pos)
    riemannianEDistOf (d.positiveSideInsertionMetric hA hAB)
        (d.positiveSideQuotientCollapseMap hA hAB p)
        (d.positiveSideQuotientCollapseMap hA hAB q) ≤
      riemannianEDistOf (g.restrictOpen d.controlledImage) p q := by
  rw [d.positiveSideQuotientCollapseMap_edist hA hAB p q]
  exact d.positiveSideCollapseMap_riemannianEDistOf_le hA hAB p q

end DifferentialGeometry.Geometry.Neck.normalizedDatum
