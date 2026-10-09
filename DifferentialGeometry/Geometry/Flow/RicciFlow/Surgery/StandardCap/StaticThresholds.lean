import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.NormalizedInsertionPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.NormalizedInsertionDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ModelWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CollapseProfile

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Topology
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) := radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) := radialCapAttachment_isManifold transitionEnd_pos hB
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) := radialCapAttachment_t2Space transitionEnd_pos hB

theorem exists_uniform_positiveCoordinate_static_estimates :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧ ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∃ (hAB : 2 * A < δ⁻¹) (hfit : D + 1 ≤ transitionEnd + δ⁻¹),
          collapseTip A ∈ Ioo (-δ⁻¹) (-2 * A - transitionEnd) ∧
          ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
            [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
            [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
            [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
            ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ (m + 4)),
              let out := d.positiveSideInsertionMetric hA hAB
              metricDerivENormSupOn
                {x : modelWindow (D + 1) | (riemannianEDistOf metric 0 x.val).toReal < D} m
                (modelWindowPullback (inv_pos.mpr d.precision_pos) hfit
                  (scaleMetric (metricScalarAt g x₀) d.scalar_pos out))
                (metric.restrictOpen (modelWindow (D + 1))) (metric.restrictOpen (modelWindow (D + 1))) <
                ENNReal.ofReal ε ∧
              (∀ x, 0 < metricScalarAt out x) ∧
              (∀ a : ℝ, 0 < a →
                (∀ q : openCylinder δ⁻¹,
                  (metricScalarAt g (d.controlledMap q),
                    2 * leastCurvatureOperatorEigenvalueAt g (d.controlledMap q)
                      (metricAlgebraicCurvatureTensorAt g (d.controlledMap q))) ∈ fixedHamiltonIveyRegion a) →
                ∀ x, (metricScalarAt out x,
                  2 * leastCurvatureOperatorEigenvalueAt out x (metricAlgebraicCurvatureTensorAt out x)) ∈
                  fixedHamiltonIveyRegion a) ∧
              ∀ q : InsertionQuotient (inv_pos.mpr d.precision_pos),
                q ∈ range (adjunctionCell (radialCapBoundary transitionEnd_pos)
                  (retainedBoundary (inv_pos.mpr d.precision_pos))) →
                (∀ j ≤ m, Real.sqrt (normSq0S out q (4 + j) (iterCov out 4 (metricRm04 out) j q)) ≤
                  C j * (metricScalarAt g x₀) ^ (1 + (j : ℝ) / 2)) ∧
                  |metricScalarAt out q| ≤ C 0 * metricScalarAt g x₀ := by
  obtain ⟨C, hC, hder⟩ := exists_normalizedDatum_positiveSideInsertionMetric_cap_derivative_bounds
  obtain ⟨A, hA, hAsmall, δp, hδp, hδphalf, hpin⟩ :=
    exists_normalizedDatum_positiveSideInsertionMetric_pinching
  refine ⟨C, hC, A, hA, hAsmall, ?_⟩
  intro D hD m ε hε
  obtain ⟨δw, hδw, _, hwin⟩ := exists_normalizedDatum_modelWindow_error_lt A hA D hD m ε hε
  obtain ⟨δc, hδc, _, hcurv⟩ := hder A hA m
  let δt := (2 * A + 5 * transitionEnd / 2 + 3)⁻¹
  have hδt : 0 < δt := inv_pos.mpr (by linarith [transitionEnd_pos])
  let δ₀ := min δp (min δw (min δc δt))
  have hδ₀ : 0 < δ₀ := lt_min hδp (lt_min hδw (lt_min hδc hδt))
  refine ⟨δ₀, hδ₀, (min_le_left _ _).trans_lt hδphalf, ?_⟩
  intro δ hδ hle
  have hp : δ ≤ δp := hle.trans (min_le_left _ _)
  have hw : δ ≤ δw := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc : δ ≤ δc := hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have ht : δ ≤ δt := hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hAB, hb⟩ := hpin δ hδ hp
  obtain ⟨_, hfit, hwbound⟩ := hwin δ hδ hw
  obtain ⟨_, hcbound⟩ := hcurv δ hδ hc
  refine ⟨hAB, hfit, collapseTip_mem_buffer hA hδ ht, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d
  obtain ⟨hR, hHI⟩ := hb (m + 4) (by omega) g x₀ d
  exact ⟨hwbound (m + 4) (by omega) g x₀ d, hR, hHI,
    hcbound (m + 4) (by omega) g x₀ d⟩
end DifferentialGeometry.PDE.RicciFlow.StandardCap
