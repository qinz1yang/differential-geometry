import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WideModelChart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FiniteStaticRequests
import DifferentialGeometry.Geometry.Neck.InsertionOrientation

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace E3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB
private def capTip : {x : E3 // ‖x‖ ≤ transitionEnd} := ⟨0, by simpa using transitionEnd_pos.le⟩

theorem exists_wideModel_request_threshold (A : ℝ) (hA : 0 < A) (P : StaticRequest) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ hAB : 2 * A < δ⁻¹, P.radius + 1 < δ⁻¹ ∧ ∀ k : ℕ, P.order ≤ k →
        ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
        ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ k),
        P.IsSatisfied (d.oriented.positiveSideInsertionMetric hA hAB)
          (metricScalarAt g x₀) d.scalar_pos (insertionBall δ⁻¹)
          (wideModelMap (inv_pos.mpr d.precision_pos))
          (wideModelMap_isLocalDiffeomorph (inv_pos.mpr d.precision_pos))
          (wideModelMap_isSmoothEmbedding (inv_pos.mpr d.precision_pos)).isEmbedding.injective
          (adjunctionCell (radialCapBoundary transitionEnd_pos)
            (retainedBoundary (inv_pos.mpr d.precision_pos)) capTip) := by
  obtain ⟨δ₀, hδ₀, hhalf, hmod⟩ := exists_normalizedDatum_insertedMetric_ball_error_lt
    A hA P.radius P.radius_pos.le P.order P.error P.error_pos
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hle
  obtain ⟨hAB, hfit, hb⟩ := hmod δ hδ hle
  refine ⟨hAB, hfit, ?_⟩
  intro k hmk E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d
  have hn := hb k hmk g x₀ d.oriented
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    change (riemannianEDistOf metric 0 x).toReal ≤ P.radius at hx
    rw [distance_zero] at hx
    change ‖x‖ < transitionEnd + δ⁻¹
    linarith [transitionEnd_pos]
  · intro h0
    exact wideModelMap_cap (inv_pos.mpr d.precision_pos) capTip
  · have he := normalizedDatum_wideModelPullback d.oriented hA hAB
    change metricDerivENormSupOn
      {x : insertionBall δ⁻¹ | x.val ∈ closedModelBall P.radius} P.order
      (wideModelPullback (inv_pos.mpr d.precision_pos)
        (scaleMetric (metricScalarAt g x₀) d.scalar_pos (d.oriented.positiveSideInsertionMetric hA hAB)))
      (metric.restrictOpen (insertionBall δ⁻¹)) (metric.restrictOpen (insertionBall δ⁻¹)) < _
    rw [he]
    have hm := metricDerivENormSupOn_mono
      (K := {x : insertionBall δ⁻¹ | x.val ∈ closedModelBall P.radius})
      (L := {x : insertionBall δ⁻¹ | ‖x.val‖ ≤ transitionEnd + P.radius})
      (p := P.order) (q := P.order) (fun x hx => ?_) le_rfl
      (insertedMetric hA hAB d.oriented.controlledMetric_cylinder_lower.1 d.oriented.controlledMetric)
      (metric.restrictOpen (insertionBall δ⁻¹)) (metric.restrictOpen (insertionBall δ⁻¹))
    · exact hm.trans_lt hn
    · change (riemannianEDistOf metric 0 x.val).toReal ≤ P.radius at hx
      rw [distance_zero] at hx
      change ‖x.val‖ ≤ transitionEnd + P.radius
      linarith [transitionEnd_pos]
end DifferentialGeometry.PDE.RicciFlow.StandardCap
