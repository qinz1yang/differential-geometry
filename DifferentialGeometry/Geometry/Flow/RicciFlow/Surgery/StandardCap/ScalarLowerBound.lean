import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness
import DifferentialGeometry.Geometry.Curvature.OpenEmbeddingPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Scalar
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.ScalarPerturbation

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev Cap := {x : E3 // ‖x‖ ≤ transitionEnd}
private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace E3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB
private local instance (U : Opens E3) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) U.isOpen)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ A D η : ℝ} {k m : ℕ} {hA : 0 < A}

theorem CanonicalStaticInsertionWitness.cap_scalar_eq_modelWindowPullback
    (d : normalizedDatum g x₀ δ k) (w : CanonicalStaticInsertionWitness d A hA D m η)
    {R : ℝ} (hfit : R ≤ transitionEnd + δ⁻¹) (x : Cap) (hx : ‖x.val‖ < R) :
    metricScalarAt w.data.outMetric (w.data.capMap x) = metricScalarAt g x₀ *
      metricScalarAt
        (modelWindowPullback (inv_pos.mpr d.precision_pos) hfit
          (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric)) ⟨x.val, hx⟩ := by
  have hpoint : modelWindowMap (inv_pos.mpr d.precision_pos) hfit ⟨x.val, hx⟩ =
      w.data.capMap x := by
    rw [w.properties.capMap_eq, w.properties.capInclusion_eq]
    exact modelWindowMap_agrees_cap _ _ x hx
  have hs := metricScalarAt_pullbackMetricOfInjectiveLocalDiffeomorph_scale w.data.outMetric
    (modelWindowMap (inv_pos.mpr d.precision_pos) hfit)
    (modelWindowMap_isLocalDiffeomorph _ _)
    (isSmoothEmbedding_modelWindowMap _ _).isEmbedding.injective
    (metricScalarAt g x₀) d.scalar_pos ⟨x.val, hx⟩
  change metricScalarAt (modelWindowPullback _ hfit
    (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric)) ⟨x.val, hx⟩ = _ at hs
  rw [hpoint] at hs
  rw [hs]
  field_simp [d.scalar_pos.ne']

end DifferentialGeometry.PDE.RicciFlow.StandardCap

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private local instance {B : ℝ} {hB : 0 < B} : ChartedSpace E3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB
private local instance (U : Opens E3) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) U.isOpen)

theorem exists_canonicalStaticInsertionWitness_cap_scalar_lower_bound (A : ℝ) (hA : 0 < A) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ k : ℕ, 2 ≤ k →
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
      ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ k)
        (D : ℝ) (m : ℕ) (η : ℝ) (w : CanonicalStaticInsertionWitness d A hA D m η),
        ∀ x ∈ range w.data.capMap,
          metricScalarAt g x₀ / 2 ≤ metricScalarAt w.data.outMetric x := by
  let U := modelWindow (transitionEnd + 1 + 1)
  let K : Set U := {x | ‖x.val‖ ≤ transitionEnd}
  have hK : IsCompact K := by
    have hcompact : IsCompact {x : E3 | ‖x‖ ≤ transitionEnd} := by
      simpa only [Metric.closedBall, dist_zero_right] using
        isCompact_closedBall (0 : E3) transitionEnd
    let j : {x : E3 // ‖x‖ ≤ transitionEnd} → U := fun x =>
      ⟨x.val, by change ‖x.val‖ < transitionEnd + 1 + 1; linarith [x.property]⟩
    have hj : Continuous j := continuous_subtype_val.subtype_mk _
    have himage : range j = K := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩
    rw [← himage]
    let : CompactSpace {x : E3 // ‖x‖ ≤ transitionEnd} := isCompact_iff_compactSpace.mp hcompact
    exact isCompact_range hj
  have hlower : ∀ x ∈ K, 1 ≤ metricScalarAt (metric.restrictOpen U) x := by
    intro x _
    rw [metricScalarAt_restrictOpen]
    exact one_le_metricScalarAt x.val
  obtain ⟨ε, hε, hstable⟩ :=
    exists_scalar_lower_bound_of_small_metric_derivatives (metric.restrictOpen U) hK
      (by norm_num : (0 : ℝ) < 1) hlower
  obtain ⟨δ₀, hδ₀, hhalf, hwindow⟩ := exists_normalizedDatum_modelWindow_error_lt
    A hA (transitionEnd + 1) (by linarith [transitionEnd_pos]) 2 ε hε
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hle k hk E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d D m η w x hx
  obtain ⟨hAB, hfit, hclose⟩ := hwindow δ hδ hle
  let out := modelWindowPullback (inv_pos.mpr d.precision_pos) hfit
    (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric)
  have hnorm := hclose k hk g x₀ d.oriented
  rw [← w.properties.outMetric_eq] at hnorm
  have hnorm' : ∀ y ∈ K, ∀ j : ℕ, j ≤ 2 →
      metricDerivNorm j out (metric.restrictOpen U) (metric.restrictOpen U) y ≤ ε := by
    intro y hy j hj
    apply (metricDerivNorm_lt_of_sup_lt _ 2 out (metric.restrictOpen U)
      (metric.restrictOpen U) hnorm hj ?_).le
    change (riemannianEDistOf metric 0 y.val).toReal < transitionEnd + 1
    rw [distance_zero]
    exact lt_of_le_of_lt hy (lt_add_one _)
  obtain ⟨z, rfl⟩ := hx
  have hzin : ‖z.val‖ < transitionEnd + 1 + 1 := by linarith [z.property]
  have hz : (⟨z.val, hzin⟩ : U) ∈ K := z.property
  have hscalar := hstable out hnorm' _ hz
  rw [w.cap_scalar_eq_modelWindowPullback d hfit z hzin]
  have hh := mul_le_mul_of_nonneg_left hscalar d.scalar_pos.le
  simpa only [out, div_eq_mul_inv, one_mul] using hh

end DifferentialGeometry.PDE.RicciFlow.StandardCap
