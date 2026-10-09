import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckMarkSideBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace ThreeSpace (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold ThreeModel ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) := radialCapAttachment_t2Space transitionEnd_pos hB

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k}
  {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}

namespace CanonicalStaticInsertionWitness

variable (w : CanonicalStaticInsertionWitness d A hA D m ε)


include w in
theorem accuracy_pos : 0 < ε :=
  ENNReal.ofReal_pos.mp (bot_le.trans_lt w.properties.window_close)

def window : C(standardCapWindow D, InsertionQuotient (inv_pos.mpr d.precision_pos)) :=
  ⟨w.data.windowMap, w.properties.window_embedding.contMDiff.continuous⟩

theorem window_smooth : IsSmoothEmbedding ThreeModel ThreeModel ∞ w.window :=
  w.properties.window_embedding

theorem window_tip (hx : (0 : ThreeSpace) ∈ standardCapWindow D) :
    w.window ⟨0, hx⟩ = w.data.tip :=
  w.properties.window_pointed

def windowMetric : SmoothRiemannianMetric ThreeModel (standardCapWindow D) :=
  pullbackMetricOfInjectiveLocalDiffeomorph
    (scaleMetric (metricScalarAt g x₀) d.scalar_pos w.data.outMetric)
    w.data.windowMap w.properties.window_local w.properties.window_embedding.isEmbedding.injective

theorem window_inner (x : standardCapWindow D) (V W : TangentSpace ThreeModel x) :
    w.windowMetric.inner x V W = metricScalarAt g x₀ *
      w.data.outMetric.inner (w.window x)
        (mfderiv ThreeModel ThreeModel w.window x V)
        (mfderiv ThreeModel ThreeModel w.window x W) := by
  unfold windowMetric
  erw [pullbackMetricOfInjectiveLocalDiffeomorph_inner, scaleMetric_inner]
  rfl

theorem window_closeness :
    metricDerivNormSupOn {x : standardCapWindow D | ‖x.val‖ < D} m w.windowMetric
      (standardCapMetric.restrictOpen (standardCapWindow D))
      (standardCapMetric.restrictOpen (standardCapWindow D)) < ε := by
  have h := w.properties.window_close
  change metricDerivENormSupOn
    {x : standardCapWindow D | (riemannianEDistOf metric 0 x.val).toReal < D} m
    w.windowMetric (metric.restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal ε at h
  simp only [distance_zero] at h
  have hε : 0 < ε := ENNReal.ofReal_pos.mp (bot_le.trans_lt h)
  have hb : BddAbove {r : ℝ | ∃ j : ℕ, j ≤ m ∧ ∃ x : standardCapWindow D,
      x ∈ {x : standardCapWindow D | ‖x.val‖ < D} ∧
      metricDerivNorm j w.windowMetric (metric.restrictOpen (standardCapWindow D))
        (metric.restrictOpen (standardCapWindow D)) x = r} := by
    refine ⟨ε, ?_⟩
    rintro r ⟨j, hj, x, hx, rfl⟩
    exact (metricDerivNorm_lt_of_sup_lt _ _ _ _ _ h hj hx).le
  rw [metricDerivENormSupOn_eq_ofReal_of_bddAbove _ _ _ _ _ hb] at h
  rw [standardCapMetric_eq_metric]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp h

end CanonicalStaticInsertionWitness
end DifferentialGeometry.PDE.RicciFlow.StandardCap
