import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Bounds.ClosedInterval
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Canonical.Compatibility

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedFlowSeq (I := I)}

theorem CanonicalMetricCompactness.metric_uniformly_equivalent_on_closed_interval
    (canon : CanonicalMetricCompactness (I := I) (X.atZero (I := I)))
    (hsrc : SourceIsSigmaCompact (pointedCGHMapsOfManifold X
      canon.compactness.limit canon.compactness.subseq canon.compactness.maps))
    (htgt : TargetIsSigmaCompact (pointedCGHMapsOfManifold X
      canon.compactness.limit canon.compactness.subseq canon.compactness.maps))
    (hcurv : FlowCurvatureBoundedOnCompactWindows X)
    {a b : ℝ} (hab : a < b) (hcarrier : Icc a b ⊆ X.D.carrier)
    (hregular : Ioo a b ⊆ X.D.regular) (hzero : (0 : ℝ) ∈ Icc a b) :
    let mc := canon.compactness
    let Φ := pointedCGHMapsOfManifold X mc.limit mc.subseq mc.maps
    ∃ B : ℝ, 1 ≤ B ∧ ∀ k : ℕ,
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      ∀ t ∈ Icc a b,
        MetricUniformEquivalentOn univ (sourceMetricRestriction Φ mc.limit.metric k)
          (sourceMetric Φ hsrc htgt k t) B := by
  let mc := canon.compactness
  let Φ := pointedCGHMapsOfManifold X mc.limit mc.subseq mc.maps
  let : TopologicalSpace mc.limit.M := mc.limit.topology
  let : ChartedSpace H mc.limit.M := mc.limit.charted
  let : T2Space mc.limit.M := mc.limit.t2
  let : IsManifold I ∞ mc.limit.M := mc.limit.smooth
  let : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
  let gRefT : ∀ k : ℕ,
      letI : TopologicalSpace (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).topology
      letI : ChartedSpace H (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).charted
      letI : IsManifold I ∞ (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).smooth
      SmoothRiemannianMetric I (X.term (mc.subseq k)).M := fun k =>
    letI : TopologicalSpace (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).topology
    letI : ChartedSpace H (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).charted
    letI : T2Space (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).t2
    letI : IsManifold I ∞ (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).smooth
    letI : SigmaCompactSpace (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).sigmaCompact
    (X.term (mc.subseq k)).S.family.metric 0
  obtain ⟨Crel, hCrel, hrelZero⟩ := canon.metric_uniformly_equivalent hsrc htgt
  obtain ⟨B, hB, hEqTarget⟩ := hcurv.metric_equiv_on_closed_interval X hab hcarrier hregular hzero
  have hrel : ∀ k : ℕ,
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      MetricUniformEquivalentOn univ (sourceMetricRestriction Φ mc.limit.metric k)
        (targetReferenceMetricPullback Φ gRefT k) Crel := fun k => hrelZero k
  have hequivT : ∀ k : ℕ,
      letI : TopologicalSpace (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).topology
      letI : ChartedSpace H (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).charted
      letI : T2Space (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).t2
      letI : IsManifold I ∞ (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).smooth
      letI : SigmaCompactSpace (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).sigmaCompact
      MetricUniformEquivalentOnWindow (Φ.target k) a b (gRefT k)
        (fun _ t => (X.term (mc.subseq k)).S.family.metric t) (fun _ => B) := by
    intro k
    let : TopologicalSpace (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).topology
    let : ChartedSpace H (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).charted
    let : T2Space (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).t2
    let : IsManifold I ∞ (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).smooth
    let : SigmaCompactSpace (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).sigmaCompact
    exact metricUniformEquivalentOnWindow_mono (subset_univ (Φ.target k)) (hEqTarget (mc.subseq k))
  refine ⟨Crel * B, one_le_mul_of_one_le_of_one_le hCrel hB, fun k t ht => ?_⟩
  exact sourceEquivOn Φ mc.limit.metric hsrc htgt a b gRefT (fun _ => B) Crel hequivT hrel k t ht

end DifferentialGeometry.CheegerGromovCompactness
