import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedIntervalDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.SourceEstimates

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set Bundle
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {subseq : ℕ → ℕ}

theorem source_metric_inner_hasDerivWithinAt_bound_on_closed_interval
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    {a b B C Rv Rw : ℝ} (hab : a < b)
    (hcarrier : Icc a b ⊆ X.D.carrier) (hregular : Ioo a b ⊆ X.D.regular)
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (hmetric : ∀ k t, t ∈ Icc a b →
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      MetricUniformEquivalentOn univ (sourceMetricRestriction Φ R k)
        (sourceMetric Φ hsrc htgt k t) B)
    (hShiT : ∀ k,
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
      letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
      letI : SigmaCompactSpace (X.term (subseq k)).M := (X.term (subseq k)).sigmaCompact
      MovingShiBoundOn (Φ.target k) a b
        (fun _ t => (X.term (subseq k)).S.family.metric t) 0 C)
    (k : ℕ) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) := sourceDomSigmaOf Φ k (hsrc k)
    ∀ t, t ∈ Icc a b → ∀ x : SourceDomain Φ k, ∀ v w : TangentSpace I x,
      Real.sqrt ((sourceMetricRestriction Φ R k).inner x v v) ≤ Rv →
      Real.sqrt ((sourceMetricRestriction Φ R k).inner x w w) ≤ Rw →
      HasDerivWithinAt (fun s => (sourceMetric Φ hsrc htgt k s).inner x v w)
        (-2 * (sourceFlow Φ k (hsrc k) (htgt k)).ricciAt t x (vec2 v w)) (Icc a b) t ∧
      ‖-2 * (sourceFlow Φ k (hsrc k) (htgt k)).ricciAt t x (vec2 v w)‖ ≤
        2 * C * B * (Rv * Rw) := by
  let : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  let : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  let : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  let : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  let : SigmaCompactSpace (SourceDomain (I := I) Φ k) := sourceDomSigmaOf Φ k (hsrc k)
  intro t ht x v w hv hw
  have hS := isSolutionOn_sourceFlow Φ k (hsrc k) (htgt k)
  have hEq := hmetric k t ht
  have hShi := sourceShi Φ hsrc htgt a b 0 C hShiT k 0 (le_refl 0) 0 t ht x (mem_univ x)
  constructor
  · exact metric_inner_hasDerivWithinAt_on_closed_interval
      (sourceFlow Φ k (hsrc k) (htgt k)) hS hab hcarrier hregular ht x v w
  · apply norm_ricci_pairing_le_of_metric_le
      (sourceFlow Φ k (hsrc k) (htgt k)) (sourceMetricRestriction Φ R k)
      (zero_le_one.trans hEq.1) x v w (fun u => (hEq.2 x (mem_univ x) u).2) ?_ hv hw
    exact hShi

end DifferentialGeometry.CheegerGromovCompactness
