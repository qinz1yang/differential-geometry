import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Defs
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.MetricSource
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity
import DifferentialGeometry.Geometry.Metric.Convergence.Time.Lipschitz
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Topology.SigmaCompactOpen

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.CheegerGromovCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]

def pointedOpenBall
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (R : ℝ) : Set Y.M := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  exact {y | riemannianEDistOf (I := I) Y.metric Y.basepoint y < ENNReal.ofReal R}

def pointedClosedBall
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (R : ℝ) : Set Y.M := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  exact {y | riemannianEDistOf (I := I) Y.metric Y.basepoint y ≤ ENNReal.ofReal R}

omit [CompleteSpace E] in
theorem pointedClosedBall_isCompact_of_complete
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hY : MetricComplete (I := I) Y) (R : ℝ) :
    letI : TopologicalSpace Y.M := Y.topology
    IsCompact (pointedClosedBall (I := I) Y R) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : T2Space Y.M := Y.t2
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  have hMetric : RiemannianMetricComplete (I := I) Y.metric := by
    refine ⟨?_⟩
    exact MetricComplete.complete (I := I) Y hY
  exact RiemannianMetricComplete.closedEBall_isCompact
    (I := I) hMetric Y.basepoint R

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
    [I.Boundaryless] in
theorem pointedClosedBall_subset_pointedOpenBall
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    {s r : ℝ} (hs : 0 ≤ s) (hsr : s < r) :
    pointedClosedBall (I := I) Y s ⊆ pointedOpenBall (I := I) Y r := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  intro y hy
  change riemannianEDistOf (I := I) Y.metric Y.basepoint y ≤ ENNReal.ofReal s at hy
  change riemannianEDistOf (I := I) Y.metric Y.basepoint y < ENNReal.ofReal r
  exact lt_of_le_of_lt hy ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs).2 hsr)

noncomputable def canonicalSourceReferenceMetric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : ℕ) :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainTopology (I := I) Φ k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainChartedSpace (I := I) Φ k
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
      metric_source_domain_smooth (I := I) Φ k
    SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomainTopology (I := I) Φ k
  letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomainChartedSpace (I := I) Φ k
  letI : T2Space (MetricSourceDomain (I := I) Φ k) :=
    metric_source_domain_t2 (I := I) Φ k
  letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
    metric_source_domain_smooth (I := I) Φ k
  exact L.metric.restrictOpen (I := I) (metricSourceOpenSubset (I := I) Φ k)

noncomputable def canonicalMetricSourceData
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : ℕ) :
    MetricSourceData (I := I) Φ k := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  have hSigma : IsSigmaCompact (Φ.source k) :=
    DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I (Φ.source_open k)
  exact MetricSourceData.ofRestrictPullback (I := I) hSigma
    (canonicalSourceReferenceMetric (I := I) Φ k)

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem canonicalMetricSourceData_reference_eq_limit
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : ℕ) :
    let D := canonicalMetricSourceData (I := I) Φ k
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
    D.referenceMetric = D.limitMetric := by
  rfl

structure CanonicalPointedRiemannianCGConverges
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (L : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (subseq : ℕ → ℕ)
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) : Prop where
  converges :
    ∀ K : Set L.M,
      (letI : TopologicalSpace L.M := L.topology; IsCompact K) →
      ∀ p : ℕ, ∀ ε : ℝ, 0 < ε →
        ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
          (canonicalMetricSourceData (I := I) Φ k).derivNormSupOn
            (I := I) K p < ε

namespace CanonicalPointedRiemannianCGConverges

noncomputable def toPointedRiemannianCGConverges
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (C : CanonicalPointedRiemannianCGConverges (I := I) X L subseq Φ) :
    PointedRiemannianConverges (I := I) X L subseq Φ :=
  PointedRiemannianConverges.ofDerivNormSupOn (I := I) Φ C.converges

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem eventually_source_contains
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (_C : CanonicalPointedRiemannianCGConverges (I := I) X L subseq Φ)
    {K : Set L.M}
    (hK : letI : TopologicalSpace L.M := L.topology; IsCompact K) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → K ⊆ Φ.source k :=
  Φ.source_subset hK

end CanonicalPointedRiemannianCGConverges

def CapturesSourceBalls
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (L : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (subseq : ℕ → ℕ)
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) : Prop :=
  ∀ R : ℝ, 0 < R →
    ∃ K : Set L.M,
      (letI : TopologicalSpace L.M := L.topology; IsCompact K) ∧
      ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
        K ⊆ Φ.source k ∧
        pointedClosedBall (I := I) (X.obj (subseq k)) R ⊆ Φ.map k '' K

namespace CapturesSourceBalls

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
    [I.Boundaryless] in
theorem exists_compact_capture
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (C : CapturesSourceBalls (I := I) X L subseq Φ)
    {R : ℝ} (hR : 0 < R) :
    ∃ K : Set L.M,
      (letI : TopologicalSpace L.M := L.topology; IsCompact K) ∧
      ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
        K ⊆ Φ.source k ∧
        pointedClosedBall (I := I) (X.obj (subseq k)) R ⊆ Φ.map k '' K :=
  C R hR

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
    [I.Boundaryless] in
theorem eventually_closedBall_subset_target
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : ℕ → ℕ}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (C : CapturesSourceBalls (I := I) X L subseq Φ)
    {R : ℝ} (hR : 0 < R) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      pointedClosedBall (I := I) (X.obj (subseq k)) R ⊆ Φ.target k := by
  obtain ⟨K, _hK, k0, hk0⟩ := C R hR
  refine ⟨k0, fun k hk y hy => ?_⟩
  obtain ⟨x, hxK, hxy⟩ := hk0 k hk |>.2 hy
  rw [← hxy]
  exact (Φ.partialDiffeomorph k).map_source (hk0 k hk |>.1 hxK)

end CapturesSourceBalls


def constantPointedRiemannianSeq
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) :
    PointedRiemannianSeq.{u, uE, uH} (I := I) where
  obj _ := Y


noncomputable def constantPointedRiemannianCGMaps
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) :
    PointedRiemannianConvergenceMaps (I := I)
      (constantPointedRiemannianSeq (I := I) Y) Y id := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  refine
    { partialDiffeomorph := fun _ =>
        (Diffeomorph.refl I Y.M (∞ : WithTop ℕ∞)).toPartialDiffeomorph
      source_exhausts := ?_
      base_mem := ?_
      basepoint_map := ?_ }
  · refine
      { isOpen := fun _ => isOpen_univ
        mono_step := fun _ => Subset.rfl
        subset := fun K _ => ⟨0, fun _ _ => subset_univ K⟩ }
  · intro k
    exact mem_univ Y.basepoint
  · intro k
    rfl

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem canonicalMetricSourceData_constant_pullback_eq_limit
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (k : ℕ) :
    let Φ := constantPointedRiemannianCGMaps (I := I) Y
    let D := canonicalMetricSourceData (I := I) Φ k
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
    D.pullbackMetric = D.limitMetric := by
  let Φ := constantPointedRiemannianCGMaps (I := I) Y
  let D := canonicalMetricSourceData (I := I) Φ k
  let : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
  let : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
  let : T2Space (MetricSourceDomain (I := I) Φ k) := D.t2
  let : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
  let : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) := D.sigmaCompact
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : T2Space Y.M := Y.t2
  let : IsManifold I ∞ Y.M := Y.smooth
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [D.pullback_inner, D.limit_inner]
  have hmap : Φ.map k (x : Y.M) = (x : Y.M) := rfl
  have hfun :
      (fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : Y.M)) =
        (fun y : MetricSourceDomain (I := I) Φ k => (y : Y.M)) := by
    funext y
    rfl
  rw [hmap, hfun]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem constantPointedRiemannianCGMaps_canonicalConverges
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) :
    CanonicalPointedRiemannianCGConverges (I := I)
      (constantPointedRiemannianSeq (I := I) Y) Y id
      (constantPointedRiemannianCGMaps (I := I) Y) := by
  refine ⟨?_⟩
  intro K hK p ε hε
  refine ⟨0, fun k _ => ?_⟩
  let Φ := constantPointedRiemannianCGMaps (I := I) Y
  let D := canonicalMetricSourceData (I := I) Φ k
  let : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
  let : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
  let : T2Space (MetricSourceDomain (I := I) Φ k) := D.t2
  let : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
  let : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) := D.sigmaCompact
  change metricDerivNormSupOn (I := I)
      (metricSourceCompactSet (I := I) Φ k K) p
      D.pullbackMetric D.limitMetric D.referenceMetric < ε
  rw [canonicalMetricSourceData_constant_pullback_eq_limit (I := I) Y k]
  refine lt_of_le_of_lt
    (metricDerivNormSupOn_le_of_forall (I := I)
      (metricSourceCompactSet (I := I) Φ k K) p
      D.limitMetric D.limitMetric D.referenceMetric 0 le_rfl ?_) hε
  intro a _ x _
  rw [metricDerivNorm_self]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
    [I.Boundaryless] in
theorem constantPointedRiemannianCGMaps_capturesSourceBalls
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcompact : ∀ R : ℝ, 0 < R →
      letI : TopologicalSpace Y.M := Y.topology
      IsCompact (pointedClosedBall (I := I) Y R)) :
    CapturesSourceBalls (I := I)
      (constantPointedRiemannianSeq (I := I) Y) Y id
      (constantPointedRiemannianCGMaps (I := I) Y) := by
  intro R hR
  refine ⟨pointedClosedBall (I := I) Y R, hcompact R hR, 0, fun k _ => ?_⟩
  constructor
  · intro x hx
    exact mem_univ x
  · intro y hy
    exact ⟨y, hy, rfl⟩

omit [CompleteSpace E] in
theorem constantPointedRiemannianCGMaps_capturesSourceBalls_of_complete
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hY : MetricComplete (I := I) Y) :
    CapturesSourceBalls (I := I)
      (constantPointedRiemannianSeq (I := I) Y) Y id
      (constantPointedRiemannianCGMaps (I := I) Y) :=
  constantPointedRiemannianCGMaps_capturesSourceBalls (I := I) Y
    (fun R _ => pointedClosedBall_isCompact_of_complete (I := I) Y hY R)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
