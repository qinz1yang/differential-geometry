import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]

section MetricCompactnessCore

variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

structure MetricSourceData
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) where
  topology : TopologicalSpace (MetricSourceDomain (I := I) Φ k)
  charted : ChartedSpace H (MetricSourceDomain (I := I) Φ k)
  t2 : T2Space (MetricSourceDomain (I := I) Φ k)
  smooth : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k)
  sigmaCompact : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k)
  limitMetric :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := charted
    SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k)
  pullbackMetric :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := charted
    SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k)
  referenceMetric :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := charted
    SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k)
  compact_preimage :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := topology
    letI : TopologicalSpace L.M := L.topology
    forall K : Set L.M, IsCompact K ->
      K ⊆ Φ.source k ->
      IsCompact (metricSourceCompactSet (I := I) Φ k K)
  limit_inner :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := charted
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : T2Space L.M := L.t2
    letI : IsManifold I ∞ L.M := L.smooth
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    forall (x : MetricSourceDomain (I := I) Φ k) (v w : TangentSpace I x),
      limitMetric.inner x v w =
        L.metric.inner (x : L.M)
          ((mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x) v)
          ((mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x) w)
  pullback_inner :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := charted
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : T2Space L.M := L.t2
    letI : IsManifold I ∞ L.M := L.smooth
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    letI : TopologicalSpace (X.obj (subseq k)).M :=
      (X.obj (subseq k)).topology
    letI : ChartedSpace H (X.obj (subseq k)).M :=
      (X.obj (subseq k)).charted
    letI : T2Space (X.obj (subseq k)).M :=
      (X.obj (subseq k)).t2
    letI : IsManifold I ∞ (X.obj (subseq k)).M :=
      (X.obj (subseq k)).smooth
    letI : SigmaCompactSpace (X.obj (subseq k)).M :=
      (X.obj (subseq k)).sigmaCompact
    forall (x : MetricSourceDomain (I := I) Φ k) (v w : TangentSpace I x),
      pullbackMetric.inner x v w =
        (X.obj (subseq k)).metric.inner
          (Φ.map k (x : L.M))
          ((mfderiv I I
            (fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : L.M)) x) v)
          ((mfderiv I I
            (fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : L.M)) x) w)

namespace MetricSourceData

def unrepoint
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : forall i : Nat, (X.obj i).M)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianConvergenceMaps (I := I) (X.repoint b) L subseq}
    (hbase : forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      Φ.partialDiffeomorph k L.basepoint = (X.obj (subseq k)).basepoint)
    (k : Nat) (D : MetricSourceData (I := I) Φ k) :
    MetricSourceData (I := I) (Φ.unrepoint b hbase) k where
  topology := D.topology
  charted := D.charted
  t2 := D.t2
  smooth := D.smooth
  sigmaCompact := D.sigmaCompact
  limitMetric := D.limitMetric
  pullbackMetric := D.pullbackMetric
  referenceMetric := D.referenceMetric
  compact_preimage := D.compact_preimage
  limit_inner := D.limit_inner
  pullback_inner := D.pullback_inner

noncomputable def ofCanonical
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    {k : Nat}
    (sigmaCompact :
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainTopology (I := I) Φ k
      SigmaCompactSpace (MetricSourceDomain (I := I) Φ k))
    (limitMetric :
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainTopology (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainChartedSpace (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metric_source_domain_smooth (I := I) Φ k
      SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k))
    (pullbackMetric :
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainTopology (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainChartedSpace (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metric_source_domain_smooth (I := I) Φ k
      SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k))
    (referenceMetric :
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainTopology (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainChartedSpace (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metric_source_domain_smooth (I := I) Φ k
      SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k))
    (limit_inner :
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainTopology (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainChartedSpace (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metric_source_domain_smooth (I := I) Φ k
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      forall (x : MetricSourceDomain (I := I) Φ k) (v w : TangentSpace I x),
        limitMetric.inner x v w =
          L.metric.inner (x : L.M)
            ((mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x) v)
            ((mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x) w))
    (pullback_inner :
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainTopology (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainChartedSpace (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metric_source_domain_smooth (I := I) Φ k
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      letI : T2Space (X.obj (subseq k)).M := (X.obj (subseq k)).t2
      letI : IsManifold I ∞ (X.obj (subseq k)).M :=
        (X.obj (subseq k)).smooth
      letI : SigmaCompactSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).sigmaCompact
      forall (x : MetricSourceDomain (I := I) Φ k) (v w : TangentSpace I x),
        pullbackMetric.inner x v w =
          (X.obj (subseq k)).metric.inner
            (Φ.map k (x : L.M))
            ((mfderiv I I
              (fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : L.M)) x) v)
            ((mfderiv I I
              (fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : L.M)) x) w)) :
    MetricSourceData (I := I) Φ k where
  topology := metricSourceDomainTopology (I := I) Φ k
  charted := metricSourceDomainChartedSpace (I := I) Φ k
  t2 := metric_source_domain_t2 (I := I) Φ k
  smooth := metric_source_domain_smooth (I := I) Φ k
  sigmaCompact := sigmaCompact
  limitMetric := limitMetric
  pullbackMetric := pullbackMetric
  referenceMetric := referenceMetric
  compact_preimage := by
    intro K hK hKsrc
    exact metric_source_compact_set_is_compact (I := I) Φ k hK hKsrc
  limit_inner := limit_inner
  pullback_inner := pullback_inner

noncomputable def ofRestrictPullback
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    {k : Nat}
    (hσsource : letI : TopologicalSpace L.M := L.topology; IsSigmaCompact (Φ.source k))
    (referenceMetric :
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainTopology (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainChartedSpace (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metric_source_domain_smooth (I := I) Φ k
      SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k)) :
    MetricSourceData (I := I) Φ k := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := by
    change IsManifold I ∞ L.M
    infer_instance
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  letI : T2Space (X.obj (subseq k)).M := (X.obj (subseq k)).t2
  letI : IsManifold I ∞ (X.obj (subseq k)).M :=
    (X.obj (subseq k)).smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (subseq k)).M := by
    change IsManifold I ∞ (X.obj (subseq k)).M
    infer_instance
  letI : SigmaCompactSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).sigmaCompact
  letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomainTopology (I := I) Φ k
  letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomainChartedSpace (I := I) Φ k
  letI : T2Space (MetricSourceDomain (I := I) Φ k) := metric_source_domain_t2 (I := I) Φ k
  letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
    metric_source_domain_smooth (I := I) Φ k
  letI : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) :=
    metric_source_domain_sigma_compact (I := I) Φ k hσsource
  letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomainTopology (I := I) Φ k
  letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomainChartedSpace (I := I) Φ k
  letI : T2Space (MetricTargetDomain (I := I) Φ k) := metric_target_domain_t2 (I := I) Φ k
  letI : IsManifold I ∞ (MetricTargetDomain (I := I) Φ k) :=
    metric_target_domain_smooth (I := I) Φ k
  refine MetricSourceData.ofCanonical (I := I)
    (Φ := Φ) (k := k)
    (metric_source_domain_sigma_compact (I := I) Φ k hσsource)
    (by
      let sourceT2 : T2Space (metricSourceOpenSubset (I := I) Φ k) := by
        change T2Space (MetricSourceDomain (I := I) Φ k)
        exact metric_source_domain_t2 (I := I) Φ k
      exact
        @SmoothRiemannianMetric.restrictOpen E inferInstance inferInstance H inferInstance I
          L.M L.topology L.charted L.smooth inferInstance
          L.metric (metricSourceOpenSubset (I := I) Φ k) sourceT2)
    (by
      let sourceT2 : T2Space (metricSourceOpenSubset (I := I) Φ k) := by
        change T2Space (MetricSourceDomain (I := I) Φ k)
        exact metric_source_domain_t2 (I := I) Φ k
      let targetT2 : T2Space (metricTargetOpenSubset (I := I) Φ k) := by
        change T2Space (MetricTargetDomain (I := I) Φ k)
        exact metric_target_domain_t2 (I := I) Φ k
      let targetMetric : SmoothRiemannianMetric I (metricTargetOpenSubset (I := I) Φ k) :=
        @SmoothRiemannianMetric.restrictOpen E inferInstance inferInstance H inferInstance I
          (X.obj (subseq k)).M (X.obj (subseq k)).topology
          (X.obj (subseq k)).charted (X.obj (subseq k)).smooth inferInstance
          (X.obj (subseq k)).metric (metricTargetOpenSubset (I := I) Φ k)
          targetT2
      exact
        @Diffeomorph.pullbackMetric E inferInstance inferInstance inferInstance H inferInstance I
          (MetricSourceDomain (I := I) Φ k) (metricSourceDomainTopology (I := I) Φ k)
          (metricSourceDomainChartedSpace (I := I) Φ k) (metric_source_domain_smooth (I := I) Φ k)
          (MetricTargetDomain (I := I) Φ k) (metricTargetDomainTopology (I := I) Φ k)
          (metricTargetDomainChartedSpace (I := I) Φ k) (metric_target_domain_smooth (I := I) Φ k)
          sourceT2 targetMetric (metricSourceTargetDiffeomorph (I := I) Φ k))
    referenceMetric
    ?_ ?_
  · intro x v w
    change L.metric.inner (x : L.M) v w =
      L.metric.inner (x : L.M)
        ((mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x) v)
        ((mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x) w)
    have hvinc :
        (mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x) v = v := by
      simpa only using
        mfderiv_subtype_val_apply (I := I) (metricSourceOpenSubset (I := I) Φ k) x v
    have hwinc :
        (mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x) w = w := by
      simpa only using
        mfderiv_subtype_val_apply (I := I) (metricSourceOpenSubset (I := I) Φ k) x w
    rw [hvinc, hwinc]
  · intro x v w
    rw [Diffeomorph.pullbackMetric_inner]
    change (X.obj (subseq k)).metric.inner
        ((metricSourceTargetDiffeomorph (I := I) Φ k x : MetricTargetDomain (I := I) Φ k) :
          (X.obj (subseq k)).M)
        ((mfderiv I I (metricSourceTargetDiffeomorph (I := I) Φ k) x) v)
        ((mfderiv I I (metricSourceTargetDiffeomorph (I := I) Φ k) x) w) =
      (X.obj (subseq k)).metric.inner
        (Φ.map k (x : L.M))
        ((mfderiv I I
          (fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : L.M)) x) v)
        ((mfderiv I I
          (fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : L.M)) x) w)
    have hchain :
        mfderiv I I
            (fun y : MetricSourceDomain (I := I) Φ k =>
              ((metricSourceTargetDiffeomorph (I := I) Φ k y : MetricTargetDomain (I := I) Φ k) :
                (X.obj (subseq k)).M)) x =
          (mfderiv I I
              (fun y : MetricTargetDomain (I := I) Φ k => (y : (X.obj (subseq k)).M))
              (metricSourceTargetDiffeomorph (I := I) Φ k x)).comp
            (mfderiv I I (metricSourceTargetDiffeomorph (I := I) Φ k) x) := by
      have hval :
          MDifferentiableAt I I
            (fun y : MetricTargetDomain (I := I) Φ k => (y : (X.obj (subseq k)).M))
            (metricSourceTargetDiffeomorph (I := I) Φ k x) := by
        exact ContMDiffAt.mdifferentiableAt
          ((contMDiff_subtype_val (I := I) (n := (∞ : WithTop ℕ∞))
            (U := metricTargetOpenSubset (I := I) Φ k)).contMDiffAt)
          (by simp)
      have hdiff :
          MDifferentiableAt I I (metricSourceTargetDiffeomorph (I := I) Φ k)
            x :=
        (metricSourceTargetDiffeomorph (I := I) Φ k).contMDiff.contMDiffAt.mdifferentiableAt
          (by simp)
      simpa [Function.comp_def] using
        (mfderiv_comp (I := I) (I' := I) (I'' := I) x hval hdiff)
    have hv :
        mfderiv I I
            (fun y : MetricSourceDomain (I := I) Φ k =>
              ((metricSourceTargetDiffeomorph (I := I) Φ k y : MetricTargetDomain (I := I) Φ k) :
                (X.obj (subseq k)).M)) x v =
          mfderiv I I (metricSourceTargetDiffeomorph (I := I) Φ k) x v := by
      rw [hchain, ContinuousLinearMap.comp_apply]
      have htarget :
          (mfderiv I I
              (fun y : MetricTargetDomain (I := I) Φ k => (y : (X.obj (subseq k)).M))
              (metricSourceTargetDiffeomorph (I := I) Φ k x))
            ((mfderiv I I (metricSourceTargetDiffeomorph (I := I) Φ k) x) v) =
            (mfderiv I I (metricSourceTargetDiffeomorph (I := I) Φ k) x) v := by
        simpa only using
          mfderiv_subtype_val_apply (I := I) (metricTargetOpenSubset (I := I) Φ k)
            (metricSourceTargetDiffeomorph (I := I) Φ k x)
            ((mfderiv I I (metricSourceTargetDiffeomorph (I := I) Φ k) x) v)
      exact htarget
    have hw :
        mfderiv I I
            (fun y : MetricSourceDomain (I := I) Φ k =>
              ((metricSourceTargetDiffeomorph (I := I) Φ k y : MetricTargetDomain (I := I) Φ k) :
                (X.obj (subseq k)).M)) x w =
          mfderiv I I (metricSourceTargetDiffeomorph (I := I) Φ k) x w := by
      rw [hchain, ContinuousLinearMap.comp_apply]
      have htarget :
          (mfderiv I I
              (fun y : MetricTargetDomain (I := I) Φ k => (y : (X.obj (subseq k)).M))
              (metricSourceTargetDiffeomorph (I := I) Φ k x))
            ((mfderiv I I (metricSourceTargetDiffeomorph (I := I) Φ k) x) w) =
            (mfderiv I I (metricSourceTargetDiffeomorph (I := I) Φ k) x) w := by
        simpa only using
          mfderiv_subtype_val_apply (I := I) (metricTargetOpenSubset (I := I) Φ k)
            (metricSourceTargetDiffeomorph (I := I) Φ k x)
            ((mfderiv I I (metricSourceTargetDiffeomorph (I := I) Φ k) x) w)
      exact htarget
    have hxmap :
        ((metricSourceTargetDiffeomorph (I := I) Φ k x : MetricTargetDomain (I := I) Φ k) :
          (X.obj (subseq k)).M) = Φ.map k (x : L.M) :=
      metric_source_target_diffeomorph_apply (I := I) Φ k x
    have hfun :
        (fun y : MetricSourceDomain (I := I) Φ k =>
          ((metricSourceTargetDiffeomorph (I := I) Φ k y : MetricTargetDomain (I := I) Φ k) :
            (X.obj (subseq k)).M)) =
          fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : L.M) := by
      funext y
      exact metric_source_target_diffeomorph_apply (I := I) Φ k y
    rw [hxmap, ← hv, ← hw, hfun]
    rfl

noncomputable def derivNormSupOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {k : Nat}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (D : MetricSourceData (I := I) Φ k)
    (K : Set L.M) (p : Nat) : Real := by
  letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
  letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
  letI : T2Space (MetricSourceDomain (I := I) Φ k) := D.t2
  letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
      (MetricSourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (MetricSourceDomain (I := I) Φ k)
    infer_instance
  letI : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) := D.sigmaCompact
  exact metricDerivNormSupOn (I := I)
    (metricSourceCompactSet (I := I) Φ k K) p
    D.pullbackMetric D.limitMetric D.referenceMetric

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] theorem unrepoint_deriv_norm_sup_on
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : forall i : Nat, (X.obj i).M)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianConvergenceMaps (I := I) (X.repoint b) L subseq}
    (hbase : forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      Φ.partialDiffeomorph k L.basepoint = (X.obj (subseq k)).basepoint)
    (k : Nat) (D : MetricSourceData (I := I) Φ k)
    (K : Set L.M) (p : Nat) :
    (D.unrepoint b hbase k).derivNormSupOn (I := I) K p =
      D.derivNormSupOn (I := I) K p := rfl

end MetricSourceData


end MetricCompactnessCore

end CheegerGromovCompactness
end DifferentialGeometry
