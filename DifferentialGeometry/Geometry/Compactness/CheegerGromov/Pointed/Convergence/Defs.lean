import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.MetricSource
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

def MetricSourceConvergesOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq)
    (D : forall k : Nat, MetricSourceData (I := I) Φ k)
    (K : Set L.M)
    (p : Nat) : Prop :=
  forall ε : Real, 0 < ε ->
    exists k0 : Nat, forall k : Nat, k0 <= k ->
      K ⊆ Φ.source k /\ (D k).derivNormSupOn (I := I) K p < ε

structure MetricConvergenceData
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) where
  domain : forall k : Nat, MetricSourceData (I := I) Φ k
  converges :
    forall K : Set L.M,
      (letI : TopologicalSpace L.M := L.topology; IsCompact K) →
      forall p : Nat, MetricSourceConvergesOn (I := I) Φ domain K p

namespace MetricConvergenceData

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
    (Cd : MetricConvergenceData (I := I) Φ) :
    MetricConvergenceData (I := I) (Φ.unrepoint b hbase) where
  domain k := (Cd.domain k).unrepoint b hbase k
  converges := by
    intro K hK p ε hε
    simpa only [PointedRiemannianConvergenceMaps.unrepoint_source,
      MetricSourceData.unrepoint_deriv_norm_sup_on] using Cd.converges K hK p ε hε

noncomputable def ofDerivNormSupOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    {D : forall k : Nat, MetricSourceData (I := I) Φ k}
    (hconv : forall K : Set L.M,
      forall _hK : letI : TopologicalSpace L.M := L.topology; IsCompact K,
      forall p : Nat,
        forall ε : Real, 0 < ε ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            (D k).derivNormSupOn (I := I) K p < ε) :
    MetricConvergenceData (I := I) Φ where
  domain := D
  converges := by
    intro K hK p ε hε
    obtain ⟨kSource, hSource⟩ := Φ.source_subset hK
    obtain ⟨kConvergence, hConvergence⟩ := hconv K hK p ε hε
    refine ⟨max kSource kConvergence, fun k hk => ?_⟩
    refine ⟨hSource k (le_trans (Nat.le_max_left kSource kConvergence) hk), ?_⟩
    exact hConvergence k (le_trans (Nat.le_max_right kSource kConvergence) hk)

noncomputable def ofRestrictPullback
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (hσsource : forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      IsSigmaCompact (Φ.source k))
    (referenceMetric : forall k : Nat,
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainTopology (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainChartedSpace (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metric_source_domain_smooth (I := I) Φ k
      SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k))
    (hconv : forall K : Set L.M,
      forall _hK : letI : TopologicalSpace L.M := L.topology; IsCompact K,
      forall p : Nat,
        forall ε : Real, 0 < ε ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            ((MetricSourceData.ofRestrictPullback (I := I)
              (Φ := Φ) (k := k) (hσsource k)
              (referenceMetric k)).derivNormSupOn (I := I) K p) < ε) :
    MetricConvergenceData (I := I) Φ :=
  MetricConvergenceData.ofDerivNormSupOn (I := I)
    (D := fun k => MetricSourceData.ofRestrictPullback (I := I)
      (Φ := Φ) (k := k) (hσsource k) (referenceMetric k))
    hconv

end MetricConvergenceData

structure PointedRiemannianConverges
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (L : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (subseq : Nat -> Nat)
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) where
  metrics : MetricConvergenceData (I := I) Φ

namespace PointedRiemannianConverges

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
    (C : PointedRiemannianConverges (I := I) (X.repoint b) L subseq Φ) :
    PointedRiemannianConverges (I := I) X L subseq (Φ.unrepoint b hbase) where
  metrics := C.metrics.unrepoint b hbase

noncomputable def ofDerivNormSupOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq)
    {D : forall k : Nat, MetricSourceData (I := I) Φ k}
    (hconv : forall K : Set L.M,
      forall _hK : letI : TopologicalSpace L.M := L.topology; IsCompact K,
      forall p : Nat,
        forall ε : Real, 0 < ε ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            (D k).derivNormSupOn (I := I) K p < ε) :
    PointedRiemannianConverges (I := I) X L subseq Φ where
  metrics := MetricConvergenceData.ofDerivNormSupOn (I := I) hconv

noncomputable def ofRestrictPullback
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq)
    (hσsource : forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      IsSigmaCompact (Φ.source k))
    (referenceMetric : forall k : Nat,
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainTopology (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainChartedSpace (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metric_source_domain_smooth (I := I) Φ k
      SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k))
    (hconv : forall K : Set L.M,
      forall _hK : letI : TopologicalSpace L.M := L.topology; IsCompact K,
      forall p : Nat,
        forall ε : Real, 0 < ε ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            ((MetricSourceData.ofRestrictPullback (I := I)
              (Φ := Φ) (k := k) (hσsource k)
              (referenceMetric k)).derivNormSupOn (I := I) K p) < ε) :
    PointedRiemannianConverges (I := I) X L subseq Φ where
  metrics := MetricConvergenceData.ofRestrictPullback (I := I)
    hσsource referenceMetric hconv

end PointedRiemannianConverges

structure MetricCompactLimit
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  subseq : Nat -> Nat
  strictMono : StrictMono subseq
  limit : PointedRiemannianManifold.{u, uE, uH} (I := I)
  limit_complete : MetricComplete (I := I) limit
  maps : PointedRiemannianConvergenceMaps (I := I) X limit subseq
  convergence : PointedRiemannianConverges (I := I) X limit subseq maps

end MetricCompactnessCore

end CheegerGromovCompactness
end DifferentialGeometry
