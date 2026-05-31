import RicciFlower.HCGCompactness.BoundedGeometry
import RicciFlower.HCGCompactness.PointedConvergence

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Metric Cheeger--Gromov Compactness

This file states the pointed Riemannian compactness theorem corresponding to
MSM135 Theorem 3.9.  Its proof is the single honest global compactness frontier:
Cheeger--Gromov compactness, direct-limit/exhaustion construction, and smooth
Arzela--Ascoli.
-/

noncomputable section

universe u uE uH

namespace RicciFlower
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

/-- Exhaustion and comparison maps for pointed Cheeger--Gromov convergence of
pointed Riemannian manifolds. -/
structure PointedRiemannianCGMaps
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (L : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (subseq : Nat -> Nat) where
  partialDiffeomorph :
    forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      PartialDiffeomorph I I L.M (X.obj (subseq k)).M (∞ : WithTop ℕ∞)
  source_exhausts :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    ExhaustsByOpen (fun k =>
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      (partialDiffeomorph k).source)
  base_mem :
    forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      L.basepoint ∈ (partialDiffeomorph k).source
  basepoint_map :
    forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      partialDiffeomorph k L.basepoint = (X.obj (subseq k)).basepoint

namespace PointedRiemannianCGMaps

def source
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) : Set L.M := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  exact (Φ.partialDiffeomorph k).source

def target
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    Set ((X.obj (subseq k)).M) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  exact (Φ.partialDiffeomorph k).target

def map
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    L.M -> (X.obj (subseq k)).M := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  exact fun x => (Φ.partialDiffeomorph k) x

theorem source_open
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace L.M := L.topology
    IsOpen (Φ.source k) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  exact (Φ.partialDiffeomorph k).open_source

theorem source_subset
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq)
    {K : Set L.M}
    (hK :
      letI : TopologicalSpace L.M := L.topology
      IsCompact K) :
    exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ Φ.source k := by
  letI : TopologicalSpace L.M := L.topology
  exact Φ.source_exhausts.subset K hK

end PointedRiemannianCGMaps

/-- Source domain of a metric Cheeger--Gromov comparison map. -/
abbrev MetricSourceDomain
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :=
  {x : L.M // x ∈ Φ.source k}

def metricSourceCompactSet
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat)
    (K : Set L.M) : Set (MetricSourceDomain (I := I) Φ k) :=
  {x | (x : L.M) ∈ K}

/-- Open-source metric data for MSM135 Definition 3.5. -/
structure MetricSourceData
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) where
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

noncomputable def derivNormSupOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {k : Nat}
    {Φ : PointedRiemannianCGMaps (I := I) X L subseq}
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

end MetricSourceData

/-- Concrete `C^p` convergence on compact subsets of the metric limit source
domains. -/
def MetricSourceCPConvOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq)
    (D : forall k : Nat, MetricSourceData (I := I) Φ k)
    (K : Set L.M)
    (_hK : letI : TopologicalSpace L.M := L.topology; IsCompact K)
    (p : Nat) : Prop :=
  forall ε : Real, 0 < ε ->
    exists k0 : Nat, forall k : Nat, k0 <= k ->
      K ⊆ Φ.source k /\ (D k).derivNormSupOn (I := I) K p < ε

/-- Compact-open smooth metric convergence after the comparison
diffeomorphisms of MSM135 Definition 3.5. -/
structure MetricCGConvergenceData
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) where
  domain : forall k : Nat, MetricSourceData (I := I) Φ k
  converges :
    forall K : Set L.M,
      forall hK : letI : TopologicalSpace L.M := L.topology; IsCompact K,
      forall p : Nat, MetricSourceCPConvOn (I := I) Φ domain K hK p

/-- MSM135 Definition 3.5, packaged around the source exhaustion and partial
diffeomorphism data. -/
structure PointedRiemannianCGConverges
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (L : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (subseq : Nat -> Nat)
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) where
  metrics : MetricCGConvergenceData (I := I) Φ

/-- Conclusion of MSM135 Theorem 3.9. -/
structure MetricCompactnessConclusion
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  subseq : Nat -> Nat
  strictMono : StrictMono subseq
  limit : PointedRiemannianManifold.{u, uE, uH} (I := I)
  limit_complete : MetricComplete (I := I) limit
  maps : PointedRiemannianCGMaps (I := I) X limit subseq
  convergence : PointedRiemannianCGConverges (I := I) X limit subseq maps

/-- MSM135 Theorem 3.9: compactness for complete pointed Riemannian manifolds
with uniformly bounded geometry and a basepoint injectivity-radius lower bound.

This is the single honest compactness frontier for the HCG interface. -/
def metricCompactness
    [I.Boundaryless]
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (_hcomplete : SeqMetricComplete (I := I) X)
    (_hgeom : SeqBoundedGeometry (I := I) X)
    (_hinj : BaseInjBound (I := I) X) :
    MetricCompactnessConclusion (I := I) X := by
  -- Chapter 4 deep geometric inputs are isolated in
  -- `RicciFlower.HCGCompactness.GeometricInputs`.
  -- Real frontier: Cheeger--Gromov compactness, direct limits, and smooth
  -- Arzela--Ascoli on the pulled-back metrics.
  sorry

end HCGCompactness
end RicciFlower
