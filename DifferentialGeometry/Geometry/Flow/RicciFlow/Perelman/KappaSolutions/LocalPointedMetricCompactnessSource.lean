import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalMetricCompactnessSeedDecomposition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StaircaseCompactnessReduction

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

def LocalPointedMetricCompactnessSource
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Prop :=
  SeqMetricComplete (I := I) X ∧
    (∀ i : ℕ,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M) ∧
    Nonempty (BaseInjBound (I := I) X) ∧
    LocalCurvatureJetBound (I := I) X

def LocalPointedMetricCompactness
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Prop :=
  ∃ P : MetricCompactLimit (I := I) X,
    (∀ k : ℕ, P.convergence.metrics.domain k =
      CanonicalMetricCompactness.canonicalSourceData (I := I) P.maps k) ∧
    (∀ k : ℕ,
      let D := P.convergence.metrics.domain k
      let _ : TopologicalSpace (MetricSourceDomain (I := I) P.maps k) := D.topology
      let _ : ChartedSpace H (MetricSourceDomain (I := I) P.maps k) := D.charted
      let _ : IsManifold I ∞ (MetricSourceDomain (I := I) P.maps k) := D.smooth
      D.referenceMetric = D.limitMetric) ∧
    (let _ : TopologicalSpace P.limit.M := P.limit.topology
     ConnectedSpace P.limit.M)

def LocalPointedMetricCompactnessSourceCompactness
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Prop :=
  LocalPointedMetricCompactnessSource (I := I) X →
    LocalPointedMetricCompactness (I := I) X

omit [CompleteSpace E] in
theorem localPointedMetricCompactnessSource_iff
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) :
    LocalPointedMetricCompactnessSource (I := I) X ↔
      SeqMetricComplete (I := I) X ∧
        (∀ i : ℕ,
          let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
          ConnectedSpace (X.obj i).M) ∧
        Nonempty (BaseInjBound (I := I) X) ∧
        LocalCurvatureJetBound (I := I) X :=
  Iff.rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem localPointedMetricCompactness_iff_exists
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) :
    LocalPointedMetricCompactness (I := I) X ↔
      ∃ P : MetricCompactLimit (I := I) X,
        (∀ k : ℕ, P.convergence.metrics.domain k =
          CanonicalMetricCompactness.canonicalSourceData (I := I) P.maps k) ∧
        (∀ k : ℕ,
          let D := P.convergence.metrics.domain k
          let _ : TopologicalSpace (MetricSourceDomain (I := I) P.maps k) := D.topology
          let _ : ChartedSpace H (MetricSourceDomain (I := I) P.maps k) := D.charted
          let _ : IsManifold I ∞ (MetricSourceDomain (I := I) P.maps k) := D.smooth
          D.referenceMetric = D.limitMetric) ∧
        (let _ : TopologicalSpace P.limit.M := P.limit.topology
         ConnectedSpace P.limit.M) :=
  Iff.rfl

theorem localPointedMetricCompactness_of_source_and_seedFrontier
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hsource : LocalPointedMetricCompactnessSource (I := I) X)
    (hseed : LocalCurvatureJetSeedFrontier (I := I) X) :
    LocalPointedMetricCompactness (I := I) X := by
  obtain ⟨hcomplete, hconnected, hinj, hjets⟩ := hsource
  exact exists_local_pointed_metric_compactness_of_localCurvatureJetSeedFrontier
    (I := I) X hcomplete hconnected (Classical.choice hinj) hjets hseed

theorem localPointedMetricCompactnessSourceCompactness_of_seedFrontier
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hseed : LocalCurvatureJetSeedFrontier (I := I) X) :
    LocalPointedMetricCompactnessSourceCompactness (I := I) X :=
  fun hsource =>
    localPointedMetricCompactness_of_source_and_seedFrontier (I := I) X hsource hseed

theorem localPointedMetricCompactnessSourceCompactness_of_staircaseFrontier
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hfrontier : LocalStaircaseCompactnessFrontier (I := I) X) :
    LocalPointedMetricCompactnessSourceCompactness (I := I) X :=
  localPointedMetricCompactnessSourceCompactness_of_seedFrontier (I := I) X
    (localCurvatureJetSeedFrontier_of_localStaircaseCompactnessFrontier (I := I) X hfrontier)

theorem localPointedMetricCompactnessSourceCompactness_of_seedFrontiers
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hdecay : ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseSeedDecayFrontier (I := I) Y)
    (hpack : ∀ (Y : PointedRiemannianSeq.{u, uE, uH} (I := I))
      (hd : InjectivityRadiusDecay (I := I) Y),
      StaircaseSeedPackingFrontier (I := I) Y hd)
    (hchart : ∀ (Y : PointedRiemannianSeq.{u, uE, uH} (I := I))
      (hd : InjectivityRadiusDecay (I := I) Y),
      StaircaseSeedChartFrontier (I := I) Y hd) :
    LocalPointedMetricCompactnessSourceCompactness (I := I) X :=
  localPointedMetricCompactnessSourceCompactness_of_staircaseFrontier (I := I) X
    (localStaircaseCompactnessFrontier_of_uniform (I := I) X
      (staircaseMetricCompactSeedFrontier_of_seedFrontiers hdecay hpack hchart))

theorem localPointedMetricCompactnessSourceCompactness_of_boundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hgeom : SeqBoundedGeometry (I := I) X) :
    LocalPointedMetricCompactnessSourceCompactness (I := I) X :=
  localPointedMetricCompactnessSourceCompactness_of_seedFrontier (I := I) X
    (localCurvatureJetSeedFrontier_of_seqBoundedGeometry (I := I) X hgeom)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem metricComplete_limit_of_localPointedMetricCompactness
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (h : LocalPointedMetricCompactness (I := I) X) :
    ∃ P : MetricCompactLimit (I := I) X,
      MetricComplete (I := I) P.limit ∧
        (let _ : TopologicalSpace P.limit.M := P.limit.topology
         ConnectedSpace P.limit.M) := by
  obtain ⟨P, _hdom, _href, hconn⟩ := h
  exact ⟨P, P.limit_complete, hconn⟩

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood in
theorem exists_local_ancient_flow_compactness_of_ancientZeroBallJetBound_and_staircaseFrontier
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D = ancientTimeInterval)
    (hcomplete : FlowMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ,
      let _ : TopologicalSpace (X.term i).M := (X.term i).topology
      ConnectedSpace (X.term i).M)
    (hinj : FlowScaleInjectivityBound (I := I) X)
    (hzero : AncientZeroBallJetBound (I := I) X)
    (hseed : LocalStaircaseCompactnessFrontier (I := I) (X.atZero (I := I)))
    (hext : ∀ P : MetricCompactLimit.{u, uE, uH} (I := I) (X.atZero (I := I)),
      (∀ k : ℕ, P.convergence.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData (I := I) P.maps k) →
      (let _ : TopologicalSpace P.limit.M := P.limit.topology
       ConnectedSpace P.limit.M) →
      ∃ (phi : ℕ → ℕ) (_ : StrictMono phi)
        (L : PointedFlowData.{u, uE, uH} (I := I) X.D)
        (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi),
        AncientFlowLimitExtension (I := I) X P phi L Phi) :
    ∃ (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi,
        (let _ : TopologicalSpace L.M := L.topology
         ConnectedSpace L.M) ∧
        (∀ t ∈ X.D.carrier, MetricComplete (I := I) (L.atTime (I := I) t)) ∧
        ∀ t ∈ X.D.carrier,
          ∃ C : MetricConvergenceData (I := I) (Phi.atTime (L := L) t),
            (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
              (I := I) (Phi.atTime (L := L) t) k) ∧
            (∀ k,
              let D := C.domain k
              let _ : TopologicalSpace
                (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.topology
              let _ : ChartedSpace H
                (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.charted
              let _ : IsManifold I ∞
                (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.smooth
              D.referenceMetric = D.limitMetric) := by
  obtain ⟨P, hdom, _href, hconn⟩ :=
    exists_metricCompactLimit_atZero_of_localStaircaseFrontier (I := I) X hD hcomplete
      hconnected hinj hzero hseed
  obtain ⟨phi, hphi, L, Phi, he⟩ := hext P hdom hconn
  refine ⟨L, phi, hphi, Phi, ?_, he.slice_complete, fun t ht => ?_⟩
  · exact Eq.subst (motive := fun Q : PointedRiemannianManifold.{u, uE, uH} (I := I) =>
      let _ : TopologicalSpace Q.M := Q.topology
      ConnectedSpace Q.M) he.atTime_zero.symm hconn
  · exact exists_metricConvergenceData_canonicalSourceData (I := I)
      (Phi.atTime (L := L) t) (he.slice_convergence t ht)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
