import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StaircaseEngineAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalMetricCompactnessStaircase

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle Set Filter
open scoped Manifold ContDiff _root_.Topology

open DifferentialGeometry.Geometry.Riemannian

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]

theorem staircaseEngineFrontier_of_framedPairwiseApproximateIsometries
    (h : ∀ (Y : PointedRiemannianSeq.{u, uE, uH} (I := I))
      (hcomplete : SeqMetricComplete (I := I) Y)
      (hconnected : ∀ i : ℕ,
        let _ : TopologicalSpace (Y.obj i).M := (Y.obj i).topology
        ConnectedSpace (Y.obj i).M),
      BaseInjBound (I := I) Y →
      Nonempty (SeqBallFramedCoordMetricBounds (I := I) Y) →
      HasSubsequencePairwiseApproximateIsometries (I := I) Y
        (fun k => properMetricOn (I := I) (Y.obj k)
          (hcomplete.complete k) (hconnected k))) :
    ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseEngineFrontier (I := I) Y := by
  intro Y hcomplete hconnected hinj hbounds
  obtain ⟨C⟩ :=
    exists_connectedCanonicalMetricCompactness_of_hasSubsequencePairwiseApproximateIsometries
      (I := I) Y hcomplete hconnected (h Y hcomplete hconnected hinj hbounds)
  refine ⟨C.canonical, ?_⟩
  exact C.connected

open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions in
theorem framedPairwiseApproximateIsometries_of_seqBoundedGeometry
    (Y : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hgeom : SeqBoundedGeometry (I := I) Y) :
    ∀ (hcomplete : SeqMetricComplete (I := I) Y)
      (hconnected : ∀ i : ℕ,
        let _ : TopologicalSpace (Y.obj i).M := (Y.obj i).topology
        ConnectedSpace (Y.obj i).M),
      BaseInjBound (I := I) Y →
      Nonempty (SeqBallFramedCoordMetricBounds (I := I) Y) →
      HasSubsequencePairwiseApproximateIsometries (I := I) Y
        (fun k => properMetricOn (I := I) (Y.obj k)
          (hcomplete.complete k) (hconnected k)) := by
  intro hcomplete hconnected hinj _hbounds
  exact hasSubsequencePairwiseApproximateIsometries_of_seqBoundedGeometry (I := I) Y
    hcomplete hconnected hgeom hinj

open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions in
theorem staircaseEngineFrontier_of_seqBoundedGeometry
    (Y : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hgeom : SeqBoundedGeometry (I := I) Y) :
    StaircaseEngineFrontier (I := I) Y := by
  intro hcomplete hconnected hinj _hbounds
  obtain ⟨φ, hφ, b, hd⟩ :=
    exists_metricCompactSeed_of_seqBoundedGeometry (I := I) Y hcomplete hconnected hgeom hinj
  let C : CanonicalMetricCompactness (I := I) (Y.subseq φ) :=
    b.higherRegularityCanonicalMetricCompactness (Classical.choice hd)
      (hcomplete.subseq φ) (PointedRiemannianSeq.connected_subseq hconnected φ)
  have hCconn : @ConnectedSpace C.compactness.limit.M C.compactness.limit.topology :=
    b.higher_regularity_canonical_metric_compactness_connected (Classical.choice hd)
      (hcomplete.subseq φ) (PointedRiemannianSeq.connected_subseq hconnected φ)
  exact ⟨C.ofSubsequence φ hφ, by
    change @ConnectedSpace C.compactness.limit.M C.compactness.limit.topology
    exact hCconn⟩

def StaircaseEngineSubsequenceFrontier
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ →
    Nonempty (SeqBallFramedCoordMetricBounds (I := I) (X.subseq φ)) →
    StaircaseEngineFrontier (I := I) (X.subseq φ)

theorem staircaseEngineSubsequenceFrontier_of_staircaseEngineFrontier
    (hfrontier : ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseEngineFrontier (I := I) Y)
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) :
    StaircaseEngineSubsequenceFrontier (I := I) X :=
  fun _φ _hφ _hbounds => hfrontier (X.subseq _φ)

theorem staircaseEngineSubsequenceFrontier_of_seqBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hgeom : SeqBoundedGeometry (I := I) X) :
    StaircaseEngineSubsequenceFrontier (I := I) X :=
  fun φ _hφ _hbounds =>
    staircaseEngineFrontier_of_seqBoundedGeometry (I := I) (X.subseq φ) (hgeom.subseq φ)

theorem exists_local_pointed_metric_compactness_of_staircaseEngineSubsequenceFrontier
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (hinj : BaseInjBound (I := I) X)
    (hjets : ∀ A : ℝ, 0 < A → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
        let _ : ChartedSpace H (X.obj i).M := (X.obj i).charted
        let _ : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
        let _ : T2Space (X.obj i).M := (X.obj i).t2
        let _ : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
        ∀ x : (X.obj i).M,
          riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint x ≤
            ENNReal.ofReal A → curvDerivNorm (I := I) p (X.obj i).metric x ≤ C)
    (hfrontier : StaircaseEngineSubsequenceFrontier (I := I) X) :
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
       ConnectedSpace P.limit.M) := by
  obtain ⟨φ, hφ, hb⟩ :=
    exists_subseq_seqBallFramedCoordMetricBounds_of_local_jets (I := I) X
      hcomplete hconnected hinj hjets (A := 1) one_pos
  obtain ⟨C, hCconn⟩ := hfrontier φ hφ hb (hcomplete.subseq φ)
    (PointedRiemannianSeq.connected_subseq hconnected φ) (hinj.subseq φ) hb
  let C₀ : CanonicalMetricCompactness (I := I) X := C.ofSubsequence φ hφ
  refine ⟨C₀.compactness, C₀.domain_eq_canonical, C₀.reference_eq_limit, ?_⟩
  change @ConnectedSpace C.compactness.limit.M C.compactness.limit.topology
  exact hCconn

theorem exists_local_pointed_metric_compactness_of_framedApproximateIsometries
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (hinj : BaseInjBound (I := I) X)
    (hjets : ∀ A : ℝ, 0 < A → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
        let _ : ChartedSpace H (X.obj i).M := (X.obj i).charted
        let _ : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
        let _ : T2Space (X.obj i).M := (X.obj i).t2
        let _ : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
        ∀ x : (X.obj i).M,
          riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint x ≤
            ENNReal.ofReal A → curvDerivNorm (I := I) p (X.obj i).metric x ≤ C)
    (hpair : ∀ (φ : ℕ → ℕ) (_hφ : StrictMono φ)
      (hcompleteφ : SeqMetricComplete (I := I) (X.subseq φ))
      (hconnectedφ : ∀ i : ℕ,
        let _ : TopologicalSpace ((X.subseq φ).obj i).M :=
          ((X.subseq φ).obj i).topology
        ConnectedSpace ((X.subseq φ).obj i).M),
      BaseInjBound (I := I) (X.subseq φ) →
      Nonempty (SeqBallFramedCoordMetricBounds (I := I) (X.subseq φ)) →
      HasSubsequencePairwiseApproximateIsometries (I := I) (X.subseq φ)
        (fun k => properMetricOn (I := I) ((X.subseq φ).obj k)
          (hcompleteφ.complete k) (hconnectedφ k))) :
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
       ConnectedSpace P.limit.M) := by
  refine exists_local_pointed_metric_compactness_of_staircaseEngineSubsequenceFrontier
    (I := I) X hcomplete hconnected hinj hjets ?_
  intro φ _hφ _hb hcompleteφ hconnectedφ hinjφ hb
  obtain ⟨C⟩ :=
    exists_connectedCanonicalMetricCompactness_of_hasSubsequencePairwiseApproximateIsometries
      (I := I) (X.subseq φ) hcompleteφ hconnectedφ
      (hpair φ _hφ hcompleteφ hconnectedφ hinjφ hb)
  exact ⟨C.canonical, C.connected⟩

end CheegerGromovCompactness
end DifferentialGeometry
