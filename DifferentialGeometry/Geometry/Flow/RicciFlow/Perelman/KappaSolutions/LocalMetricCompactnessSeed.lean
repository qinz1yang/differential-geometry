import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.NormalCharts
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.BoundedGeometry
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalChart.Existence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.BallGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalInjectivityRadiusDecaySeqBall

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

theorem exists_local_pointed_metric_compactness_of_metricCompactSeed
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (hseed : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ b : MetricCompactSeed (I := I) (X.subseq φ),
        Nonempty (BoundedGeometryNormalChartData (I := I) (X.subseq φ) b.decay)) :
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
  classical
  obtain ⟨φ, hφ, b, hd⟩ := hseed
  have hcomplete' : SeqMetricComplete (I := I) (X.subseq φ) := hcomplete.subseq φ
  have hconnected' : ∀ i : ℕ,
      let _ : TopologicalSpace ((X.subseq φ).obj i).M := ((X.subseq φ).obj i).topology
      ConnectedSpace ((X.subseq φ).obj i).M :=
    PointedRiemannianSeq.connected_subseq hconnected φ
  let C : CanonicalMetricCompactness (I := I) (X.subseq φ) :=
    b.higherRegularityCanonicalMetricCompactness (Classical.choice hd) hcomplete' hconnected'
  have hCconnected : let _ : TopologicalSpace C.compactness.limit.M :=
      C.compactness.limit.topology
      ConnectedSpace C.compactness.limit.M :=
    b.higher_regularity_canonical_metric_compactness_connected (Classical.choice hd)
      hcomplete' hconnected'
  let C₀ : CanonicalMetricCompactness (I := I) X := C.ofSubsequence φ hφ
  refine ⟨C₀.compactness, C₀.domain_eq_canonical, C₀.reference_eq_limit, ?_⟩
  change @ConnectedSpace C.compactness.limit.M C.compactness.limit.topology
  exact hCconnected

theorem exists_metricCompactSeed_of_seqBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (hgeom : SeqBoundedGeometry (I := I) X)
    (hinj : BaseInjBound (I := I) X) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ b : MetricCompactSeed (I := I) (X.subseq φ),
        Nonempty (BoundedGeometryNormalChartData (I := I) (X.subseq φ) b.decay) := by
  classical
  let b : MetricCompactSeed (I := I) X :=
    metricCompactSeedOfBoundedGeometry (I := I) X hcomplete hgeom hinj hconnected
  have hd : Nonempty (BoundedGeometryNormalChartData (I := I) X b.decay) :=
    nonempty_bounded_geometry_normal_chart_data (I := I) X hcomplete hconnected hgeom
      b.decay b.realizes
  exact ⟨id, strictMono_id, b, hd⟩

theorem exists_local_pointed_metric_compactness_of_local_boundedGeometry_frontier
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
    (hfrontier : ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      SeqMetricComplete (I := I) Y →
      (∀ i : ℕ,
        let _ : TopologicalSpace (Y.obj i).M := (Y.obj i).topology
        ConnectedSpace (Y.obj i).M) →
      BaseInjBound (I := I) Y →
      Nonempty (SeqBallGeometry (I := I) Y) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∃ b : MetricCompactSeed (I := I) (Y.subseq ψ),
          Nonempty (BoundedGeometryNormalChartData (I := I) (Y.subseq ψ) b.decay)) :
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
  obtain ⟨φ, hφ, hball⟩ := exists_subseq_seqBallGeometry_of_local_jets (I := I) X hjets
  have hcomplete' : SeqMetricComplete (I := I) (X.subseq φ) := hcomplete.subseq φ
  have hconnected' : ∀ i : ℕ,
      let _ : TopologicalSpace ((X.subseq φ).obj i).M := ((X.subseq φ).obj i).topology
      ConnectedSpace ((X.subseq φ).obj i).M :=
    PointedRiemannianSeq.connected_subseq hconnected φ
  have hinj' : BaseInjBound (I := I) (X.subseq φ) := hinj.subseq φ
  obtain ⟨ψ, hψ, b, hd⟩ := hfrontier (X.subseq φ) hcomplete' hconnected' hinj' hball
  refine exists_local_pointed_metric_compactness_of_metricCompactSeed X hcomplete hconnected
    ⟨fun i => φ (ψ i), hφ.comp hψ, b, hd⟩

theorem exists_subseq_seqBallGeometry_and_uniform_injectivityRadius_of_local_jets
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
    (A : ℝ) (hA : 0 < A) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Nonempty (SeqBallGeometry (I := I) (X.subseq φ)) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ j in atTop,
        let _ : TopologicalSpace ((X.subseq φ).obj j).M := ((X.subseq φ).obj j).topology
        let _ : EMetricSpace ((X.subseq φ).obj j).M :=
          ((X.subseq φ).obj j).emetricSpace (I := I)
        ∀ x : ((X.subseq φ).obj j).M,
          edist ((X.subseq φ).obj j).basepoint x ≤ ENNReal.ofReal A →
            HasInjRadiusAt (I := I) ((X.subseq φ).obj j) x ρ := by
  obtain ⟨φ, hφ, hball⟩ := exists_subseq_seqBallGeometry_of_local_jets (I := I) X hjets
  have hcomplete' : SeqMetricComplete (I := I) (X.subseq φ) := hcomplete.subseq φ
  have hconnected' : ∀ i : ℕ,
      let _ : TopologicalSpace ((X.subseq φ).obj i).M := ((X.subseq φ).obj i).topology
      ConnectedSpace ((X.subseq φ).obj i).M :=
    PointedRiemannianSeq.connected_subseq hconnected φ
  have hinj' : BaseInjBound (I := I) (X.subseq φ) := hinj.subseq φ
  obtain ⟨ρ, hρ, hρev⟩ :=
    exists_uniform_injectivity_radius_on_ball_of_seqBallGeometry (I := I) (X.subseq φ)
      hcomplete' hconnected' hinj' (Classical.choice hball) A hA
  exact ⟨φ, hφ, hball, ρ, hρ, hρev⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
