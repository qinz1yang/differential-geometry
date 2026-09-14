import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalMetricCompactnessStaircase
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompactnessFrontierReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalAncientFlowCompactnessReduction
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.CenteredJetBounds

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff ENNReal _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

def SeqGlobalCurvatureBound
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Prop :=
  ∃ C : ℕ → ℝ, (∀ k : ℕ, 0 ≤ C k) ∧
    ∀ (i k : ℕ), HasCurvDerivBound (I := I) (X.obj i) k (C k)

def SeqUniformLocalCurvatureBound
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ C : ℕ → ℝ, (∀ k : ℕ, 0 ≤ C k) ∧
    ∀ (i k : ℕ) (x : (X.obj i).M),
      HasLocalCurvDerivBound (I := I) (X.obj i) x A k (C k)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem seqUniformLocalCurvatureBound_of_seqGlobalCurvatureBound
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (h : SeqGlobalCurvatureBound (I := I) X) :
    SeqUniformLocalCurvatureBound (I := I) X := by
  obtain ⟨C, hC, hglob⟩ := h
  refine ⟨1, one_pos, C, hC, ?_⟩
  intro i k x
  with_unfolding_all
    intro y _
    exact hglob i k y

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem seqGlobalCurvatureBound_of_seqUniformLocalCurvatureBound
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (h : SeqUniformLocalCurvatureBound (I := I) X) :
    SeqGlobalCurvatureBound (I := I) X := by
  obtain ⟨_A, _hA, C, hC, hloc⟩ := h
  refine ⟨C, hC, fun i k => ?_⟩
  let : TopologicalSpace (X.obj i).M := (X.obj i).topology
  let : ChartedSpace H (X.obj i).M := (X.obj i).charted
  let : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
  let : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
  let : T2Space (X.obj i).M := (X.obj i).t2
  intro x
  exact hloc i k x x (by rw [riemannianEDistOf_self]; exact bot_le)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem seqGlobalCurvatureBound_iff_seqUniformLocalCurvatureBound
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) :
    SeqGlobalCurvatureBound (I := I) X ↔ SeqUniformLocalCurvatureBound (I := I) X :=
  ⟨seqUniformLocalCurvatureBound_of_seqGlobalCurvatureBound (I := I) X,
    seqGlobalCurvatureBound_of_seqUniformLocalCurvatureBound (I := I) X⟩

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem seqGlobalCurvatureBound_of_seqBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hgeom : SeqBoundedGeometry (I := I) X) :
    SeqGlobalCurvatureBound (I := I) X :=
  ⟨hgeom.C, hgeom.nonneg, fun i k => hgeom.bound i k⟩

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
def seqBoundedGeometry_of_seqGlobalCurvatureBound
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (h : SeqGlobalCurvatureBound (I := I) X) :
    SeqBoundedGeometry (I := I) X := by
  exact ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2⟩

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
def seqBoundedGeometry_of_seqUniformLocalCurvatureBound
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (h : SeqUniformLocalCurvatureBound (I := I) X) :
    SeqBoundedGeometry (I := I) X :=
  seqBoundedGeometry_of_seqGlobalCurvatureBound (I := I) X
    (seqGlobalCurvatureBound_of_seqUniformLocalCurvatureBound (I := I) X h)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem seqUniformLocalCurvatureBound_of_seqBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hgeom : SeqBoundedGeometry (I := I) X) :
    SeqUniformLocalCurvatureBound (I := I) X :=
  seqUniformLocalCurvatureBound_of_seqGlobalCurvatureBound (I := I) X
    (seqGlobalCurvatureBound_of_seqBoundedGeometry (I := I) X hgeom)

def LocalCurvatureJetBound
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Prop :=
  ∀ A : ℝ, 0 < A → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ i in atTop,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      let _ : ChartedSpace H (X.obj i).M := (X.obj i).charted
      let _ : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
      let _ : T2Space (X.obj i).M := (X.obj i).t2
      let _ : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
      ∀ x : (X.obj i).M,
        riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint x ≤
          ENNReal.ofReal A → curvDerivNorm (I := I) p (X.obj i).metric x ≤ C

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem localCurvatureJetBound_of_seqBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hgeom : SeqBoundedGeometry (I := I) X) :
    LocalCurvatureJetBound (I := I) X := by
  intro A _hA p
  refine ⟨hgeom.C p, hgeom.nonneg p, ?_⟩
  filter_upwards with i
  exact fun x _hx => hgeom.bound i p x

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem localCurvatureJetBound_of_seqBallGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hball : SeqBallGeometry (I := I) X) :
    LocalCurvatureJetBound (I := I) X := by
  intro A hA p
  obtain ⟨n, hn⟩ := exists_nat_ge A
  refine ⟨hball.C n p, hball.nonneg n p, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (n + p)] with i hi
  exact fun x hx =>
    hball.bound n p i hi x (hx.trans (ENNReal.ofReal_le_ofReal hn))

def LocalCurvatureJetSeedFrontier
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Prop :=
  SeqMetricComplete (I := I) X →
  (∀ i : ℕ,
    let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
    ConnectedSpace (X.obj i).M) →
  BaseInjBound (I := I) X →
  LocalCurvatureJetBound (I := I) X →
  ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
    ∃ b : MetricCompactSeed (I := I) (X.subseq ψ),
      Nonempty (BoundedGeometryNormalChartData (I := I) (X.subseq ψ) b.decay)

omit [CompleteSpace E] in
theorem localCurvatureJetSeedFrontier_of_localStaircaseCompactnessFrontier
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (h : LocalStaircaseCompactnessFrontier (I := I) X) :
    LocalCurvatureJetSeedFrontier (I := I) X := by
  intro hcomplete hconn hinj hjets
  obtain ⟨φ, hφ, hball⟩ := exists_subseq_seqBallGeometry_of_local_jets (I := I) X hjets
  obtain ⟨ψ, hψ, b, hd⟩ :=
    h φ hφ (hcomplete.subseq φ)
      (PointedRiemannianSeq.connected_subseq hconn φ) (hinj.subseq φ) hball
  exact ⟨fun i => φ (ψ i), hφ.comp hψ, b, hd⟩

omit [CompleteSpace E] in
theorem localCurvatureJetSeedFrontier_of_staircaseMetricCompactSeedFrontier
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (h : ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseMetricCompactSeedFrontier (I := I) Y) :
    LocalCurvatureJetSeedFrontier (I := I) X :=
  localCurvatureJetSeedFrontier_of_localStaircaseCompactnessFrontier (I := I) X
    (localStaircaseCompactnessFrontier_of_uniform (I := I) X h)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_subseq_seqBallGeometry_of_localCurvatureJetBound
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hjets : LocalCurvatureJetBound (I := I) X) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Nonempty (SeqBallGeometry (I := I) (X.subseq φ)) :=
  exists_subseq_seqBallGeometry_of_local_jets (I := I) X hjets

def LocalCurvatureJetSeedFrontierUniform
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ → LocalCurvatureJetSeedFrontier (I := I) (X.subseq φ)

omit [CompleteSpace E] in
theorem localCurvatureJetSeedFrontierUniform_of_localStaircaseCompactnessFrontier
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (h : LocalStaircaseCompactnessFrontier (I := I) X) :
    LocalCurvatureJetSeedFrontierUniform (I := I) X := by
  intro φ hφ hcomplete hconn hinj hjets
  obtain ⟨σ, hσ, hball⟩ :=
    exists_subseq_seqBallGeometry_of_local_jets (I := I) (X.subseq φ) hjets
  obtain ⟨ψ, hψ, b, hd⟩ :=
    h (fun i => φ (σ i)) (hφ.comp hσ) (hcomplete.subseq σ)
      (PointedRiemannianSeq.connected_subseq hconn σ) (hinj.subseq σ) hball
  exact ⟨fun i => σ (ψ i), hσ.comp hψ, b, hd⟩

omit [CompleteSpace E] in
theorem localStaircaseCompactnessFrontier_of_localCurvatureJetSeedFrontierUniform
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (h : LocalCurvatureJetSeedFrontierUniform (I := I) X) :
    LocalStaircaseCompactnessFrontier (I := I) X := by
  intro φ hφ hcomplete hconn hinj hball
  exact h φ hφ hcomplete hconn hinj
    (localCurvatureJetBound_of_seqBallGeometry (I := I) (X.subseq φ)
      (Classical.choice hball))

omit [CompleteSpace E] in
theorem localStaircaseCompactnessFrontier_iff_localCurvatureJetSeedFrontierUniform
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) :
    LocalStaircaseCompactnessFrontier (I := I) X ↔
      LocalCurvatureJetSeedFrontierUniform (I := I) X :=
  ⟨localCurvatureJetSeedFrontierUniform_of_localStaircaseCompactnessFrontier (I := I) X,
    localStaircaseCompactnessFrontier_of_localCurvatureJetSeedFrontierUniform (I := I) X⟩

theorem localCurvatureJetSeedFrontier_of_seqBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hgeom : SeqBoundedGeometry (I := I) X) :
    LocalCurvatureJetSeedFrontier (I := I) X := by
  intro hcomplete hconnected hinj _hjets
  exact exists_metricCompactSeed_of_seqBoundedGeometry (I := I) X hcomplete hconnected
    hgeom hinj

theorem exists_local_pointed_metric_compactness_of_localCurvatureJetSeedFrontier
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (hinj : BaseInjBound (I := I) X)
    (hjets : LocalCurvatureJetBound (I := I) X)
    (hseed : LocalCurvatureJetSeedFrontier (I := I) X) :
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
  obtain ⟨ψ, hψ, b, hd⟩ := hseed hcomplete hconnected hinj hjets
  exact exists_local_pointed_metric_compactness_of_metricCompactSeed (I := I) X hcomplete
    hconnected ⟨ψ, hψ, b, hd⟩

theorem exists_local_pointed_metric_compactness_of_seqBoundedGeometry_and_localCurvatureJetBound
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (hinj : BaseInjBound (I := I) X)
    (hjets : LocalCurvatureJetBound (I := I) X)
    (hgeom : SeqBoundedGeometry (I := I) X) :
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
  exists_local_pointed_metric_compactness_of_localCurvatureJetSeedFrontier (I := I) X
    hcomplete hconnected hinj hjets
    (localCurvatureJetSeedFrontier_of_seqBoundedGeometry (I := I) X hgeom)

theorem exists_metricCompactLimit_atZero_of_localCurvatureJetSeedFrontier
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D = ancientTimeInterval)
    (hcomplete : FlowMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ,
      let _ : TopologicalSpace (X.term i).M := (X.term i).topology
      ConnectedSpace (X.term i).M)
    (hinj : FlowScaleInjectivityBound (I := I) X)
    (hzero : AncientZeroBallJetBound (I := I) X)
    (hseed : LocalCurvatureJetSeedFrontier (I := I) (X.atZero (I := I))) :
    ∃ P : MetricCompactLimit.{u, uE, uH} (I := I) (X.atZero (I := I)),
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
  have h0 : (0 : ℝ) ∈ X.D.carrier := by
    simp only [hD, ancientTimeInterval_carrier, Set.mem_Iic, le_refl]
  exact exists_local_pointed_metric_compactness_of_localCurvatureJetSeedFrontier (I := I)
    (X.atZero (I := I)) (hcomplete.at_time h0) (fun i => hconnected i) hinj hzero.bound
    hseed

theorem exists_local_ancient_flow_compactness_of_localCurvatureJetSeedFrontier_and_extension
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D = ancientTimeInterval)
    (hcomplete : FlowMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ,
      let _ : TopologicalSpace (X.term i).M := (X.term i).topology
      ConnectedSpace (X.term i).M)
    (hinj : FlowScaleInjectivityBound (I := I) X)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hlocal : ∀ A : ℝ, 0 < A → ∀ T : ℝ, 0 < T → ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.term i).M := (X.term i).topology
        let _ : ChartedSpace H (X.term i).M := (X.term i).charted
        let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
        ∀ t ∈ Set.Icc (-T) 0, ∀ x : (X.term i).M,
          riemannianEDistOf (I := I) ((X.term i).S.base.metric 0)
              (X.term i).basepoint x ≤ ENNReal.ofReal A →
            (X.term i).rmNormSq (I := I) t x ≤ K)
    (hlower : ∀ T : ℝ, 0 < T → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.term i).M := (X.term i).topology
        let _ : ChartedSpace H (X.term i).M := (X.term i).charted
        let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
        ∀ t ∈ Set.Icc (-T) 0, ∀ x : (X.term i).M, ∀ v : TangentSpace I x,
          c * ((X.term i).S.base.metric 0).inner x v v ≤
            ((X.term i).S.base.metric t).inner x v v)
    (hseed : LocalCurvatureJetSeedFrontier (I := I) (X.atZero (I := I)))
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
    exists_metricCompactLimit_atZero_of_localCurvatureJetSeedFrontier (I := I) X hD hcomplete
      hconnected hinj
      (ancientZeroBallJetBound_of_local_curvature_bound (I := I) X hD hcomplete hdim
        hlocal hlower)
      hseed
  obtain ⟨phi, hphi, L, Phi, he⟩ := hext P hdom hconn
  refine ⟨L, phi, hphi, Phi, ?_, he.slice_complete, fun t ht => ?_⟩
  · exact Eq.subst (motive := fun Q : PointedRiemannianManifold.{u, uE, uH} (I := I) =>
      let _ : TopologicalSpace Q.M := Q.topology
      ConnectedSpace Q.M) he.atTime_zero.symm hconn
  · exact exists_metricConvergenceData_canonicalSourceData (I := I)
      (Phi.atTime (L := L) t) (he.slice_convergence t ht)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
