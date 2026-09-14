import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedFlowSlices
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalMetricCompactnessSeed
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalMetricCompactnessStaircase
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalCurvatureJetBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Canonical.ReferenceChange

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

structure AncientZeroBallJetBound (X : PointedFlowSeq.{u, uE, uH} (I := I)) : Prop where
  bound : ∀ A : ℝ, 0 < A → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ i in atTop,
      let _ : TopologicalSpace (X.term i).M := (X.term i).topology
      let _ : ChartedSpace H (X.term i).M := (X.term i).charted
      let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
      let _ : T2Space (X.term i).M := (X.term i).t2
      let _ : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
      ∀ x : (X.term i).M,
        riemannianEDistOf (I := I) ((X.term i).S.base.metric 0) (X.term i).basepoint x ≤
          ENNReal.ofReal A →
        curvDerivNorm (I := I) p ((X.term i).S.base.metric 0) x ≤ C

omit [NeZero (Module.finrank ℝ E)] in
theorem ancientZeroBallJetBound_of_local_curvature_bound
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D = ancientTimeInterval)
    (hcomplete : FlowMetricComplete (I := I) X)
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
            ((X.term i).S.base.metric t).inner x v v) :
    AncientZeroBallJetBound (I := I) X :=
  ⟨exists_eventually_curvDerivNorm_le_of_local_curvature_bound_atZero (I := I) X hD
    hcomplete hdim hlocal hlower⟩

theorem staircaseMetricCompactSeedFrontier_of_seqBoundedGeometry
    (Y : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hgeom : SeqBoundedGeometry (I := I) Y) :
    StaircaseMetricCompactSeedFrontier (I := I) Y := by
  intro hcomplete hconnected hinj _hball
  exact exists_metricCompactSeed_of_seqBoundedGeometry (I := I) Y hcomplete hconnected
    hgeom hinj

theorem exists_metricCompactLimit_atZero_of_staircaseMetricCompactSeedFrontier
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D = ancientTimeInterval)
    (hcomplete : FlowMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ,
      let _ : TopologicalSpace (X.term i).M := (X.term i).topology
      ConnectedSpace (X.term i).M)
    (hinj : FlowScaleInjectivityBound (I := I) X)
    (hzero : AncientZeroBallJetBound (I := I) X)
    (hseed : ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseMetricCompactSeedFrontier (I := I) Y) :
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
  exact exists_local_pointed_metric_compactness_of_staircaseApproximateIsometryFrontier (I := I)
    (X.atZero (I := I)) (hcomplete.at_time h0) (fun i => hconnected i) hinj hzero.bound
    (staircaseApproximateIsometryFrontier_of_metricCompactSeedFrontier hseed)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem eventually_le_edistOf_atZero_of_lower_bound
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hlower : ∀ T : ℝ, 0 < T → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.term i).M := (X.term i).topology
        let _ : ChartedSpace H (X.term i).M := (X.term i).charted
        let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
        ∀ t ∈ Set.Icc (-T) 0, ∀ x : (X.term i).M, ∀ v : TangentSpace I x,
          c * ((X.term i).S.base.metric 0).inner x v v ≤
            ((X.term i).S.base.metric t).inner x v v) :
    ∀ T : ℝ, 0 < T → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.term i).M := (X.term i).topology
        let _ : ChartedSpace H (X.term i).M := (X.term i).charted
        let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
        ∀ t ∈ Set.Icc (-T) 0, ∀ x y : (X.term i).M,
          ENNReal.ofReal (Real.sqrt c) *
              riemannianEDistOf (I := I) ((X.term i).S.base.metric 0) x y ≤
            riemannianEDistOf (I := I) ((X.term i).S.base.metric t) x y := by
  intro T hT
  obtain ⟨c, hc, hev⟩ := hlower T hT
  refine ⟨c, hc, hev.mono ?_⟩
  intro i hi _ _ _ t ht x y
  exact le_edistOf_of_quad (I := I) ((X.term i).S.base.metric 0)
    ((X.term i).S.base.metric t) hc (hi t ht) x y

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem eventually_riemannianClosedBall_atTime_subset_atZero
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hlower : ∀ T : ℝ, 0 < T → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.term i).M := (X.term i).topology
        let _ : ChartedSpace H (X.term i).M := (X.term i).charted
        let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
        ∀ t ∈ Set.Icc (-T) 0, ∀ x : (X.term i).M, ∀ v : TangentSpace I x,
          c * ((X.term i).S.base.metric 0).inner x v v ≤
            ((X.term i).S.base.metric t).inner x v v) :
    ∀ T : ℝ, 0 < T → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.term i).M := (X.term i).topology
        let _ : ChartedSpace H (X.term i).M := (X.term i).charted
        let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
        ∀ t ∈ Set.Icc (-T) 0, ∀ A : ℝ, 0 < A →
          {y : (X.term i).M |
              riemannianEDistOf (I := I) ((X.term i).S.base.metric t)
                (X.term i).basepoint y ≤ ENNReal.ofReal (Real.sqrt c * A)} ⊆
            {y : (X.term i).M |
              riemannianEDistOf (I := I) ((X.term i).S.base.metric 0)
                (X.term i).basepoint y ≤ ENNReal.ofReal A} := by
  intro T hT
  obtain ⟨c, hc, hev⟩ := eventually_le_edistOf_atZero_of_lower_bound (I := I) X hlower T hT
  refine ⟨c, hc, hev.mono ?_⟩
  intro i hi _ _ _ t ht A hA y hy
  have hstep := hi t ht (X.term i).basepoint y
  have hsplit : ENNReal.ofReal (Real.sqrt c * A) =
      ENNReal.ofReal (Real.sqrt c) * ENNReal.ofReal A :=
    ENNReal.ofReal_mul (Real.sqrt_nonneg c)
  rw [hsplit] at hy
  have h0 : ENNReal.ofReal (Real.sqrt c) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hc))
  have htop : ENNReal.ofReal (Real.sqrt c) ≠ ⊤ := ENNReal.ofReal_ne_top
  exact (ENNReal.mul_le_mul_iff_right h0 htop).mp (hstep.trans hy)

structure AncientFlowLimitExtension
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (P : MetricCompactLimit.{u, uE, uH} (I := I) (X.atZero (I := I)))
    (phi : ℕ → ℕ) (L : PointedFlowData.{u, uE, uH} (I := I) X.D)
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi) : Prop where
  atTime_zero : L.atTime (I := I) 0 = P.limit
  slice_complete : ∀ t ∈ X.D.carrier, MetricComplete (I := I) (L.atTime (I := I) t)
  slice_convergence : ∀ t ∈ X.D.carrier, ∀ K : Set L.M,
    (let _ : TopologicalSpace L.M := L.topology
     IsCompact K) →
    ∀ p : ℕ, ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      (CanonicalMetricCompactness.canonicalSourceData (I := I)
        (Phi.atTime (L := L) t) k).derivNormSupOn (I := I) K p < ε

theorem exists_local_ancient_flow_compactness_of_frontier
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D = ancientTimeInterval)
    (hcomplete : FlowMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ,
      let _ : TopologicalSpace (X.term i).M := (X.term i).topology
      ConnectedSpace (X.term i).M)
    (hinj : FlowScaleInjectivityBound (I := I) X)
    (hzero : AncientZeroBallJetBound (I := I) X)
    (hseed : ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseMetricCompactSeedFrontier (I := I) Y)
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
    exists_metricCompactLimit_atZero_of_staircaseMetricCompactSeedFrontier (I := I) X hD hcomplete
      hconnected hinj hzero hseed
  obtain ⟨phi, hphi, L, Phi, he⟩ := hext P hdom hconn
  refine ⟨L, phi, hphi, Phi, ?_, he.slice_complete, fun t ht => ?_⟩
  · exact Eq.subst (motive := fun Q : PointedRiemannianManifold.{u, uE, uH} (I := I) =>
      let _ : TopologicalSpace Q.M := Q.topology
      ConnectedSpace Q.M) he.atTime_zero.symm hconn
  · exact exists_metricConvergenceData_canonicalSourceData (I := I)
      (Phi.atTime (L := L) t) (he.slice_convergence t ht)


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem ancientFlowLimitExtension_slice_convergence_iff
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) (phi : ℕ → ℕ)
    (L : PointedFlowData.{u, uE, uH} (I := I) X.D)
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi) :
    (∀ t ∈ X.D.carrier, ∀ K : Set L.M,
      (let _ : TopologicalSpace L.M := L.topology
       IsCompact K) →
      ∀ p : ℕ, ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
        (CanonicalMetricCompactness.canonicalSourceData (I := I)
          (Phi.atTime (L := L) t) k).derivNormSupOn (I := I) K p < ε) ↔
    (∀ t ∈ X.D.carrier,
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
          D.referenceMetric = D.limitMetric)) := by
  constructor
  · intro h t ht
    exact (exists_metricConvergenceData_canonicalSourceData_iff (I := I)
      (Phi.atTime (L := L) t)).mpr (h t ht)
  · intro h t ht K hK p ε hε
    exact (exists_metricConvergenceData_canonicalSourceData_iff (I := I)
      (Phi.atTime (L := L) t)).mp (h t ht) K hK p ε hε

theorem exists_local_ancient_flow_compactness_of_local_curvature_bound_and_frontier
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
    (hseed : ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseMetricCompactSeedFrontier (I := I) Y)
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
              D.referenceMetric = D.limitMetric) :=
  exists_local_ancient_flow_compactness_of_frontier (I := I) X hD hcomplete hconnected hinj
    (ancientZeroBallJetBound_of_local_curvature_bound (I := I) X hD hcomplete hdim hlocal hlower)
    hseed hext

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
