import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalMetricCompactnessStaircase
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalAncientFlowCompactnessReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSplittingNegativeTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSplittingNullPlane
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSplittingFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NoncompactShrinkerMassClassification

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold ContDiff ENNReal _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

def LocalStaircaseCompactnessFrontier
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ → StaircaseMetricCompactSeedFrontier (I := I) (X.subseq φ)

omit [CompleteSpace E] in
theorem localStaircaseCompactnessFrontier_of_uniform
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (h : ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseMetricCompactSeedFrontier (I := I) Y) :
    LocalStaircaseCompactnessFrontier (I := I) X :=
  fun _ _ => h _

theorem staircaseApproximateIsometryFrontier_of_seqBoundedGeometry
    (Y : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hgeom : SeqBoundedGeometry (I := I) Y) :
    StaircaseApproximateIsometryFrontier (I := I) Y :=
  fun hcomplete hconnected hinj _hball =>
    hasSubsequencePairwiseApproximateIsometries_of_seqBoundedGeometry (I := I) Y
      hcomplete hconnected hgeom hinj

omit [CompleteSpace E] in
theorem localStaircaseCompactnessFrontier_of_seqBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hgeom : SeqBoundedGeometry (I := I) X) :
    LocalStaircaseCompactnessFrontier (I := I) X :=
  fun φ _ => staircaseMetricCompactSeedFrontier_of_seqBoundedGeometry (I := I) (X.subseq φ)
    (hgeom.subseq φ)

theorem exists_local_pointed_metric_compactness_of_localStaircaseCompactnessFrontier
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
    (hfrontier : LocalStaircaseCompactnessFrontier (I := I) X) :
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
  obtain ⟨ψ, hψ, b, hd⟩ :=
    hfrontier φ hφ (hcomplete.subseq φ)
      (PointedRiemannianSeq.connected_subseq hconnected φ) (hinj.subseq φ) hball
  exact exists_local_pointed_metric_compactness_of_metricCompactSeed X hcomplete hconnected
    ⟨fun i => φ (ψ i), hφ.comp hψ, b, hd⟩

theorem exists_metricCompactLimit_atZero_of_localStaircaseFrontier
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D = ancientTimeInterval)
    (hcomplete : FlowMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ,
      let _ : TopologicalSpace (X.term i).M := (X.term i).topology
      ConnectedSpace (X.term i).M)
    (hinj : FlowScaleInjectivityBound (I := I) X)
    (hzero : AncientZeroBallJetBound (I := I) X)
    (hseed : LocalStaircaseCompactnessFrontier (I := I) (X.atZero (I := I))) :
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
  exact exists_local_pointed_metric_compactness_of_localStaircaseCompactnessFrontier
    (X.atZero (I := I)) (hcomplete.at_time h0) (fun i => hconnected i) hinj hzero.bound hseed

theorem exists_local_ancient_flow_compactness_of_localStaircaseFrontier_and_extension
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

section AncientSplittingFrontierAt

variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance compactnessFrontierReductionTopology : TopologicalSpace F.M := F.topology
local instance compactnessFrontierReductionCharted : ChartedSpace H F.M := F.charted
local instance compactnessFrontierReductionSmooth : IsManifold I ∞ F.M := F.smooth
local instance compactnessFrontierReductionC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance compactnessFrontierReductionT2 : T2Space F.M := F.t2
local instance compactnessFrontierReductionSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance compactnessFrontierReductionInhabited : Inhabited F.M := ⟨F.basepoint⟩
local instance compactnessFrontierReductionLocallyPathConnected :
    LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M
local instance compactnessFrontierReductionSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

def NullPlaneUniversalCoverSplittingAt (t₀ : ℝ) : Prop :=
  t₀ ≤ 0 →
    Module.finrank ℝ E = 3 →
    (∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t)) →
    (∀ t : ℝ, t ≤ 0 → PointedFlowNonnegativeCurvatureOperator (I := I) F t) →
    (∀ a b : ℝ, a < b → b ≤ 0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ x : F.M,
        F.rmNormSq (I := I) t x ≤ C) →
    PointedFlowNotFlat (I := I) F →
    ∀ (x₀ : F.M) (v₀ w₀ : TangentSpace I x₀),
      0 <
        (F.S.family.metric t₀).inner x₀ v₀ v₀ *
          (F.S.family.metric t₀).inner x₀ w₀ w₀ -
            ((F.S.family.metric t₀).inner x₀ v₀ w₀) ^ 2 →
      F.S.base.rm04 t₀ x₀ (vec4 (I := I) v₀ w₀ w₀ v₀) = 0 →
      ∃ G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval,
        let _ : TopologicalSpace G.M := G.topology
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G.M := G.charted
        let _ : IsManifold (𝓡 2) ∞ G.M := G.smooth
        let _ : IsManifold (𝓡 2) 1 G.M :=
          IsManifold.of_le (I := 𝓡 2) (M := G.M) (n := ∞) (by decide)
        let _ : T2Space G.M := G.t2
        let _ : SigmaCompactSpace G.M := G.sigmaCompact
        ∃ Phi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M,
          (∀ t : ℝ, t < 0 → ∀ y : G.M, 0 < G.S.scalar t y) ∧
          (∀ y : G.M, 0 < G.S.scalar 0 y) ∧
          ∀ (t : ℝ), t < 0 → ∀ (y : G.M) (s : ℝ)
            (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
            (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
                (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (v, a))
                (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (w, c)) =
              (G.S.family.metric t).inner y v w + a * c

omit [NeZero (Module.finrank ℝ E)] in
theorem nullPlaneUniversalCoverSplittingAt_of_global
    (h : NullPlaneUniversalCoverSplitting (I := I) F) (t₀ : ℝ) :
    NullPlaneUniversalCoverSplittingAt (I := I) F t₀ :=
  h t₀

omit [NeZero (Module.finrank ℝ E)] in
theorem nullPlaneUniversalCoverSplittingAt_of_negativeTimeSplitting
    (h : NegativeTimeUniversalCoverSplitting (I := I) F) (t₀ : ℝ) :
    NullPlaneUniversalCoverSplittingAt (I := I) F t₀ := by
  intro _ht₀ _hdim _hcomplete _hcurvature _hbounded _hnotFlat _x₀ _v₀ _w₀ _hplane _hnull
  obtain ⟨G, hconnG, hsimplyG, hcompleteG, hscalarG, hscalar0, Phi, hprod⟩ := h
  exact ⟨G, Phi, hscalarG, hscalar0, hprod⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem ancient_fixed_universal_cover_product_of_null_plane_of_nullPlaneSplittingAt
    (hconnected : ConnectedSpace F.M)
    (hcomplete : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t))
    (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (hdim : Module.finrank ℝ E = 3)
    (hcurvature : ∀ t : ℝ, t ≤ 0 →
      PointedFlowNonnegativeCurvatureOperator (I := I) F t)
    (hbounded : ∀ a b : ℝ, a < b → b ≤ 0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ x : F.M,
        F.rmNormSq (I := I) t x ≤ C)
    (hnotFlat : PointedFlowNotFlat (I := I) F)
    (x₀ : F.M) (v₀ w₀ : TangentSpace I x₀)
    (hplane : 0 <
      (F.S.family.metric t₀).inner x₀ v₀ v₀ *
        (F.S.family.metric t₀).inner x₀ w₀ w₀ -
          ((F.S.family.metric t₀).inner x₀ v₀ w₀) ^ 2)
    (hnull : F.S.base.rm04 t₀ x₀ (vec4 (I := I) v₀ w₀ w₀ v₀) = 0)
    (hsplit : NullPlaneUniversalCoverSplittingAt (I := I) F t₀) :
    let _ : ConnectedSpace F.M := hconnected
    ∃ G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval,
      let _ : TopologicalSpace G.M := G.topology
      let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G.M := G.charted
      let _ : IsManifold (𝓡 2) ∞ G.M := G.smooth
      let _ : IsManifold (𝓡 2) 1 G.M :=
        IsManifold.of_le (I := 𝓡 2) (M := G.M) (n := ∞) (by decide)
      let _ : T2Space G.M := G.t2
      let _ : SigmaCompactSpace G.M := G.sigmaCompact
      ConnectedSpace G.M ∧ SimplyConnectedSpace G.M ∧
      (∀ t : ℝ, t ≤ 0 → MetricComplete (I := 𝓡 2) (G.atTime t)) ∧
      (∀ t : ℝ, t ≤ 0 → ∀ y : G.M, 0 < G.S.scalar t y) ∧
      ∃ Phi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M,
        ∀ (t : ℝ), t ≤ 0 → ∀ (y : G.M) (s : ℝ)
          (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
          (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (v, a))
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (w, c)) =
            (G.S.family.metric t).inner y v w + a * c := by
  obtain ⟨G, hG⟩ :=
    hsplit ht₀ hdim hcomplete hcurvature hbounded hnotFlat x₀ v₀ w₀ hplane hnull
  let _ : TopologicalSpace G.M := G.topology
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G.M := G.charted
  let _ : IsManifold (𝓡 2) ∞ G.M := G.smooth
  let _ : IsManifold (𝓡 2) 1 G.M :=
    IsManifold.of_le (I := 𝓡 2) (M := G.M) (n := ∞) (by decide)
  let _ : T2Space G.M := G.t2
  let _ : SigmaCompactSpace G.M := G.sigmaCompact
  obtain ⟨Phi, hscalarG, hscalar0, hprod⟩ := hG
  exact ancient_fixed_universal_cover_product_of_negative_time_metric_product
    (I := I) F G Phi hconnected hcomplete hscalarG hscalar0 hprod

end AncientSplittingFrontierAt

section ShrinkerMass

variable (L : PointedRiemannianManifold.{u, uE, uH} (I := I))

local instance compactnessFrontierReductionManifoldTopology : TopologicalSpace L.M := L.topology
local instance compactnessFrontierReductionManifoldCharted : ChartedSpace H L.M := L.charted
local instance compactnessFrontierReductionManifoldSmooth : IsManifold I ∞ L.M := L.smooth
local instance compactnessFrontierReductionManifoldT2 : T2Space L.M := L.t2
local instance compactnessFrontierReductionManifoldSigma : SigmaCompactSpace L.M := L.sigmaCompact

omit [NeZero (Module.finrank ℝ E)] in
theorem normalized_nonflat_three_shrinker_noncompact_mass_dichotomy
    (hdim : Module.finrank ℝ E = 3) (hcomplete : MetricComplete (I := I) L)
    (hconnected : ConnectedSpace L.M)
    (hnonflat : ∃ x : L.M, metricScalarAt L.metric x ≠ 0)
    (hnco : ∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x),
      0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j))
    (f : C^∞⟮I, L.M; ℝ⟯) (hsoliton : gradientRicciSoliton L.metric f 1)
    (hnormal : IsHamiltonNormalizedPotential L.metric f)
    (hnoncompact : ¬ CompactSpace L.M) :
    normalizedShrinkerMass L.metric f = ENNReal.ofReal (2 * Real.exp (-1)) ∨
      normalizedShrinkerMass L.metric f = ENNReal.ofReal (Real.exp (-1)) := by
  rcases normalized_nonflat_three_shrinker_round_or_mass_of_noncompactModels (I := I) L hdim f
    (noncompactShrinkerIsometryModels_of_noncompact_of_nonflat_three_shrinker (I := I) L hdim
      hcomplete hconnected hnonflat hnco f hsoliton hnormal hnoncompact)
    noncompactShrinkerModelMasses with hround | hmass
  · exact absurd hround.1 hnoncompact
  · exact hmass

end ShrinkerMass

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
