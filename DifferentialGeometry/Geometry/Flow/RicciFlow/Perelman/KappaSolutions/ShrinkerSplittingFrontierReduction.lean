import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompactnessFrontierReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinkerBlowdown
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinkerNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSplitting
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSplittingNegativeTime

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

section MetricCompactnessAtBase

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

def SubsequenceStaircaseCompactnessFrontier
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (_hinj : BaseInjBound (I := I) X) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ → Nonempty (SeqBallGeometry (I := I) (X.subseq φ)) →
    HasSubsequencePairwiseApproximateIsometries (I := I) (X.subseq φ)
      (fun k => properMetricOn (I := I) ((X.subseq φ).obj k)
        ((hcomplete.subseq φ).complete k)
        ((PointedRiemannianSeq.connected_subseq hconnected φ) k))

theorem subsequenceStaircaseCompactnessFrontier_of_localStaircaseCompactnessFrontier
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (hinj : BaseInjBound (I := I) X)
    (h : LocalStaircaseCompactnessFrontier (I := I) X) :
    SubsequenceStaircaseCompactnessFrontier (I := I) X hcomplete hconnected hinj := by
  intro φ hφ hball
  obtain ⟨ψ, hψ, b, hd⟩ := h φ hφ (hcomplete.subseq φ)
    (PointedRiemannianSeq.connected_subseq hconnected φ) (hinj.subseq φ) hball
  obtain ⟨σ, hσ, hpair⟩ :=
    b.exists_pairwise_approximate_isometry_subsequence_of_bounded_geometry (Classical.choice hd)
      (hcomplete.subseq (φ ∘ ψ))
      (PointedRiemannianSeq.connected_subseq hconnected (φ ∘ ψ))
  exact ⟨ψ ∘ σ, hψ.comp hσ, hpair⟩

theorem subsequenceStaircaseCompactnessFrontier_of_seqBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (hinj : BaseInjBound (I := I) X)
    (hgeom : SeqBoundedGeometry (I := I) X) :
    SubsequenceStaircaseCompactnessFrontier (I := I) X hcomplete hconnected hinj := by
  intro φ hφ hball
  exact staircaseApproximateIsometryFrontier_of_seqBoundedGeometry (I := I) (X.subseq φ)
    (hgeom.subseq φ) (hcomplete.subseq φ)
    (PointedRiemannianSeq.connected_subseq hconnected φ) (hinj.subseq φ) hball

theorem exists_local_pointed_metric_compactness_of_subsequenceStaircaseFrontier
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
    (hfrontier : SubsequenceStaircaseCompactnessFrontier (I := I) X hcomplete hconnected hinj) :
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
  obtain ⟨σ, hσ, hpair⟩ := hfrontier φ hφ hball
  have hpairX : HasPairwiseApproximateIsometries (I := I) (X := X.subseq (φ ∘ σ))
      (fun k => properMetricOn (I := I) (X.obj ((φ ∘ σ) k))
        (hcomplete.complete ((φ ∘ σ) k)) (hconnected ((φ ∘ σ) k))) := hpair
  obtain ⟨C⟩ :=
    exists_connectedCanonicalMetricCompactness_of_hasSubsequencePairwiseApproximateIsometries
      (I := I) X hcomplete hconnected ⟨φ ∘ σ, hφ.comp hσ, hpairX⟩
  exact ⟨C.canonical.compactness, C.canonical.domain_eq_canonical,
    C.canonical.reference_eq_limit, C.connected⟩

end MetricCompactnessAtBase

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section BackwardSlice

variable {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
variable [NeZero (Module.finrank ℝ E)]

local instance rescaledBackwardSliceTopology : TopologicalSpace F.M := F.topology
local instance rescaledBackwardSliceCharted : ChartedSpace H F.M := F.charted
local instance rescaledBackwardSliceSmooth : IsManifold I ∞ F.M := F.smooth
local instance rescaledBackwardSliceT2 : T2Space F.M := F.t2
local instance rescaledBackwardSliceSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance rescaledBackwardSliceTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle

def RescaledBackwardSliceShrinkerLimit {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) : Prop :=
  ∃ (q : ℕ → F.M) (p : F.M),
    AntitoneOn (intrinsicReducedVolume F.S 0 p) (Set.Ioi 0) ∧
    backwardSliceApproximateMetricCompactness (I := I) F hF tau htau q ∧
    backwardSliceLimitGradientShrinker (I := I) F tau htau q p

theorem exists_backward_slice_asymptotic_shrinker_of_rescaledSliceShrinkerLimit
    {kappa : ℝ} (hF : IsAncientKappaSolution (I := I) kappa F)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i)
    (h : RescaledBackwardSliceShrinkerLimit (I := I) F hF tau htau) :
    ∃ (q : ℕ → F.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence F tau htau q) L phi)
        (C : MetricConvergenceData (I := I) Phi),
        (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I) Phi k) ∧
        (∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric) ∧
        MetricComplete (I := I) L ∧
        (let _ : TopologicalSpace L.M := L.topology
         let _ : ChartedSpace H L.M := L.charted
         let _ : IsManifold I ∞ L.M := L.smooth
         let _ : T2Space L.M := L.t2
         ConnectedSpace L.M ∧
         (∃ x : L.M, metricScalarAt (I := I) L.metric x ≠ 0) ∧
         ∃ f : C^∞⟮I, L.M; ℝ⟯, gradientRicciSoliton (I := I) L.metric f 1) := by
  obtain ⟨q, p, hmono, hcompact, hlimit⟩ := h
  obtain ⟨L, phi, hphi, Phi, C, hdomain, hreference, hcomplete, hgeometry⟩ :=
    exists_backward_slice_asymptotic_shrinker_of_blowdownInput (I := I) F hF tau htau q p
      hmono hcompact hlimit
  exact ⟨q, L, phi, hphi, Phi, C, hdomain, hreference, hcomplete, hgeometry⟩

end BackwardSlice

section SamePole

variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
variable [NeZero (Module.finrank ℝ E)]

local instance samePoleRescaledSliceTopology : TopologicalSpace F.M := F.topology
local instance samePoleRescaledSliceCharted : ChartedSpace H F.M := F.charted
local instance samePoleRescaledSliceSmooth : IsManifold I ∞ F.M := F.smooth
local instance samePoleRescaledSliceT2 : T2Space F.M := F.t2
local instance samePoleRescaledSliceSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance samePoleRescaledSliceTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle

def SamePoleRescaledSliceLimit {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) : Prop :=
  ∃ q : ℕ → F.M,
    (∀ i, lCost F.S 0 p (q i) (tau i) / (2 * Real.sqrt (tau i)) ≤
      (Module.finrank ℝ E : ℝ) / 2) ∧
    backwardSliceApproximateMetricCompactness (I := I) F hF tau htau q ∧
    ∀ (phi : ℕ → ℕ) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)),
      StrictMono phi →
      ∀ (Phi : PointedRiemannianConvergenceMaps (I := I)
        (backwardSliceSequence F tau htau q) L phi)
        (C : MetricConvergenceData (I := I) Phi),
      (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I) Phi k) →
      MetricComplete (I := I) L →
      (let _ : TopologicalSpace L.M := L.topology
       let _ : ChartedSpace H L.M := L.charted
       let _ : IsManifold I ∞ L.M := L.smooth
       let _ : T2Space L.M := L.t2
       let _ : SigmaCompactSpace L.M := L.sigmaCompact
       ConnectedSpace L.M →
       (∃ x : L.M, metricScalarAt (I := I) L.metric x ≠ 0) ∧
       (∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x),
         0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j)) ∧
       ∃ f : C^∞⟮I, L.M; ℝ⟯,
         gradientRicciSoliton L.metric f 1 ∧
         IsHamiltonNormalizedPotential L.metric f ∧
         Tendsto (fun i => intrinsicReducedVolume F.S 0 p (tau (phi i)))
           atTop (𝓝 (normalizedShrinkerMass L.metric f)))

theorem exists_samePole_normalized_asymptotic_shrinker_of_samePoleRescaledSliceLimit
    {kappa : ℝ} (hF : IsAncientKappaSolution (I := I) kappa F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i)
    (h : SamePoleRescaledSliceLimit (I := I) F hF p tau htau) :
    ∃ (q : ℕ → F.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      (∀ i, lCost F.S 0 p (q i) (tau i) / (2 * Real.sqrt (tau i)) ≤
        (Module.finrank ℝ E : ℝ) / 2) ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence F tau htau q) L phi)
        (C : MetricConvergenceData (I := I) Phi),
        (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k) ∧
        MetricComplete (I := I) L ∧
        (let _ : TopologicalSpace L.M := L.topology
         let _ : ChartedSpace H L.M := L.charted
         let _ : IsManifold I ∞ L.M := L.smooth
         let _ : T2Space L.M := L.t2
         let _ : SigmaCompactSpace L.M := L.sigmaCompact
         ConnectedSpace L.M ∧
         (∃ x : L.M, metricScalarAt (I := I) L.metric x ≠ 0) ∧
         (∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x),
           0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j)) ∧
         ∃ f : C^∞⟮I, L.M; ℝ⟯,
           gradientRicciSoliton L.metric f 1 ∧
           IsHamiltonNormalizedPotential L.metric f ∧
           Tendsto (fun i => intrinsicReducedVolume F.S 0 p (tau (phi i)))
             atTop (𝓝 (normalizedShrinkerMass L.metric f))) := by
  obtain ⟨q, hcost, hcompact, hlimit⟩ := h
  obtain ⟨L, phi, hphi, Phi, C, hdomain, _hreference, hcomplete, hconnected⟩ :=
    exists_backward_slice_pointed_limit (I := I) F hF tau htau q hcompact
  exact ⟨q, L, phi, hphi, hcost, Phi, C, hdomain, hcomplete,
    hconnected, hlimit phi L hphi Phi C hdomain hcomplete hconnected⟩

end SamePole

section ReducedVolumeSlab

variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance slabTerminalTopology : TopologicalSpace F.M := F.topology
local instance slabTerminalCharted : ChartedSpace H F.M := F.charted
local instance slabTerminalSmooth : IsManifold I ∞ F.M := F.smooth
local instance slabTerminalT2 : T2Space F.M := F.t2
local instance slabTerminalSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance slabTerminalTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle

omit [I.Boundaryless] in
theorem ancient_reducedVolume_antitone_of_slabAntitone
    (h : redVolumeIcoSlabAntitone (I := I) (D := ancientTimeInterval) F.S) (p : F.M) :
    AntitoneOn (intrinsicReducedVolume F.S 0 p) (Set.Ioi 0) := by
  intro tau1 h1 tau2 h2 h12
  have hle := h 0 p F.isSolution h1 h12 (by simp)
    (fun t ht => by
      simp only [ancientTimeInterval_regular, Set.mem_Iio]
      exact ht.2)
  simpa only [intrinsicReducedVolume_eq_redVolume] using hle

omit [I.Boundaryless] in
theorem not_Icc_neg_one_zero_subset_ancientTimeInterval_regular :
    ¬ (Set.Icc (-1 : ℝ) 0 ⊆ ancientTimeInterval.regular) := by
  intro h
  have h0 := h (Set.mem_Icc.mpr ⟨by norm_num, le_rfl⟩)
  simp only [ancientTimeInterval_regular, Set.mem_Iio] at h0
  exact absurd h0 (lt_irrefl (0 : ℝ))

omit [I.Boundaryless] in
theorem Ico_neg_one_zero_subset_ancientTimeInterval_regular :
    Set.Ico (-1 : ℝ) 0 ⊆ ancientTimeInterval.regular := by
  intro t ht
  simp only [ancientTimeInterval_regular, Set.mem_Iio]
  exact ht.2

end ReducedVolumeSlab

section NullPlane

variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance nullPlaneTerminalTopology : TopologicalSpace F.M := F.topology
local instance nullPlaneTerminalCharted : ChartedSpace H F.M := F.charted
local instance nullPlaneTerminalSmooth : IsManifold I ∞ F.M := F.smooth
local instance nullPlaneTerminalC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance nullPlaneTerminalT2 : T2Space F.M := F.t2
local instance nullPlaneTerminalSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance nullPlaneTerminalInhabited : Inhabited F.M := ⟨F.basepoint⟩
local instance nullPlaneTerminalLocallyPathConnected : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M
local instance nullPlaneTerminalSemilocallySimplyConnected : SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

theorem ancient_fixed_universal_cover_product_of_null_plane_of_negativeTimeSplitting
    (hconnected : ConnectedSpace F.M)
    (hcomplete : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t))
    (hsplit : NegativeTimeUniversalCoverSplitting (I := I) F) :
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
            (G.S.family.metric t).inner y v w + a * c :=
  ancient_fixed_universal_cover_product_of_negative_time_splitting F hconnected hcomplete hsplit

end NullPlane

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
