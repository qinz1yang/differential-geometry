import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedVolumeNormalization
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval}

section BackwardSliceBlowdown

variable {kappa : ℝ} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance blowdownSourceTopology : TopologicalSpace F.M := F.topology
local instance blowdownSourceCharted : ChartedSpace H F.M := F.charted
local instance blowdownSourceSmooth : IsManifold I ∞ F.M := F.smooth
local instance blowdownSourceT2 : T2Space F.M := F.t2
local instance blowdownSourceSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance blowdownSourceTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle

def backwardSliceApproximateMetricCompactness (hF : IsAncientKappaSolution kappa F)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M) : Prop :=
  HasSubsequencePairwiseApproximateIsometries (I := I) (backwardSliceSequence F tau htau q)
    (fun k => properMetricOn (I := I) ((backwardSliceSequence F tau htau q).obj k)
      ((backwardSliceSequence_complete F hF tau htau q).complete k)
      (backwardSliceSequence_connected F hF tau htau q k))


def backwardSliceLimitGradientShrinker
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M) (p : F.M) : Prop :=
  AntitoneOn (intrinsicReducedVolume F.S 0 p) (Ioi 0) →
    ∀ L : PointedRiemannianManifold.{u, uE, uH} (I := I),
      (∃ (phi : ℕ → ℕ) (_ : PointedRiemannianConvergenceMaps (I := I)
          (backwardSliceSequence F tau htau q) L phi), StrictMono phi) →
      MetricComplete (I := I) L →
      (let _ : TopologicalSpace L.M := L.topology
       let _ : ChartedSpace H L.M := L.charted
       let _ : IsManifold I ∞ L.M := L.smooth
       let _ : T2Space L.M := L.t2
       ConnectedSpace L.M ∧
       (∃ x : L.M, metricScalarAt (I := I) L.metric x ≠ 0) ∧
       ∃ f : C^∞⟮I, L.M; ℝ⟯, gradientRicciSoliton (I := I) L.metric f 1)


theorem exists_backward_slice_pointed_limit
    (hF : IsAncientKappaSolution kappa F)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (hcompact : backwardSliceApproximateMetricCompactness F hF tau htau q) :
    ∃ (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (I := I)
            (backwardSliceSequence F tau htau q) L phi)
        (C : MetricConvergenceData (I := I) Phi),
        (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I) Phi k) ∧
        (∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric) ∧
        MetricComplete (I := I) L ∧
        (let _ : TopologicalSpace L.M := L.topology
         let _ : ChartedSpace H L.M := L.charted
         let _ : IsManifold I ∞ L.M := L.smooth
         let _ : T2Space L.M := L.t2
         ConnectedSpace L.M) := by
  classical
  obtain ⟨CC⟩ :=
    exists_connectedCanonicalMetricCompactness_of_hasSubsequencePairwiseApproximateIsometries
      (I := I) (backwardSliceSequence F tau htau q)
      (backwardSliceSequence_complete F hF tau htau q)
      (backwardSliceSequence_connected F hF tau htau q) hcompact
  refine ⟨CC.canonical.compactness.limit, CC.canonical.compactness.subseq,
    CC.canonical.compactness.strictMono, CC.canonical.compactness.maps,
    CC.canonical.compactness.convergence.metrics, ?_, ?_, ?_, ?_⟩
  · intro k
    exact CC.canonical.domain_eq_canonical k
  · intro k
    exact CC.canonical.reference_eq_limit k
  · exact CC.canonical.compactness.limit_complete
  · exact CC.connected


theorem exists_backward_slice_asymptotic_shrinker_of_blowdownInput
    (hF : IsAncientKappaSolution kappa F)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i)
    (q : ℕ → F.M) (p : F.M)
    (hmono : AntitoneOn (intrinsicReducedVolume F.S 0 p) (Ioi 0))
    (hcompact : backwardSliceApproximateMetricCompactness F hF tau htau q)
    (hlimit : backwardSliceLimitGradientShrinker F tau htau q p) :
    ∃ (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (I := I)
            (backwardSliceSequence F tau htau q) L phi)
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
  obtain ⟨L, phi, hphi, Phi, C, hdomain, hreference, hcomplete, hconnected⟩ :=
    exists_backward_slice_pointed_limit F hF tau htau q hcompact
  exact ⟨L, phi, hphi, Phi, C, hdomain, hreference, hcomplete,
    hlimit hmono L ⟨phi, Phi, hphi⟩ hcomplete⟩

end BackwardSliceBlowdown

section ModelWitness

local notation "RoundSphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

theorem exists_nonflat_connected_gradientShrinker_model :
    ∃ L : PointedRiemannianManifold.{0, 0, 0} (I := 𝓡 2),
      MetricComplete (I := 𝓡 2) L ∧
      (let _ : TopologicalSpace L.M := L.topology
       let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) L.M := L.charted
       let _ : IsManifold (𝓡 2) ∞ L.M := L.smooth
       let _ : T2Space L.M := L.t2
       ConnectedSpace L.M ∧
       (∃ x : L.M, metricScalarAt (I := 𝓡 2) L.metric x ≠ 0) ∧
       ∃ f : C^∞⟮𝓡 2, L.M; ℝ⟯, gradientRicciSoliton (I := 𝓡 2) L.metric f 1) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let x₀ : RoundSphereTwo :=
    ⟨PiLp.single 2 (0 : Fin 3) (1 : ℝ), by
      rw [mem_sphere_zero_iff_norm, PiLp.norm_single, norm_one]⟩
  let L : PointedRiemannianManifold.{0, 0, 0} (I := 𝓡 2) :=
    { M := RoundSphereTwo
      basepoint := x₀
      metric := roundTwoSphereShrinkerMetric }
  refine ⟨L, ?_, ?_⟩
  · exact (roundSphereShrinkerMetric_complete (A := EuclideanSpace ℝ (Fin 3)) (n := 2)
      (by decide)).complete
  · refine ⟨?_, ?_, ?_⟩
    · have hdim : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
        rw [← Module.finrank_eq_rank]
        norm_num
      exact isConnected_iff_connectedSpace.mp (isConnected_sphere hdim 0 zero_le_one)
    · exact ⟨x₀, by
        rw [roundTwoSphereShrinkerMetric_scalarCurvature]
        norm_num⟩
    · exact ⟨roundTwoSphereShrinkerPotential,
        (normalizedGradientRicciSoliton_roundTwoSphere).2.1⟩

theorem exists_flat_gradientShrinker_model :
    ∃ L : PointedRiemannianManifold.{0, 0, 0} (I := 𝓘(ℝ, ℝ)),
      MetricComplete (I := 𝓘(ℝ, ℝ)) L ∧
      (let _ : TopologicalSpace L.M := L.topology
       let _ : ChartedSpace ℝ L.M := L.charted
       let _ : IsManifold (𝓘(ℝ, ℝ)) ∞ L.M := L.smooth
       let _ : T2Space L.M := L.t2
       ConnectedSpace L.M ∧
       (∀ x : L.M, metricScalarAt (I := 𝓘(ℝ, ℝ)) L.metric x = 0) ∧
       ∃ f : C^∞⟮𝓘(ℝ, ℝ), L.M; ℝ⟯, gradientRicciSoliton (I := 𝓘(ℝ, ℝ)) L.metric f 1) := by
  let L : PointedRiemannianManifold.{0, 0, 0} (I := 𝓘(ℝ, ℝ)) :=
    { M := ℝ
      basepoint := 0
      metric := euclideanMetric (E := ℝ) }
  refine ⟨L, ?_, ?_⟩
  · exact (euclideanMetric_complete (E := ℝ)).complete
  · refine ⟨?_, ?_, ?_⟩
    · infer_instance
    · intro x
      exact euclideanMetric_scalarCurvature (E := ℝ) x
    · exact ⟨gaussianPotential (E := ℝ), gradientRicciSoliton_gaussian (E := ℝ)⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem not_forall_complete_pointed_gradientShrinker_nonflat :
    ¬ (∀ L : PointedRiemannianManifold.{0, 0, 0} (I := 𝓘(ℝ, ℝ)),
        MetricComplete (I := 𝓘(ℝ, ℝ)) L →
        (let _ : TopologicalSpace L.M := L.topology
         let _ : ChartedSpace ℝ L.M := L.charted
         let _ : IsManifold (𝓘(ℝ, ℝ)) ∞ L.M := L.smooth
         let _ : T2Space L.M := L.t2
         ∃ x : L.M, metricScalarAt (I := 𝓘(ℝ, ℝ)) L.metric x ≠ 0)) := by
  intro h
  obtain ⟨L, hcomplete, _hconnected, hflat, _hsoliton⟩ := exists_flat_gradientShrinker_model
  obtain ⟨x, hx⟩ := h L hcomplete
  exact hx (hflat x)

end ModelWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
