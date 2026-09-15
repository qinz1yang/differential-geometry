import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinkerFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinkerHeadlineReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinkerReduction

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

namespace Blowdown

section General

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {D : RealTimeInterval} (G : PointedFlowData.{u, uE, uH} (I := I) D)

local instance generalTopology : TopologicalSpace G.M := G.topology
local instance generalCharted : ChartedSpace H G.M := G.charted
local instance generalSmooth : IsManifold I ∞ G.M := G.smooth
local instance generalT2 : T2Space G.M := G.t2
local instance generalSigma : SigmaCompactSpace G.M := G.sigmaCompact

def BackwardSliceAsymptoticShrinkerInput [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa G)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) : Prop :=
  ∃ (q : ℕ → G.M) (p : G.M),
    AntitoneOn (intrinsicReducedVolume G.S 0 p) (Ioi 0) ∧
    backwardSliceApproximateMetricCompactness (F := G) hF tau htau q ∧
    backwardSliceLimitGradientShrinker (F := G) tau htau q p

theorem exists_backward_slice_asymptotic_shrinker_of_input
    [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa G)
    (_hdim : 2 ≤ Module.finrank ℝ E)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (_hescape : Tendsto tau atTop atTop)
    (h : BackwardSliceAsymptoticShrinkerInput (G := G) hF tau htau) :
    ∃ (q : ℕ → G.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence G tau htau q) L phi)
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
  exact ⟨q, exists_backward_slice_asymptotic_shrinker_of_blowdownInput (F := G) hF tau htau q p
    hmono hcompact hlimit⟩

def HasBackwardSliceShrinkerInput [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa G)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (p : G.M) : Prop :=
  ∃ q : ℕ → G.M, backwardSliceApproximateMetricCompactness (F := G) hF tau htau q ∧
    backwardSliceLimitGradientShrinker (F := G) tau htau q p

theorem exists_backward_slice_asymptotic_shrinker_of_shrinkerInput
    [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa G)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (p : G.M)
    (hmono : AntitoneOn (intrinsicReducedVolume G.S 0 p) (Set.Ioi 0))
    (hinput : HasBackwardSliceShrinkerInput (G := G) hF tau htau p) :
    ∃ (q : ℕ → G.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence G tau htau q) L phi)
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
  obtain ⟨q, hcompact, hlimit⟩ := hinput
  obtain ⟨L, phi, hphi, Phi, C, hdomain, hreference, hcomplete, hgeometry⟩ :=
    exists_backward_slice_asymptotic_shrinker_of_blowdownInput (F := G) hF tau htau q p hmono
      hcompact hlimit
  exact ⟨q, L, phi, hphi, Phi, C, hdomain, hreference, hcomplete, hgeometry⟩

def BackwardSliceReducedVolumeAntitoneInput (p : G.M) : Prop :=
  AntitoneOn (intrinsicReducedVolume G.S 0 p) (Ioi 0)

def BackwardSliceMetricCompactnessInput [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa G)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) : Prop :=
  ∃ q : ℕ → G.M, backwardSliceApproximateMetricCompactness (F := G) hF tau htau q

def BackwardSliceLimitRigidityInput
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (p : G.M) : Prop :=
  ∀ q : ℕ → G.M, backwardSliceLimitGradientShrinker (F := G) tau htau q p

theorem exists_backward_slice_asymptotic_shrinker_of_components
    [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa G)
    (_hdim : 2 ≤ Module.finrank ℝ E)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (_hescape : Tendsto tau atTop atTop)
    (p : G.M)
    (hmono : BackwardSliceReducedVolumeAntitoneInput (G := G) p)
    (hcompact : BackwardSliceMetricCompactnessInput (G := G) hF tau htau)
    (hrigid : BackwardSliceLimitRigidityInput (G := G) tau htau p) :
    ∃ (q : ℕ → G.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence G tau htau q) L phi)
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
  obtain ⟨q, hq⟩ := hcompact
  exact exists_backward_slice_asymptotic_shrinker_of_input (G := G) hF _hdim tau htau _hescape
    ⟨q, p, hmono, hq, hrigid q⟩

end General

section Ancient

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable (G : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientTopology : TopologicalSpace G.M := G.topology
local instance ancientCharted : ChartedSpace H G.M := G.charted
local instance ancientSmooth : IsManifold I ∞ G.M := G.smooth
local instance ancientT2 : T2Space G.M := G.t2
local instance ancientSigma : SigmaCompactSpace G.M := G.sigmaCompact

def SamePoleLimitGeometry
    (p : G.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i)
    (q : ℕ → G.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ) : Prop :=
  StrictMono phi ∧
  (∀ i, lCost G.S 0 p (q i) (tau i) / (2 * Real.sqrt (tau i)) ≤
    (Module.finrank ℝ E : ℝ) / 2) ∧
  ∃ (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence G tau htau q) L phi)
    (C : MetricConvergenceData (I := I) Phi),
    (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I) Phi k) ∧
    MetricComplete (I := I) L ∧
    (let _ : TopologicalSpace L.M := L.topology
     let _ : ChartedSpace H L.M := L.charted
     let _ : IsManifold I ∞ L.M := L.smooth
     let _ : T2Space L.M := L.t2
     let _ : SigmaCompactSpace L.M := L.sigmaCompact
     ConnectedSpace L.M ∧
     (∃ x : L.M, metricScalarAt L.metric x ≠ 0) ∧
     (∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x),
       0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j)))

def SamePoleAsymptoticShrinkerData
    (p : G.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) : Prop :=
  ∃ (q : ℕ → G.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
    SamePoleLimitGeometry (G := G) p tau htau q L phi

def NormalizedShrinkerMassConvergence
    (p : G.M) (tau : ℕ → ℝ) (phi : ℕ → ℕ)
    (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) : Prop :=
  let _ : TopologicalSpace L.M := L.topology
  let _ : ChartedSpace H L.M := L.charted
  let _ : IsManifold I ∞ L.M := L.smooth
  let _ : T2Space L.M := L.t2
  let _ : SigmaCompactSpace L.M := L.sigmaCompact
  ∃ f : C^∞⟮I, L.M; ℝ⟯,
    gradientRicciSoliton L.metric f 1 ∧
    IsHamiltonNormalizedPotential L.metric f ∧
    Tendsto (fun i => intrinsicReducedVolume G.S 0 p (tau (phi i)))
      atTop (𝓝 (normalizedShrinkerMass L.metric f))

def SamePoleNormalizedMassLimit
    (p : G.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) : Prop :=
  ∀ (q : ℕ → G.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
    SamePoleLimitGeometry (G := G) p tau htau q L phi →
    NormalizedShrinkerMassConvergence (G := G) p tau phi L

theorem exists_samePole_normalized_asymptotic_shrinker_of_data_and_mass
    {kappa : ℝ} (_hF : IsAncientKappaSolution kappa G)
    (_hdim : 2 ≤ Module.finrank ℝ E) (p : G.M)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (_hescape : Tendsto tau atTop atTop)
    (hdata : SamePoleAsymptoticShrinkerData (G := G) p tau htau)
    (hmass : SamePoleNormalizedMassLimit (G := G) p tau htau) :
    ∃ (q : ℕ → G.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      (∀ i, lCost G.S 0 p (q i) (tau i) / (2 * Real.sqrt (tau i)) ≤
        (Module.finrank ℝ E : ℝ) / 2) ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence G tau htau q) L phi)
        (C : MetricConvergenceData (I := I) Phi),
        (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k) ∧
        MetricComplete (I := I) L ∧
        (let _ : TopologicalSpace L.M := L.topology
         let _ : ChartedSpace H L.M := L.charted
         let _ : IsManifold I ∞ L.M := L.smooth
         let _ : T2Space L.M := L.t2
         let _ : SigmaCompactSpace L.M := L.sigmaCompact
         ConnectedSpace L.M ∧
         (∃ x : L.M, metricScalarAt L.metric x ≠ 0) ∧
         (∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x),
           0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j)) ∧
         ∃ f : C^∞⟮I, L.M; ℝ⟯,
           gradientRicciSoliton L.metric f 1 ∧
           IsHamiltonNormalizedPotential L.metric f ∧
           Tendsto (fun i => intrinsicReducedVolume G.S 0 p (tau (phi i)))
             atTop (𝓝 (normalizedShrinkerMass L.metric f))) := by
  obtain ⟨q, L, phi, hgeom⟩ := hdata
  obtain ⟨hphi, hcenter, hrest⟩ := hgeom
  obtain ⟨Phi, hrest⟩ := hrest
  obtain ⟨C, hrest⟩ := hrest
  obtain ⟨hcanon, hcomplete, hshape⟩ := hrest
  have hgeom' : SamePoleLimitGeometry (G := G) p tau htau q L phi :=
    ⟨hphi, hcenter, Phi, C, hcanon, hcomplete, hshape⟩
  obtain ⟨hconn, hnonflat, hnco⟩ := hshape
  obtain ⟨f, hsol, hham, hmassconv⟩ := hmass q L phi hgeom'
  let _ : TopologicalSpace L.M := L.topology
  let _ : ChartedSpace H L.M := L.charted
  let _ : IsManifold I ∞ L.M := L.smooth
  let _ : T2Space L.M := L.t2
  let _ : SigmaCompactSpace L.M := L.sigmaCompact
  refine ⟨q, L, phi, hphi, hcenter, Phi, C, hcanon, hcomplete, hconn, hnonflat, hnco, ?_⟩
  exact ⟨f, hsol, hham, hmassconv⟩

omit [I.Boundaryless] in
theorem backwardSliceReducedVolumeAntitoneInput_of_icoSlabAntitone
    (h : ∀ (D : RealTimeInterval) (S : SolutionOn (I := I) (M := G.M) D),
      redVolumeIcoSlabAntitone (I := I) (D := D) S)
    (p : G.M) : BackwardSliceReducedVolumeAntitoneInput (G := G) p :=
  ancient_reducedVolume_antitone_of_icoSlabAntitone (F := G) h p

def HasSamePoleNormalizedShrinkerInput [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa G)
    (p : G.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) : Prop :=
  ∃ q : ℕ → G.M,
    (∀ i, lCost G.S 0 p (q i) (tau i) / (2 * Real.sqrt (tau i)) ≤
      (Module.finrank ℝ E : ℝ) / 2) ∧
    backwardSliceApproximateMetricCompactness (F := G) hF tau htau q ∧
    ∀ (phi : ℕ → ℕ) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)),
      StrictMono phi →
      ∀ (Phi : PointedRiemannianConvergenceMaps (I := I)
        (backwardSliceSequence G tau htau q) L phi)
        (C : MetricConvergenceData (I := I) Phi),
      (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I) Phi k) →
      MetricComplete (I := I) L →
      (let _ : TopologicalSpace L.M := L.topology
       let _ : ChartedSpace H L.M := L.charted
       let _ : IsManifold I ∞ L.M := L.smooth
       let _ : T2Space L.M := L.t2
       let _ : SigmaCompactSpace L.M := L.sigmaCompact
       ConnectedSpace L.M →
       (∃ x : L.M, metricScalarAt L.metric x ≠ 0) ∧
       (∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x),
         0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j)) ∧
       ∃ f : C^∞⟮I, L.M; ℝ⟯,
         gradientRicciSoliton L.metric f 1 ∧
         IsHamiltonNormalizedPotential L.metric f ∧
         Tendsto (fun i => intrinsicReducedVolume G.S 0 p (tau (phi i)))
           atTop (𝓝 (normalizedShrinkerMass L.metric f)))

theorem exists_samePole_normalized_asymptotic_shrinker_of_input [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa G) (p : G.M)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i)
    (hinput : HasSamePoleNormalizedShrinkerInput (G := G) hF p tau htau) :
    ∃ (q : ℕ → G.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      (∀ i, lCost G.S 0 p (q i) (tau i) / (2 * Real.sqrt (tau i)) ≤
        (Module.finrank ℝ E : ℝ) / 2) ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence G tau htau q) L phi)
        (C : MetricConvergenceData (I := I) Phi),
        (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k) ∧
        MetricComplete (I := I) L ∧
        (let _ : TopologicalSpace L.M := L.topology
         let _ : ChartedSpace H L.M := L.charted
         let _ : IsManifold I ∞ L.M := L.smooth
         let _ : T2Space L.M := L.t2
         let _ : SigmaCompactSpace L.M := L.sigmaCompact
         ConnectedSpace L.M ∧
         (∃ x : L.M, metricScalarAt L.metric x ≠ 0) ∧
         (∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x),
           0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j)) ∧
         ∃ f : C^∞⟮I, L.M; ℝ⟯,
           gradientRicciSoliton L.metric f 1 ∧
           IsHamiltonNormalizedPotential L.metric f ∧
           Tendsto (fun i => intrinsicReducedVolume G.S 0 p (tau (phi i)))
             atTop (𝓝 (normalizedShrinkerMass L.metric f))) := by
  obtain ⟨q, hcost, hcompact, hlimit⟩ := hinput
  obtain ⟨L, phi, hphi, Phi, C, hdomain, hreference, hcomplete, hconnected⟩ :=
    exists_backward_slice_pointed_limit (F := G) hF tau htau q hcompact
  exact ⟨q, L, phi, hphi, hcost, Phi, C, hdomain, hcomplete,
    hconnected, hlimit phi L hphi Phi C hdomain hcomplete hconnected⟩

end Ancient

end Blowdown

section Bridge

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

theorem backwardSliceAsymptoticShrinkerInput_iff {D : RealTimeInterval}
    (G : PointedFlowData.{u, uE, uH} (I := I) D) [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa G)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) :
    BackwardSliceAsymptoticShrinkerInput (G := G) hF tau htau ↔
      Blowdown.BackwardSliceAsymptoticShrinkerInput (G := G) hF tau htau :=
  Iff.rfl

theorem hasBackwardSliceShrinkerInput_iff {D : RealTimeInterval}
    (G : PointedFlowData.{u, uE, uH} (I := I) D) [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa G)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (p : G.M) :
    HasBackwardSliceShrinkerInput (F := G) hF tau htau p ↔
      Blowdown.HasBackwardSliceShrinkerInput (G := G) hF tau htau p :=
  Iff.rfl

omit [I.Boundaryless] in
theorem backwardSliceReducedVolumeAntitoneInput_iff {D : RealTimeInterval}
    (G : PointedFlowData.{u, uE, uH} (I := I) D) (p : G.M) :
    BackwardSliceReducedVolumeAntitoneInput (G := G) p ↔
      Blowdown.BackwardSliceReducedVolumeAntitoneInput (G := G) p :=
  Iff.rfl

theorem backwardSliceMetricCompactnessInput_iff {D : RealTimeInterval}
    (G : PointedFlowData.{u, uE, uH} (I := I) D) [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa G)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) :
    BackwardSliceMetricCompactnessInput (G := G) hF tau htau ↔
      Blowdown.BackwardSliceMetricCompactnessInput (G := G) hF tau htau :=
  Iff.rfl

theorem backwardSliceLimitRigidityInput_iff {D : RealTimeInterval}
    (G : PointedFlowData.{u, uE, uH} (I := I) D)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (p : G.M) :
    BackwardSliceLimitRigidityInput (G := G) tau htau p ↔
      Blowdown.BackwardSliceLimitRigidityInput (G := G) tau htau p :=
  Iff.rfl

omit [I.Boundaryless] in
theorem samePoleLimitGeometry_iff
    (G : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    (p : G.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i)
    (q : ℕ → G.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ) :
    SamePoleLimitGeometry (G := G) p tau htau q L phi ↔
      Blowdown.SamePoleLimitGeometry (G := G) p tau htau q L phi :=
  Iff.rfl

omit [I.Boundaryless] in
theorem samePoleAsymptoticShrinkerData_iff
    (G : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    (p : G.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) :
    SamePoleAsymptoticShrinkerData (G := G) p tau htau ↔
      Blowdown.SamePoleAsymptoticShrinkerData (G := G) p tau htau :=
  Iff.rfl

theorem normalizedShrinkerMassConvergence_iff
    (G : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    (p : G.M) (tau : ℕ → ℝ) (phi : ℕ → ℕ)
    (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) :
    NormalizedShrinkerMassConvergence (G := G) p tau phi L ↔
      Blowdown.NormalizedShrinkerMassConvergence (G := G) p tau phi L :=
  Iff.rfl

theorem samePoleNormalizedMassLimit_iff
    (G : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    (p : G.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) :
    SamePoleNormalizedMassLimit (G := G) p tau htau ↔
      Blowdown.SamePoleNormalizedMassLimit (G := G) p tau htau :=
  Iff.rfl

theorem hasSamePoleNormalizedShrinkerInput_iff
    (G : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    [NeZero (Module.finrank ℝ E)] {kappa : ℝ} (hF : IsAncientKappaSolution kappa G)
    (p : G.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) :
    HasSamePoleNormalizedShrinkerInput (F := G) hF p tau htau ↔
      Blowdown.HasSamePoleNormalizedShrinkerInput (G := G) hF p tau htau :=
  Iff.rfl

end Bridge

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
