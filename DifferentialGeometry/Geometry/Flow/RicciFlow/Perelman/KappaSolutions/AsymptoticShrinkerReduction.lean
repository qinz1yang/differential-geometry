import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinkerBlowdown
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinkerNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeTerminalSemicontinuity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section General

variable {D : RealTimeInterval} (G : PointedFlowData.{u, uE, uH} (I := I) D)

local instance reductionGeneralTopology : TopologicalSpace G.M := G.topology
local instance reductionGeneralCharted : ChartedSpace H G.M := G.charted
local instance reductionGeneralSmooth : IsManifold I ∞ G.M := G.smooth
local instance reductionGeneralT2 : T2Space G.M := G.t2
local instance reductionGeneralSigma : SigmaCompactSpace G.M := G.sigmaCompact

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

end General

section Ancient

variable (G : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance reductionAncientTopology : TopologicalSpace G.M := G.topology
local instance reductionAncientCharted : ChartedSpace H G.M := G.charted
local instance reductionAncientSmooth : IsManifold I ∞ G.M := G.smooth
local instance reductionAncientT2 : T2Space G.M := G.t2
local instance reductionAncientSigma : SigmaCompactSpace G.M := G.sigmaCompact

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

def TerminalReducedVolumeSemicontinuityInput (p : G.M) : Prop :=
  TerminalReducedVolumeLowerSemicontinuous G p ∧
    TerminalReducedVolumeUpperSemicontinuous G p

theorem ancient_reducedVolume_antitone_of_terminalInput
    [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa G) (p : G.M)
    (h : TerminalReducedVolumeSemicontinuityInput (G := G) p) :
    AntitoneOn (intrinsicReducedVolume G.S 0 p) (Ioi 0) :=
  ancient_reducedVolume_antitone_of_terminal_semicontinuity G hF p h.1 h.2

omit [I.Boundaryless] in
theorem terminalReducedVolumeSemicontinuityInput_of_metric_eq_const
    (p : G.M) (g : SmoothRiemannianMetric I G.M)
    (hconst : G.S.base.metric = fun _ => g) :
    TerminalReducedVolumeSemicontinuityInput (G := G) p :=
  ⟨terminalReducedVolume_lowerSemicontinuous_of_metric_eq_const G p g hconst,
    terminalReducedVolume_upperSemicontinuous_of_metric_eq_const G p g hconst⟩

end Ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
