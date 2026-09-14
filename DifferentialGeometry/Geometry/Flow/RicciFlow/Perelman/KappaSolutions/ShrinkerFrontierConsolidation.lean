import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinkerReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkerMassClassificationReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NoncompactShrinkerMassClassification

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

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section MassClassification

variable (L : PointedRiemannianManifold.{u, uE, uH} (I := I))

local instance consolidationMassTopology : TopologicalSpace L.M := L.topology
local instance consolidationMassCharted : ChartedSpace H L.M := L.charted
local instance consolidationMassSmooth : IsManifold I ∞ L.M := L.smooth
local instance consolidationMassT2 : T2Space L.M := L.t2
local instance consolidationMassSigma : SigmaCompactSpace L.M := L.sigmaCompact

theorem shrinkerMassClassification_round_or_mass
    (hdim : Module.finrank ℝ E = 3) (hcomplete : MetricComplete (I := I) L)
    (hconnected : ConnectedSpace L.M)
    (hnonflat : ∃ x : L.M, metricScalarAt L.metric x ≠ 0)
    (hnco : ∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x),
      0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j))
    (f : C^∞⟮I, L.M; ℝ⟯) (hsoliton : gradientRicciSoliton L.metric f 1)
    (hnormal : IsHamiltonNormalizedPotential L.metric f) :
    (CompactSpace L.M ∧ (∀ x : L.M, metricScalarAt L.metric x = (3 : ℝ) / 2) ∧
      ∀ x : L.M, ∀ v : TangentSpace I x,
        ricciTensor L.metric x v v = ((3 / 2 : ℝ) / 3) * L.metric.inner x v v) ∨
    normalizedShrinkerMass L.metric f = ENNReal.ofReal (2 * Real.exp (-1)) ∨
    normalizedShrinkerMass L.metric f = ENNReal.ofReal (Real.exp (-1)) :=
  normalized_nonflat_three_shrinker_classification L hdim hcomplete hconnected hnonflat
    hnco f hsoliton hnormal

end MassClassification

section AsymptoticGeneral

variable {D : RealTimeInterval} (G : PointedFlowData.{u, uE, uH} (I := I) D)

local instance consolidationGeneralTopology : TopologicalSpace G.M := G.topology
local instance consolidationGeneralCharted : ChartedSpace H G.M := G.charted
local instance consolidationGeneralSmooth : IsManifold I ∞ G.M := G.smooth
local instance consolidationGeneralT2 : T2Space G.M := G.t2
local instance consolidationGeneralSigma : SigmaCompactSpace G.M := G.sigmaCompact

def BackwardSliceReducedVolumeAntitoneFrontier (p : G.M) : Prop :=
  AntitoneOn (intrinsicReducedVolume G.S 0 p) (Ioi 0)

def BackwardSliceMetricCompactnessFrontier [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa G)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) : Prop :=
  ∃ q : ℕ → G.M, backwardSliceApproximateMetricCompactness (F := G) hF tau htau q

def BackwardSliceLimitRigidityFrontier
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (p : G.M) : Prop :=
  ∀ q : ℕ → G.M, backwardSliceLimitGradientShrinker (F := G) tau htau q p

theorem exists_backward_slice_asymptotic_shrinker_of_frontiers
    [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa G)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop)
    (p : G.M)
    (hmono : BackwardSliceReducedVolumeAntitoneFrontier (G := G) p)
    (hcompact : BackwardSliceMetricCompactnessFrontier (G := G) hF tau htau)
    (hrigid : BackwardSliceLimitRigidityFrontier (G := G) tau htau p) :
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
  exact exists_backward_slice_asymptotic_shrinker_of_input (G := G) hF hdim tau htau hescape
    ⟨q, p, hmono, hq, hrigid q⟩

end AsymptoticGeneral

section AsymptoticAncient

variable (G : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance consolidationAncientTopology : TopologicalSpace G.M := G.topology
local instance consolidationAncientCharted : ChartedSpace H G.M := G.charted
local instance consolidationAncientSmooth : IsManifold I ∞ G.M := G.smooth
local instance consolidationAncientT2 : T2Space G.M := G.t2
local instance consolidationAncientSigma : SigmaCompactSpace G.M := G.sigmaCompact

theorem ancientReducedVolume_antitone_of_terminalFrontier
    [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa G) (p : G.M)
    (h : TerminalReducedVolumeSemicontinuityInput (G := G) p) :
    AntitoneOn (intrinsicReducedVolume G.S 0 p) (Ioi 0) :=
  ancient_reducedVolume_antitone_of_terminalInput (G := G) hF p h

omit [I.Boundaryless] in
theorem ancientReducedVolumeTerminalFrontier_of_metric_eq_const
    [NeZero (Module.finrank ℝ E)]
    (p : G.M)
    (g : SmoothRiemannianMetric I G.M) (hconst : G.S.base.metric = fun _ => g) :
    TerminalReducedVolumeSemicontinuityInput (G := G) p :=
  terminalReducedVolumeSemicontinuityInput_of_metric_eq_const (G := G) p g hconst

theorem backwardSliceReducedVolumeAntitoneFrontier_of_metric_eq_const
    [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa G) (p : G.M)
    (g : SmoothRiemannianMetric I G.M) (hconst : G.S.base.metric = fun _ => g) :
    BackwardSliceReducedVolumeAntitoneFrontier (G := G) p :=
  ancient_reducedVolume_antitone_of_metric_eq_const (F := G) hF p g hconst

theorem exists_samePole_normalized_asymptotic_shrinker_of_components
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa G)
    (hdim : 2 ≤ Module.finrank ℝ E) (p : G.M)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop)
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
             atTop (𝓝 (normalizedShrinkerMass L.metric f))) :=
  exists_samePole_normalized_asymptotic_shrinker_of_data_and_mass (G := G) hF hdim p tau htau
    hescape hdata hmass

end AsymptoticAncient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
