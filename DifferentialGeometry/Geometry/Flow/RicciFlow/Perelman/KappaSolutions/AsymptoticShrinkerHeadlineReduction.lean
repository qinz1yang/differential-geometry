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

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section General

variable {D : RealTimeInterval} (G : PointedFlowData.{u, uE, uH} (I := I) D)

local instance headlineGeneralTopology : TopologicalSpace G.M := G.topology
local instance headlineGeneralCharted : ChartedSpace H G.M := G.charted
local instance headlineGeneralSmooth : IsManifold I ∞ G.M := G.smooth
local instance headlineGeneralT2 : T2Space G.M := G.t2
local instance headlineGeneralSigma : SigmaCompactSpace G.M := G.sigmaCompact

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
    (hdim : 2 ≤ Module.finrank ℝ E)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop)
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
  exact exists_backward_slice_asymptotic_shrinker_of_input (G := G) hF hdim tau htau hescape
    ⟨q, p, hmono, hq, hrigid q⟩

end General

section Ancient

variable (G : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance headlineAncientTopology : TopologicalSpace G.M := G.topology
local instance headlineAncientCharted : ChartedSpace H G.M := G.charted
local instance headlineAncientSmooth : IsManifold I ∞ G.M := G.smooth
local instance headlineAncientT2 : T2Space G.M := G.t2
local instance headlineAncientSigma : SigmaCompactSpace G.M := G.sigmaCompact

theorem backwardSliceReducedVolumeAntitoneInput_of_metric_eq_const
    [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa G) (p : G.M)
    (g : SmoothRiemannianMetric I G.M) (hconst : G.S.base.metric = fun _ => g) :
    BackwardSliceReducedVolumeAntitoneInput (G := G) p :=
  ancient_reducedVolume_antitone_of_metric_eq_const (F := G) hF p g hconst

end Ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
