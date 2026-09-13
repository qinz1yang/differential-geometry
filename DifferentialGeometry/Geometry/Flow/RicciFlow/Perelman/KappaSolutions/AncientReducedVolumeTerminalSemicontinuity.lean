import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeTerminalReduction

set_option autoImplicit false
noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance terminalSemicontinuityTopology : TopologicalSpace F.M := F.topology
local instance terminalSemicontinuityCharted : ChartedSpace H F.M := F.charted
local instance terminalSemicontinuitySmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalSemicontinuityC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
local instance terminalSemicontinuityT2 : T2Space F.M := F.t2
local instance terminalSemicontinuityTangentT2 : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle
local instance terminalSemicontinuitySigma : SigmaCompactSpace F.M := F.sigmaCompact

def TerminalReducedVolumeLowerSemicontinuous (p : F.M) : Prop :=
  ∀ tau ∈ Set.Ioi 0,
    intrinsicReducedVolume F.S 0 p tau ≤
      liminf (fun T : ℝ => intrinsicReducedVolume F.S T p tau) (𝓝[<] (0 : ℝ))

def TerminalReducedVolumeUpperSemicontinuous (p : F.M) : Prop :=
  ∀ tau ∈ Set.Ioi 0,
    limsup (fun T : ℝ => intrinsicReducedVolume F.S T p tau) (𝓝[<] (0 : ℝ)) ≤
      intrinsicReducedVolume F.S 0 p tau

theorem ancient_reducedVolume_antitone_of_terminal_semicontinuity
    [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (hlower : TerminalReducedVolumeLowerSemicontinuous F p)
    (hupper : TerminalReducedVolumeUpperSemicontinuous F p) :
    AntitoneOn (intrinsicReducedVolume F.S 0 p) (Set.Ioi 0) := by
  intro tau₁ h₁ tau₂ h₂ h₁₂
  have hregular : ∀ᶠ T in 𝓝[<] (0 : ℝ), T ∈ ancientTimeInterval.regular := by
    filter_upwards [self_mem_nhdsWithin] with T hT
    simpa only [ancientTimeInterval_regular, Set.mem_Iio] using hT
  have hcompare : ∀ᶠ T in 𝓝[<] (0 : ℝ),
      intrinsicReducedVolume F.S T p tau₂ ≤ intrinsicReducedVolume F.S T p tau₁ := by
    filter_upwards [hregular] with T hT
    exact (ancient_reducedVolume_antitone_of_regular_base F hF p hT) h₁ h₂ h₁₂
  have hliminf := Filter.liminf_le_liminf hcompare
  have hliminf_limsup := Filter.liminf_le_limsup (f := 𝓝[<] (0 : ℝ))
    (u := fun T : ℝ => intrinsicReducedVolume F.S T p tau₁)
  exact (hlower tau₂ h₂).trans
    (hliminf.trans (hliminf_limsup.trans (hupper tau₁ h₁)))

omit [I.Boundaryless] in
theorem terminalReducedVolume_lowerSemicontinuous_of_metric_eq_const
    (p : F.M)
    (g : SmoothRiemannianMetric I F.M) (hconst : F.S.base.metric = fun _ => g) :
    TerminalReducedVolumeLowerSemicontinuous F p := by
  let : TopologicalSpace.MetrizableSpace F.M :=
    Manifold.metrizableSpace I F.M
  let : PseudoMetricSpace F.M :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  intro tau htau
  have htend := tendsto_intrinsicReducedVolume_of_metric_eq_const F.S g hconst p tau
  rw [htend.liminf_eq]

omit [I.Boundaryless] in
theorem terminalReducedVolume_upperSemicontinuous_of_metric_eq_const
    (p : F.M)
    (g : SmoothRiemannianMetric I F.M) (hconst : F.S.base.metric = fun _ => g) :
    TerminalReducedVolumeUpperSemicontinuous F p := by
  let : TopologicalSpace.MetrizableSpace F.M :=
    Manifold.metrizableSpace I F.M
  let : PseudoMetricSpace F.M :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  intro tau htau
  have htend := tendsto_intrinsicReducedVolume_of_metric_eq_const F.S g hconst p tau
  rw [htend.limsup_eq]

omit [I.Boundaryless] in
theorem not_exists_terminal_extension_of_not_contDiffAt_zero
    (x : F.M) (v w : TangentSpace I x)
    (hbad : ¬ ContDiffAt ℝ ∞ (fun t : ℝ => (F.S.base.metric t).inner x v w) 0) :
    ¬ ∃ (D' : RealTimeInterval) (S' : SolutionOn (I := I) (M := F.M) D'),
      Set.Iic (0 : ℝ) ⊆ D'.regular ∧ S'.base = F.S.base ∧ IsSolutionOn (I := I) S' := by
  rintro ⟨D', S', hcover, hbase, hS'⟩
  exact hbad (contDiffAt_zero_of_terminal_extension F D' hcover S' hbase hS' x v w)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
