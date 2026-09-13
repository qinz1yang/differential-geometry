import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeMonotonicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Injectivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Minimizer.Domain

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace Set

theorem Icc_subset_iff_Ico_subset_and_mem {α : Type*} [LinearOrder α]
    {s : Set α} {a b : α} (hab : a ≤ b) :
    Icc a b ⊆ s ↔ Ico a b ⊆ s ∧ b ∈ s := by
  constructor
  · intro h
    exact ⟨fun x hx => h ⟨hx.1, hx.2.le⟩, h (right_mem_Icc.mpr hab)⟩
  · rintro ⟨h₁, h₂⟩ x hx
    rcases eq_or_lt_of_le hx.2 with hxb | hxb
    · simpa only [hxb] using h₂
    · exact h₁ ⟨hx.1, hxb⟩

end Set

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set Filter
open scoped Manifold ContDiff _root_.Topology ENNReal

section Obstruction

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem mem_regular_of_mem_lRegularizedDomain
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (Z : TangentSpace I x) {s : ℝ}
    (hs : s ∈ lRegularizedDomain S T x Z) : T ∈ D.regular := by
  obtain ⟨alpha, J, _hJopen, _hJconn, h0J, _hsJ, halpha⟩ := hs
  have h := (halpha.2.2 0 h0J).1
  simpa using h

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem zero_mem_lRegularizedDomain_iff_mem_regular
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M) (Z : TangentSpace I x) :
    (0 : ℝ) ∈ lRegularizedDomain S T x Z ↔ T ∈ D.regular :=
  ⟨fun h => mem_regular_of_mem_lRegularizedDomain S T x Z h,
    fun h => zero_mem_lRegularizedDomain S hS T x Z h⟩

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lExpPosDom_eq_empty_of_not_mem_regular
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M)
    (hT : T ∉ D.regular) : lExpPosDom S T x = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  exact hT (mem_regular_of_mem_lRegularizedDomain S T x p.1
    ((mem_lExpPosDom S T x p.1 p.2).1 hp).2.2)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lMinDomain_eq_empty_of_not_mem_regular
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M)
    (hT : T ∉ D.regular) : lMinDomain S T x = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  exact hT (mem_regular_of_mem_lRegularizedDomain S T x p.1
    ((mem_lExpPosDom S T x p.1 p.2).1
      ((mem_lMinDomain S T x p.1 p.2).1 hp).1).2.2)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lInjDomain_eq_empty_of_not_mem_regular
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M)
    (hT : T ∉ D.regular) (tau : ℝ) : lInjDomain S T x tau = ∅ := by
  ext Z
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hZ
  obtain ⟨sigma, _hsigma, hmin⟩ := hZ
  have hmem : (Z, sigma) ∈ lMinDomain S T x := hmin
  rw [lMinDomain_eq_empty_of_not_mem_regular S T x hT] at hmem
  exact Set.notMem_empty _ hmem

end Obstruction

section DegenerateCutLocus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem setLIntegral_lInjDomain_eq_zero_of_not_mem_regular
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M) (tau : ℝ)
    (hT : T ∉ D.regular) :
    ∫⁻ Z in lInjDomain S T x tau,
        ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
        ∂DifferentialGeometry.Integral.Measure.modelHaar (E := E) = 0 := by
  rw [lInjDomain_eq_empty_of_not_mem_regular S T x hT tau]
  simp

end DegenerateCutLocus

section IcoBaseEq

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [CompactSpace M]

theorem redVolume_anti_Ico_of_base_eq_of_mem_regular
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (S' : SolutionOn (I := I) (M := M) D')
    (hbase : S'.base = S.base) (hS' : IsSolutionOn (I := I) S')
    (T : ℝ) (x : M) {tau₁ tau₂ : ℝ}
    (htau₁ : 0 < tau₁) (h12 : tau₁ ≤ tau₂) (hT : T ∈ D'.regular)
    (hslab : Set.Ico (T - tau₂) T ⊆ D'.regular) :
    DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume S T x tau₂ ≤
      DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume S T x tau₁ :=
  redVolume_anti_Ico_of_base_eq S S' hbase hS' T x htau₁ h12
    ((Set.Icc_subset_iff_Ico_subset_and_mem (by linarith only [htau₁, h12])).mpr
      ⟨hslab, hT⟩)

end IcoBaseEq

end DifferentialGeometry.PDE.RicciFlow.Perelman

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set Filter
open CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff _root_.Topology

section AncientTerminal

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientReducedVolumeTerminalTopology : TopologicalSpace F.M := F.topology
local instance ancientReducedVolumeTerminalCharted : ChartedSpace H F.M := F.charted
local instance ancientReducedVolumeTerminalSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientReducedVolumeTerminalC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
local instance ancientReducedVolumeTerminalT2 : T2Space F.M := F.t2
local instance ancientReducedVolumeTerminalTangentT2 : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle
local instance ancientReducedVolumeTerminalSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem ancientTimeInterval_terminal_lInjDomain_eq_empty (x : F.M) (tau : ℝ) :
    lInjDomain F.S 0 x tau = ∅ :=
  lInjDomain_eq_empty_of_not_mem_regular F.S 0 x
    not_ancientTimeInterval_zero_mem_regular tau

theorem exists_Ico_ancientTimeInterval_regular_not_Icc (tau : ℝ) (htau : 0 < tau) :
    Set.Ico ((0 : ℝ) - tau) 0 ⊆ ancientTimeInterval.regular ∧
      ¬ (Set.Icc ((0 : ℝ) - tau) 0 ⊆ ancientTimeInterval.regular) ∧
      (0 : ℝ) ∈ ancientTimeInterval.carrier := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    simpa only [ancientTimeInterval_regular, Set.mem_Iio] using ht.2
  · exact not_Icc_subset_ancientTimeInterval_regular
      not_ancientTimeInterval_zero_mem_regular htau.le
  · simpa only [ancientTimeInterval_carrier, Set.mem_Iic] using le_rfl

theorem ancient_reducedVolume_antitone_of_baseTime_continuity
    [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (hcont : ∀ tau ∈ Set.Ioi 0,
      Tendsto (fun T : ℝ => intrinsicReducedVolume F.S T p tau)
        (𝓝[<] (0 : ℝ)) (𝓝 (intrinsicReducedVolume F.S 0 p tau))) :
    AntitoneOn (intrinsicReducedVolume F.S 0 p) (Set.Ioi 0) := by
  intro tau₁ h₁ tau₂ h₂ h₁₂
  have hreg : ∀ T : ℝ, T < 0 →
      intrinsicReducedVolume F.S T p tau₂ ≤
        intrinsicReducedVolume F.S T p tau₁ := by
    intro T hT
    have hanti := ancient_reducedVolume_antitone_of_regular_base F hF p (T := T)
      (by simpa only [ancientTimeInterval_regular, Set.mem_Iio] using hT)
    exact hanti h₁ h₂ h₁₂
  exact le_of_tendsto_of_tendsto (hcont tau₂ h₂) (hcont tau₁ h₁)
    (Filter.mem_of_superset self_mem_nhdsWithin fun T hT => hreg T hT)

end AncientTerminal

section MetricConstant

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

theorem intrinsicReducedVolume_eq_of_metric_eq_const
    (S : SolutionOn (I := I) (M := M) D) (g : SmoothRiemannianMetric I M)
    (hS : S.base.metric = fun _ => g) (T : ℝ) (p : M) (tau : ℝ) :
    intrinsicReducedVolume S T p tau = intrinsicReducedVolume S 0 p tau := by
  simp only [intrinsicReducedVolume, lCost, lLength, lDensity, lSpeedSq,
    SolutionOn.scalar, SolutionFamily.scalar, hS]

theorem tendsto_intrinsicReducedVolume_of_metric_eq_const
    (S : SolutionOn (I := I) (M := M) D) (g : SmoothRiemannianMetric I M)
    (hS : S.base.metric = fun _ => g) (p : M) (tau : ℝ) :
    Tendsto (fun T : ℝ => intrinsicReducedVolume S T p tau) (𝓝[<] (0 : ℝ))
      (𝓝 (intrinsicReducedVolume S 0 p tau)) := by
  have hfun : (fun T : ℝ => intrinsicReducedVolume S T p tau) =
      fun _ : ℝ => intrinsicReducedVolume S 0 p tau :=
    funext fun T => intrinsicReducedVolume_eq_of_metric_eq_const S g hS T p tau
  rw [hfun]
  exact tendsto_const_nhds

end MetricConstant

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
