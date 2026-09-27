import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeTerminal

set_option autoImplicit false
noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance terminalReductionTopology : TopologicalSpace F.M := F.topology
local instance terminalReductionCharted : ChartedSpace H F.M := F.charted
local instance terminalReductionSmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalReductionC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
local instance terminalReductionT2 : T2Space F.M := F.t2
local instance terminalReductionTangentT2 : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle
local instance terminalReductionSigma : SigmaCompactSpace F.M := F.sigmaCompact

omit [I.Boundaryless] in
private theorem exists_terminal_rmNormSq_le
    {kappa C : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hC : PointedFlowScalarBounded (I := I) F C)
    {a b : ℝ} (hb : b ≤ 0) :
    ∃ K : ℝ, ∀ t ∈ Set.Icc a b, ∀ z : F.M,
      normSq0S (I := I) (F.S.base.metric t) z 4 (F.S.base.rm04 t z) ≤ K := by
  refine ⟨((Module.finrank ℝ E : ℝ) ^ 2 * C) ^ 2, ?_⟩
  intro t ht z
  have htc : t ∈ ancientTimeInterval.carrier := by
    rw [ancientTimeInterval_carrier]
    exact ht.2.trans hb
  have hnonnegC : 0 ≤ C := (hC t htc z).1.trans (hC t htc z).2
  have hop : metricAlgebraicCurvatureTensorAt (I := I) (M := F.M) (F.S.base.metric t) z ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (F.S.base.metric t) z).mpr
    intro n c a b
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      hF.nonnegativeCurvatureOperator t htc z n c a b
  have hsqrt := sqrt_metricRm_normSq_le_finrank_sq_mul_scalar (I := I) (F.S.base.metric t) z hop
  have hscalar : metricScalarAt (I := I) (F.S.base.metric t) z ≤ C := (hC t htc z).2
  have hn2 : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 := sq_nonneg _
  have hs := hsqrt.trans (mul_le_mul_of_nonneg_left hscalar hn2)
  exact (Real.sqrt_le_left (mul_nonneg hn2 hnonnegC)).mp hs

theorem redVolume_anti_terminal_of_slab_extension
    [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (D' : RealTimeInterval) (hzero : (0 : ℝ) ∈ D'.regular)
    (S' : SolutionOn (I := I) (M := F.M) D')
    (hbase : S'.base = F.S.base) (hS' : IsSolutionOn (I := I) S')
    {tau₁ tau₂ : ℝ} (htau₁ : 0 < tau₁) (h₁₂ : tau₁ ≤ tau₂)
    (hslab : Set.Ico ((0 : ℝ) - tau₂) 0 ⊆ D'.regular) :
    DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume F.S 0 p tau₂ ≤
      DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume F.S 0 p tau₁ := by
  let _ : ConnectedSpace F.M := hF.connected
  let : TopologicalSpace.MetrizableSpace F.M :=
    Manifold.metrizableSpace I F.M
  let : PseudoMetricSpace F.M :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  have h0 : (0 : ℝ) ∈ ancientTimeInterval.carrier := by
    change (0 : ℝ) ≤ 0
    exact le_rfl
  have hcomplete : RiemannianMetricComplete (I := I) (F.S.base.metric 0) :=
    ⟨hF.complete 0 h0⟩
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  have htau₂ : 0 < tau₂ := htau₁.trans_le h₁₂
  have htau₂_nonneg : 0 ≤ tau₂ := le_of_lt htau₂
  have hslabIcc : Set.Icc ((0 : ℝ) - tau₂) 0 ⊆ D'.regular :=
    (Set.Icc_subset_iff_Ico_subset_and_mem (sub_nonpos.mpr htau₂_nonneg)).mpr
      ⟨hslab, hzero⟩
  exact DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_anti_of_rm_Ico_of_base_eq
    (I := I) (M := F.M) (D := ancientTimeInterval) (D' := D')
    F.S S' hbase hS' 0 p hcomplete
    (fun sigma _ _ => exists_terminal_rmNormSq_le F hF hC le_rfl)
    htau₁ h₁₂ hslabIcc

theorem ancient_reducedVolume_antitone_of_terminal_slab_extension
    [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (D' : RealTimeInterval) (hzero : (0 : ℝ) ∈ D'.regular)
    (hslab : ∀ {tau₂ : ℝ}, 0 < tau₂ → Set.Ico ((0 : ℝ) - tau₂) 0 ⊆ D'.regular)
    (S' : SolutionOn (I := I) (M := F.M) D')
    (hbase : S'.base = F.S.base) (hS' : IsSolutionOn (I := I) S') :
    AntitoneOn (intrinsicReducedVolume F.S 0 p) (Set.Ioi 0) := by
  intro tau₁ h₁ tau₂ h₂ h₁₂
  exact redVolume_anti_terminal_of_slab_extension F hF p D' hzero S' hbase hS'
    h₁ h₁₂ (hslab h₂)

theorem ancient_reducedVolume_antitone_of_exists_terminal_slab_extension
    [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (hext : ∃ (D' : RealTimeInterval) (S' : SolutionOn (I := I) (M := F.M) D'),
      (0 : ℝ) ∈ D'.regular ∧
      (∀ {tau₂ : ℝ}, 0 < tau₂ → Set.Ico ((0 : ℝ) - tau₂) 0 ⊆ D'.regular) ∧
      S'.base = F.S.base ∧ IsSolutionOn (I := I) S') :
    AntitoneOn (intrinsicReducedVolume F.S 0 p) (Set.Ioi 0) := by
  obtain ⟨D', S', hzero, hslab, hbase, hS'⟩ := hext
  exact ancient_reducedVolume_antitone_of_terminal_slab_extension F hF p D' hzero hslab S' hbase hS'

omit [I.Boundaryless] in
theorem infiniteOpen_terminal_slab_regular (b : ℝ) (hb : 0 < b) :
    (0 : ℝ) ∈ (RealTimeInterval.infiniteOpen b 0 hb).regular ∧
      ∀ {tau₂ : ℝ}, 0 < tau₂ →
        Set.Ico ((0 : ℝ) - tau₂) 0 ⊆ (RealTimeInterval.infiniteOpen b 0 hb).regular := by
  refine ⟨hb, ?_⟩
  intro tau₂ htau₂ t ht
  exact ht.2.trans hb

theorem ancient_reducedVolume_antitone_of_metric_eq_const
    [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    (g : SmoothRiemannianMetric I F.M) (hconst : F.S.base.metric = fun _ => g) :
    AntitoneOn (intrinsicReducedVolume F.S 0 p) (Set.Ioi 0) := by
  let : TopologicalSpace.MetrizableSpace F.M :=
    Manifold.metrizableSpace I F.M
  let : PseudoMetricSpace F.M :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  exact ancient_reducedVolume_antitone_of_baseTime_continuity F hF p
    (fun tau _ => tendsto_intrinsicReducedVolume_of_metric_eq_const F.S g hconst p tau)

omit [I.Boundaryless] in
theorem contDiffAt_zero_of_terminal_extension
    (D' : RealTimeInterval) (hcover : Set.Iic (0 : ℝ) ⊆ D'.regular)
    (S' : SolutionOn (I := I) (M := F.M) D')
    (hbase : S'.base = F.S.base) (hS' : IsSolutionOn (I := I) S')
    (x : F.M) (v w : TangentSpace I x) :
    ContDiffAt ℝ ∞ (fun t : ℝ => (F.S.base.metric t).inner x v w) 0 := by
  have hzero : (0 : ℝ) ∈ D'.regular := hcover (by simp)
  have hcoeff := (hS'.smoothMetric.coeff x v w).contDiffAt
    (D'.regular_isOpen.mem_nhds hzero)
  simpa only [SolutionOn.family_metric, hbase] using hcoeff

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
