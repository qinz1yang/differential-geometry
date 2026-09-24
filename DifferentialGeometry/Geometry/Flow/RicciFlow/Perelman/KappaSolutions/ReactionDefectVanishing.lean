import DifferentialGeometry.Analysis.TimeInterval
import DifferentialGeometry.Geometry.Curvature.DimensionThree.Algebra.Pinching
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.NullSectionalRicciReactionRank
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureKernel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalRankKernelFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkerAsymptoticFrontierReduction

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

theorem curvatureReactionSumSquares3_eq_zero_iff_of_const_or_two_zero
    (lambda mu nu : ℝ) :
    curvatureReactionSumSquares3 lambda mu nu = 0 ↔
      (lambda = mu ∧ mu = nu) ∨
        (lambda = 0 ∧ mu = 0) ∨ (lambda = 0 ∧ nu = 0) ∨ (mu = 0 ∧ nu = 0) := by
  unfold curvatureReactionSumSquares3
  constructor
  · intro h
    have hsum : lambda ^ 2 * (mu - nu) ^ 2 + mu ^ 2 * (lambda - nu) ^ 2 +
        nu ^ 2 * (lambda - mu) ^ 2 = 0 := by linarith
    have h12 : lambda * (mu - nu) = 0 := by
      have hterm : lambda ^ 2 * (mu - nu) ^ 2 = 0 := by
        nlinarith [sq_nonneg (mu * (lambda - nu)), sq_nonneg (nu * (lambda - mu))]
      have hself : (lambda * (mu - nu)) * (lambda * (mu - nu)) = 0 := by nlinarith
      exact mul_self_eq_zero.mp hself
    have h23 : mu * (lambda - nu) = 0 := by
      have hterm : mu ^ 2 * (lambda - nu) ^ 2 = 0 := by
        nlinarith [sq_nonneg (lambda * (mu - nu)), sq_nonneg (nu * (lambda - mu))]
      have hself : (mu * (lambda - nu)) * (mu * (lambda - nu)) = 0 := by nlinarith
      exact mul_self_eq_zero.mp hself
    have h31 : nu * (lambda - mu) = 0 := by
      have hterm : nu ^ 2 * (lambda - mu) ^ 2 = 0 := by
        nlinarith [sq_nonneg (lambda * (mu - nu)), sq_nonneg (mu * (lambda - nu))]
      have hself : (nu * (lambda - mu)) * (nu * (lambda - mu)) = 0 := by nlinarith
      exact mul_self_eq_zero.mp hself
    have h1 : lambda = 0 ∨ mu = nu := by
      rcases mul_eq_zero.mp h12 with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.mp h)
    have h2 : mu = 0 ∨ lambda = nu := by
      rcases mul_eq_zero.mp h23 with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.mp h)
    have h3 : nu = 0 ∨ lambda = mu := by
      rcases mul_eq_zero.mp h31 with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.mp h)
    rcases h1 with hlam | hmunu
    · rcases h3 with hnu | hlamu
      · exact Or.inr (Or.inr (Or.inl ⟨hlam, hnu⟩))
      · exact Or.inr (Or.inl ⟨hlam, by linarith⟩)
    · rcases h2 with hmu | hlamnu
      · rcases h3 with hnu | hlamu
        · exact Or.inr (Or.inr (Or.inr ⟨hmu, hnu⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨hmu, by linarith⟩))
      · exact Or.inl ⟨by linarith, hmunu⟩
  · rintro (⟨hlm, hmn⟩ | ⟨hl, hm⟩ | ⟨hl, hn⟩ | ⟨hm, hn⟩)
    · subst hlm
      subst hmn
      ring
    · subst hl
      subst hm
      ring
    · subst hl
      subst hn
      ring
    · subst hm
      subst hn
      ring

theorem curvatureReactionSumSquares3_one_zero_zero :
    curvatureReactionSumSquares3 1 0 0 = 0 := by
  norm_num [curvatureReactionSumSquares3]

theorem curvatureReactionSumSquares3_one_one_zero :
    curvatureReactionSumSquares3 1 1 0 = 1 / 4 := by
  norm_num [curvatureReactionSumSquares3]

theorem curvatureReactionSumSquares3_three_two_one :
    curvatureReactionSumSquares3 3 2 1 = 13 / 4 := by
  norm_num [curvatureReactionSumSquares3]

theorem exists_nonnegative_curvatureEigenvalues_defect_zero_not_einstein :
    ∃ lambda mu nu : ℝ, 0 ≤ lambda ∧ 0 ≤ mu ∧ 0 ≤ nu ∧
      curvatureReactionSumSquares3 lambda mu nu = 0 ∧ ¬ (lambda = mu ∧ mu = nu) :=
  ⟨1, 0, 0, by norm_num, by norm_num, by norm_num,
    curvatureReactionSumSquares3_one_zero_zero, by norm_num⟩

theorem exists_nonnegative_curvatureEigenvalues_defect_ne_zero :
    ∃ lambda mu nu : ℝ, 0 ≤ lambda ∧ 0 ≤ mu ∧ 0 ≤ nu ∧
      curvatureReactionSumSquares3 lambda mu nu ≠ 0 :=
  ⟨1, 1, 0, by norm_num, by norm_num, by norm_num, by
    rw [curvatureReactionSumSquares3_one_one_zero]
    norm_num⟩

end DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff

section SliceKernel

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance reactionDefectVanishingTopology : TopologicalSpace F.M := F.topology
local instance reactionDefectVanishingCharted : ChartedSpace H F.M := F.charted
local instance reactionDefectVanishingSmooth : IsManifold I ∞ F.M := F.smooth
local instance reactionDefectVanishingC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance reactionDefectVanishingC2 : IsManifold I 2 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance reactionDefectVanishingT2 : T2Space F.M := F.t2
local instance reactionDefectVanishingSigma : SigmaCompactSpace F.M := F.sigmaCompact

noncomputable abbrev terminalSliceCurvatureKernelAt (t : ℝ) (x : F.M) :
    Submodule ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) :=
  curvatureOperatorKernelAt (I := I) (F.S.family.metric t) x
    ⟨metricRm04At (I := I) (F.S.family.metric t) x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (F.S.family.metric t) x⟩

omit [I.Boundaryless] in
theorem terminalSliceCurvatureKernelAt_zero (x : F.M) :
    terminalSliceCurvatureKernelAt (I := I) F 0 x = terminalCurvatureKernelAt (I := I) F x :=
  rfl

theorem not_le_zero_and_zero_mem_Ioo {a b : ℝ} :
    ¬ (b ≤ 0 ∧ (0 : ℝ) ∈ Set.Ioo a b) := by
  rintro ⟨hb, h0⟩
  exact absurd h0.2 (not_lt.mpr hb)

theorem not_exists_pastWindow_containing_zero :
    ¬ ∃ a b : ℝ, b ≤ 0 ∧ (0 : ℝ) ∈ Set.Ioo a b := by
  rintro ⟨a, b, hb, h0⟩
  exact absurd h0.2 (not_lt.mpr hb)

omit [I.Boundaryless] in
theorem not_exists_pastWindow_containing_zero_of_kLim {kappa : ℝ}
    (hK : KLim (I := I) kappa F) :
    ¬ ∃ a b : ℝ, b ≤ 0 ∧ Set.Ioo a b ⊆ D.regular ∧ (0 : ℝ) ∈ Set.Ioo a b := by
  rintro ⟨a, b, _hb, hreg, h0⟩
  have hmem : (0 : ℝ) ∈ Set.Iio (0 : ℝ) := by
    simpa only [hK.regular_eq] using hreg h0
  exact lt_irrefl 0 (Set.mem_Iio.mp hmem)

theorem exists_regular_window_containing_zero :
    ∃ (D : RealTimeInterval) (a b : ℝ), Set.Ioo a b ⊆ D.regular ∧ (0 : ℝ) ∈ Set.Ioo a b := by
  refine ⟨{ carrier := Set.univ
            regular := Set.univ
            initial := 0
            initial_mem := trivial
            regular_subset := fun _ _ => trivial
            regular_isOpen := isOpen_univ
            regular_mem_nhds := fun {_} _ => Filter.univ_mem },
    -1, 1, fun _ _ => trivial, ⟨by norm_num, by norm_num⟩⟩

theorem terminalSliceCurvatureKernelAt_parallel_of_sliceConstantRank_of_past
    {kappa : ℝ} (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    {a b t : ℝ} (hb : b ≤ 0) (hreg : Set.Ioo a b ⊆ D.regular) (ht : t ∈ Set.Ioo a b)
    (q : ℕ)
    (hrank : ∀ r ∈ Set.Ioo a b, ∀ x : F.M, terminalSliceCurvatureRankAt (I := I) F r x = q) :
    IsParallelContinuousAlternatingSubmoduleFamily (F.S.family.metric t)
      (fun x => terminalSliceCurvatureKernelAt (I := I) F t x) := by
  have hR : ∀ r ∈ Set.Ioo a b, ∀ x : F.M,
      (⟨metricRm04At (I := I) (F.S.base.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (F.S.base.metric r) x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := F.M) x) ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    intro r hr x
    have hrc : r ∈ D.carrier := by
      simpa only [hK.carrier_eq, Set.mem_Iic] using le_trans (le_of_lt hr.2) hb
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    have h := hK.nonnegativeCurvatureOperator r hrc x n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
      tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using h
  have hR' : ∀ r ∈ Set.Ioo a b, ∀ x : F.M,
      (⟨metricRm04At (I := I) (F.S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (F.S.family.metric r) x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := F.M) x) ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    intro r hr x
    rw [SolutionOn.family_metric F.S]
    exact hR r hr x
  exact DifferentialGeometry.PDE.RicciFlow.curvatureOperatorKernelAt_parallel_of_constant_rank
    (I := I) (M := F.M) F.S F.isSolution hdim (t := t) ht hreg hR' q
    (fun r hr x => hrank r hr x)

theorem terminalCurvatureKernelAt_parallel_of_sliceConstantRank_of_mem
    (hdim : Module.finrank ℝ E = 3)
    {a b : ℝ} (hreg : Set.Ioo a b ⊆ D.regular) (h0 : (0 : ℝ) ∈ Set.Ioo a b) (q : ℕ)
    (hR : ∀ r ∈ Set.Ioo a b, ∀ x : F.M,
      (⟨metricRm04At (I := I) (F.S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (F.S.family.metric r) x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := F.M) x) ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M))
    (hrank : ∀ r ∈ Set.Ioo a b, ∀ x : F.M,
      terminalSliceCurvatureRankAt (I := I) F r x = q) :
    IsParallelContinuousAlternatingSubmoduleFamily (F.S.base.metric 0)
      (fun x => terminalCurvatureKernelAt (I := I) F x) :=
  DifferentialGeometry.PDE.RicciFlow.curvatureOperatorKernelAt_parallel_of_constant_rank
    (I := I) (M := F.M) F.S F.isSolution hdim (t := 0) h0 hreg hR q
    (fun r hr x => hrank r hr x)

end SliceKernel

section DefectCompression

universe u₂ uE₂ uH₂

variable {E : Type uE₂} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH₂} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u₂, uE₂, uH₂} (I := I) D)

local instance reactionDefectCompressionTopology : TopologicalSpace F.M := F.topology
local instance reactionDefectCompressionCharted : ChartedSpace H F.M := F.charted
local instance reactionDefectCompressionSmooth : IsManifold I ∞ F.M := F.smooth
local instance reactionDefectCompressionC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance reactionDefectCompressionC2 : IsManifold I 2 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance reactionDefectCompressionT2 : T2Space F.M := F.t2
local instance reactionDefectCompressionSigma : SigmaCompactSpace F.M := F.sigmaCompact

local instance reactionDefectCompressionInhabited : Inhabited F.M := ⟨F.basepoint⟩

local instance reactionDefectCompressionLocallyPathConnected : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M

local instance reactionDefectCompressionSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

def NullPlaneReactionDefectVanishing (F : PointedFlowData.{u₂, uE₂, uH₂} (I := I) D) : Prop :=
  ∀ x : F.M, ∀ a b : TangentSpace I x,
    0 < (F.S.base.metric 0).inner x a a * (F.S.base.metric 0).inner x b b -
        ((F.S.base.metric 0).inner x a b) ^ 2 →
      metricRm04StandardAt (I := I) (M := F.M) (F.S.base.metric 0) x a b b a = 0 →
        ricciReactionDefectAt (I := I) (F.S.base.metric 0) x = 0

theorem nullPlaneReactionDefectVanishing_of_terminalReactionDefectVanishing
    (h : TerminalReactionDefectVanishing (I := I) F) :
    NullPlaneReactionDefectVanishing (I := I) F :=
  fun x _ _ _ _ => h x

theorem terminalCurvatureRankAt_ne_two_of_null_plane_of_ricciReactionDefectAt_eq_zero
    (hdim : Module.finrank ℝ E = 3)
    {x : F.M} {a b : TangentSpace I x}
    (hcone : metricAlgebraicCurvatureTensorAt (I := I) (M := F.M) (F.S.base.metric 0) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M))
    (hdefect : ricciReactionDefectAt (I := I) (F.S.base.metric 0) x = 0)
    (hgram : 0 < (F.S.base.metric 0).inner x a a * (F.S.base.metric 0).inner x b b -
        ((F.S.base.metric 0).inner x a b) ^ 2)
    (hsec : metricRm04StandardAt (I := I) (M := F.M) (F.S.base.metric 0) x a b b a = 0) :
    terminalCurvatureRankAt (I := I) F x ≠ 2 := by
  have hdimx : Module.finrank ℝ (TangentSpace I x) = 3 :=
    (show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from rfl).trans hdim
  have hsub : (⟨metricRm04At (I := I) (F.S.base.metric 0) x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (F.S.base.metric 0) x⟩ :
      algebraicCurvatureTensorSubmodule (I := I) (M := F.M) x) =
      ⟨metricRm04 (I := I) (F.S.base.metric 0) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (F.S.base.metric 0) x⟩ :=
    Subtype.ext (metricRm04_apply (I := I) (M := F.M) (F.S.base.metric 0) x).symm
  have hne :=
    finrank_curvatureOperatorImageAt_ne_two_of_null_sectional_of_ricciReactionDefect_eq_zero
      (I := I) (M := F.M) (F.S.base.metric 0) x hdimx hcone hdefect hgram hsec
  intro htwo
  refine hne ?_
  rw [← hsub]
  exact htwo

theorem terminalCurvatureRankAt_ne_two_of_nullPlaneReactionDefectVanishing
    (hdim : Module.finrank ℝ E = 3)
    (hcone : ∀ x : F.M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := F.M) (F.S.base.metric 0) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M))
    (hvan : NullPlaneReactionDefectVanishing (I := I) F)
    {x : F.M} {a b : TangentSpace I x}
    (hgram : 0 < (F.S.base.metric 0).inner x a a * (F.S.base.metric 0).inner x b b -
        ((F.S.base.metric 0).inner x a b) ^ 2)
    (hsec : metricRm04StandardAt (I := I) (M := F.M) (F.S.base.metric 0) x a b b a = 0) :
    terminalCurvatureRankAt (I := I) F x ≠ 2 :=
  terminalCurvatureRankAt_ne_two_of_null_plane_of_ricciReactionDefectAt_eq_zero
    (I := I) F hdim (hcone x) (hvan x a b hgram hsec) hgram hsec

theorem terminalCurvatureRankAt_eq_zero_or_one_of_null_plane_of_ricciReactionDefectAt_eq_zero
    (hdim : Module.finrank ℝ E = 3)
    {x : F.M} {a b : TangentSpace I x}
    (hcone : metricAlgebraicCurvatureTensorAt (I := I) (M := F.M) (F.S.base.metric 0) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M))
    (hdefect : ricciReactionDefectAt (I := I) (F.S.base.metric 0) x = 0)
    (hgram : 0 < (F.S.base.metric 0).inner x a a * (F.S.base.metric 0).inner x b b -
        ((F.S.base.metric 0).inner x a b) ^ 2)
    (hsec : metricRm04StandardAt (I := I) (M := F.M) (F.S.base.metric 0) x a b b a = 0) :
    terminalCurvatureRankAt (I := I) F x = 0 ∨ terminalCurvatureRankAt (I := I) F x = 1 := by
  have hdimx : Module.finrank ℝ (TangentSpace I x) = 3 :=
    (show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from rfl).trans hdim
  have h := metricCurvatureOperatorRankAt_eq_zero_or_one_of_null_sectional
    (I := I) (M := F.M) (F.S.base.metric 0) x hdimx hcone hdefect hgram hsec
  rw [metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank
    (I := I) (M := F.M) (F.S.base.metric 0) x hdimx] at h
  simpa only [terminalCurvatureRankAt, terminalCurvatureImageAt] using h

theorem terminalNullPlaneSplitting_of_constantRank_of_nullPlaneReactionDefectVanishing
    {kappa : ℝ} (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hG3 : ∃ q : ℕ, ∀ x : F.M, terminalCurvatureRankAt (I := I) F x = q)
    (hvan : NullPlaneReactionDefectVanishing (I := I) F)
    (hsplit : ∀ q : ℕ, (∀ x : F.M, terminalCurvatureRankAt (I := I) F x = q) → q = 1 →
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0))) :
    TerminalNullPlaneSplitting (I := I) F := by
  intro x a b hgram hnull
  obtain ⟨q, hq⟩ := hG3
  have hcone := terminalCurvatureTensorAt_mem_nonnegativeCone (I := I) F hK
  rcases terminalCurvatureRankAt_eq_zero_or_one_of_null_plane_of_ricciReactionDefectAt_eq_zero
      (I := I) F hdim (hcone x) (hvan x a b hgram hnull) hgram hnull with h0 | h1
  · refine Or.inl fun y => ?_
    have hqx : q = 0 := (hq x).symm.trans h0
    exact rmNormSq_eq_zero_of_terminalCurvatureRankAt_eq_zero
      (I := I) F hdim y ((hq y).trans hqx)
  · exact Or.inr (hsplit q hq ((hq x).symm.trans h1))

theorem klim_terminal_curvature_trichotomy_of_constantRank_of_nullPlaneReactionDefectVanishing
    {kappa : ℝ} (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hG3 : ∃ q : ℕ, ∀ x : F.M, terminalCurvatureRankAt (I := I) F x = q)
    (hvan : NullPlaneReactionDefectVanishing (I := I) F)
    (hsplit : ∀ q : ℕ, (∀ x : F.M, terminalCurvatureRankAt (I := I) F x = q) → q = 1 →
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0))) :
    DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) (F.S.base.metric 0) ∨
      (∀ x : F.M, F.rmNormSq (I := I) 0 x = 0) ∨
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) :=
  klim_terminal_curvature_trichotomy_of_nullPlaneSplitting F
    (terminalNullPlaneSplitting_of_constantRank_of_nullPlaneReactionDefectVanishing
      (I := I) F hK hdim hG3 hvan hsplit) hK hdim

end DefectCompression

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
