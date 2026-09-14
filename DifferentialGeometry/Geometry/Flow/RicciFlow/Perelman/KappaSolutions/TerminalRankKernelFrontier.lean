import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalNullPlaneProduct
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureKernel
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankRigidity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorPositiveSectional
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorVanishing
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorRank
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ScalarPositivity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorEigenvalues
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.LeastEigenvalue
import DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance terminalRankFrontierTopology : TopologicalSpace F.M := F.topology
local instance terminalRankFrontierCharted : ChartedSpace H F.M := F.charted
local instance terminalRankFrontierSmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalRankFrontierC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance terminalRankFrontierT2 : T2Space F.M := F.t2
local instance terminalRankFrontierSigma : SigmaCompactSpace F.M := F.sigmaCompact


local instance terminalRankFrontierInhabited : Inhabited F.M := ⟨F.basepoint⟩


local instance terminalRankFrontierLocallyPathConnected : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M


local instance terminalRankFrontierSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)


noncomputable abbrev terminalCurvatureEndomorphismAt (x : F.M) :
    (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) :=
  curvatureOperatorEndomorphismAt (I := I) (F.S.base.metric 0) x
    ⟨metricRm04At (I := I) (F.S.base.metric 0) x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (F.S.base.metric 0) x⟩


noncomputable abbrev terminalCurvatureImageAt (x : F.M) :
    Submodule ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) :=
  curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x
    ⟨metricRm04At (I := I) (F.S.base.metric 0) x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (F.S.base.metric 0) x⟩


noncomputable abbrev terminalCurvatureKernelAt (x : F.M) :
    Submodule ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) :=
  curvatureOperatorKernelAt (I := I) (F.S.base.metric 0) x
    ⟨metricRm04At (I := I) (F.S.base.metric 0) x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (F.S.base.metric 0) x⟩


noncomputable abbrev terminalCurvatureRankAt (x : F.M) : ℕ :=
  Module.finrank ℝ (terminalCurvatureImageAt (I := I) F x)


noncomputable abbrev terminalSliceCurvatureRankAt (t : ℝ) (x : F.M) : ℕ :=
  Module.finrank ℝ (curvatureOperatorImageAt (I := I) (F.S.family.metric t) x
    ⟨metricRm04At (I := I) (F.S.family.metric t) x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (F.S.family.metric t) x⟩)


omit [I.Boundaryless] in
theorem terminalCurvatureRankAt_le_three (hdim : Module.finrank ℝ E = 3) (x : F.M) :
    terminalCurvatureRankAt (I := I) F x ≤ 3 := by
  have hfiber : Module.finrank ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) = 3 := by
    rw [ContinuousAlternatingMap.finrank_continuousAlternatingMap]
    have hfin : Module.finrank ℝ (TangentSpace I x) = 3 :=
      (show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from rfl).trans hdim
    rw [hfin]
    norm_num
  exact (Submodule.finrank_le (terminalCurvatureImageAt (I := I) F x)).trans_eq hfiber


omit [I.Boundaryless] in
theorem terminalCurvatureTensorAt_mem_nonnegativeCone {kappa : ℝ}
    (hK : KLim (I := I) kappa F) :
    ∀ x : F.M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := F.M) (F.S.base.metric 0) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
  intro x
  apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
  intro n c v w
  have h0 : (0 : ℝ) ∈ D.carrier := by
    simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)
  have h := hK.nonnegativeCurvatureOperator 0 h0 x n c v w
  simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
    tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using h


omit [I.Boundaryless] in
theorem terminalCurvatureKernelAnnihilation_of_rank_ne_two
    (hdim : Module.finrank ℝ E = 3) (x : F.M)
    (hrank : terminalCurvatureRankAt (I := I) F x ≠ 2) :
    ∀ a : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ,
      terminalCurvatureEndomorphismAt (I := I) F x a = 0 →
        DimensionThree.curvatureOperatorReactionEndomorphism3
          (terminalCurvatureEndomorphismAt (I := I) F x).toLinearMap a = 0 := by
  have hdim₂ : Module.finrank ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) = 3 := by
    rw [ContinuousAlternatingMap.finrank_continuousAlternatingMap]
    have hfin : Module.finrank ℝ (TangentSpace I x) = 3 :=
      (show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from rfl).trans hdim
    rw [hfin]
    norm_num
  have hrank' : Module.finrank ℝ
      (terminalCurvatureEndomorphismAt (I := I) F x).toLinearMap.range ≠ 2 := by
    rw [show (terminalCurvatureEndomorphismAt (I := I) F x).toLinearMap.range =
        (terminalCurvatureEndomorphismAt (I := I) F x).range from rfl]
    exact hrank
  intro a ha
  exact DimensionThree.curvatureOperatorReactionEndomorphism3_eq_zero_of_mem_ker_of_finrank_range_ne_two
    hdim₂ (terminalCurvatureEndomorphismAt (I := I) F x).toLinearMap hrank' ha


omit [I.Boundaryless] in
theorem terminalCurvatureRankAt_ne_two_of_kernelAnnihilation
    {kappa : ℝ} (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hnull : ∀ x : F.M, ∀ a : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ,
      terminalCurvatureEndomorphismAt (I := I) F x a = 0 →
        DimensionThree.curvatureOperatorReactionEndomorphism3
          (terminalCurvatureEndomorphismAt (I := I) F x).toLinearMap a = 0) :
    ∀ x : F.M, terminalCurvatureRankAt (I := I) F x ≠ 2 := by
  have hcone : ∀ x : F.M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := F.M) (F.S.base.metric 0) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) :=
    terminalCurvatureTensorAt_mem_nonnegativeCone F hK
  intro x htwo
  have hne := DimensionThree.curvatureOperatorImageAt_finrank_ne_two
    (I := I) hdim (F.S.base.metric 0) x
    ⟨metricRm04At (I := I) (F.S.base.metric 0) x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (F.S.base.metric 0) x⟩
    (fun a => DimensionThree.curvatureOperatorEndomorphismAt_inner_nonneg_of_mem_nonnegativeCone
      hdim (F.S.base.metric 0) x _ (hcone x) a)
    (fun a ha => hnull x a (by simpa only [terminalCurvatureEndomorphismAt] using ha))
  exact hne (by
    show Module.finrank ℝ (curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x
      ⟨metricRm04At (I := I) (F.S.base.metric 0) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (F.S.base.metric 0) x⟩) = 2
    exact htwo)


omit [I.Boundaryless] in
theorem terminalCurvatureRankAt_ne_two_iff_kernelAnnihilation
    {kappa : ℝ} (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3) :
    (∀ x : F.M, terminalCurvatureRankAt (I := I) F x ≠ 2) ↔
      (∀ x : F.M, ∀ a : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ,
        terminalCurvatureEndomorphismAt (I := I) F x a = 0 →
          DimensionThree.curvatureOperatorReactionEndomorphism3
            (terminalCurvatureEndomorphismAt (I := I) F x).toLinearMap a = 0) := by
  constructor
  · intro h x
    exact terminalCurvatureKernelAnnihilation_of_rank_ne_two F hdim x (h x)
  · intro h
    exact terminalCurvatureRankAt_ne_two_of_kernelAnnihilation F hK hdim h


theorem terminalCurvatureKernelAt_parallel_of_sliceConstantRank
    {kappa : ℝ} (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    {a b : ℝ} (hb : b ≤ 0) (hreg : Set.Ioo a b ⊆ D.regular)
    (h0 : (0 : ℝ) ∈ Set.Ioo a b) (q : ℕ)
    (hrank : ∀ r ∈ Set.Ioo a b, ∀ x : F.M,
      terminalSliceCurvatureRankAt (I := I) F r x = q) :
    IsParallelContinuousAlternatingSubmoduleFamily (F.S.base.metric 0)
      (fun x => terminalCurvatureKernelAt (I := I) F x) := by
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
  have hpar := DifferentialGeometry.PDE.RicciFlow.curvatureOperatorKernelAt_parallel_of_constant_rank
    (I := I) (M := F.M) F.S F.isSolution hdim (a := a) (b := b) (t := 0) h0 hreg hR' q
    (fun r hr x => hrank r hr x)
  exact hpar


omit [I.Boundaryless] in
theorem rmNormSq_eq_zero_of_terminalCurvatureRankAt_eq_zero
    (hdim : Module.finrank ℝ E = 3) (y : F.M)
    (hzero : terminalCurvatureRankAt (I := I) F y = 0) :
    F.rmNormSq (I := I) 0 y = 0 := by
  have himg : curvatureOperatorImageAt (I := I) (F.S.base.metric 0) y
      ⟨metricRm04At (I := I) (F.S.base.metric 0) y,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (F.S.base.metric 0) y⟩ = ⊥ :=
    Submodule.finrank_eq_zero.mp hzero
  have hbot : (terminalCurvatureEndomorphismAt (I := I) F y).range = ⊥ := by
    rw [← curvatureOperatorImageAt_eq_range]
    exact himg
  have hop : terminalCurvatureEndomorphismAt (I := I) F y = 0 := by
    refine ContinuousLinearMap.ext fun a => ?_
    have ha : terminalCurvatureEndomorphismAt (I := I) F y a ∈
        (terminalCurvatureEndomorphismAt (I := I) F y).range := ⟨a, rfl⟩
    rw [hbot] at ha
    simpa using ha
  have hrm : metricRm04At (I := I) (F.S.base.metric 0) y = 0 :=
    DimensionThree.metricRm04At_eq_zero_of_curvatureOperatorEndomorphismAt_eq_zero
      (I := I) (F.S.base.metric 0) y hdim
      (by simpa only [terminalCurvatureEndomorphismAt] using hop)
  have hrm' : F.S.base.rm04 0 y = 0 := by
    have h1 : F.S.base.rm04 0 y =
        metricRm04 (I := I) (M := F.M) (F.S.base.metric 0) y := rfl
    rw [h1, metricRm04_apply, hrm]
  rw [show F.rmNormSq (I := I) 0 y = Tensor0SBundle.normSq0S (I := I)
      (F.S.base.metric 0) y 4 (F.S.base.rm04 0 y) from by
    simp only [PointedFlowData.rmNormSq, SolutionOn.family_metric]]
  rw [hrm']
  simp only [Tensor0SBundle.normSq0S, Tensor0SBundle.inner0S, Tensor0SBundle.MetricFiberData.inner,
    map_zero]


def KLimTerminalRankNeTwo (F : PointedFlowData.{u, uE, uH} (I := I) D) (kappa : ℝ) : Prop :=
  KLim (I := I) kappa F → Module.finrank ℝ E = 3 →
    ∀ x : F.M, terminalCurvatureRankAt (I := I) F x ≠ 2


def KLimTerminalConstantRank (F : PointedFlowData.{u, uE, uH} (I := I) D) (kappa : ℝ) : Prop :=
  KLim (I := I) kappa F → Module.finrank ℝ E = 3 →
    ∃ q : ℕ, ∀ x : F.M, terminalCurvatureRankAt (I := I) F x = q


def KLimTerminalParallelKernel (F : PointedFlowData.{u, uE, uH} (I := I) D) (kappa : ℝ) : Prop :=
  KLim (I := I) kappa F → Module.finrank ℝ E = 3 →
    IsParallelContinuousAlternatingSubmoduleFamily (F.S.base.metric 0)
      (fun x => terminalCurvatureKernelAt (I := I) F x)


def KLimTerminalRankOneSplitting (F : PointedFlowData.{u, uE, uH} (I := I) D)
    (kappa : ℝ) : Prop :=
  KLim (I := I) kappa F → Module.finrank ℝ E = 3 →
    (∀ x : F.M, terminalCurvatureRankAt (I := I) F x = 1) →
    IsParallelContinuousAlternatingSubmoduleFamily (F.S.base.metric 0)
      (fun x => terminalCurvatureKernelAt (I := I) F x) →
    Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0))


theorem terminalNullPlaneSplitting_of_terminalRankFrontier {kappa : ℝ}
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hG2 : ∀ x : F.M, terminalCurvatureRankAt (I := I) F x ≠ 2)
    (hG3 : ∃ q : ℕ, ∀ x : F.M, terminalCurvatureRankAt (I := I) F x = q)
    (hsplit : ∀ q : ℕ, (∀ x : F.M, terminalCurvatureRankAt (I := I) F x = q) → q = 1 →
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0))) :
    TerminalNullPlaneSplitting (I := I) F := by
  intro x a b hgram hnull
  obtain ⟨q, hq⟩ := hG3
  have hcases : q = 0 ∨ q = 1 ∨ q = 3 := by
    have hle : q ≤ 3 := by
      rw [← hq x]
      exact terminalCurvatureRankAt_le_three F hdim x
    have hne : q ≠ 2 := by
      rw [← hq x]
      exact hG2 x
    omega
  rcases hcases with h0 | h1 | h3
  · refine Or.inl fun y => ?_
    exact rmNormSq_eq_zero_of_terminalCurvatureRankAt_eq_zero F hdim y ((hq y).trans h0)
  · exact Or.inr (hsplit q hq h1)
  · exfalso
    have hdimx : Module.finrank ℝ (TangentSpace I x) = 3 :=
      (show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from rfl).trans hdim
    have hcone : ∀ z : F.M,
        metricAlgebraicCurvatureTensorAt (I := I) (M := F.M) (F.S.base.metric 0) z ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) :=
      terminalCurvatureTensorAt_mem_nonnegativeCone F hK
    have hrank3 : Module.finrank ℝ (curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x
        ⟨metricRm04At (I := I) (F.S.base.metric 0) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (F.S.base.metric 0) x⟩) = 3 :=
      (hq x).trans h3
    let A : algebraicCurvatureTensorSubmodule (I := I) (M := F.M) x :=
      ⟨metricRm04 (I := I) (F.S.base.metric 0) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (F.S.base.metric 0) x⟩
    have hAcone : A ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
      simpa only [A, metricRm04_apply, metricAlgebraicCurvatureTensorAt] using hcone x
    have hArank : Module.finrank ℝ (curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x A) = 3 :=
      hrank3
    have hleast := DimensionThree.leastCurvatureOperatorEigenvalueAt_pos_of_image_finrank_eq_three
      (I := I) (M := F.M) (F.S.base.metric 0) x hdimx A hAcone hArank
    obtain ⟨basis, horth⟩ :=
      exists_orthonormalBasisAt (I := I) (F.S.base.metric 0) x hdimx
    have hbound : curvatureOperatorLowerBoundAt (I := I) (F.S.base.metric 0) x A
        (-(leastCurvatureOperatorEigenvalueAt (I := I) (F.S.base.metric 0) x A)) :=
      (DimensionThree.curvatureOperatorLowerBoundAt_iff_neg_leastCurvatureOperatorEigenvalueAt_le
        (I := I) basis horth).mpr le_rfl
    have hquad := hbound 1 (fun _ : Fin 1 => 1) (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)
    have hid : 0 < algebraicCurvatureIdentityQuadraticEval (I := I) (F.S.base.metric 0)
        (fun _ : Fin 1 => 1) (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) := by
      simpa only [algebraicCurvatureIdentityQuadraticEval, Fin.sum_univ_one, one_mul,
        (F.S.base.metric 0).symm x b a, ← pow_two, one_pow] using hgram
    have hop : 0 < algebraicCurvatureOperatorQuadraticEval (I := I) (M := F.M) A
        (fun _ : Fin 1 => 1) (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) :=
      lt_of_lt_of_le (mul_pos hleast hid) (by linarith [hquad])
    have hop04 : 0 < metricRm04StandardAt (I := I) (M := F.M) (F.S.base.metric 0) x a b b a := by
      simpa only [A, algebraicCurvatureOperatorQuadraticEval, Fin.sum_univ_one, one_mul,
        metricRm04StandardAt, metricRm04_apply, tensor04StandardAt] using hop
    rw [hnull] at hop04
    exact lt_irrefl 0 hop04


theorem klim_terminal_curvature_trichotomy_of_terminalRankFrontier {kappa : ℝ}
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hG2 : ∀ x : F.M, terminalCurvatureRankAt (I := I) F x ≠ 2)
    (hG3 : ∃ q : ℕ, ∀ x : F.M, terminalCurvatureRankAt (I := I) F x = q)
    (hsplit : ∀ q : ℕ, (∀ x : F.M, terminalCurvatureRankAt (I := I) F x = q) → q = 1 →
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0))) :
    DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) (F.S.base.metric 0) ∨
      (∀ x : F.M, F.rmNormSq (I := I) 0 x = 0) ∨
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) :=
  klim_terminal_curvature_trichotomy_of_nullPlaneSplitting F
    (terminalNullPlaneSplitting_of_terminalRankFrontier F hK hdim hG2 hG3 hsplit) hK hdim


theorem klim_terminal_curvature_trichotomy_of_namedFrontiers {kappa : ℝ}
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hG2 : KLimTerminalRankNeTwo (I := I) F kappa)
    (hG3 : KLimTerminalConstantRank (I := I) F kappa)
    (hG4 : KLimTerminalParallelKernel (I := I) F kappa)
    (hsplit : KLimTerminalRankOneSplitting (I := I) F kappa) :
    DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) (F.S.base.metric 0) ∨
      (∀ x : F.M, F.rmNormSq (I := I) 0 x = 0) ∨
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) :=
  klim_terminal_curvature_trichotomy_of_terminalRankFrontier F hK hdim
    (hG2 hK hdim) (hG3 hK hdim)
    (fun _q hq h1 => hsplit hK hdim (fun x => (hq x).trans h1) (hG4 hK hdim))


theorem terminalRankFrontier_not_constantRank_countermodel :
    ∃ A : ℝ → (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ),
      (∀ t : ℝ, Module.finrank ℝ (A t).range ≠ 2) ∧
        ¬ ∃ q : ℕ, ∀ t : ℝ, Module.finrank ℝ (A t).range = q := by
  let id3 : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := LinearMap.id
  have hbot : Module.finrank ℝ (LinearMap.range ((0 : ℝ) • id3)) = 0 := by
    rw [zero_smul ℝ id3, LinearMap.range_zero]
    simp
  have htop : Module.finrank ℝ (LinearMap.range ((1 : ℝ) • id3)) = 3 := by
    rw [one_smul ℝ id3, LinearMap.range_id, finrank_top, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin]
  refine ⟨fun t => t • id3, ?_, ?_⟩
  · intro t
    by_cases ht : t = 0
    · subst ht
      rw [hbot]
      norm_num
    · have hrange : LinearMap.range (t • id3) = ⊤ := by
        refine LinearMap.range_eq_top.mpr fun y => ⟨t⁻¹ • y, ?_⟩
        simp [id3, ht, smul_smul]
      rw [hrange, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
      norm_num
  · rintro ⟨q, hq⟩
    have h0 := hq 0
    have h1 := hq 1
    rw [hbot] at h0
    rw [htop] at h1
    omega


end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
