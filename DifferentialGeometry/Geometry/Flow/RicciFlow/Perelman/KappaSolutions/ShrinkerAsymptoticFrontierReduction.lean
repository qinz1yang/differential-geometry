import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.NullSectionalRankRigidity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinkerFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalRankKernelFrontier
import Mathlib.Analysis.Matrix.Order


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [T2Space M]

theorem finrank_curvatureOperatorImageAt_eq_zero_or_one_of_null_sectional
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank ℝ (TangentSpace I x) = 3)
    (hcone : metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hdefect : ricciReactionDefectAt (I := I) g x = 0)
    {a b : TangentSpace I x}
    (hgram : 0 < g.inner x a a * g.inner x b b - (g.inner x a b) ^ 2)
    (hsec : metricRm04StandardAt (I := I) (M := M) g x a b b a = 0) :
    Module.finrank ℝ (curvatureOperatorImageAt (I := I) g x
      ⟨metricRm04At (I := I) (M := M) g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩) = 0 ∨
    Module.finrank ℝ (curvatureOperatorImageAt (I := I) g x
      ⟨metricRm04At (I := I) (M := M) g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩) = 1 := by
  have h := metricCurvatureOperatorRankAt_eq_zero_or_one_of_null_sectional
    (I := I) (M := M) g x hdim hcone hdefect hgram hsec
  rw [metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank
    (I := I) (M := M) g x hdim] at h
  exact h

end DifferentialGeometry.Geometry.Curvature.DimensionThree

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Topology
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance terminalDefectTopology : TopologicalSpace F.M := F.topology
local instance terminalDefectCharted : ChartedSpace H F.M := F.charted
local instance terminalDefectSmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalDefectC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance terminalDefectC2 : IsManifold I 2 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance terminalDefectT2 : T2Space F.M := F.t2
local instance terminalDefectSigma : SigmaCompactSpace F.M := F.sigmaCompact


def TerminalReactionDefectVanishing (F : PointedFlowData.{u, uE, uH} (I := I) D) : Prop :=
  ∀ x : F.M, ricciReactionDefectAt (I := I) (F.S.base.metric 0) x = 0


theorem terminalReactionDefectVanishing_iff :
    TerminalReactionDefectVanishing (I := I) F ↔
      ∀ x : F.M, ricciReactionDefectAt (I := I) (F.S.base.metric 0) x = 0 :=
  Iff.rfl


omit [I.Boundaryless] in
theorem terminalCurvatureImageAt_eq_metricRm04_form (x : F.M) :
    terminalCurvatureImageAt (I := I) F x =
      curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x
        ⟨metricRm04 (I := I) (F.S.base.metric 0) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (F.S.base.metric 0) x⟩ :=
  congrArg (fun A : algebraicCurvatureTensorSubmodule (I := I) (M := F.M) x =>
      curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x A)
    (Subtype.ext (metricRm04_apply (I := I) (M := F.M) (F.S.base.metric 0) x))


omit [I.Boundaryless] in
theorem terminalCurvatureRankAt_eq_finrank_metricRm04_form (x : F.M) :
    terminalCurvatureRankAt (I := I) F x =
      Module.finrank ℝ (curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x
        ⟨metricRm04 (I := I) (F.S.base.metric 0) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (F.S.base.metric 0) x⟩) := by
  refine congrArg
    (fun s : Submodule ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) => Module.finrank ℝ s) ?_
  exact terminalCurvatureImageAt_eq_metricRm04_form (I := I) F x


omit [I.Boundaryless] in
theorem terminalCurvatureRankAt_of_finrank_metricRm04_form (x : F.M)
    (h : Module.finrank ℝ (curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x
        ⟨metricRm04 (I := I) (F.S.base.metric 0) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (F.S.base.metric 0) x⟩) = 0 ∨
      Module.finrank ℝ (curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x
        ⟨metricRm04 (I := I) (F.S.base.metric 0) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (F.S.base.metric 0) x⟩) = 1) :
    terminalCurvatureRankAt (I := I) F x = 0 ∨ terminalCurvatureRankAt (I := I) F x = 1 := by
  rw [terminalCurvatureRankAt_eq_finrank_metricRm04_form (I := I) F x]
  exact h

open Matrix in
theorem rank_two_posSemidef_with_null_vector_countermodel :
    ∃ A : Matrix (Fin 3) (Fin 3) ℝ, A.PosSemidef ∧ A.rank = 2 ∧
      ∃ v : Fin 3 → ℝ, v ≠ 0 ∧ A.mulVec v ⬝ᵥ v = 0 := by
  refine ⟨Matrix.diagonal ![0, 1, 1], ?_, ?_, ?_⟩
  · exact Matrix.PosSemidef.diagonal fun i => by fin_cases i <;> norm_num
  · have hf : (Finset.univ.filter
        (fun i : Fin 3 => (![0, 1, 1] : Fin 3 → ℝ) i ≠ 0)) = {1, 2} := by
      ext i
      fin_cases i <;> simp
    rw [Matrix.rank_diagonal, Fintype.card_subtype, hf]
    decide
  · refine ⟨![1, 0, 0], ?_, ?_⟩
    · intro h
      simpa using congrFun h 0
    · simp [Matrix.mulVec, dotProduct, Matrix.diagonal, Fin.sum_univ_three]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
