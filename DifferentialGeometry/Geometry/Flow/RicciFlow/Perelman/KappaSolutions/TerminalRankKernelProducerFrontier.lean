import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalRankKernelFrontier
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankRigidity


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance terminalProducerTopology : TopologicalSpace F.M := F.topology
local instance terminalProducerCharted : ChartedSpace H F.M := F.charted
local instance terminalProducerSmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalProducerC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance terminalProducerT2 : T2Space F.M := F.t2
local instance terminalProducerSigma : SigmaCompactSpace F.M := F.sigmaCompact


local instance terminalProducerInhabited : Inhabited F.M := ⟨F.basepoint⟩


local instance terminalProducerLocallyPathConnected : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M


local instance terminalProducerSemilocallySimplyConnected : SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)


def KLimTerminalKernelAnnihilation (F : PointedFlowData.{u, uE, uH} (I := I) D) : Prop :=
  ∀ x : F.M, ∀ a : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ,
    terminalCurvatureEndomorphismAt (I := I) F x a = 0 →
      DimensionThree.curvatureOperatorReactionEndomorphism3
        (terminalCurvatureEndomorphismAt (I := I) F x).toLinearMap a = 0


omit [I.Boundaryless] in
theorem terminalCurvatureRankAt_ne_two_of_terminalKernelAnnihilation
    {kappa : ℝ} (hann : KLimTerminalKernelAnnihilation (I := I) F)
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3) :
    ∀ x : F.M, terminalCurvatureRankAt (I := I) F x ≠ 2 :=
  terminalCurvatureRankAt_ne_two_of_kernelAnnihilation F hK hdim hann


theorem terminalNullPlaneSplitting_of_terminalKernelAnnihilation {kappa : ℝ}
    (hann : KLimTerminalKernelAnnihilation (I := I) F)
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hG3 : ∃ q : ℕ, ∀ x : F.M, terminalCurvatureRankAt (I := I) F x = q)
    (hsplit : ∀ q : ℕ, (∀ x : F.M, terminalCurvatureRankAt (I := I) F x = q) → q = 1 →
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0))) :
    TerminalNullPlaneSplitting (I := I) F :=
  terminalNullPlaneSplitting_of_terminalRankFrontier F hK hdim
    (terminalCurvatureRankAt_ne_two_of_terminalKernelAnnihilation F hann hK hdim) hG3 hsplit


theorem klim_terminal_curvature_trichotomy_of_terminalKernelAnnihilation {kappa : ℝ}
    (hann : KLimTerminalKernelAnnihilation (I := I) F)
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hG3 : ∃ q : ℕ, ∀ x : F.M, terminalCurvatureRankAt (I := I) F x = q)
    (hsplit : ∀ q : ℕ, (∀ x : F.M, terminalCurvatureRankAt (I := I) F x = q) → q = 1 →
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0))) :
    DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) (F.S.base.metric 0) ∨
      (∀ x : F.M, F.rmNormSq (I := I) 0 x = 0) ∨
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) :=
  klim_terminal_curvature_trichotomy_of_nullPlaneSplitting F
    (terminalNullPlaneSplitting_of_terminalKernelAnnihilation F hann hK hdim hG3 hsplit) hK hdim


theorem posSemidef_rank_two_kernel_not_annihilated :
    ∃ A : Matrix (Fin 3) (Fin 3) ℝ, A.PosSemidef ∧ A.rank = 2 ∧
      ¬ (∀ v : Fin 3 → ℝ, Matrix.mulVec A v = 0 →
        Matrix.mulVec (curvatureOperatorReaction3 A) v = 0) := by
  refine ⟨Matrix.diagonal ![0, 1, 1], ?_, ?_, ?_⟩
  · refine Matrix.PosSemidef.diagonal fun i => ?_
    fin_cases i <;> norm_num
  · have hf : (Finset.univ.filter
        (fun i : Fin 3 => (![0, 1, 1] : Fin 3 → ℝ) i ≠ 0)) = {1, 2} := by
      ext i
      fin_cases i <;> simp
    rw [Matrix.rank_diagonal, Fintype.card_subtype, hf]
    decide
  · intro hann
    have hA : (Matrix.diagonal ![0, 1, 1] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef :=
      Matrix.PosSemidef.diagonal fun i => by fin_cases i <;> norm_num
    have hrank : (Matrix.diagonal ![0, 1, 1] : Matrix (Fin 3) (Fin 3) ℝ).rank = 2 := by
      have hf : (Finset.univ.filter
          (fun i : Fin 3 => (![0, 1, 1] : Fin 3 → ℝ) i ≠ 0)) = {1, 2} := by
        ext i
        fin_cases i <;> simp
      rw [Matrix.rank_diagonal, Fintype.card_subtype, hf]
      decide
    exact curvatureOperator_rank_two_reaction_annihilation_impossible hA hrank hann


theorem exists_posSemidef_rank_zero_kernel_annihilated :
    ∃ A : Matrix (Fin 3) (Fin 3) ℝ, A.PosSemidef ∧ A.rank = 0 ∧
      (∀ v : Fin 3 → ℝ, Matrix.mulVec A v = 0 →
        Matrix.mulVec (curvatureOperatorReaction3 A) v = 0) := by
  refine ⟨0, Matrix.PosSemidef.zero, Matrix.rank_zero, ?_⟩
  intro v _
  simp [curvatureOperatorReaction3]


end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
