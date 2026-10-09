import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalConstantRankFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalNullPlaneProduct

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff

universe uH

variable {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ
    (DifferentialGeometry.Topology.Morse.MorseModel 3) H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{0, 0, uH} (I := I) D)

local instance terminalDichotomyTopology : TopologicalSpace F.M := F.topology
local instance terminalDichotomyCharted : ChartedSpace H F.M := F.charted
local instance terminalDichotomySmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalDichotomyT2 : T2Space F.M := F.t2
local instance terminalDichotomySigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance terminalDichotomyInhabited : Inhabited F.M := ⟨F.basepoint⟩
local instance terminalDichotomyLocallyPathConnected :
    LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M
local instance terminalDichotomySemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

def TerminalConstantRankDichotomyFrontier
    (F : PointedFlowData.{0, 0, uH} (I := I) D) : Prop :=
  TerminalConstantRankParallelKernel (I := I) F →
    (∀ x : F.M, F.rmNormSq (I := I) 0 x = 0) ∨
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0))

theorem terminalConstantRankDichotomyFrontier_of_terminal_flat
    (hflat : ∀ x : F.M, F.rmNormSq (I := I) 0 x = 0) :
    TerminalConstantRankDichotomyFrontier (I := I) F :=
  fun _ => Or.inl hflat

theorem terminalConstantRankDichotomyFrontier_of_terminal_product
    (hprod : Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0))) :
    TerminalConstantRankDichotomyFrontier (I := I) F :=
  fun _ => Or.inr hprod

theorem terminalConstantRankParallelKernel_branch
    (h : TerminalConstantRankParallelKernel (I := I) F) :
    ∃ q : ℕ, (q = 0 ∨ q = 1 ∨ q = 3) ∧
      (∀ x : F.M, Module.finrank ℝ
        (curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x
          ⟨metricRm04 (I := I) (F.S.base.metric 0) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (F.S.base.metric 0) x⟩) = q) ∧
      IsParallelContinuousAlternatingSubmoduleFamily (F.S.base.metric 0)
        (fun x => curvatureOperatorKernelAt (I := I) (F.S.base.metric 0) x
          ⟨metricRm04 (I := I) (F.S.base.metric 0) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (F.S.base.metric 0) x⟩) := h

theorem terminalNullPlaneSplitting_of_constantRankDichotomyFrontier
    (hfrontier : TerminalConstantRankDichotomyFrontier (I := I) F)
    (h : TerminalConstantRankParallelKernel (I := I) F) :
    TerminalNullPlaneSplitting (I := I) F :=
  fun _ _ _ _ _ => hfrontier h

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
