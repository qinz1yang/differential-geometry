import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalSurfaceProductEuclidean
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackLimit

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff

universe uH

variable {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ
    (DifferentialGeometry.Topology.Morse.MorseModel 3) H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{0, 0, uH} (I := I) D)

local instance terminalConstantRankTopology : TopologicalSpace F.M := F.topology
local instance terminalConstantRankCharted : ChartedSpace H F.M := F.charted
local instance terminalConstantRankSmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalConstantRankT2 : T2Space F.M := F.t2
local instance terminalConstantRankSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance terminalConstantRankInhabited : Inhabited F.M := ⟨F.basepoint⟩
local instance terminalConstantRankLocallyPathConnected :
    LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M
local instance terminalConstantRankSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

def TerminalConstantRankParallelKernel
    (F : PointedFlowData.{0, 0, uH} (I := I) D) : Prop :=
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
            (I := I) (F.S.base.metric 0) x⟩)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
