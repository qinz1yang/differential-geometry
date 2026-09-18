import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalCurvatureTrichotomy

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance terminalBranchesTopology : TopologicalSpace F.M := F.topology
local instance terminalBranchesCharted : ChartedSpace H F.M := F.charted
local instance terminalBranchesSmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalBranchesC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance terminalBranchesT2 : T2Space F.M := F.t2
local instance terminalBranchesSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance terminalBranchesInhabited : Inhabited F.M := ⟨F.basepoint⟩

local instance terminalBranchesLocallyPathConnected : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M

local instance terminalBranchesSemilocallySimplyConnected : SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

theorem terminalNullPlaneSplitting_of_terminalFlat
    (hflat : ∀ x : F.M, F.rmNormSq (I := I) 0 x = 0) :
    TerminalNullPlaneSplitting (I := I) F :=
  fun _ _ _ _ _ => Or.inl hflat

theorem terminalNullPlaneSplitting_of_terminalSurfaceProduct
    (hproduct : Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0))) :
    TerminalNullPlaneSplitting (I := I) F :=
  fun _ _ _ _ _ => Or.inr hproduct

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
