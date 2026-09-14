import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorPositiveSectional
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorVanishing
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureTrichotomy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalConstantRankReaction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalCurvatureRankSplitting

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff

variable {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{0, 0, 0} (I := I) D)

local instance terminalConstantRankProductTopology : TopologicalSpace F.M := F.topology
local instance terminalConstantRankProductCharted : ChartedSpace H F.M := F.charted
local instance terminalConstantRankProductSmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalConstantRankProductT2 : T2Space F.M := F.t2
local instance terminalConstantRankProductSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance terminalConstantRankProductInhabited : Inhabited F.M := ⟨F.basepoint⟩
local instance terminalConstantRankProductLocallyPathConnected :
    LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M
local instance terminalConstantRankProductSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

private theorem finrank_morseModel_three_aux :
    Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3 := by
  simp [DifferentialGeometry.Topology.Morse.MorseModel]

omit [I.Boundaryless] in
private theorem terminalTangentFinrank_aux (x : F.M) :
    Module.finrank ℝ (TangentSpace I x) = 3 :=
  (show Module.finrank ℝ (TangentSpace I x) =
    Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) from rfl).trans
    finrank_morseModel_three_aux

theorem terminalGlobalAlternative_of_terminalConstantRankParallelKernel
    [ConnectedSpace F.M] {kappa : ℝ}
    (hK : KLim (I := I) kappa F)
    (hker : TerminalConstantRankParallelKernel (I := I) F) :
    DifferentialGeometry.PDE.RicciFlow.DimensionThree.CurvatureTimeSliceGlobalAlternative
      (I := I) (M := F.M) (F.S.base.metric 0) := by
  obtain ⟨hnonneg, hnull, hrank, hkernel⟩ :=
    terminalConstantRank_derivedData_hypotheses_of_kLim F hK hker
  have hcomplete : RiemannianMetricComplete (I := I) (F.S.base.metric 0) :=
    ⟨hK.complete 0 (by simpa only [hK.carrier_eq, Set.mem_Iic] using le_rfl)⟩
  exact DifferentialGeometry.PDE.RicciFlow.DimensionThree.curvature_time_slice_global_trichotomy_of_derived_data
    (I := I) (M := F.M) (F.S.base.metric 0) hcomplete hnonneg hnull hrank hkernel

theorem terminalNullPlaneRankNeTwo_of_terminalConstantRankParallelKernel
    (hker : TerminalConstantRankParallelKernel (I := I) F) :
    TerminalNullPlaneRankNeTwo (I := I) F := by
  obtain ⟨q, hq, hconst, _⟩ := hker
  have hq2 : q ≠ 2 := by rcases hq with h | h | h <;> omega
  intro x a b _ _ h2
  exact hq2 (hconst x ▸ h2)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
