import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalSurfaceProduct
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackLimit


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance terminalTrichotomyTopology : TopologicalSpace F.M := F.topology
local instance terminalTrichotomyCharted : ChartedSpace H F.M := F.charted
local instance terminalTrichotomySmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalTrichotomyC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance terminalTrichotomyT2 : T2Space F.M := F.t2
local instance terminalTrichotomySigma : SigmaCompactSpace F.M := F.sigmaCompact


local instance terminalTrichotomyInhabited : Inhabited F.M := ⟨F.basepoint⟩


local instance terminalTrichotomyLocallyPathConnected :
    LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M


local instance terminalTrichotomySemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)


theorem klim_terminal_curvature_trichotomy {kappa : ℝ} (hK : KLim (I := I) kappa F)
    (hdim : Module.finrank ℝ E = 3) :
    DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) (F.S.base.metric 0) ∨
      (∀ x : F.M, F.rmNormSq (I := I) 0 x = 0) ∨
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
