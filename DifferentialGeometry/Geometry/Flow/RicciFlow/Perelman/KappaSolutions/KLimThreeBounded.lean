import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalCurvatureTrichotomy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimTerminalFlat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimPositiveTerminalBounded


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance threeBoundedTopology : TopologicalSpace F.M := F.topology
local instance threeBoundedCharted : ChartedSpace H F.M := F.charted
local instance threeBoundedSmooth : IsManifold I ∞ F.M := F.smooth
local instance threeBoundedT2 : T2Space F.M := F.t2
local instance threeBoundedSigma : SigmaCompactSpace F.M := F.sigmaCompact

attribute [local instance] terminalTrichotomyInhabited
  terminalTrichotomyLocallyPathConnected
  terminalTrichotomySemilocallySimplyConnected


theorem KLim.three_terminal_scalar_bddAbove_of_rankOne {kappa : ℝ}
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hnoEmbedding : ∀ f : SphereAntipodalQuotient → EuclideanSpace ℝ (Fin 3),
      ¬ _root_.Topology.IsEmbedding f)
    (hrankOne : ∀ _P : TerminalSurfaceProduct (I := I) (F.S.base.metric 0),
      BddAbove (Set.range (F.S.scalar 0))) :
    BddAbove (Set.range (F.S.scalar 0)) := by
  rcases klim_terminal_curvature_trichotomy F hK hdim with hpos | hflat | hprod
  · exact hK.three_terminal_bddAbove_of_positive F hdim hpos hnoEmbedding
  · exact absurd hflat (hK.not_terminal_flat F hdim)
  · exact hprod.elim hrankOne


theorem KLim.scalar_bounded_of_rankOne {kappa : ℝ}
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hnoEmbedding : ∀ f : SphereAntipodalQuotient → EuclideanSpace ℝ (Fin 3),
      ¬ _root_.Topology.IsEmbedding f)
    (hrankOne : ∀ _P : TerminalSurfaceProduct (I := I) (F.S.base.metric 0),
      BddAbove (Set.range (F.S.scalar 0))) :
    ∃ C : ℝ, PointedFlowScalarBounded (I := I) F C := by
  obtain ⟨C, hC⟩ :=
    hK.three_terminal_scalar_bddAbove_of_rankOne F hdim hnoEmbedding hrankOne
  exact ⟨C, hK.scalarBounded_of_terminal_bound fun x => hC (Set.mem_range_self x)⟩


theorem KLim.isAncientKappaSolution_of_rankOne {kappa : ℝ}
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hnoEmbedding : ∀ f : SphereAntipodalQuotient → EuclideanSpace ℝ (Fin 3),
      ¬ _root_.Topology.IsEmbedding f)
    (hrankOne : ∀ _P : TerminalSurfaceProduct (I := I) (F.S.base.metric 0),
      BddAbove (Set.range (F.S.scalar 0))) :
    IsAncientKappaSolution (I := I) kappa F := by
  obtain ⟨C, hC⟩ :=
    hK.three_terminal_scalar_bddAbove_of_rankOne F hdim hnoEmbedding hrankOne
  exact hK.toIsAncientKappaSolution fun x => hC (Set.mem_range_self x)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
