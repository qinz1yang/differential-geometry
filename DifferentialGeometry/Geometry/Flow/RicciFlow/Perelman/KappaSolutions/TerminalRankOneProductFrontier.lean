import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalRankKernelFrontier

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

local instance terminalRankOneProductTopology : TopologicalSpace F.M := F.topology
local instance terminalRankOneProductCharted : ChartedSpace H F.M := F.charted
local instance terminalRankOneProductSmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalRankOneProductC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance terminalRankOneProductT2 : T2Space F.M := F.t2
local instance terminalRankOneProductSigma : SigmaCompactSpace F.M := F.sigmaCompact


local instance terminalRankOneProductInhabited : Inhabited F.M := ⟨F.basepoint⟩


local instance terminalRankOneProductLocallyPathConnected :
    LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M


local instance terminalRankOneProductSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)


def KLimTerminalRankOneProduct (F : PointedFlowData.{u, uE, uH} (I := I) D)
    (kappa : ℝ) : Prop :=
  KLim (I := I) kappa F → Module.finrank ℝ E = 3 →
    (∀ x : F.M, terminalCurvatureRankAt (I := I) F x = 1) →
    Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0))

theorem kLimTerminalRankOneProduct_of_rankOneSplitting {kappa : ℝ}
    (hsplit : KLimTerminalRankOneSplitting (I := I) F kappa)
    (hpar : KLimTerminalParallelKernel (I := I) F kappa) :
    KLimTerminalRankOneProduct (I := I) F kappa :=
  fun hK hdim hrank => hsplit hK hdim hrank (hpar hK hdim)

theorem klim_terminal_curvature_trichotomy_of_rankOneProductFrontier {kappa : ℝ}
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hG2 : ∀ x : F.M, terminalCurvatureRankAt (I := I) F x ≠ 2)
    (hG3 : ∃ q : ℕ, ∀ x : F.M, terminalCurvatureRankAt (I := I) F x = q)
    (hprod : (∀ x : F.M, terminalCurvatureRankAt (I := I) F x = 1) →
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0))) :
    DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) (F.S.base.metric 0) ∨
      (∀ x : F.M, F.rmNormSq (I := I) 0 x = 0) ∨
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) :=
  klim_terminal_curvature_trichotomy_of_terminalRankFrontier (I := I) F hK hdim hG2 hG3
    (fun _q hq h1 => hprod (fun x => (hq x).trans h1))

theorem klim_terminal_curvature_trichotomy_of_rankOneProductNamedFrontier {kappa : ℝ}
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hG2 : KLimTerminalRankNeTwo (I := I) F kappa)
    (hG3 : KLimTerminalConstantRank (I := I) F kappa)
    (hprod : KLimTerminalRankOneProduct (I := I) F kappa) :
    DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) (F.S.base.metric 0) ∨
      (∀ x : F.M, F.rmNormSq (I := I) 0 x = 0) ∨
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) :=
  klim_terminal_curvature_trichotomy_of_rankOneProductFrontier (I := I) F hK hdim
    (fun x => hG2 hK hdim x) (hG3 hK hdim)
    (fun hx => hprod hK hdim hx)

theorem klim_terminal_curvature_trichotomy_of_namedFrontiers_of_rankOneProduct {kappa : ℝ}
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hG2 : KLimTerminalRankNeTwo (I := I) F kappa)
    (hG3 : KLimTerminalConstantRank (I := I) F kappa)
    (hpar : KLimTerminalParallelKernel (I := I) F kappa)
    (hsplit : KLimTerminalRankOneSplitting (I := I) F kappa) :
    DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) (F.S.base.metric 0) ∨
      (∀ x : F.M, F.rmNormSq (I := I) 0 x = 0) ∨
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) :=
  klim_terminal_curvature_trichotomy_of_rankOneProductNamedFrontier (I := I) F hK hdim hG2 hG3
    (kLimTerminalRankOneProduct_of_rankOneSplitting (I := I) F hsplit hpar)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
