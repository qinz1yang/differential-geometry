import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimTerminalFlat
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

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance terminalProductTopology : TopologicalSpace F.M := F.topology
local instance terminalProductCharted : ChartedSpace H F.M := F.charted
local instance terminalProductSmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalProductC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance terminalProductT2 : T2Space F.M := F.t2
local instance terminalProductSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance terminalProductInhabited : Inhabited F.M := ⟨F.basepoint⟩

local instance terminalProductLocallyPathConnected :
    LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M

local instance terminalProductSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

def TerminalProductBranch (F : PointedFlowData.{u, uE, uH} (I := I) D) : Prop :=
  ¬ DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I)
      (F.S.base.metric 0) →
    Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0))

namespace KLim

omit [I.Boundaryless] in
theorem exists_terminal_null_plane_of_not_positiveSectional {kappa : ℝ}
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hnot : ¬ DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I)
      (F.S.base.metric 0)) :
    ∃ x : F.M, ∃ a b : TangentSpace I x,
      0 < (F.S.base.metric 0).inner x a a * (F.S.base.metric 0).inner x b b -
        ((F.S.base.metric 0).inner x a b) ^ 2 ∧
      metricRm04StandardAt (I := I) (M := F.M) (F.S.base.metric 0) x a b b a = 0 := by
  have hnotOp : ¬ ∀ x : F.M,
      CurvatureOperatorPositiveAt (I := I) (M := F.M) (F.S.base.metric 0) x :=
    fun h => hnot
      ((hasPositiveSectionalCurvature_iff_forall_curvatureOperatorPositiveAt
        (I := I) (M := F.M) (F.S.base.metric 0) hdim).mpr h)
  have hnonneg : ∀ x : F.M,
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
  exact exists_nullPlane_of_not_forall_curvatureOperatorPositiveAt (I := I) (M := F.M)
    (F.S.base.metric 0) hdim hnonneg hnotOp

end KLim

theorem terminal_nullPlaneSplitting_iff_terminalProductBranch {kappa : ℝ}
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3) :
    TerminalNullPlaneSplitting (I := I) F ↔ TerminalProductBranch (I := I) F := by
  constructor
  · intro hsplit hnotpos
    obtain ⟨x, a, b, hgram, hnull⟩ :=
      KLim.exists_terminal_null_plane_of_not_positiveSectional (F := F) hK hdim hnotpos
    rcases hsplit x a b hgram hnull with hflat | hprod
    · exact absurd hflat (hK.not_terminal_flat F hdim)
    · exact hprod
  · intro hbranch x a b hgram hnull
    refine Or.inr (hbranch fun hpos => ?_)
    have hpair : LinearIndependent ℝ ![a, b] :=
      Geometry.Riemannian.linearIndependent_pair_of_sectionalCurvatureDenominator_pos
        (I := I) (M := F.M) (F.S.base.metric 0) x a b
        (by simpa only [Geometry.Riemannian.sectionalCurvatureDenominator_def] using hgram)
    exact (ne_of_gt (hpos x a b hpair)) hnull

theorem klim_terminal_curvature_trichotomy_of_terminalProductBranch
    (hbranch : TerminalProductBranch (I := I) F)
    {kappa : ℝ} (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3) :
    DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) (F.S.base.metric 0) ∨
      (∀ x : F.M, F.rmNormSq (I := I) 0 x = 0) ∨
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) :=
  klim_terminal_curvature_trichotomy_of_nullPlaneSplitting F
    ((terminal_nullPlaneSplitting_iff_terminalProductBranch F hK hdim).mpr hbranch) hK hdim

theorem KLim.terminal_curvature_trichotomy_iff_positive_or_terminalProduct {kappa : ℝ}
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3) :
    (DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I)
        (F.S.base.metric 0) ∨
      (∀ x : F.M, F.rmNormSq (I := I) 0 x = 0) ∨
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0))) ↔
    (DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I)
        (F.S.base.metric 0) ∨
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0))) := by
  constructor
  · rintro (hpos | hflat | hprod)
    · exact Or.inl hpos
    · exact absurd hflat (hK.not_terminal_flat F hdim)
    · exact Or.inr hprod
  · rintro (hpos | hprod)
    · exact Or.inl hpos
    · exact Or.inr (Or.inr hprod)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
