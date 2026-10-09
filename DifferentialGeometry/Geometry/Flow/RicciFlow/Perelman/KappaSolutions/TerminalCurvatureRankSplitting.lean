import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalNullPlaneProduct
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalConstantRankFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalRankKernelPersistence

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff

universe uHF

variable {H : Type uHF} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{0, 0, uHF} (I := I) D)

local instance terminalRankSplittingTopology : TopologicalSpace F.M := F.topology
local instance terminalRankSplittingCharted : ChartedSpace H F.M := F.charted
local instance terminalRankSplittingSmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalRankSplittingC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance terminalRankSplittingT2 : T2Space F.M := F.t2
local instance terminalRankSplittingSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance terminalRankSplittingInhabited : Inhabited F.M := ⟨F.basepoint⟩

local instance terminalRankSplittingLocallyPathConnected :
    LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M

local instance terminalRankSplittingSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

abbrev terminalCurvatureOperatorImageRank (F : PointedFlowData.{0, 0, uHF} (I := I) D)
    (x : F.M) : ℕ :=
  Module.finrank ℝ (curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x
    ⟨metricRm04 (I := I) (F.S.base.metric 0) x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (F.S.base.metric 0) x⟩)

def TerminalNullPlaneRankNeTwo : Prop :=
  ∀ (x : F.M) (a b : TangentSpace I x),
    0 < (F.S.base.metric 0).inner x a a * (F.S.base.metric 0).inner x b b -
        ((F.S.base.metric 0).inner x a b) ^ 2 →
      metricRm04StandardAt (I := I) (M := F.M) (F.S.base.metric 0) x a b b a = 0 →
        terminalCurvatureOperatorImageRank (I := I) F x ≠ 2

def TerminalNullPlaneRankSplitting : Prop :=
  ∀ (x : F.M) (a b : TangentSpace I x),
    0 < (F.S.base.metric 0).inner x a a * (F.S.base.metric 0).inner x b b -
        ((F.S.base.metric 0).inner x a b) ^ 2 →
      metricRm04StandardAt (I := I) (M := F.M) (F.S.base.metric 0) x a b b a = 0 →
        terminalCurvatureOperatorImageRank (I := I) F x ≠ 2 →
          (∀ y : F.M, F.rmNormSq (I := I) 0 y = 0) ∨
            Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0))

theorem terminalNullPlaneSplitting_of_rankNeTwo_and_rankSplitting
    (hne : TerminalNullPlaneRankNeTwo (I := I) F)
    (hspl : TerminalNullPlaneRankSplitting (I := I) F) :
    TerminalNullPlaneSplitting (I := I) F :=
  fun x a b hgram hnull => hspl x a b hgram hnull (hne x a b hgram hnull)

theorem klim_terminal_curvature_trichotomy_of_rankNeTwo_and_rankSplitting
    (hne : TerminalNullPlaneRankNeTwo (I := I) F)
    (hspl : TerminalNullPlaneRankSplitting (I := I) F)
    {kappa : ℝ} (hK : KLim (I := I) kappa F) :
    DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I)
        (F.S.base.metric 0) ∨
      (∀ x : F.M, F.rmNormSq (I := I) 0 x = 0) ∨
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) :=
  klim_terminal_curvature_trichotomy_of_nullPlaneSplitting (I := I) F
    (terminalNullPlaneSplitting_of_rankNeTwo_and_rankSplitting (I := I) F hne hspl)
    hK (by simp [DifferentialGeometry.Topology.Morse.MorseModel])

section TerminalProductRankInstance

variable {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
variable {H₂ : Type*} [TopologicalSpace H₂]
variable {I₂ : ModelWithCorners ℝ E₂ H₂} [I₂.Boundaryless]
variable {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [IsManifold I₂ ∞ M₂] [T2Space M₂]

theorem terminalProductCurvatureOperatorImageRank_eq_one_and_ne_two
    (g₂ : SmoothRiemannianMetric I₂ M₂) (hdim : Module.finrank ℝ E₂ = 2) (x : M₂ × ℝ)
    (hscalar : metricScalarAt (I := I₂) g₂ x.1 ≠ 0) :
    (Module.finrank ℝ
        (curvatureOperatorImageAt (g₂.prod (euclideanMetric (E := ℝ))) x
          ⟨metricRm04At (g₂.prod (euclideanMetric (E := ℝ))) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (g₂.prod (euclideanMetric (E := ℝ))) x⟩) = 1) ∧
      (Module.finrank ℝ
        (curvatureOperatorImageAt (g₂.prod (euclideanMetric (E := ℝ))) x
          ⟨metricRm04At (g₂.prod (euclideanMetric (E := ℝ))) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (g₂.prod (euclideanMetric (E := ℝ))) x⟩) ≠ 2) :=
  ⟨curvatureOperatorImageAt_finrank_prod_real_eq_one g₂ hdim x hscalar,
    curvatureOperatorImageAt_finrank_prod_real_ne_two g₂ hdim x hscalar⟩

end TerminalProductRankInstance

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
