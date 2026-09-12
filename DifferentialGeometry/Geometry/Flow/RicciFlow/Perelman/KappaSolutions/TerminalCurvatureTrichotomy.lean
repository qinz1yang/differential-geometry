import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalSurfaceProduct
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackLimit
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Positivity
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature


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

section TerminalNullPlaneDichotomy

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem hasPositiveSectionalCurvature_iff_forall_curvatureOperatorPositiveAt
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3) :
    DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) g ↔
      ∀ x : M, CurvatureOperatorPositiveAt (I := I) (M := M) g x := by
  constructor
  · intro hsec x
    rw [curvatureOperatorPositiveAt_iff_sectional (I := I) (M := M) g x hdim]
    intro a b hgram
    exact hsec x a b
      (Geometry.Riemannian.linearIndependent_pair_of_sectionalCurvatureDenominator_pos
        (I := I) (M := M) g x a b (by
          simpa only [Geometry.Riemannian.sectionalCurvatureDenominator_def] using hgram))
  · intro hpos x a b hab
    have hgram : 0 < g.inner x a a * g.inner x b b - (g.inner x a b) ^ 2 := by
      simpa only [Geometry.Riemannian.sectionalCurvatureDenominator_def] using
        Geometry.Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent
          (I := I) (M := M) g x a b hab
    exact ((curvatureOperatorPositiveAt_iff_sectional (I := I) (M := M) g x hdim).mp
      (hpos x) a b hgram)

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem exists_nullPlane_of_not_forall_curvatureOperatorPositiveAt
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3)
    (hnonneg : ∀ x : M, metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hnot : ¬ ∀ x : M, CurvatureOperatorPositiveAt (I := I) (M := M) g x) :
    ∃ x : M, ∃ a b : TangentSpace I x,
      0 < g.inner x a a * g.inner x b b - (g.inner x a b) ^ 2 ∧
      metricRm04StandardAt (I := I) (M := M) g x a b b a = 0 := by
  push Not at hnot
  obtain ⟨x, hx⟩ := hnot
  have hplanes := (not_congr
    (curvatureOperatorPositiveAt_iff_sectional (I := I) (M := M) g x hdim)).mp hx
  push Not at hplanes
  obtain ⟨a, b, hgram, hnonpos⟩ := hplanes
  refine ⟨x, a, b, ?_, ?_⟩
  · simpa only [Geometry.Riemannian.sectionalCurvatureDenominator_def] using hgram
  · have hnonneg' : 0 ≤ metricRm04StandardAt (I := I) (M := M) g x a b b a := by
      have h := mem_algebraicCurvatureOperatorNonnegativeCone.mp (hnonneg x)
        1 (fun _ : Fin 1 => 1) (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)
      simpa only [algebraicCurvatureOperatorQuadraticEval, Fin.sum_univ_one, one_mul,
        metricAlgebraicCurvatureTensorAt_coe, metricRm04StandardAt] using h
    exact le_antisymm hnonpos hnonneg'

end TerminalNullPlaneDichotomy

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
