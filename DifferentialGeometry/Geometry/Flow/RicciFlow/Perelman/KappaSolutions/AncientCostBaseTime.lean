import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.BaseTimeSemicontinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.AncientScalarTimeControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientMetricMonotonicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorNormFinrankNeZero

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open scoped ContDiff Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance terminalCostTopology : TopologicalSpace F.M := F.topology
private local instance terminalCostCharted : ChartedSpace H F.M := F.charted
private local instance terminalCostSmooth : IsManifold I ∞ F.M := F.smooth
private local instance terminalCostC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance terminalCostT2 : T2Space F.M := F.t2
private local instance terminalCostSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem exists_lCost_base_time_bound_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R T tau : ℝ}, R ≤ T → T ≤ 0 → 0 < tau →
      ∀ p q : F.M, lCost F.S T p q tau ≤ lCost F.S R p q tau +
        2 * Real.sqrt tau ^ 3 * C * (T - R) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : ConnectedSpace F.M := hF.connected
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _ht, x, hx⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) x (by decide : 0 < 4) (F.S.base.rm04 t x) hx⟩
  obtain ⟨B, hB⟩ := ancientKappa_rmNormSqBounded_finrank F hF
  let K := |B| + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hBK : B ≤ K ^ 2 := by
    dsimp only [K]
    nlinarith [le_abs_self B, abs_nonneg B, sq_nonneg (|B|)]
  obtain ⟨C, hC, hscalarTime⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_scalar_time_lipschitz_bound_of_complete_ancient_bounded_curvature
      F.S F.isSolution hF.carrier_eq hF.regular_eq hK
      (fun t ht => ⟨hF.complete t ht⟩) (fun t ht x => (hB t ht x).trans hBK)
  have hmetric (x : F.M) (v : TangentSpace I x) :
      AntitoneOn (fun t => (F.S.base.metric t).inner x v v) (Iic 0) :=
    ancientModel_metric_inner_antitoneOn F hF x v
  obtain ⟨Bscalar, hBscalar⟩ := hF.globalScalarBound
  refine ⟨C, hC, ?_⟩
  intro R T tau hRT hT htau p q
  exact lCost_le_add_of_metric_antitone_of_scalar_time_lipschitz F.S F.isSolution
    hF.carrier_eq hC hmetric hscalarTime (fun t ht x => (hBscalar t ht x).1)
    hRT hT htau p q

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
