import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.BaseTimeSemicontinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.AncientScalarTimeControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Defs

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Manifold _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance terminalCostTopology : TopologicalSpace F.M := F.topology
private local instance terminalCostCharted : ChartedSpace H F.M := F.charted
private local instance terminalCostSmooth : IsManifold I ∞ F.M := F.smooth
private local instance terminalCostC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance terminalCostT2 : T2Space F.M := F.t2
private local instance terminalCostSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem ancient_lCost_lowerSemicontinuousWithinAt_terminal
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {tau : ℝ} (htau : 0 < tau) (p q : F.M) :
    LowerSemicontinuousWithinAt (fun T => lCost F.S T p q tau) (Iic 0) 0 := by
  let _ : ConnectedSpace F.M := hF.connected
  have hdim : Module.finrank ℝ E ≠ 0 := by
    intro hzero
    obtain ⟨t, ht, x, hx⟩ := hF.notFlat
    have hb := ancientKappa_rmNormLeScalar_finrank F hF t ht x
    rw [hzero, Nat.cast_zero] at hb
    norm_num at hb
    have hn : 0 ≤ F.rmNormSq (I := I) t x := by
      simpa only [PointedFlowData.rmNormSq, SolutionOn.family] using
        DifferentialGeometry.Tensor0SBundle.normSq0S_nonneg
          (I := I) (F.S.base.metric t) x 4 (F.S.base.rm04 t x)
    have hz : Real.sqrt (F.rmNormSq (I := I) t x) = 0 :=
      le_antisymm hb (Real.sqrt_nonneg _)
    exact hx ((Real.sqrt_eq_zero hn).mp hz)
  have : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
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
      AntitoneOn (fun t => (F.S.base.metric t).inner x v v) (Iic 0) := by
    intro s hs t ht hst
    have hRic : ∀ r ∈ Ioo s t, ∀ y : F.M, ∀ w : TangentSpace I y,
        0 ≤ F.S.ricciAt r y (vec2 w w) := by
      intro r hr y w
      apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
      apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
        (I := I) (F.S.base.metric r) y).mpr
      intro n c a b
      simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
        hF.nonnegativeCurvatureOperator r (hr.2.le.trans ht) y n c a b
    exact CanonicalNeighborhood.metric_inner_antitoneOn_of_ricci_nonnegative_interior F.S F.isSolution
      (fun _ hr => hr.2.trans ht) (fun _ hr => hr.2.trans_le ht) hRic x v
      ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
  obtain ⟨Bscalar, hBscalar⟩ := hF.globalScalarBound
  exact lCost_lowerSemicontinuousWithinAt_of_metric_antitone_of_scalar_time_lipschitz
    F.S F.isSolution hF.carrier_eq hC hmetric hscalarTime
    (fun t ht x => (hBscalar t ht x).1) le_rfl htau p q

theorem ancient_lCost_continuousWithinAt_terminal
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {tau : ℝ} (htau : 0 < tau) (p q : F.M) :
    ContinuousWithinAt (fun T => lCost F.S T p q tau) (Iic 0) 0 := by
  let _ : ConnectedSpace F.M := hF.connected
  obtain ⟨B, hB⟩ := hF.globalScalarBound
  refine continuousWithinAt_iff_lower_upperSemicontinuousWithinAt.mpr ⟨?_, ?_⟩
  · exact ancient_lCost_lowerSemicontinuousWithinAt_terminal F hF htau p q
  · exact lCost_upperSemicontinuousWithinAt_of_scalar_nonneg F.S F.isSolution
      (fun {_ _} hb hab => hab.trans hb) (fun t ht x => (hB t ht x).1)
      (T := 0) (by simp only [ancientTimeInterval_carrier, mem_Iic, le_refl]) htau p q

theorem ancient_redDensity_continuousWithinAt_terminal
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {tau : ℝ} (htau : 0 < tau) (p q : F.M) :
    ContinuousWithinAt (fun T => redDensity F.S T p q tau) (Iic 0) 0 := by
  have hcost := ancient_lCost_continuousWithinAt_terminal F hF htau p q
  have harg := (((hcost.div_const (2 * Real.sqrt tau)).neg.sub_const
    ((Module.finrank ℝ E : ℝ) / 2 * Real.log tau)).sub_const
    ((Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi)))
  change ContinuousWithinAt (fun T => Real.exp
    (-(lCost F.S T p q tau / (2 * Real.sqrt tau)) -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))) (Iic 0) 0
  exact Real.continuous_exp.continuousAt.comp_continuousWithinAt harg

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
