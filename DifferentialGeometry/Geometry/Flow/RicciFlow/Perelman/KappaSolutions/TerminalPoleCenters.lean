import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleCenters
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.BaseTimeSemicontinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.AncientScalarTimeControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedDensityGaussian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCostContinuity
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Metric.Distance.Finiteness
import Mathlib.Topology.Order.Compact


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped ContDiff _root_.Manifold _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance terminalCenterComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E
private local instance terminalCenterTopology : TopologicalSpace F.M := F.topology
private local instance terminalCenterCharted : ChartedSpace H F.M := F.charted
private local instance terminalCenterSmooth : IsManifold I ∞ F.M := F.smooth
private local instance terminalCenterC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance terminalCenterT2 : T2Space F.M := F.t2
private local instance terminalCenterSigma : SigmaCompactSpace F.M := F.sigmaCompact

private theorem exists_terminal_redLength_comparison
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) {tau : ℝ} (htau : 0 < tau) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ≤ 0, ∀ q : F.M,
      redLength F.S 0 p q tau ≤ redLength F.S b p q tau + C * (-b) := by
  let _ : ConnectedSpace F.M := hF.connected
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _, x, hx⟩ := hF.notFlat
    exact ⟨DifferentialGeometry.Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) x (by norm_num : 0 < 4) _ hx⟩
  obtain ⟨B, hB⟩ := ancientKappa_rmNormSqBounded_finrank F hF
  let K := |B| + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hBK : B ≤ K ^ 2 := by
    dsimp only [K]
    nlinarith [le_abs_self B, abs_nonneg B, sq_nonneg (|B|)]
  obtain ⟨C, hC, hscalarTime⟩ :=
    exists_scalar_time_lipschitz_bound_of_complete_ancient_bounded_curvature
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
    exact CanonicalNeighborhood.metric_inner_antitoneOn_of_ricci_nonnegative_interior
      F.S F.isSolution (fun _ hr => hr.2.trans ht) (fun _ hr => hr.2.trans_le ht)
      hRic x v ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
  obtain ⟨Bscalar, hBscalar⟩ := hF.globalScalarBound
  let A : ℝ := (2 * Real.sqrt tau ^ 3 * C) / (2 * Real.sqrt tau)
  have hden : 0 < 2 * Real.sqrt tau := by positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨A, hA, fun b hb q => ?_⟩
  have hcost := lCost_le_add_of_metric_antitone_of_scalar_time_lipschitz
    F.S F.isSolution hF.carrier_eq hC hmetric hscalarTime
    (fun t ht x => (hBscalar t ht x).1) hb le_rfl htau p q
  have hquot := div_le_div_of_nonneg_right hcost hden.le
  change lCost F.S 0 p q tau / (2 * Real.sqrt tau) ≤
    lCost F.S b p q tau / (2 * Real.sqrt tau) + A * (-b)
  calc
    lCost F.S 0 p q tau / (2 * Real.sqrt tau)
        ≤ (lCost F.S b p q tau +
          2 * Real.sqrt tau ^ 3 * C * (0 - b)) / (2 * Real.sqrt tau) := hquot
    _ = lCost F.S b p q tau / (2 * Real.sqrt tau) + A * (-b) := by
      dsimp only [A]
      ring

private theorem exists_terminal_redLength_lt_half_finrank_add
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) {tau eps : ℝ} (htau : 0 < tau) (heps : 0 < eps) :
    ∃ q : F.M, redLength F.S 0 p q tau < (Module.finrank ℝ E : ℝ) / 2 + eps := by
  obtain ⟨C, hC, hcompare⟩ := exists_terminal_redLength_comparison F hF p htau
  have hC1 : 0 < C + 1 := by linarith
  let b : ℝ := -(eps / (C + 1))
  have hb : b < 0 := by
    dsimp only [b]
    exact neg_lt_zero.mpr (div_pos heps hC1)
  obtain ⟨q, hq⟩ := exists_redLength_le_half_finrank_of_ancient_of_neg F hF p hb htau
  refine ⟨q, ?_⟩
  have herr : C * (-b) < eps := by
    dsimp only [b]
    rw [neg_neg, ← mul_div_assoc]
    exact (div_lt_iff₀ hC1).mpr (by nlinarith)
  exact (hcompare b hb.le q).trans_lt (add_lt_add_of_le_of_lt hq herr)

theorem exists_redLength_minimizer_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) {tau : ℝ} (htau : 0 < tau) :
    ∃ q : F.M, ∀ y : F.M, redLength F.S 0 p q tau ≤ redLength F.S 0 p y tau := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : ConnectedSpace F.M := hF.connected
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _ht, x, hx⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) x (by decide : 0 < 4) (F.S.base.rm04 t x) hx⟩
  let f : F.M → ℝ := fun q => redLength F.S 0 p q tau
  let R : ℝ := |4 * tau * f p| + 1
  have hcompact := RiemannianMetricComplete.closedEBall_isCompact (I := I)
    (g := F.S.base.metric 0) ⟨hF.complete 0 (by simp [ancientTimeInterval_carrier])⟩ p R
  apply (continuous_redLength_of_ancient F hF p htau).exists_forall_le' p
  filter_upwards [hcompact.compl_mem_cocompact] with q hq
  by_contra hlt
  have hlt' : f q < f p := lt_of_not_ge hlt
  have hlower := ancient_redLength_ge_terminal_distance_sq F hF le_rfl p q htau
  have hsquare : (riemannianEDistOf (F.S.base.metric 0) p q).toReal ^ 2 ≤
      4 * tau * f p := by
    have := (div_le_iff₀ (show 0 < 4 * tau by positivity)).mp hlower
    change _ ≤ f q * (4 * tau) at this
    nlinarith
  have hdist : (riemannianEDistOf (F.S.base.metric 0) p q).toReal ≤ R := by
    dsimp only [R]
    nlinarith [sq_nonneg ((riemannianEDistOf (F.S.base.metric 0) p q).toReal - 1 / 2),
      le_abs_self (4 * tau * f p)]
  apply hq
  change riemannianEDistOf (F.S.base.metric 0) p q ≤ ENNReal.ofReal R
  rw [← ENNReal.ofReal_toReal (riemannianEDistOf_ne_top (F.S.base.metric 0) p q)]
  exact ENNReal.ofReal_le_ofReal hdist

theorem exists_redLength_le_half_finrank_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) {tau : ℝ} (htau : 0 < tau) :
    ∃ q : F.M, redLength F.S 0 p q tau ≤ (Module.finrank ℝ E : ℝ) / 2 := by
  let _ : ConnectedSpace F.M := hF.connected
  let _ : T2Space (TangentBundle I F.M) := F.t2TangentBundle
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _, x, hx⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) x (by decide : 0 < 4) (F.S.base.rm04 t x) hx⟩
  have hg : RiemannianMetricComplete (I := I) (F.S.base.metric 0) :=
    ⟨hF.complete 0 (by simp only [ancientTimeInterval_carrier, mem_Iic, le_refl])⟩
  let f : F.M → ℝ := fun q => redLength F.S 0 p q tau
  have hf : Continuous f := continuous_redLength_of_ancient F hF p htau
  have hden : 0 < 4 * tau := by positivity
  have hcompact : IsCompact {q : F.M | f q ≤ f p} := by
    refine (hg.closedEBall_isCompact p (Real.sqrt (f p * (4 * tau)))).of_isClosed_subset
      (isClosed_le hf continuous_const) ?_
    intro q hq
    have hlower := ancient_redLength_ge_terminal_distance_sq F hF le_rfl p q htau
    have hsq : (riemannianEDistOf (F.S.base.metric 0) p q).toReal ^ 2 ≤
        f p * (4 * tau) :=
      (div_le_iff₀ hden).mp (hlower.trans hq)
    have hdist := Real.le_sqrt_of_sq_le hsq
    have hfin := riemannianEDistOf_ne_top (F.S.base.metric 0) p q
    change riemannianEDistOf (F.S.base.metric 0) p q ≤
      ENNReal.ofReal (Real.sqrt (f p * (4 * tau)))
    calc
      riemannianEDistOf (F.S.base.metric 0) p q =
          ENNReal.ofReal (riemannianEDistOf (F.S.base.metric 0) p q).toReal :=
        (ENNReal.ofReal_toReal hfin).symm
      _ ≤ ENNReal.ofReal (Real.sqrt (f p * (4 * tau))) :=
        ENNReal.ofReal_le_ofReal hdist
  obtain ⟨q, hq, hmin⟩ := hcompact.exists_isMinOn
    ⟨p, by change f p ≤ f p; exact le_rfl⟩ hf.continuousOn
  have hglobal : ∀ x : F.M, f q ≤ f x := by
    intro x
    by_cases hx : f x ≤ f p
    · exact hmin hx
    · exact hq.trans (lt_of_not_ge hx).le
  refine ⟨q, ?_⟩
  change f q ≤ (Module.finrank ℝ E : ℝ) / 2
  by_contra h
  have heps : 0 < (f q - (Module.finrank ℝ E : ℝ) / 2) / 2 := by linarith
  obtain ⟨x, hx⟩ := exists_terminal_redLength_lt_half_finrank_add F hF p htau heps
  have hqx := hglobal x
  change f x < (Module.finrank ℝ E : ℝ) / 2 +
    (f q - (Module.finrank ℝ E : ℝ) / 2) / 2 at hx
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
