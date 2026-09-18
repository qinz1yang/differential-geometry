import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCostBaseTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCostContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedDensityGaussian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleCenters
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance terminalCenterTopology : TopologicalSpace F.M := F.topology
private local instance terminalCenterCharted : ChartedSpace H F.M := F.charted
private local instance terminalCenterSmooth : IsManifold I ∞ F.M := F.smooth
private local instance terminalCenterT2 : T2Space F.M := F.t2
private local instance terminalCenterTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle
private local instance terminalCenterSigma : SigmaCompactSpace F.M := F.sigmaCompact

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
  obtain ⟨q, hmin⟩ := exists_redLength_minimizer_of_ancient F hF p htau
  obtain ⟨C, _hC, hbound⟩ := exists_lCost_base_time_bound_of_ancient F hF
  refine ⟨q, ?_⟩
  have hle (n : ℕ) : redLength F.S 0 p q tau ≤
      (Module.finrank ℝ E : ℝ) / 2 + tau * C * (1 / ((n : ℝ) + 1)) := by
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hb : -1 / ((n : ℝ) + 1) < 0 := div_neg_of_neg_of_pos (by norm_num) hn
    obtain ⟨y, hy⟩ := exists_redLength_le_half_finrank_of_ancient_of_neg F hF p hb htau
    have hc := hbound hb.le le_rfl htau p y
    have hquot := div_le_div_of_nonneg_right hc
      (show 0 ≤ 2 * Real.sqrt tau by positivity)
    have herr : (2 * Real.sqrt tau ^ 3 * C * (0 - (-1 / ((n : ℝ) + 1)))) /
        (2 * Real.sqrt tau) = tau * C * (1 / ((n : ℝ) + 1)) := by
      rw [show Real.sqrt tau ^ 3 = tau * Real.sqrt tau by
        rw [pow_succ, Real.sq_sqrt htau.le]]
      field_simp
      ring
    rw [add_div, herr] at hquot
    exact (hmin y).trans (hquot.trans (add_le_add hy le_rfl))
  have hlim : Tendsto (fun n : ℕ => (Module.finrank ℝ E : ℝ) / 2 +
      tau * C * (1 / ((n : ℝ) + 1))) atTop (nhds ((Module.finrank ℝ E : ℝ) / 2)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  exact ge_of_tendsto' hlim hle

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
