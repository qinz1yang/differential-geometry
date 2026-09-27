import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientAdditiveDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientGeometricCurveEnergy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedCostUpperBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.SquareRootShift
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.DynamicProgramming
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalBounds

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set MeasureTheory CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Manifold ContDiff

private theorem distance_prefix_bound
    {d s r D D0 C R : ℝ} (hd : 0 ≤ d) (hs : 0 < s) (hr : 0 < r)
    (hrsq : r ^ 2 = s ^ 2 - d) (hds : 4 * d ≤ s ^ 2)
    (hD : 0 ≤ D) (hD0 : 0 ≤ D0) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hcompare : D ≤ D0 + C * s ^ 2) :
    D ^ 2 / (2 * r) + 2 * R * r ^ 3 ≤
      2 * (D0 ^ 2 / s) + 2 * (C ^ 2 + R) * s ^ 3 := by
  have hsr : s ≤ 2 * r := by nlinarith
  have hrs : r ≤ s := by nlinarith
  have hnum : D ^ 2 ≤ 2 * D0 ^ 2 + 2 * C ^ 2 * s ^ 4 := by
    have hsquare := (sq_le_sq₀ hD
      (add_nonneg hD0 (mul_nonneg hC (sq_nonneg s)))).mpr hcompare
    nlinarith [sq_nonneg (D0 - C * s ^ 2)]
  have hnum0 : 0 ≤ 2 * D0 ^ 2 + 2 * C ^ 2 * s ^ 4 := by positivity
  have hquot : D ^ 2 / (2 * r) ≤ 2 * (D0 ^ 2 / s) + 2 * C ^ 2 * s ^ 3 := by
    calc
      D ^ 2 / (2 * r) ≤ (2 * D0 ^ 2 + 2 * C ^ 2 * s ^ 4) / (2 * r) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (2 * D0 ^ 2 + 2 * C ^ 2 * s ^ 4) / s :=
        div_le_div_of_nonneg_left hnum0 hs hsr
      _ = _ := by field_simp [hs.ne']
  have hcube : r ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ hr.le hrs 3
  have hscalar := mul_le_mul_of_nonneg_left hcube
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hR)
  nlinarith [hquot, hscalar]

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact

private theorem lCost_le_mul_action_add_of_distance_bound
    {kappa C R : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hC : 0 ≤ C) (hR : PointedFlowScalarBounded F R)
    (hdistance : ∀ s : ℝ, 0 ≤ s → ∀ x y : F.M,
      (riemannianEDistOf (F.S.base.metric (-(s ^ 2))) x y).toReal ≤
        (riemannianEDistOf (F.S.base.metric 0) x y).toReal + C * s ^ 2)
    {d L c : ℝ} (hd : 0 < d) (hL : 0 < L) (hdL : 4 * d ≤ L ^ 2)
    (n : ℕ) (hc : L * (4 : ℝ) ^ n < c)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha) :
    lCost F.S (-d) (alpha 0) (alpha c) (c ^ 2 - d) ≤
      (1 + 16 / (n + 1 : ℝ)) * lRegularizedAction F.S 0 alpha 0 c +
        2 * (C ^ 2 + R) * (L * (4 : ℝ) ^ n) ^ 3 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : ConnectedSpace F.M := hF.connected
  let _ : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let _ : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  have hR0 : 0 ≤ R :=
    (hR 0 (by simp only [ancientTimeInterval_carrier, mem_Iic, le_refl]) (alpha 0)).1.trans
      (hR 0 (by simp only [ancientTimeInterval_carrier, mem_Iic, le_refl]) (alpha 0)).2
  have hpow (j : ℕ) : 1 ≤ (4 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hcnonneg : 0 < c := (mul_pos hL (pow_pos (by norm_num) n)).trans hc
  obtain ⟨j, hj, hsmall⟩ := exists_ancientKappa_riemannianEDist_sq_div_le_action
    F hF alpha halpha hL n hc.le
  let s : ℝ := L * (4 : ℝ) ^ j
  let r : ℝ := Real.sqrt (s ^ 2 - d)
  let b : ℝ := Real.sqrt (c ^ 2 - d)
  let tail : ℝ → F.M := fun t => alpha (Real.sqrt (t ^ 2 + d))
  have hLs : L ≤ s := by
    simpa only [mul_one, s] using mul_le_mul_of_nonneg_left (hpow j) hL.le
  have hs : 0 < s := hL.trans_le hLs
  have hsmax : s ≤ L * (4 : ℝ) ^ n :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hj) hL.le
  have hsc : s < c := hsmax.trans_lt hc
  have hds : 4 * d ≤ s ^ 2 := hdL.trans ((sq_le_sq₀ hL.le hs.le).mpr hLs)
  have hrad : 0 < s ^ 2 - d := by nlinarith
  have hr : 0 < r := Real.sqrt_pos.mpr hrad
  have hrsq : r ^ 2 = s ^ 2 - d := Real.sq_sqrt hrad.le
  have hbrad : 0 < c ^ 2 - d := by nlinarith
  have hb : 0 < b := Real.sqrt_pos.mpr hbrad
  have hbsq : b ^ 2 = c ^ 2 - d := Real.sq_sqrt hbrad.le
  have hrb : r < b := by
    apply Real.sqrt_lt_sqrt hrad.le
    nlinarith
  have hclock : ContDiff ℝ 1 (fun t : ℝ => Real.sqrt (t ^ 2 + d)) :=
    ((contDiff_id.pow 2).add contDiff_const).sqrt (fun t => by positivity)
  have htail : ContMDiff 𝓘(ℝ, ℝ) I 1 tail := halpha.comp hclock.contMDiff
  have hstartr : tail r = alpha s := by
    dsimp only [tail]
    rw [hrsq, sub_add_cancel, Real.sqrt_sq hs.le]
  have hendb : tail b = alpha c := by
    dsimp only [tail]
    rw [hbsq, sub_add_cancel, Real.sqrt_sq hcnonneg.le]
  obtain ⟨K, hK⟩ := ancientKappa_rmNormSqBounded_finrank F hF
  have hjoin := lCost_le_add_lRegularizedAction_of_curvature_bound_on_carrier
    F.S F.isSolution K (-d) hr hrb
    (fun t ht => ht.2.trans (neg_nonpos.mpr hd.le))
    (fun t ht x => hK t (ht.2.trans (neg_nonpos.mpr hd.le)) x)
    (alpha 0) tail htail
  rw [hstartr, hendb, hbsq] at hjoin
  have hprefix := ancient_lCost_le_earlier_distance_sq_div_add F hF hR
    (T := -d) (neg_nonpos.mpr hd.le) hr (alpha 0) (alpha s)
  have htime : -d - r ^ 2 = -(s ^ 2) := by rw [hrsq]; ring
  rw [htime] at hprefix
  have hdist := hdistance s hs.le (alpha 0) (alpha s)
  have hnumeric := distance_prefix_bound hd.le hs hr hrsq hds
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg hC hR0 hdist
  have hprefix' : lCost F.S (-d) (alpha 0) (alpha s) (r ^ 2) ≤
      2 * ((riemannianEDistOf (F.S.base.metric 0) (alpha 0) (alpha s)).toReal ^ 2 / s) +
        2 * (C ^ 2 + R) * s ^ 3 := hprefix.trans hnumeric
  have htailBound := lRegularizedAction_sqrt_add_sq_le F.S F.isSolution hd hr hrb.le
    (by intro t _; change -d - t ^ 2 ≤ 0; linarith [sq_nonneg t])
    (fun t _ x => (hR _ (show -d - t ^ 2 ≤ 0 by linarith [sq_nonneg t]) x).1)
    alpha halpha
  have hrsqrt : Real.sqrt (r ^ 2 + d) = s := by rw [hrsq, sub_add_cancel, Real.sqrt_sq hs.le]
  have hbsqrt : Real.sqrt (b ^ 2 + d) = c := by rw [hbsq, sub_add_cancel, Real.sqrt_sq hcnonneg.le]
  rw [hrsqrt, hbsqrt] at htailBound
  have hcont : ContinuousOn (lRegularizedLagrangian F.S 0 alpha) (Icc 0 c) := by
    apply (lRegularizedLagrangian_continuousOn_carrier F.S F.isSolution alpha halpha).comp
      (continuous_const.prodMk continuous_id).continuousOn
    intro t _
    exact sub_nonpos.mpr (sq_nonneg t)
  have htailLe : lRegularizedAction F.S 0 alpha s c ≤ lRegularizedAction F.S 0 alpha 0 c := by
    apply intervalIntegral.integral_mono_interval hs.le hsc.le le_rfl
    · apply Filter.Eventually.of_forall
      intro t
      unfold lRegularizedLagrangian
      exact add_nonneg (mul_nonneg (by norm_num) (metric_inner_self_nonneg _ _ _))
        (mul_nonneg (by positivity) (hR _ (sub_nonpos.mpr (sq_nonneg t)) (alpha t)).1)
    · exact hcont.intervalIntegrable_of_Icc hcnonneg.le
  have hscaled := mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 2)
  have hcube := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.le hsmax 3)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (add_nonneg (sq_nonneg C) hR0))
  have hpreFinal : lCost F.S (-d) (alpha 0) (alpha s) (r ^ 2) ≤
      16 * lRegularizedAction F.S 0 alpha 0 c / (n + 1 : ℝ) +
        2 * (C ^ 2 + R) * (L * (4 : ℝ) ^ n) ^ 3 := by
    apply hprefix'.trans
    change 2 * ((riemannianEDistOf (F.S.base.metric 0) (alpha 0) (alpha s)).toReal ^ 2 / s) ≤
      2 * (8 * lRegularizedAction F.S 0 alpha 0 c / (n + 1 : ℝ)) at hscaled
    exact (add_le_add hscaled hcube).trans_eq (by ring)
  exact hjoin.trans ((add_le_add hpreFinal (htailBound.trans htailLe)).trans_eq (by ring))


theorem exists_ancientKappa_lCost_shift_le_mul_terminal_add
    (hdim : 2 ≤ Module.finrank ℝ E) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ d L tau : ℝ, ∀ n : ℕ,
      0 < d → 0 < L → 4 * d ≤ L ^ 2 → (L * (4 : ℝ) ^ n) ^ 2 < tau →
      ∀ p q : F.M,
      lCost F.S (-d) p q (tau - d) ≤
        (1 + 16 / (n + 1 : ℝ)) * lCost F.S 0 p q tau +
          B * (L * (4 : ℝ) ^ n) ^ 3 := by
  let _ : ConnectedSpace F.M := hF.connected
  obtain ⟨C, hC, hdist⟩ := exists_ancientKappa_riemannianEDist_sub_le F hdim hF
  obtain ⟨R, hR⟩ := hF.globalScalarBound
  have hR0 : 0 ≤ R :=
    (hR 0 (by simp only [ancientTimeInterval_carrier, mem_Iic, le_refl]) F.basepoint).1.trans
      (hR 0 (by simp only [ancientTimeInterval_carrier, mem_Iic, le_refl]) F.basepoint).2
  refine ⟨2 * (C ^ 2 + R), by positivity, ?_⟩
  intro d L tau n hd hL hdL htau p q
  have htaupos : 0 < tau := lt_of_le_of_lt (sq_nonneg _) htau
  have hc : L * (4 : ℝ) ^ n < Real.sqrt tau := Real.lt_sqrt_of_sq_lt htau
  have hfactor : 0 < 1 + 16 / (n + 1 : ℝ) := by positivity
  by_contra! hnot
  have hthreshold : lCost F.S 0 p q tau <
      (lCost F.S (-d) p q (tau - d) -
        (2 * (C ^ 2 + R)) * (L * (4 : ℝ) ^ n) ^ 3) /
          (1 + 16 / (n + 1 : ℝ)) := by
    apply (lt_div_iff₀ hfactor).mpr
    nlinarith
  obtain ⟨alpha, halpha, hstart, hend, hsmall⟩ :=
    exists_lRegularizedAction_lt_of_lCost_lt_of_preconnected F.S 0 p q tau htaupos _ hthreshold
  have hcompare := lCost_le_mul_action_add_of_distance_bound F hF hC hR
    (fun s _ x y => by
      have h := (hdist (-(s ^ 2)) 0 (neg_nonpos.mpr (sq_nonneg s)) le_rfl x y).2
      simpa only [zero_sub, neg_neg, sub_le_iff_le_add, add_comm] using h)
    hd hL hdL n hc alpha halpha
  rw [hstart, hend, Real.sq_sqrt htaupos.le] at hcompare
  have hstrict := (lt_div_iff₀ hfactor).mp hsmall
  nlinarith [hcompare, hstrict]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
