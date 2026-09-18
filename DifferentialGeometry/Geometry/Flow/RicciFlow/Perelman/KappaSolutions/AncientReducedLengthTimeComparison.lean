import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSqrtLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientPrefix
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalEnergy

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Bundle Set MeasureTheory
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] in
private theorem curveEnergy_le_action
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    curveEnergy (F.S.base.metric (-(a ^ 2))) alpha a b ≤
      2 * lRegularizedAction F.S 0 alpha 0 b := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hscalar (r : ℝ) : 0 ≤ F.S.scalar (0 - r ^ 2) (alpha r) := by
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    exact (hC _ (by change (0 : ℝ) - r ^ 2 ≤ 0; nlinarith [sq_nonneg r]) _).1
  have hlag (r : ℝ) : 0 ≤ lRegularizedLagrangian F.S 0 alpha r := by
    change 0 ≤ (1 / 2 : ℝ) * lRegularizedSpeedSq F.S 0 alpha r +
      2 * r ^ 2 * F.S.scalar (0 - r ^ 2) (alpha r)
    exact add_nonneg (mul_nonneg (by norm_num) (lRegularizedSpeedSq_nonneg F.S 0 alpha r))
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg r)) (hscalar r))
  have hcont : ContinuousOn (lRegularizedLagrangian F.S 0 alpha) (Icc 0 b) := by
    apply (lRegularizedLagrangian_continuousOn_carrier F.S F.isSolution alpha halpha).comp
      (continuous_const.prodMk continuous_id).continuousOn
    intro r _
    change (0 : ℝ) - r ^ 2 ≤ 0
    nlinarith [sq_nonneg r]
  have hLag : IntervalIntegrable (lRegularizedLagrangian F.S 0 alpha) volume 0 b :=
    hcont.intervalIntegrable_of_Icc (ha.trans hab)
  have hLagTail : IntervalIntegrable (lRegularizedLagrangian F.S 0 alpha) volume a b :=
    (hcont.mono (Icc_subset_Icc ha le_rfl)).intervalIntegrable_of_Icc hab
  have hEint : IntervalIntegrable (fun r => (F.S.base.metric (-(a ^ 2))).inner (alpha r)
      (lVelocity (I := I) alpha r) (lVelocity (I := I) alpha r)) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact integrableOn_riemannianMetric_inner_lVelocity_self_of_contMDiff_one
      (F.S.base.metric (-(a ^ 2))) alpha halpha a b
  have hpoint : ∀ r ∈ Icc a b,
      (F.S.base.metric (-(a ^ 2))).inner (alpha r)
        (lVelocity (I := I) alpha r) (lVelocity (I := I) alpha r) ≤
      2 * lRegularizedLagrangian F.S 0 alpha r := by
    intro r hr
    have hm := ancientModel_metric_inner_antitoneOn F hF (alpha r) (lVelocity alpha r)
      (neg_nonpos.mpr (sq_nonneg r)) (neg_nonpos.mpr (sq_nonneg a))
      (neg_le_neg ((sq_le_sq₀ ha (ha.trans hr.1)).mpr hr.1))
    change (F.S.base.metric (-(a ^ 2))).inner (alpha r) _ _ ≤
      2 * ((1 / 2 : ℝ) * lRegularizedSpeedSq F.S 0 alpha r +
        2 * r ^ 2 * F.S.scalar (0 - r ^ 2) (alpha r))
    have hm' : (F.S.base.metric (-(a ^ 2))).inner (alpha r)
        (lVelocity alpha r) (lVelocity alpha r) ≤ lRegularizedSpeedSq F.S 0 alpha r := by
      simpa only [lRegularizedSpeedSq, zero_sub] using hm
    nlinarith [mul_nonneg (sq_nonneg r) (hscalar r)]
  have hint := intervalIntegral.integral_mono_on hab hEint (hLagTail.const_mul 2) hpoint
  rw [intervalIntegral.integral_const_mul] at hint
  have haction : lRegularizedAction F.S 0 alpha a b ≤ lRegularizedAction F.S 0 alpha 0 b :=
    intervalIntegral.integral_mono_interval ha hab le_rfl (Filter.Eventually.of_forall hlag) hLag
  exact hint.trans (mul_le_mul_of_nonneg_left haction (by norm_num))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem redLength_le_of_backward_time_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {s tau A : ℝ} (hs : 0 < s) (hst : s ≤ tau)
    (hbase : redLength F.S 0 p q tau ≤ A) :
    redLength F.S 0 p q s ≤ (1 + Real.sqrt 3) ^ 2 * (tau / s) * A := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _ht, z, hz⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) z (by norm_num : 0 < 4) _ hz⟩
  have htau := hs.trans_le hst
  have hnonneg (r : ℝ) (hr : 0 < r) : 0 ≤ redLength F.S 0 p q r := by
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    apply div_nonneg _ (by positivity)
    apply lCost_nonneg_of_scalar_nonneg F.S 0 hr.le
    intro t ht y
    simpa only [zero_sub] using (hC (-t) (neg_nonpos.mpr ht.1) y).1
  have hA : 0 ≤ A := (hnonneg tau htau).trans hbase
  let a := Real.sqrt s
  let b := Real.sqrt tau
  have ha : 0 < a := Real.sqrt_pos.mpr hs
  have hb : 0 < b := Real.sqrt_pos.mpr htau
  have hab : a ≤ b := Real.sqrt_le_sqrt hst
  have ha2 : a ^ 2 = s := Real.sq_sqrt hs.le
  have hb2 : b ^ 2 = tau := Real.sq_sqrt htau.le
  have hr : 1 ≤ b / a := (le_div_iff₀ ha).mpr (by simpa using hab)
  obtain ⟨alpha, halpha, hstart, hend, _hgeo, hcost⟩ :=
    exists_lRegularized_minimizer_of_ancient F hF p q htau
  have hprefix : redLength F.S 0 p (alpha a) s ≤ b / a * A :=
    (redLength_prefix_le_of_ancient_action_eq_lCost F hF alpha halpha p q
      hs hst hstart hend hcost).trans (mul_le_mul_of_nonneg_left hbase (by positivity))
  have hrootPrefix : Real.sqrt (redLength F.S 0 p (alpha a) s) ≤ b / a * Real.sqrt A := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, hprefix.trans ?_⟩
    rw [mul_pow, Real.sq_sqrt hA]
    have hh : b / a ≤ (b / a) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hh hA
  have hfull : lRegularizedAction F.S 0 alpha 0 b ≤ 2 * b * A := by
    have hbound := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hb)).mp hbase
    change lCost F.S 0 p q tau ≤ A * (2 * b) at hbound
    rw [hcost, hend]
    nlinarith
  have henergy : curveEnergy (F.S.base.metric (-s)) alpha a b ≤ 4 * b * A := by
    have h := (curveEnergy_le_action F hF alpha halpha ha.le hab).trans
      (mul_le_mul_of_nonneg_left hfull (by norm_num : (0 : ℝ) ≤ 2))
    simpa only [ha2] using h.trans_eq (by ring)
  have hE := integrableOn_riemannianMetric_inner_lVelocity_self_of_contMDiff_one
    (F.S.base.metric (-s)) alpha halpha a b
  have hdist := edistOf_le_budget (F.S.base.metric (-s)) hab halpha.contMDiffOn hE henergy
  have hbudget : Real.sqrt (b - a) * Real.sqrt (4 * b * A) ≤ 2 * b * Real.sqrt A := by
    calc
      _ ≤ Real.sqrt b * Real.sqrt (4 * b * A) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
      _ = Real.sqrt (b ^ 2 * (4 * A)) := by rw [← Real.sqrt_mul hb.le]; congr 1; ring
      _ = 2 * b * Real.sqrt A := by
        rw [Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb.le,
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
        ring
  have hreal : (riemannianEDistOf (F.S.base.metric (-s)) (alpha a) q).toReal ≤
      2 * b * Real.sqrt A := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (hdist.trans (ENNReal.ofReal_le_ofReal hbudget))
    rw [ENNReal.toReal_ofReal (by positivity), hend] at h
    exact h
  have hroot := sqrt_redLength_sub_le_distance_of_continuous_and_minimizers F hF p (alpha a) q hs
    (continuous_redLength_of_ancient F hF p hs)
    (fun y => exists_lRegularized_minimizer_of_ancient F hF p y hs)
  have hbound : Real.sqrt (redLength F.S 0 p q s) ≤
      (1 + Real.sqrt 3) * (b / a) * Real.sqrt A := by
    calc
      _ ≤ b / a * Real.sqrt A + Real.sqrt 3 / (2 * a) * (2 * b * Real.sqrt A) :=
        hroot.trans (add_le_add hrootPrefix
          (mul_le_mul_of_nonneg_left hreal (by positivity)))
      _ = _ := by field_simp
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg (redLength F.S 0 p q s))
    (by positivity : 0 ≤ (1 + Real.sqrt 3) * (b / a) * Real.sqrt A)).mpr hbound
  rw [Real.sq_sqrt (hnonneg s hs), mul_pow, mul_pow, div_pow, ha2, hb2, Real.sq_sqrt hA] at hsq
  exact hsq

theorem scalar_le_on_past_of_redLength_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {s tau A t : ℝ} (hs : 0 < s) (hst : s ≤ tau)
    (hbase : redLength F.S 0 p q tau ≤ A) (ht : t ≤ -s) :
    s ^ 2 * F.S.scalar t q ≤ 3 * (1 + Real.sqrt 3) ^ 2 * tau * A := by
  have hlength := redLength_le_of_backward_time_le F hF p q hs hst hbase
  have hscalar := (le_div_iff₀ hs).mp
    (scalar_le_three_mul_redLength_div_of_ancient F hF p q hs)
  have hmono := ancientKappa_scalar_monotoneOn F hF q
    (ht.trans (neg_nonpos.mpr hs.le)) (neg_nonpos.mpr hs.le) ht
  calc
    s ^ 2 * F.S.scalar t q ≤ s ^ 2 * F.S.scalar (-s) q :=
      mul_le_mul_of_nonneg_left hmono (sq_nonneg s)
    _ ≤ 3 * s * redLength F.S 0 p q s := by
      nlinarith [mul_le_mul_of_nonneg_left hscalar hs.le]
    _ ≤ 3 * s * ((1 + Real.sqrt 3) ^ 2 * (tau / s) * A) :=
      mul_le_mul_of_nonneg_left hlength (by positivity)
    _ = 3 * (1 + Real.sqrt 3) ^ 2 * tau * A := by field_simp

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
