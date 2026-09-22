import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSqrtLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientPrefix
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalEnergy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedLengthHamiltonJacobi

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Bundle Set MeasureTheory
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff
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

omit [I.Boundaryless] in
private theorem time_length_nonneg
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {tau : ℝ} (htau : 0 < tau) : 0 ≤ redLength F.S 0 p q tau := by
  obtain ⟨B, hB⟩ := hF.globalScalarBound
  apply div_nonneg _ (by positivity)
  apply lCost_nonneg_of_scalar_nonneg F.S 0 htau.le
  intro t ht y
  simpa only [zero_sub] using (hB (-t) (neg_nonpos.mpr ht.1) y).1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem curveEnergy_le_length_mul_action
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hgeo : IsLRegularizedGeodesicOn F.S 0 alpha (Ioo 0 b)) :
    curveEnergy (F.S.base.metric (-(a ^ 2))) alpha a b ≤
      (b - a) * (6 * lRegularizedAction F.S 0 alpha 0 b / a) := by
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
    hcont.intervalIntegrable_of_Icc (ha.le.trans hab)
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
      (neg_le_neg ((sq_le_sq₀ ha.le (ha.le.trans hr.1)).mpr hr.1))
    change (F.S.base.metric (-(a ^ 2))).inner (alpha r) _ _ ≤
      2 * ((1 / 2 : ℝ) * lRegularizedSpeedSq F.S 0 alpha r +
        2 * r ^ 2 * F.S.scalar (0 - r ^ 2) (alpha r))
    have hm' : (F.S.base.metric (-(a ^ 2))).inner (alpha r)
        (lVelocity alpha r) (lVelocity alpha r) ≤ lRegularizedSpeedSq F.S 0 alpha r := by
      simpa only [lRegularizedSpeedSq, zero_sub] using hm
    nlinarith [mul_nonneg (sq_nonneg r) (hscalar r)]
  have hupper : ∀ r ∈ Icc a b,
      (F.S.base.metric (-(a ^ 2))).inner (alpha r)
        (lVelocity (I := I) alpha r) (lVelocity (I := I) alpha r) ≤
      6 * lRegularizedAction F.S 0 alpha 0 b / a := by
    intro r hr
    have hr0 := ha.le.trans hr.1
    have hendpoint := lRegularizedLagrangian_mul_le_three_mul_action_of_ancientKappa
      F hF alpha halpha hr0 (fun t ht => hgeo t ⟨ht.1, ht.2.trans_le hr.2⟩)
    have hprefix : lRegularizedAction F.S 0 alpha 0 r ≤
        lRegularizedAction F.S 0 alpha 0 b :=
      intervalIntegral.integral_mono_interval le_rfl hr0 hr.2
        (Filter.Eventually.of_forall hlag) hLag
    have hmul := mul_le_mul_of_nonneg_left (hpoint r hr) ha.le
    have htime := mul_le_mul_of_nonneg_right hr.1 (hlag r)
    apply (le_div_iff₀ ha).mpr
    nlinarith
  have hint := intervalIntegral.integral_mono_on hab hEint
    (intervalIntegrable_const (c := 6 * lRegularizedAction F.S 0 alpha 0 b / a)) hupper
  simpa only [intervalIntegral.integral_const, smul_eq_mul, curveEnergy, lVelocity] using hint

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem sqrt_redLength_le_of_backward_time_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {s tau A : ℝ} (hs : 0 < s) (hst : s ≤ tau)
    (hbase : redLength F.S 0 p q tau ≤ A) :
    Real.sqrt (redLength F.S 0 p q s) ≤
      Real.sqrt tau / Real.sqrt s * Real.sqrt A +
        Real.sqrt 3 / (2 * Real.sqrt s) *
          ((Real.sqrt tau - Real.sqrt s) * Real.sqrt (12 * Real.sqrt tau * A / Real.sqrt s)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _ht, z, hz⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) z (by norm_num : 0 < 4) _ hz⟩
  have htau := hs.trans_le hst
  have hnonneg (r : ℝ) (hr : 0 < r) : 0 ≤ redLength F.S 0 p q r :=
    time_length_nonneg F hF p q hr
  have hA : 0 ≤ A := (hnonneg tau htau).trans hbase
  let a := Real.sqrt s
  let b := Real.sqrt tau
  have ha : 0 < a := Real.sqrt_pos.mpr hs
  have hb : 0 < b := Real.sqrt_pos.mpr htau
  have hab : a ≤ b := Real.sqrt_le_sqrt hst
  have ha2 : a ^ 2 = s := Real.sq_sqrt hs.le
  have hr : 1 ≤ b / a := (le_div_iff₀ ha).mpr (by simpa using hab)
  obtain ⟨alpha, halpha, hstart, hend, hgeo, hcost⟩ :=
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
  have henergy : curveEnergy (F.S.base.metric (-s)) alpha a b ≤
      (b - a) * (12 * b * A / a) := by
    have h := curveEnergy_le_length_mul_action F hF alpha halpha ha hab
      (fun r hr => hgeo r ⟨hr.1, hr.2.le⟩)
    rw [ha2] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hab)
    apply div_le_div_of_nonneg_right _ ha.le
    nlinarith only [hfull]
  have hE := integrableOn_riemannianMetric_inner_lVelocity_self_of_contMDiff_one
    (F.S.base.metric (-s)) alpha halpha a b
  have hdist := edistOf_le_budget (F.S.base.metric (-s)) hab halpha.contMDiffOn hE henergy
  have hreal : (riemannianEDistOf (F.S.base.metric (-s)) (alpha a) q).toReal ≤
      (b - a) * Real.sqrt (12 * b * A / a) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdist
    rw [ENNReal.toReal_ofReal (by positivity), hend] at h
    simpa only [Real.sqrt_mul (sub_nonneg.mpr hab), ← mul_assoc,
      Real.mul_self_sqrt (sub_nonneg.mpr hab)] using h
  have hroot := sqrt_redLength_sub_le_distance_of_continuous_and_minimizers F hF p (alpha a) q hs
    (continuous_redLength_of_ancient F hF p hs)
    (fun y => exists_lRegularized_minimizer_of_ancient F hF p y hs)
  exact hroot.trans (add_le_add hrootPrefix
    (mul_le_mul_of_nonneg_left hreal (by positivity)))

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

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Set Filter MeasureTheory
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact

private theorem redLength_le_of_backward_time_ge_of_innerProductSpace
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {s tau : ℝ} (hs : 0 < s) (hst : s ≤ tau) :
    redLength F.S 0 p q tau ≤
      (Real.sqrt s / Real.sqrt tau +
        3 * Real.sqrt tau * (Real.sqrt tau - Real.sqrt s) / s) * redLength F.S 0 p q s := by
  obtain rfl | hst := hst.eq_or_lt
  · have hroot : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
    simp only [div_self hroot, sub_self, mul_zero, zero_div, add_zero, one_mul, le_refl]
  have htau := hs.trans hst
  let a := Real.sqrt s
  let b := Real.sqrt tau
  have ha : 0 < a := Real.sqrt_pos.mpr hs
  have hb : 0 < b := Real.sqrt_pos.mpr htau
  have hab : a < b := Real.sqrt_lt_sqrt hs.le hst
  have ha2 : a ^ 2 = s := Real.sq_sqrt hs.le
  have hb2 : b ^ 2 = tau := Real.sq_sqrt htau.le
  let alpha : ℝ → F.M := fun _ => q
  have halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha := contMDiff_const
  have hcost := ancient_lCost_terminal_le_add_lRegularizedAction F hF ha hab p alpha halpha
  change lCost F.S 0 p q (b ^ 2) ≤ lCost F.S 0 p q (a ^ 2) +
    lRegularizedAction F.S 0 alpha a b at hcost
  rw [ha2, hb2] at hcost
  have hR := scalar_le_three_mul_redLength_div_of_ancient F hF p q hs
  have hnonneg : 0 ≤ 3 * redLength F.S 0 p q s / s := by
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    exact (hC (-s) (neg_nonpos.mpr hs.le) q).1.trans hR
  have hlag : Continuous (lRegularizedLagrangian F.S 0 alpha) := by
    have h := lRegularizedLagrangian_continuousOn_carrier F.S F.isSolution alpha halpha
    exact h.comp_continuous (continuous_const.prodMk continuous_id)
      (fun r => by change (0 : ℝ) - r ^ 2 ≤ 0; nlinarith [sq_nonneg r])
  have hupper (r : ℝ) (hr : r ∈ Icc a b) :
      lRegularizedLagrangian F.S 0 alpha r ≤ 2 * tau * (3 * redLength F.S 0 p q s / s) := by
    have hr0 : 0 ≤ r := ha.le.trans hr.1
    have hrs : s ≤ r ^ 2 := by rw [← ha2]; exact pow_le_pow_left₀ ha.le hr.1 2
    have hrt : r ^ 2 ≤ tau := by rw [← hb2]; exact pow_le_pow_left₀ hr0 hr.2 2
    have hscalar : F.S.scalar (-(r ^ 2)) q ≤ 3 * redLength F.S 0 p q s / s :=
      (ancientKappa_scalar_monotoneOn F hF q (neg_nonpos.mpr (sq_nonneg r))
        (neg_nonpos.mpr hs.le) (neg_le_neg hrs)).trans hR
    have heq : lRegularizedLagrangian F.S 0 alpha r = 2 * r ^ 2 * F.S.scalar (-(r ^ 2)) q := by
      simp only [lRegularizedLagrangian, lVelocity, alpha, mfderiv_const, zero_sub]
      have hz : (F.S.base.metric (-(r ^ 2))).inner q
          (0 : TangentSpace I q) 0 = 0 := ((F.S.base.metric (-(r ^ 2))).inner q 0).map_zero
      change (1 / 2 : ℝ) * (F.S.base.metric (-(r ^ 2))).inner q 0 0 +
        2 * r ^ 2 * F.S.scalar (-(r ^ 2)) q = _
      rw [hz, mul_zero, zero_add]
    rw [heq]
    exact (mul_le_mul_of_nonneg_left hscalar (by positivity)).trans
      (mul_le_mul_of_nonneg_right (by linarith) hnonneg)
  have hint := intervalIntegral.integral_mono_on hab.le (hlag.intervalIntegrable (μ := volume) a b)
    (intervalIntegrable_const (c := 2 * tau * (3 * redLength F.S 0 p q s / s))) hupper
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have hbound := hcost.trans (add_le_add le_rfl hint)
  have hLs : lCost F.S 0 p q s = 2 * a * redLength F.S 0 p q s := by
    unfold redLength
    change lCost F.S 0 p q s = 2 * a * (lCost F.S 0 p q s / (2 * a))
    field_simp
  calc
    redLength F.S 0 p q tau = lCost F.S 0 p q tau / (2 * b) := rfl
    _ ≤ (lCost F.S 0 p q s + (b - a) * (2 * tau * (3 * redLength F.S 0 p q s / s))) /
        (2 * b) := div_le_div_of_nonneg_right hbound (by positivity)
    _ = _ := by
      rw [hLs]
      change (2 * a * redLength F.S 0 p q s +
        (b - a) * (2 * tau * (3 * redLength F.S 0 p q s / s))) / (2 * b) =
        (a / b + 3 * b * (b - a) / s) * redLength F.S 0 p q s
      rw [← hb2]
      field_simp

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open scoped _root_.Manifold ContDiff
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact

theorem redLength_le_of_backward_time_ge
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {s tau : ℝ} (hs : 0 < s) (hst : s ≤ tau) :
    redLength F.S 0 p q tau ≤
      (Real.sqrt s / Real.sqrt tau +
        3 * Real.sqrt tau * (Real.sqrt tau - Real.sqrt s) / s) * redLength F.S 0 p q s := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean
  let J := I.transContinuousLinearEquiv e
  let Phi : F.M ≃ₘ⟮I, J⟯ F.M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I F.M e
  let G := F.pullback Phi.symm
  have hG : IsAncientKappaSolution kappa G := F.pullback_isAncientKappaSolution Phi.symm hF
  have h := redLength_le_of_backward_time_ge_of_innerProductSpace G hG p q hs hst
  change redLength (F.S.pullback Phi.symm) 0 p q tau ≤
    (Real.sqrt s / Real.sqrt tau +
      3 * Real.sqrt tau * (Real.sqrt tau - Real.sqrt s) / s) *
        redLength (F.S.pullback Phi.symm) 0 p q s at h
  have hp : Phi.symm p = p := rfl
  have hq : Phi.symm q = q := rfl
  simpa only [redLength, lCost_pullback, hp, hq] using h

private theorem sqrt_ratio_bounds {tau s t T : ℝ} (htau : 0 < tau)
    (hs : 1 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    1 ≤ Real.sqrt (tau * t) / Real.sqrt (tau * s) ∧
      Real.sqrt (tau * t) / Real.sqrt (tau * s) ≤ T ∧
      Real.sqrt (tau * t) / Real.sqrt (tau * s) - 1 ≤ t - s := by
  let a := Real.sqrt (tau * s)
  let b := Real.sqrt (tau * t)
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have ht0 : 0 < t := hs0.trans_le hst
  have hT : 1 ≤ T := hs.trans (hst.trans ht)
  have ha : 0 < a := Real.sqrt_pos.mpr (mul_pos htau hs0)
  have hb : 0 < b := Real.sqrt_pos.mpr (mul_pos htau ht0)
  have hab : a ≤ b := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hst htau.le)
  have ha2 : a ^ 2 = tau * s := Real.sq_sqrt (mul_pos htau hs0).le
  have hb2 : b ^ 2 = tau * t := Real.sq_sqrt (mul_pos htau ht0).le
  change 1 ≤ b / a ∧ b / a ≤ T ∧ b / a - 1 ≤ t - s
  refine ⟨(le_div_iff₀ ha).mpr (by simpa using hab), ?_, ?_⟩
  · apply (div_le_iff₀ ha).mpr
    have hT2 : T ≤ T ^ 2 := by nlinarith
    have hstT : t ≤ T ^ 2 * s := ht.trans (hT2.trans
      (by nlinarith [mul_nonneg (sq_nonneg T) (sub_nonneg.mpr hs)]))
    have hsq := mul_le_mul_of_nonneg_left hstT htau.le
    have hprod : 0 ≤ T * a := mul_nonneg (zero_le_one.trans hT) ha.le
    nlinarith only [ha2, hb2, hsq, hprod, hb.le]
  · have hdelta : 0 ≤ t - s := sub_nonneg.mpr hst
    have htauA : tau ≤ a ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right htauA hdelta
    have hgap : a * (b - a) ≤ tau * (t - s) := by
      nlinarith only [ha2, hb2, mul_nonneg (sub_nonneg.mpr hab) hb.le]
    have hgap' : b - a ≤ a * (t - s) := by
      nlinarith only [hmul, hgap, ha]
    have hdiv : b / a ≤ (t - s) + 1 := (div_le_iff₀ ha).mpr (by nlinarith)
    linarith

theorem redLength_le_mul_on_rescaled_time_interval
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {tau T t : ℝ} (htau : 0 < tau)
    (ht : t ∈ Set.Icc 1 T) :
    redLength F.S 0 p q (tau * t) ≤ (1 + 3 * T ^ 2) * redLength F.S 0 p q tau := by
  let a := Real.sqrt tau
  let b := Real.sqrt (tau * t)
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have ha : 0 < a := Real.sqrt_pos.mpr htau
  have hb : 0 < b := Real.sqrt_pos.mpr (mul_pos htau ht0)
  have ha2 : a ^ 2 = tau := Real.sq_sqrt htau.le
  have hab : a ≤ b := Real.sqrt_le_sqrt (by nlinarith only [htau, ht.1])
  have hr := sqrt_ratio_bounds htau (s := 1) le_rfl ht.1 ht.2
  simp only [mul_one] at hr
  change 1 ≤ b / a ∧ b / a ≤ T ∧ b / a - 1 ≤ t - 1 at hr
  have hforward := redLength_le_of_backward_time_ge F hF p q htau
    (show tau ≤ tau * t by nlinarith only [htau, ht.1])
  change redLength F.S 0 p q (tau * t) ≤
    (a / b + 3 * b * (b - a) / tau) * redLength F.S 0 p q tau at hforward
  have hfirst : a / b ≤ 1 := (div_le_iff₀ hb).mpr (by simpa using hab)
  have heq : 3 * b * (b - a) / tau = 3 * (b / a) * (b / a - 1) := by
    rw [← ha2]
    field_simp
  have hr0 : 0 ≤ b / a := by positivity
  have hT0 : 0 ≤ T := hr0.trans hr.2.1
  have hsq := (sq_le_sq₀ hr0 hT0).mpr hr.2.1
  have hcoef : a / b + 3 * b * (b - a) / tau ≤ 1 + 3 * T ^ 2 := by
    rw [heq]
    nlinarith only [hfirst, hsq, hr0]
  exact hforward.trans (mul_le_mul_of_nonneg_right hcoef (time_length_nonneg F hF p q htau))

private theorem redLength_rescaled_time_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {tau T A t : ℝ} (htau : 0 < tau)
    (ht : t ∈ Set.Icc 1 T) (hbase : redLength F.S 0 p q tau ≤ A) :
    redLength F.S 0 p q (tau * t) ≤ (1 + 3 * T ^ 2) * max A 0 :=
  (redLength_le_mul_on_rescaled_time_interval F hF p q htau ht).trans
    (mul_le_mul_of_nonneg_left (hbase.trans (le_max_left A 0)) (by positivity))

private theorem abs_redLength_sub_le_on_rescaled_time_interval
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {tau T A s t : ℝ} (htau : 0 < tau)
    (hs : s ∈ Set.Icc 1 T) (ht : t ∈ Set.Icc 1 T) (hst : s ≤ t)
    (hbase : redLength F.S 0 p q tau ≤ A) :
    |redLength F.S 0 p q (tau * t) - redLength F.S 0 p q (tau * s)| ≤
      ((2 + 6 * T) * ((1 + 3 * T ^ 2) * max A 0)) * (t - s) := by
  let L := (1 + 3 * T ^ 2) * max A 0
  let X := redLength F.S 0 p q (tau * s)
  let Y := redLength F.S 0 p q (tau * t)
  let a := Real.sqrt (tau * s)
  let b := Real.sqrt (tau * t)
  have hT : 1 ≤ T := hs.1.trans hs.2
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hs0 : 0 < tau * s := mul_pos htau (lt_of_lt_of_le zero_lt_one hs.1)
  have ht0 : 0 < tau * t := mul_pos htau (lt_of_lt_of_le zero_lt_one ht.1)
  have ha : 0 < a := Real.sqrt_pos.mpr hs0
  have hb : 0 < b := Real.sqrt_pos.mpr ht0
  have ha2 : a ^ 2 = tau * s := Real.sq_sqrt hs0.le
  have hab : a ≤ b := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hst htau.le)
  have hdelta : 0 ≤ t - s := sub_nonneg.mpr hst
  have hL : 0 ≤ L := mul_nonneg (by positivity) (le_max_right A 0)
  have hX0 : 0 ≤ X := time_length_nonneg F hF p q hs0
  have hY0 : 0 ≤ Y := time_length_nonneg F hF p q ht0
  have hXL : X ≤ L := redLength_rescaled_time_le F hF p q htau hs hbase
  have hYL : Y ≤ L := redLength_rescaled_time_le F hF p q htau ht hbase
  have hr := sqrt_ratio_bounds htau hs.1 hst ht.2
  change 1 ≤ b / a ∧ b / a ≤ T ∧ b / a - 1 ≤ t - s at hr
  have hr0 : 0 ≤ b / a := zero_le_one.trans hr.1
  have hgap0 : 0 ≤ b / a - 1 := sub_nonneg.mpr hr.1
  have hforward : Y - X ≤ (2 + 6 * T) * L * (t - s) := by
    have hf := redLength_le_of_backward_time_ge F hF p q hs0
      (mul_le_mul_of_nonneg_left hst htau.le)
    change Y ≤ (a / b + 3 * b * (b - a) / (tau * s)) * X at hf
    have hfirst : a / b ≤ 1 := (div_le_iff₀ hb).mpr (by simpa using hab)
    have heq : 3 * b * (b - a) / (tau * s) = 3 * (b / a) * (b / a - 1) := by
      rw [← ha2]
      field_simp
    have hprod := mul_le_mul hr.2.1 hr.2.2 hgap0 hT0
    have hcoef : a / b + 3 * b * (b - a) / (tau * s) ≤ 1 + 3 * T * (t - s) := by
      rw [heq]
      nlinarith only [hfirst, hprod]
    have hf' := hf.trans (mul_le_mul_of_nonneg_right hcoef hX0)
    have hmul := mul_le_mul_of_nonneg_left hXL
      (show 0 ≤ 3 * T * (t - s) by positivity)
    have hcoeff : 3 * T * L ≤ (2 + 6 * T) * L :=
      mul_le_mul_of_nonneg_right (by linarith) hL
    have hlast := mul_le_mul_of_nonneg_right hcoeff hdelta
    nlinarith only [hf', hmul, hlast]
  have hsqrtL : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL
  have hsqrt3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hspeed : Real.sqrt (12 * b * Y / a) ≤ 2 * Real.sqrt 3 * T * Real.sqrt L := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hprod := mul_le_mul hr.2.1 hYL hY0 hT0
    have hT2 : T ≤ T ^ 2 := by nlinarith only [hT]
    have hmul := mul_le_mul_of_nonneg_right hT2 hL
    have heq : 12 * b * Y / a = 12 * (b / a * Y) := by ring
    rw [heq, mul_pow, mul_pow, mul_pow, hsqrt3, hsqrtL]
    nlinarith only [hprod, hmul]
  have hback := sqrt_redLength_le_of_backward_time_le F hF p q hs0
    (mul_le_mul_of_nonneg_left hst htau.le) (A := Y) le_rfl
  change Real.sqrt X ≤ b / a * Real.sqrt Y +
    Real.sqrt 3 / (2 * a) * ((b - a) * Real.sqrt (12 * b * Y / a)) at hback
  have hterm : Real.sqrt 3 / (2 * a) * ((b - a) * Real.sqrt (12 * b * Y / a)) ≤
      3 * T * Real.sqrt L * (b / a - 1) := by
    calc
      _ ≤ Real.sqrt 3 / (2 * a) * ((b - a) * (2 * Real.sqrt 3 * T * Real.sqrt L)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hspeed (sub_nonneg.mpr hab))
          (by positivity)
      _ = (Real.sqrt 3 * Real.sqrt 3) * T * Real.sqrt L * (b / a - 1) := by
        field_simp
      _ = _ := by rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hroot : Real.sqrt X - Real.sqrt Y ≤ (1 + 3 * T) * Real.sqrt L * (t - s) := by
    have hback' := hback.trans (add_le_add le_rfl hterm)
    have hYs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hYL) hgap0
    have hlast := mul_le_mul_of_nonneg_left hr.2.2
      (show 0 ≤ (1 + 3 * T) * Real.sqrt L by positivity)
    nlinarith only [hback', hYs, hlast]
  have hsum : Real.sqrt X + Real.sqrt Y ≤ 2 * Real.sqrt L := by
    linarith only [Real.sqrt_le_sqrt hXL, Real.sqrt_le_sqrt hYL]
  have hreverse : X - Y ≤ (2 + 6 * T) * L * (t - s) := by
    calc
      X - Y = (Real.sqrt X - Real.sqrt Y) * (Real.sqrt X + Real.sqrt Y) := by
        nlinarith only [Real.sq_sqrt hX0, Real.sq_sqrt hY0]
      _ ≤ ((1 + 3 * T) * Real.sqrt L * (t - s)) * (Real.sqrt X + Real.sqrt Y) :=
        mul_le_mul_of_nonneg_right hroot (by positivity)
      _ ≤ ((1 + 3 * T) * Real.sqrt L * (t - s)) * (2 * Real.sqrt L) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (2 + 6 * T) * (Real.sqrt L ^ 2) * (t - s) := by ring
      _ = _ := by rw [hsqrtL]
  exact abs_le.mpr ⟨by linarith only [hreverse], hforward⟩

theorem exists_lipschitzOnWith_redLength_rescaled_time
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) {T A : ℝ} (hT : 1 ≤ T) :
    ∃ K : NNReal, ∀ (tau : ℝ), 0 < tau → ∀ q : F.M,
      redLength F.S 0 p q tau ≤ A →
        LipschitzOnWith K (fun t => redLength F.S 0 p q (tau * t)) (Set.Icc 1 T) := by
  let K : NNReal := ⟨(2 + 6 * T) * ((1 + 3 * T ^ 2) * max A 0), by positivity⟩
  refine ⟨K, fun tau htau q hbase => LipschitzOnWith.of_dist_le_mul ?_⟩
  intro s hs t ht
  change |redLength F.S 0 p q (tau * s) - redLength F.S 0 p q (tau * t)| ≤
    (K : ℝ) * |s - t|
  rcases le_total s t with hst | hts
  · rw [abs_sub_comm (redLength F.S 0 p q (tau * s)), abs_sub_comm s t,
      abs_of_nonneg (sub_nonneg.mpr hst)]
    exact abs_redLength_sub_le_on_rescaled_time_interval F hF p q htau hs ht hst hbase
  · rw [abs_of_nonneg (sub_nonneg.mpr hts)]
    exact abs_redLength_sub_le_on_rescaled_time_interval F hF p q htau ht hs hts hbase

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
