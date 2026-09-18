import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientScalarMonotonicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalMetricLowerBound
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciUpper
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientEndpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalEnergy
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

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
private local instance topology : TopologicalSpace F.M := F.topology
private local instance charted : ChartedSpace H F.M := F.charted
private local instance smooth : IsManifold I ∞ F.M := F.smooth
private local instance t2 : T2Space F.M := F.t2
private local instance sigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem metric_inner_le_exp_scalar_bound_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {a b C : ℝ} (hab : a ≤ b) (hb : b ≤ 0)
    (x : F.M) (hC : F.S.scalar b x ≤ C) (v : TangentSpace I x) :
    (F.S.base.metric a).inner x v v ≤
      Real.exp (C * (b - a)) * (F.S.base.metric b).inner x v v := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hslab : Icc a b ⊆ ancientTimeInterval.carrier := fun t ht => ht.2.trans hb
  have hreg : Ioo a b ⊆ ancientTimeInterval.regular := fun t ht => ht.2.trans_le hb
  have hRic : ∀ t ∈ Ioo a b, ∀ y ∈ ({x} : Set F.M), ∀ w : TangentSpace I y,
      F.S.ricciAt t y (vec2 w w) ≤ (C / 2) * (F.S.base.metric t).inner y w w := by
    intro t ht y hy w
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    have ht0 : t ≤ 0 := ht.2.le.trans hb
    have hR : F.S.scalar t x ≤ C :=
      (ancientKappa_scalar_monotoneOn F hF x ht0 hb ht.2.le).trans hC
    have hcone : metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
      apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
        (I := I) (F.S.base.metric t) x).mpr
      intro n c u w
      simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
        hF.nonnegativeCurvatureOperator t ht0 x n c u w
    have hupper := metricRicciAt_le_half_scalar_mul_inner_of_curvatureOperator_nonnegative
      (F.S.base.metric t) x hcone w
    exact hupper.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hR (by norm_num))
      (metric_inner_self_nonneg (F.S.base.metric t) x w))
  have hraw := metric_inner_lower_bound_of_ricci_upper_interior F.S F.isSolution
    hab hslab hreg hRic (Set.mem_singleton x) v
  have heq : 2 * (C / 2) * (b - a) = C * (b - a) := by ring
  rw [heq] at hraw
  calc
    (F.S.base.metric a).inner x v v =
        Real.exp (C * (b - a)) *
          (Real.exp (-(C * (b - a))) * (F.S.base.metric a).inner x v v) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp only [add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (C * (b - a)) * (F.S.base.metric b).inner x v v :=
      mul_le_mul_of_nonneg_left hraw (Real.exp_pos _).le

theorem metric_inner_le_exp_redLength_on_half_tail_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (p : F.M) {tau s A : ℝ} (htau : 0 < tau)
    (hs : s ∈ Icc (Real.sqrt tau / 2) (Real.sqrt tau))
    (hgeo : IsLRegularizedGeodesicOn F.S 0 alpha (Ioo 0 (Real.sqrt tau)))
    (hcost : lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
      lCost F.S 0 p (alpha (Real.sqrt tau)) tau)
    (hlength : redLength F.S 0 p (alpha (Real.sqrt tau)) tau ≤ A)
    (v : TangentSpace I (alpha s)) :
    (F.S.base.metric (-tau)).inner (alpha s) v v ≤
      Real.exp (24 * A) * (F.S.base.metric (-(s ^ 2))).inner (alpha s) v v := by
  have hs0 : 0 ≤ s := (div_nonneg (Real.sqrt_nonneg tau) (by norm_num : (0 : ℝ) ≤ 2)).trans hs.1
  have hsq : s ^ 2 ≤ tau := by
    calc
      s ^ 2 ≤ (Real.sqrt tau) ^ 2 := pow_le_pow_left₀ hs0 hs.2 2
      _ = tau := Real.sq_sqrt htau.le
  have hscalar := scalar_le_twenty_four_mul_redLength_div_on_half_tail_of_ancient
    F hF alpha halpha p htau hs hgeo hcost
  have hscalarA : F.S.scalar (-(s ^ 2)) (alpha s) ≤ 24 * A / tau :=
    hscalar.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlength (by norm_num)) htau.le)
  have hscalarNonneg : 0 ≤ F.S.scalar (-(s ^ 2)) (alpha s) := by
    obtain ⟨B, hB⟩ := hF.globalScalarBound
    exact (hB (-(s ^ 2)) (neg_nonpos.mpr (sq_nonneg s)) (alpha s)).1
  have hA : 0 ≤ A := by
    have hnum := (le_div_iff₀ htau).mp (hscalarNonneg.trans hscalarA)
    linarith
  have hcomp := metric_inner_le_exp_scalar_bound_of_ancient F hF
    (neg_le_neg hsq) (neg_nonpos.mpr (sq_nonneg s)) (alpha s) hscalarA v
  apply hcomp.trans
  apply mul_le_mul_of_nonneg_right _ (metric_inner_self_nonneg _ _ _)
  apply Real.exp_le_exp.mpr
  calc
    (24 * A / tau) * (-(s ^ 2) - -tau) ≤ (24 * A / tau) * tau :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg s]) (by positivity)
    _ = 24 * A := div_mul_cancel₀ _ htau.ne'

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem curveEnergy_endpoint_le_exp_redLength_on_half_tail_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (p : F.M) {tau A : ℝ} (htau : 0 < tau)
    (hgeo : IsLRegularizedGeodesicOn F.S 0 alpha (Ioo 0 (Real.sqrt tau)))
    (hcost : lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
      lCost F.S 0 p (alpha (Real.sqrt tau)) tau)
    (hlength : redLength F.S 0 p (alpha (Real.sqrt tau)) tau ≤ A) :
    curveEnergy (F.S.base.metric (-tau)) alpha (Real.sqrt tau / 2) (Real.sqrt tau) ≤
      4 * Real.exp (24 * A) * Real.sqrt tau * A := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let b := Real.sqrt tau
  let c := b / 2
  have hb : 0 < b := Real.sqrt_pos.mpr htau
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcb : c ≤ b := by dsimp [c]; linarith
  have hscalar (r : ℝ) : 0 ≤ F.S.scalar (0 - r ^ 2) (alpha r) := by
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    exact (hC _ (by
      simpa only [ancientTimeInterval_carrier, mem_Iic, zero_sub] using
        neg_nonpos.mpr (sq_nonneg r)) (alpha r)).1
  have hlag (r : ℝ) : 0 ≤ lRegularizedLagrangian F.S 0 alpha r := by
    change 0 ≤ (1 / 2 : ℝ) * lRegularizedSpeedSq F.S 0 alpha r +
      2 * r ^ 2 * F.S.scalar (0 - r ^ 2) (alpha r)
    exact add_nonneg (mul_nonneg (by norm_num) (lRegularizedSpeedSq_nonneg F.S 0 alpha r))
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg r)) (hscalar r))
  have hcont : ContinuousOn (lRegularizedLagrangian F.S 0 alpha) (Icc 0 b) := by
    apply (lRegularizedLagrangian_continuousOn_carrier F.S F.isSolution alpha halpha).comp
      (continuous_const.prodMk continuous_id).continuousOn
    intro r _
    change (0 : ℝ) - r ^ 2 ∈ ancientTimeInterval.carrier
    simpa only [ancientTimeInterval_carrier, mem_Iic, zero_sub] using
      neg_nonpos.mpr (sq_nonneg r)
  have hLag : IntervalIntegrable (lRegularizedLagrangian F.S 0 alpha) volume 0 b :=
    hcont.intervalIntegrable_of_Icc hb.le
  have hLagTail : IntervalIntegrable (lRegularizedLagrangian F.S 0 alpha) volume c b :=
    (hcont.mono (Icc_subset_Icc hc le_rfl)).intervalIntegrable_of_Icc hcb
  have hEint : IntervalIntegrable (fun r => (F.S.base.metric (-tau)).inner (alpha r)
      (lVelocity (I := I) alpha r) (lVelocity (I := I) alpha r)) volume c b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hcb]
    exact integrableOn_riemannianMetric_inner_lVelocity_self_of_contMDiff_one
      (F.S.base.metric (-tau)) alpha halpha c b
  have hpoint : ∀ r ∈ Icc c b,
      (F.S.base.metric (-tau)).inner (alpha r)
        (lVelocity (I := I) alpha r) (lVelocity (I := I) alpha r) ≤
      (2 * Real.exp (24 * A)) * lRegularizedLagrangian F.S 0 alpha r := by
    intro r hr
    have hm := metric_inner_le_exp_redLength_on_half_tail_of_ancient
      F hF alpha halpha p htau hr hgeo hcost hlength
      (lVelocity (I := I) alpha r)
    have hpot := mul_nonneg (sq_nonneg r) (hscalar r)
    have hspeed : lRegularizedSpeedSq F.S 0 alpha r ≤
        2 * lRegularizedLagrangian F.S 0 alpha r := by
      change lRegularizedSpeedSq F.S 0 alpha r ≤
        2 * ((1 / 2 : ℝ) * lRegularizedSpeedSq F.S 0 alpha r +
          2 * r ^ 2 * F.S.scalar (0 - r ^ 2) (alpha r))
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hspeed (Real.exp_pos (24 * A)).le
    change (F.S.base.metric (-tau)).inner (alpha r)
      (lVelocity (I := I) alpha r) (lVelocity (I := I) alpha r) ≤ _
    have hm' : (F.S.base.metric (-tau)).inner (alpha r)
        (lVelocity (I := I) alpha r) (lVelocity (I := I) alpha r) ≤
      Real.exp (24 * A) * lRegularizedSpeedSq F.S 0 alpha r := by
      simpa only [lRegularizedSpeedSq, zero_sub] using hm
    nlinarith
  have hint := intervalIntegral.integral_mono_on hcb hEint
    (hLagTail.const_mul (2 * Real.exp (24 * A))) hpoint
  rw [intervalIntegral.integral_const_mul] at hint
  have haction : lRegularizedAction F.S 0 alpha c b ≤
      lRegularizedAction F.S 0 alpha 0 b :=
    intervalIntegral.integral_mono_interval hc hcb le_rfl
      (Filter.Eventually.of_forall hlag) hLag
  have hfull : lRegularizedAction F.S 0 alpha 0 b ≤ 2 * b * A := by
    have hbound := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hb)).mp hlength
    change lCost F.S 0 p (alpha b) tau ≤ A * (2 * b) at hbound
    rw [hcost]
    nlinarith
  have htotal := (haction.trans hfull)
  have hscaled := mul_le_mul_of_nonneg_left htotal
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos (24 * A)).le)
  change curveEnergy (F.S.base.metric (-tau)) alpha c b ≤ 4 * Real.exp (24 * A) * b * A
  change (2 * Real.exp (24 * A)) *
    (∫ r in c..b, lRegularizedLagrangian F.S 0 alpha r) ≤
      (2 * Real.exp (24 * A)) * (2 * b * A) at hscaled
  exact hint.trans (by nlinarith [hscaled])

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDist_endpoint_le_exp_redLength_on_half_tail_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (p : F.M) {tau s A : ℝ} (htau : 0 < tau)
    (hs : s ∈ Icc (Real.sqrt tau / 2) (Real.sqrt tau))
    (hgeo : IsLRegularizedGeodesicOn F.S 0 alpha (Ioo 0 (Real.sqrt tau)))
    (hcost : lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
      lCost F.S 0 p (alpha (Real.sqrt tau)) tau)
    (hlength : redLength F.S 0 p (alpha (Real.sqrt tau)) tau ≤ A) :
    riemannianEDistOf (F.S.base.metric (-tau)) (alpha s) (alpha (Real.sqrt tau)) ≤
      ENNReal.ofReal (Real.sqrt tau * Real.sqrt (2 * Real.exp (24 * A) * A)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let b := Real.sqrt tau
  let c := b / 2
  have hb : 0 ≤ b := Real.sqrt_nonneg tau
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hE := integrableOn_riemannianMetric_inner_lVelocity_self_of_contMDiff_one
    (F.S.base.metric (-tau)) alpha halpha c b
  have henergy := curveEnergy_endpoint_le_exp_redLength_on_half_tail_of_ancient
    F hF alpha halpha p htau hgeo hcost hlength
  have hdist := edistOf_le_budget (F.S.base.metric (-tau)) hs.2 halpha.contMDiffOn
    (hE.mono_set (Icc_subset_Icc hs.1 le_rfl))
    ((curveEnergy_mono (F.S.base.metric (-tau)) hs.1 hs.2 le_rfl hE).trans henergy)
  apply hdist.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    Real.sqrt (b - s) * Real.sqrt (4 * Real.exp (24 * A) * b * A) ≤
        Real.sqrt c * Real.sqrt (4 * Real.exp (24 * A) * b * A) := by
      apply mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt _) (Real.sqrt_nonneg _)
      dsimp [c, b] at *
      linarith [hs.1]
    _ = Real.sqrt (c * (4 * Real.exp (24 * A) * b * A)) :=
      (Real.sqrt_mul hc _).symm
    _ = Real.sqrt (b ^ 2 * (2 * Real.exp (24 * A) * A)) := by
      congr 1
      dsimp [c]
      ring
    _ = b * Real.sqrt (2 * Real.exp (24 * A) * A) := by
      rw [Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb]

theorem riemannianEDist_scaled_endpoint_le_exp_redLength_on_half_tail_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (p : F.M) {tau s A : ℝ} (htau : 0 < tau)
    (hs : s ∈ Icc (Real.sqrt tau / 2) (Real.sqrt tau))
    (hgeo : IsLRegularizedGeodesicOn F.S 0 alpha (Ioo 0 (Real.sqrt tau)))
    (hcost : lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
      lCost F.S 0 p (alpha (Real.sqrt tau)) tau)
    (hlength : redLength F.S 0 p (alpha (Real.sqrt tau)) tau ≤ A) :
    riemannianEDistOf
      (scaleMetric tau⁻¹ (inv_pos.mpr htau) (F.S.base.metric (-tau)))
      (alpha s) (alpha (Real.sqrt tau)) ≤
      ENNReal.ofReal (Real.sqrt (2 * Real.exp (24 * A) * A)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : T2Space (TangentBundle I F.M) := F.t2TangentBundle
  have hdist := riemannianEDist_endpoint_le_exp_redLength_on_half_tail_of_ancient
    F hF alpha halpha p htau hs hgeo hcost hlength
  have hb : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  rw [edistOf_scale, Real.sqrt_inv, ENNReal.ofReal_inv_of_pos hb]
  calc
    _ ≤ (ENNReal.ofReal (Real.sqrt tau))⁻¹ *
        ENNReal.ofReal (Real.sqrt tau * Real.sqrt (2 * Real.exp (24 * A) * A)) :=
      mul_le_mul_right hdist _
    _ = ENNReal.ofReal (Real.sqrt (2 * Real.exp (24 * A) * A)) := by
      rw [ENNReal.ofReal_mul hb.le, ← mul_assoc,
        ENNReal.inv_mul_cancel (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hb)
          ENNReal.ofReal_ne_top, one_mul]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
