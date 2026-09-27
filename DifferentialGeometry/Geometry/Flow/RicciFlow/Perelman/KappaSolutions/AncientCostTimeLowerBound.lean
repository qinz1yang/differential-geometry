import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSqrtLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Approximation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Coercivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set Filter MeasureTheory
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance topology : TopologicalSpace F.M := F.topology
private local instance charted : ChartedSpace H F.M := F.charted
private local instance smooth : IsManifold I ∞ F.M := F.smooth
private local instance c1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
private local instance t2 : T2Space F.M := F.t2
private local instance sigma : SigmaCompactSpace F.M := F.sigmaCompact

omit [I.Boundaryless] in
private theorem ancient_metric_inner_antitone
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (x : F.M) (v : TangentSpace I x) :
    AntitoneOn (fun t ↦ (F.S.base.metric t).inner x v v) (Iic 0) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
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
    F.S F.isSolution (fun _ hr ↦ hr.2.trans ht)
    (fun _ hr ↦ hr.2.trans_le ht) hRic x v
    ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst

omit [I.Boundaryless] in
private theorem ancient_lRegularizedAction_nonneg
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ lRegularizedAction F.S 0 alpha a b := by
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  apply intervalIntegral.integral_nonneg hab
  intro r _hr
  have hR : 0 ≤ F.S.scalar (0 - r ^ 2) (alpha r) :=
    (hC (0 - r ^ 2) (by
      simpa only [ancientTimeInterval_carrier, mem_Iic, zero_sub] using
        neg_nonpos.mpr (sq_nonneg r)) (alpha r)).1
  exact add_nonneg
    (mul_nonneg (by norm_num) (lRegularizedSpeedSq_nonneg F.S 0 alpha r))
    (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg r)) hR)

omit [I.Boundaryless] in
private theorem ancient_lRegularizedLagrangian_intervalIntegrable
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha) (a b : ℝ) :
    IntervalIntegrable (lRegularizedLagrangian F.S 0 alpha) volume a b := by
  have hcont : ContinuousOn (lRegularizedLagrangian F.S 0 alpha) (uIcc a b) := by
    apply (lRegularizedLagrangian_continuousOn_carrier F.S F.isSolution alpha halpha).comp
      (continuous_const.prodMk continuous_id).continuousOn
    intro r _hr
    change 0 - r ^ 2 ∈ ancientTimeInterval.carrier
    simpa only [ancientTimeInterval_carrier, mem_Iic, zero_sub] using
      neg_nonpos.mpr (sq_nonneg r)
  exact hcont.intervalIntegrable

omit [I.Boundaryless] in
theorem ancient_minimizer_tail_edist_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (hend : alpha b = q)
    (hcost : lRegularizedAction F.S 0 alpha 0 b = lCost F.S 0 p q (b ^ 2)) :
    riemannianEDistOf (F.S.base.metric (-(a ^ 2))) (alpha a) q ≤
      ENNReal.ofReal (Real.sqrt (b - a) * Real.sqrt (2 * lCost F.S 0 p q (b ^ 2))) := by
  let g := F.S.base.metric (-(a ^ 2))
  have hE := integrableOn_inner_mfderiv_self_of_contMDiffOn g
    (halpha.contMDiffOn : ContMDiffOn 𝓘(ℝ, ℝ) I 1 alpha (Icc a b))
  have href : IntervalIntegrable
      (fun r ↦ g.inner (alpha r) (lVelocity (I := I) alpha r)
        (lVelocity (I := I) alpha r)) volume a b := by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le hab, lVelocity] using hE
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  have hcoerc := lRegularizedAction_ge_reference_energy_add_constant F.S 0 alpha g
    a b 1 0 hab (fun r hr ↦ by
      simp only [one_mul, zero_sub]
      exact ancient_metric_inner_antitone F hF (alpha r) (lVelocity alpha r)
        (neg_nonpos.mpr (sq_nonneg r)) (neg_nonpos.mpr (sq_nonneg a))
        (neg_le_neg ((sq_le_sq₀ ha.le (ha.le.trans hr.1)).mpr hr.1)))
    (fun r _hr ↦ by
      have hR : 0 ≤ F.S.scalar (0 - r ^ 2) (alpha r) :=
        (hC (0 - r ^ 2) (by
          simpa only [ancientTimeInterval_carrier, mem_Iic, zero_sub] using
            neg_nonpos.mpr (sq_nonneg r)) (alpha r)).1
      exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg r)) hR)
    href (ancient_lRegularizedLagrangian_intervalIntegrable F alpha halpha a b)
  have henergy : curveEnergy g alpha a b ≤ 2 * lRegularizedAction F.S 0 alpha a b := by
    simp only [one_div, zero_mul, add_zero, intervalIntegral.integral_const_mul] at hcoerc
    have hcoerc' : (1 / 2 : ℝ) * curveEnergy g alpha a b ≤
        lRegularizedAction F.S 0 alpha a b := by
      simpa only [curveEnergy, lVelocity, one_div] using hcoerc
    linarith
  have hadd := lRegularizedAction_add F.S 0 alpha 0 a b
    (ancient_lRegularizedLagrangian_intervalIntegrable F alpha halpha 0 a)
    (ancient_lRegularizedLagrangian_intervalIntegrable F alpha halpha a b)
  have hhead := ancient_lRegularizedAction_nonneg F hF alpha ha.le
  have htail : lRegularizedAction F.S 0 alpha a b ≤ lCost F.S 0 p q (b ^ 2) := by
    rw [hcost] at hadd
    linarith
  have hbudget := henergy.trans (mul_le_mul_of_nonneg_left htail (by norm_num))
  simpa only [g, hend] using edistOf_le_budget g hab halpha.contMDiffOn hE hbudget

theorem ancient_sqrt_lCost_le_mul_of_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.sqrt (lCost F.S 0 p q (a ^ 2)) ≤
      (1 + (Real.sqrt (2 * a) * Real.sqrt 3 / (2 * a)) *
        Real.sqrt (b - a) * Real.sqrt 2) *
        Real.sqrt (lCost F.S 0 p q (b ^ 2)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _ht, x, hx⟩ := hF.notFlat
    exact ⟨finrank_ne_zero_of_normSq0S_ne_zero (F.S.base.metric t) x
      (by norm_num : 0 < 4) _ hx⟩
  have hb : 0 < b := ha.trans_le hab
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  obtain ⟨alpha, halpha, hstart, hend, _, hcost⟩ :=
    exists_lRegularized_minimizer_of_ancient F hF p q hb2
  rw [Real.sqrt_sq hb.le] at hend hcost
  rw [hend] at hcost
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  have hscalar : ∀ r ∈ Icc 0 (b ^ 2), ∀ x : F.M, 0 ≤ F.S.scalar (0 - r) x := by
    intro r hr x
    exact (hC (0 - r) (by
      simpa only [ancientTimeInterval_carrier, mem_Iic, zero_sub] using
        neg_nonpos.mpr hr.1) x).1
  have hscalarA : ∀ r ∈ Icc 0 (a ^ 2), ∀ x : F.M, 0 ≤ F.S.scalar (0 - r) x := by
    intro r hr x
    exact hscalar r ⟨hr.1, hr.2.trans ((sq_le_sq₀ ha.le hb.le).mpr hab)⟩ x
  have hCa := lCost_nonneg_of_scalar_nonneg F.S 0 ha2.le hscalarA p q
  have hCb := lCost_nonneg_of_scalar_nonneg F.S 0 hb2.le hscalar p q
  have hprefix := lCost_le_lRegularizedAction_of_scalar_nonneg F.S ha2.le hscalarA
    alpha halpha
  rw [hstart, Real.sqrt_sq ha.le] at hprefix
  have hadd := lRegularizedAction_add F.S 0 alpha 0 a b
    (ancient_lRegularizedLagrangian_intervalIntegrable F alpha halpha 0 a)
    (ancient_lRegularizedLagrangian_intervalIntegrable F alpha halpha a b)
  have htail := ancient_lRegularizedAction_nonneg F hF alpha hab
  have hprefixCost : lCost F.S 0 p (alpha a) (a ^ 2) ≤ lCost F.S 0 p q (b ^ 2) := by
    rw [hcost] at hadd
    linarith
  have hdist := ancient_minimizer_tail_edist_le F hF p q ha hab alpha halpha hend hcost
  have hdistReal := ENNReal.toReal_le_of_le_ofReal (by positivity) hdist
  have hspatial := sqrt_redLength_sub_le_distance_of_continuous_and_minimizers
    F hF p (alpha a) q ha2 (continuous_redLength_of_ancient F hF p ha2)
    (fun x ↦ exists_lRegularized_minimizer_of_ancient F hF p x ha2)
  unfold redLength at hspatial
  rw [Real.sqrt_sq ha.le] at hspatial
  have hbound : Real.sqrt (lCost F.S 0 p q (a ^ 2) / (2 * a)) ≤
      Real.sqrt (lCost F.S 0 p q (b ^ 2) / (2 * a)) +
        Real.sqrt 3 / (2 * a) *
          (Real.sqrt (b - a) * Real.sqrt (2 * lCost F.S 0 p q (b ^ 2))) := by
    refine hspatial.trans (add_le_add ?_ ?_)
    · exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hprefixCost (by positivity))
    · exact mul_le_mul_of_nonneg_left hdistReal (by positivity)
  rw [Real.sqrt_div hCa, Real.sqrt_div hCb,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)
      (lCost F.S 0 p q (b ^ 2))] at hbound
  have hroot : 0 < Real.sqrt (2 * a) := Real.sqrt_pos.mpr (by positivity)
  have hmul := (div_le_iff₀ hroot).mp hbound
  refine hmul.trans_eq ?_
  field_simp [hroot.ne', ha.ne']

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
