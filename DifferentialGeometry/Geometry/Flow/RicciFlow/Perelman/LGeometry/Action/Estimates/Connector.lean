import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Metric.CurveEnergy.CompactBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime
import DifferentialGeometry.Analysis.Integration.Integral.Comparison

noncomputable section
open Set MeasureTheory Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lRegularizedAction_le_reference_energy_add_scalar_bound
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (g : SmoothRiemannianMetric I M)
    (α : ℝ → M) {a b Λ C : ℝ} (hab : a ≤ b)
    (href : IntervalIntegrable (fun t => g.inner (α t) (lVelocity α t) (lVelocity α t)) volume a b)
    (hint : IntervalIntegrable (lRegularizedLagrangian S T α) volume a b)
    (hmetric : ∀ t ∈ Ioo a b,
      (S.base.metric (T - t ^ 2)).inner (α t) (lVelocity α t) (lVelocity α t) ≤
        Λ * g.inner (α t) (lVelocity α t) (lVelocity α t))
    (hscalar : ∀ t ∈ Ioo a b, S.scalar (T - t ^ 2) (α t) ≤ C) :
    lRegularizedAction S T α a b ≤ Λ / 2 * curveEnergy g α a b + (2 * C / 3) * (b ^ 3 - a ^ 3) := by
  have hi := (href.const_mul (Λ / 2)).sub hint
  have hlow := intervalIntegral.integral_ge_of_mul_sq_le hab hi (C := -(2 * C)) (fun t ht => ?_)
  · rw [intervalIntegral.integral_sub (href.const_mul (Λ / 2)) hint,
      intervalIntegral.integral_const_mul] at hlow
    change -(2 * C) / 3 * (b ^ 3 - a ^ 3) ≤
      Λ / 2 * curveEnergy g α a b - lRegularizedAction S T α a b at hlow
    linarith
  have hm := hmetric t ht
  have hs := mul_le_mul_of_nonneg_left (hscalar t ht) (by positivity : 0 ≤ 2 * t ^ 2)
  dsimp only [Pi.sub_apply, lRegularizedLagrangian]
  nlinarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_lRegularizedAction_le_of_compact_ball
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    (g : SmoothRiemannianMetric I M) (p q : M) {a b R Λ C : ℝ} (hab : a < b)
    (hR : riemannianEDistOf g p q < ENNReal.ofReal R)
    (hcompact : IsCompact (riemannianClosedBallOf g p R))
    (htime : ∀ t ∈ Icc a b, T - t ^ 2 ∈ D.carrier)
    (hmetric : ∀ t ∈ Ioo a b, ∀ z ∈ riemannianClosedBallOf g p R, ∀ w : TangentSpace I z,
      (S.base.metric (T - t ^ 2)).inner z w w ≤ Λ * g.inner z w w)
    (hscalar : ∀ t ∈ Ioo a b, ∀ z ∈ riemannianClosedBallOf g p R, S.scalar (T - t ^ 2) z ≤ C) :
    ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ α ∧ α a = p ∧ α b = q ∧
      MapsTo α (Icc a b) (riemannianClosedBallOf g p R) ∧
      lRegularizedAction S T α a b ≤
        Λ * (riemannianEDistOf g p q).toReal ^ 2 / (2 * (b - a)) +
          (2 * C / 3) * (b ^ 3 - a ^ 3) := by
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  obtain ⟨α, hα, hstart, hend, hstay, henergy⟩ :=
    exists_contMDiff_curve_energy_eq_of_isCompact_riemannianClosedBall (I := I) (M := M) g p q hab hR hcompact
  have hα1 : ContMDiff 𝓘(ℝ, ℝ) I 1 α := hα.of_le (by norm_num)
  have hint : IntervalIntegrable (lRegularizedLagrangian S T α) volume a b := by
    have hc := lRegularizedLagrangian_continuousOn_carrier (I := I) (M := M) S hS α hα1
    have hh : ContinuousOn (lRegularizedLagrangian S T α) (Icc a b) :=
      hc.comp (f := fun t : ℝ => (T, t))
        (continuous_const.prodMk continuous_id).continuousOn htime
    exact hh.intervalIntegrable_of_Icc hab.le
  have href : IntervalIntegrable (fun t => g.inner (α t) (lVelocity α t) (lVelocity α t)) volume a b := by
    apply IntegrableOn.intervalIntegrable
    rw [uIcc_of_le hab.le]
    exact integrableOn_inner_mfderiv_self_of_contMDiffOn (I := I) (a := a) (b := b) g hα1.contMDiffOn
  have hle := lRegularizedAction_le_reference_energy_add_scalar_bound S T g α hab.le href hint
    (fun t ht => hmetric t ht (α t) (hstay (Ioo_subset_Icc_self ht)) (lVelocity α t))
    (fun t ht => hscalar t ht (α t) (hstay (Ioo_subset_Icc_self ht)))
  rw [henergy] at hle
  refine ⟨α, hα, hstart, hend, hstay, ?_⟩
  have heq : Λ / 2 * ((riemannianEDistOf g p q).toReal ^ 2 / (b - a)) =
      Λ * (riemannianEDistOf g p q).toReal ^ 2 / (2 * (b - a)) := by
    field_simp
  simpa only [heq] using hle

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

noncomputable section
open Set Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

theorem exists_lRegularizedAction_le_of_curvature_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {u s K : ℝ} (hK : 0 ≤ K) (hus : u ≤ s)
    (hcarrier : Icc u s ⊆ D.carrier) (hregular : Ioo u s ⊆ D.regular)
    (hRm : ∀ t ∈ Icc u s, ∀ x : M,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K ^ 2)
    (p q : M) {R T a b : ℝ} (hab : a < b)
    (hdist : riemannianEDistOf (S.base.metric s) p q < ENNReal.ofReal R)
    (hcompact : IsCompact (riemannianClosedBallOf (S.base.metric s) p R))
    (hclock : ∀ t ∈ Icc a b, T - t ^ 2 ∈ Icc u s) :
    ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ α ∧ α a = p ∧ α b = q ∧
      MapsTo α (Icc a b) (riemannianClosedBallOf (S.base.metric s) p R) ∧
      lRegularizedAction S T α a b ≤
        Real.exp (2 * (Module.finrank ℝ E : ℝ)^2 * K * (s-u)) *
          (riemannianEDistOf (S.base.metric s) p q).toReal ^ 2 / (2 * (b-a)) +
            (2 * ((Module.finrank ℝ E : ℝ)^2 * K) / 3) * (b^3-a^3) := by
  apply exists_lRegularizedAction_le_of_compact_ball S hS T (S.base.metric s) p q hab hdist hcompact
    (fun t ht => hcarrier (hclock t ht))
  · intro t ht x _ v
    have htime := hclock t (Ioo_subset_Icc_self ht)
    have hh := (metric_inner_exp_bounds_of_curvature_bound S hS hcarrier hregular x
      (fun t ht => hRm t ht x) htime (show s ∈ Icc u s from ⟨hus,le_rfl⟩) v).2
    rw [Real.sqrt_sq hK, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr htime.2)] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (metric_inner_self_nonneg _ _ _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left htime.1 s) (by positivity)
  · intro t ht x _
    have htime := hclock t (Ioo_subset_Icc_self ht)
    have hh := scalar_abs_le_rm (S.base.metric (T-t^2)) x
    have hn : Real.sqrt (normSq0S (S.base.metric (T-t^2)) x 4 (S.base.rm04 (T-t^2) x)) ≤ K :=
      (Real.sqrt_le_iff).mpr ⟨hK,hRm _ htime x⟩
    change S.scalar (T-t^2) x ≤ (Module.finrank ℝ E : ℝ)^2 * K
    exact (le_abs_self _).trans (hh.trans (mul_le_mul_of_nonneg_left hn (sq_nonneg _)))


theorem exists_lRegularizedAction_le_of_backward_ball
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {u s K : ℝ} (hK : 0 ≤ K) (hus : u ≤ s)
    (hcarrier : Icc u s ⊆ D.carrier) (hregular : Ioo u s ⊆ D.regular)
    (hRm : ∀ t ∈ Icc u s, ∀ x : M,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K ^ 2)
    (p q : M) {r T Emax : ℝ} (hr : 0 < r)
    (hdist : riemannianEDistOf (S.base.metric s) p q < ENNReal.ofReal r)
    (hcompact : IsCompact (riemannianClosedBallOf (S.base.metric s) p r))
    (hroom : u ≤ s - r ^ 2) (hsT : s ≤ T) (hE : T - s + r ^ 2 ≤ Emax) :
    ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ α ∧
      α (Real.sqrt (T-s)) = p ∧ α (Real.sqrt (T-s+r^2)) = q ∧
      MapsTo α (Icc (Real.sqrt (T-s)) (Real.sqrt (T-s+r^2)))
        (riemannianClosedBallOf (S.base.metric s) p r) ∧
      lRegularizedAction S T α (Real.sqrt (T-s)) (Real.sqrt (T-s+r^2)) ≤
        (Real.exp (2 * (Module.finrank ℝ E : ℝ)^2 * K * (s-u)) +
          2 * (Module.finrank ℝ E : ℝ)^2 * K * r^2) * Real.sqrt Emax := by
  let a := Real.sqrt (T-s)
  let b := Real.sqrt (T-s+r^2)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a^2 = T-s := Real.sq_sqrt (sub_nonneg.mpr hsT)
  have hb2 : b^2 = T-s+r^2 := Real.sq_sqrt (by positivity)
  have hab : a < b := Real.sqrt_lt_sqrt (sub_nonneg.mpr hsT) (by nlinarith [sq_pos_of_pos hr])
  have hbE : b ≤ Real.sqrt Emax := Real.sqrt_le_sqrt hE
  have htime : ∀ t ∈ Icc a b, T-t^2 ∈ Icc u s := by
    intro t ht
    have hta := pow_le_pow_left₀ ha ht.1 2
    have htb := pow_le_pow_left₀ (ha.trans ht.1) ht.2 2
    exact ⟨by nlinarith,by nlinarith⟩
  obtain ⟨α,hα,hap,hbq,hstay,hact⟩ := exists_lRegularizedAction_le_of_curvature_bound
    S hS hK hus hcarrier hregular hRm p q hab hdist hcompact htime
  refine ⟨α,hα,hap,hbq,hstay,le_trans hact ?_⟩
  have hd : 0 ≤ (riemannianEDistOf (S.base.metric s) p q).toReal := ENNReal.toReal_nonneg
  have hdr : (riemannianEDistOf (S.base.metric s) p q).toReal ≤ r :=
    (ENNReal.toReal_le_of_le_ofReal hr.le hdist.le)
  have hd2 : (riemannianEDistOf (S.base.metric s) p q).toReal^2 ≤ r^2 :=
    pow_le_pow_left₀ hd hdr 2
  let Λ := Real.exp (2 * (Module.finrank ℝ E : ℝ)^2 * K * (s-u))
  let C := (Module.finrank ℝ E : ℝ)^2 * K
  have hΛ : 0 < Λ := Real.exp_pos _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hkin : Λ * (riemannianEDistOf (S.base.metric s) p q).toReal^2 / (2*(b-a)) ≤ Λ*b := by
    apply (div_le_iff₀ (by linarith : 0 < 2*(b-a))).mpr
    have hdprod := mul_le_mul_of_nonneg_left hd2 hΛ.le
    have habprod : 0 ≤ (b-a)^2 := sq_nonneg _
    nlinarith
  have hsc : (2*C/3)*(b^3-a^3) ≤ 2*C*r^2*b := by
    have hpoly : b^3-a^3 ≤ 3*b*(b^2-a^2) := by
      have h1 : 0 ≤ (b-a)^2*(2*b+a) := mul_nonneg (sq_nonneg _) (by positivity)
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hpoly (by positivity : 0 ≤ 2*C/3)
    have heq : b^2-a^2 = r^2 := by linarith
    rw [heq] at hh
    nlinarith only [hh]
  have hcoef : 2 * (Module.finrank ℝ E : ℝ)^2 * K = 2*C := by dsimp [C]; ring
  change Λ * _ / (2*(b-a)) + (2*C/3)*(b^3-a^3) ≤ _
  conv_rhs => rw [hcoef]
  have hexp : Real.exp (2*C*(s-u)) = Λ := by dsimp [Λ,C]; congr 1; ring
  rw [hexp]
  exact (add_le_add hkin hsc).trans
    (by nlinarith [mul_le_mul_of_nonneg_left hbE (show 0 ≤ Λ+2*C*r^2 by positivity)])

end DifferentialGeometry.PDE.RicciFlow.Perelman
