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
