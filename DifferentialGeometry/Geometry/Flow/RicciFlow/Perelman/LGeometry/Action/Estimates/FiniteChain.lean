import DifferentialGeometry.Geometry.Metric.CurveEnergy.FiniteChain
import DifferentialGeometry.Analysis.Integration.Integral.Comparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Basic

noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem lRegularizedAction_ge_reference_energy_sub_scalar_bound
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (g : SmoothRiemannianMetric I M)
    (α : ℝ → M) {a b μ B : ℝ} (hab : a ≤ b)
    (href : IntervalIntegrable
      (fun t => g.inner (α t) (lVelocity α t) (lVelocity α t)) volume a b)
    (hmetric : ∀ t ∈ Ioo a b, μ * g.inner (α t) (lVelocity α t) (lVelocity α t) ≤
      (S.base.metric (T - t ^ 2)).inner (α t) (lVelocity α t) (lVelocity α t))
    (hscalar : ∀ t ∈ Ioo a b, -B ≤ S.scalar (T - t ^ 2) (α t))
    (hint : IntervalIntegrable (lRegularizedLagrangian S T α) volume a b) :
    (μ / 2) * curveEnergy g α a b - (2 * B / 3) * (b ^ 3 - a ^ 3) ≤
      lRegularizedAction S T α a b := by
  have hq := href.const_mul (μ / 2)
  have hh := intervalIntegral.integral_ge_of_mul_sq_le hab (hint.sub hq)
    (C := -(2 * B)) (fun t ht => ?_)
  · rw [intervalIntegral.integral_sub hint hq, intervalIntegral.integral_const_mul] at hh
    change -(2 * B) / 3 * (b ^ 3 - a ^ 3) ≤
      lRegularizedAction S T α a b - (μ / 2) * curveEnergy g α a b at hh
    linarith
  have hmet := hmetric t ht
  have hsc := mul_le_mul_of_nonneg_left (hscalar t ht) (by positivity : 0 ≤ 2 * t ^ 2)
  dsimp only [Pi.sub_apply, lRegularizedLagrangian]
  nlinarith

theorem sum_lRegularizedAction_ge_of_curve_chain_separation
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (g : SmoothRiemannianMetric I M)
    (n : ℕ) (t : ℕ → ℝ) (β : ℕ → ℝ → M)
    (ht : ∀ k < n, t k ≤ t (k + 1)) (hinterval : t 0 < t n)
    (hβ : ∀ k < n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 (β k) (Icc (t k) (t (k + 1))))
    (hnode : ∀ k, k + 1 < n → β k (t (k + 1)) = β (k + 1) (t (k + 1)))
    {μ B r : ℝ} (hμ : 0 ≤ μ) (hr : 0 ≤ r)
    (hmetric : ∀ k < n, ∀ s ∈ Ioo (t k) (t (k + 1)),
      μ * g.inner (β k s) (lVelocity (β k) s) (lVelocity (β k) s) ≤
        (S.base.metric (T - s ^ 2)).inner (β k s) (lVelocity (β k) s) (lVelocity (β k) s))
    (hscalar : ∀ k < n, ∀ s ∈ Ioo (t k) (t (k + 1)), -B ≤ S.scalar (T - s ^ 2) (β k s))
    (hint : ∀ k < n, IntervalIntegrable (lRegularizedLagrangian S T (β k)) volume (t k) (t (k + 1)))
    (hsep : ENNReal.ofReal r ≤ riemannianEDistOf g (β 0 (t 0)) (β (n - 1) (t n))) :
    μ * r ^ 2 / (2 * (t n - t 0)) - (2 * B / 3) * (t n ^ 3 - t 0 ^ 3) ≤
      ∑ k ∈ Finset.range n, lRegularizedAction S T (β k) (t k) (t (k + 1)) := by
  have hfinite := riemannianEDistOf_ne_top_of_curve_chain g n t β ht hβ hnode
  have hreal : r ≤ (riemannianEDistOf g (β 0 (t 0)) (β (n - 1) (t n))).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfinite).mp hsep
  have hdistance := riemannianEDistOf_toReal_sq_le_sum_curveEnergy g n t β ht hβ hnode
  have henergy : r ^ 2 ≤ (t n - t 0) *
      ∑ k ∈ Finset.range n, curveEnergy g (β k) (t k) (t (k + 1)) :=
    (pow_le_pow_left₀ hr hreal 2).trans hdistance
  have hmul := mul_le_mul_of_nonneg_left henergy (div_nonneg hμ (by norm_num : (0 : ℝ) ≤ 2))
  have hkin : μ * r ^ 2 / (2 * (t n - t 0)) ≤
      (μ / 2) * ∑ k ∈ Finset.range n, curveEnergy g (β k) (t k) (t (k + 1)) := by
    apply (div_le_iff₀ (mul_pos (by norm_num) (sub_pos.mpr hinterval))).mpr
    nlinarith
  have hlower := Finset.sum_le_sum (fun k hk =>
    lRegularizedAction_ge_reference_energy_sub_scalar_bound S T g (β k)
      (ht k (Finset.mem_range.mp hk)) (by
        apply IntegrableOn.intervalIntegrable
        rw [uIcc_of_le (ht k (Finset.mem_range.mp hk))]
        exact integrableOn_inner_mfderiv_self_of_contMDiffOn g (hβ k (Finset.mem_range.mp hk)))
      (hmetric k (Finset.mem_range.mp hk)) (hscalar k (Finset.mem_range.mp hk))
      (hint k (Finset.mem_range.mp hk)))
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_range_sub (fun k => t k ^ 3) n] at hlower
  exact (sub_le_sub_right hkin _).trans hlower

end DifferentialGeometry.PDE.RicciFlow.Perelman
