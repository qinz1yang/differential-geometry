import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {D D' : RealTimeInterval}

theorem lRegularizedAction_le_mul_of_metric_le_of_scalar_le
    (S : SolutionOn (I := I) (M := M) D) (U : SolutionOn (I := I) (M := M) D')
    (hS : IsSolutionOn S) (hU : IsSolutionOn U)
    {T R a A : ℝ} (ha : 0 ≤ a)
    (hT : ∀ s ∈ Icc 0 a, T - s ^ 2 ∈ D.carrier)
    (hR : ∀ s ∈ Icc 0 a, R - s ^ 2 ∈ D'.carrier)
    (alpha : ℝ → M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (hmetric : ∀ s ∈ Icc 0 a,
      (S.base.metric (T - s ^ 2)).inner (alpha s) (lVelocity alpha s) (lVelocity alpha s) ≤
        A * (U.base.metric (R - s ^ 2)).inner (alpha s) (lVelocity alpha s) (lVelocity alpha s))
    (hscalar : ∀ s ∈ Icc 0 a, S.scalar (T - s ^ 2) (alpha s) ≤ A * U.scalar (R - s ^ 2) (alpha s)) :
    lRegularizedAction S T alpha 0 a ≤ A * lRegularizedAction U R alpha 0 a := by
  have hST : ContinuousOn (lRegularizedLagrangian S T alpha) (Icc 0 a) := by
    have hmap : ContinuousOn (fun s : ℝ => (T, s)) (Icc 0 a) :=
      (continuous_const.prodMk continuous_id).continuousOn
    have hmaps : MapsTo (fun s : ℝ => (T, s)) (Icc 0 a)
        {z : ℝ × ℝ | z.1 - z.2 ^ 2 ∈ D.carrier} := hT
    have hc := (lRegularizedLagrangian_continuousOn_carrier S hS alpha halpha).comp hmap hmaps
    exact hc
  have hUR : ContinuousOn (lRegularizedLagrangian U R alpha) (Icc 0 a) := by
    have hmap : ContinuousOn (fun s : ℝ => (R, s)) (Icc 0 a) :=
      (continuous_const.prodMk continuous_id).continuousOn
    have hmaps : MapsTo (fun s : ℝ => (R, s)) (Icc 0 a)
        {z : ℝ × ℝ | z.1 - z.2 ^ 2 ∈ D'.carrier} := hR
    have hc := (lRegularizedLagrangian_continuousOn_carrier U hU alpha halpha).comp hmap hmaps
    exact hc
  have hpoint (s : ℝ) (hs : s ∈ Icc 0 a) :
      lRegularizedLagrangian S T alpha s ≤ A * lRegularizedLagrangian U R alpha s := by
    have hkin := mul_le_mul_of_nonneg_left (hmetric s hs) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hscal := mul_le_mul_of_nonneg_left (hscalar s hs) (by positivity : 0 ≤ 2 * s ^ 2)
    change (1 / 2 : ℝ) * _ + 2 * s ^ 2 * _ ≤ A * ((1 / 2 : ℝ) * _ + 2 * s ^ 2 * _)
    nlinarith only [hkin, hscal]
  have h := intervalIntegral.integral_mono_on (μ := volume) ha (hST.intervalIntegrable_of_Icc ha)
    ((hUR.intervalIntegrable_of_Icc ha).const_mul A) hpoint
  simpa only [lRegularizedAction, intervalIntegral.integral_const_mul] using h


end DifferentialGeometry.PDE.RicciFlow.Perelman
