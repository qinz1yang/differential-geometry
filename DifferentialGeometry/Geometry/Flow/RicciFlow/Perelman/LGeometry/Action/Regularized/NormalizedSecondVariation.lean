import DifferentialGeometry.Geometry.Comparison.Variation.EndpointAccelerationGerm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.MovingEndpointSecondVariation

open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {D : RealTimeInterval}

theorem hasDerivAt_deriv_lRegularizedAction_div_of_initial_germ
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f)
    (a b : ℝ) (hgeo : IsLRegularizedGeodesicOn S T (f 0) (uIcc a b))
    {p : M} (hinitial : (fun u ↦ f u a) =ᶠ[𝓝 (0 : ℝ)] fun _ ↦ p)
    {beta : ℝ → M} (hterminal : (fun u ↦ f u b) =ᶠ[𝓝 (0 : ℝ)] beta)
    (head : ℝ) :
    HasDerivAt
      (fun u ↦ deriv
        (fun v ↦ (head + lRegularizedAction S T (f v) a b) / (2 * b)) u)
      (lRegularizedIndex S T (f 0)
          (fun s ↦ lVelocity (I := I) (fun u ↦ f u s) 0)
          (fun s ↦ lVelocity (I := I) (fun u ↦ f u s) 0) a b / b +
        (S.base.metric (T - b ^ 2)).inner (beta 0)
          (covDerivAlong (S.base.metric (T - b ^ 2)) beta
            (fun u ↦ mfderiv 𝓘(ℝ, ℝ) I beta u (1 : ℝ)) 0)
          (lVelocity (I := I) (f 0) b) / (2 * b)) 0 := by
  have ha := centralVariationAcceleration_eq_zero_of_eventually_constant
    (I := I) (S.base.metric (T - a ^ 2)) f a p hinitial
  have hb := centralVariationAcceleration_eq_of_endpoint_germ
    (I := I) (S.base.metric (T - b ^ 2)) f b hterminal
  change covDerivAlong (S.base.metric (T - a ^ 2))
    (fun u ↦ f u a) (fun u ↦ lVelocity (I := I) (fun v ↦ f v a) u) 0 = 0 at ha
  change covDerivAlong (S.base.metric (T - b ^ 2))
      (fun u ↦ f u b) (fun u ↦ lVelocity (I := I) (fun v ↦ f v b) u) 0 =
    covDerivAlong (S.base.metric (T - b ^ 2)) beta
      (fun u ↦ mfderiv 𝓘(ℝ, ℝ) I beta u (1 : ℝ)) 0 at hb
  have hsecond := lRegularizedAction_second_variation_moving_endpoints
    S hS T f hf a b hgeo
  rw [ha, hb, hterminal.eq_of_nhds] at hsecond
  simp only [map_zero, zero_apply, sub_zero] at hsecond
  have hscaled := hsecond.div_const (2 * b)
  have hfun :
      (fun u ↦ deriv
        (fun v ↦ (head + lRegularizedAction S T (f v) a b) / (2 * b)) u) =
      (fun u ↦ deriv (fun v ↦ lRegularizedAction S T (f v) a b) u / (2 * b)) := by
    funext u
    rw [deriv_div_const, deriv_const_add]
  rw [hfun]
  apply hscaled.congr_deriv
  rw [add_div, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]

end DifferentialGeometry.PDE.RicciFlow.Perelman
