import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic
import DifferentialGeometry.Geometry.Curve.VelocityScaling

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem lRegularizedLagrangian_parabolic
    (S : SolutionOn (I := I) (M := M) D)
    (t0 R T s : ℝ) (hR : 0 < R) (ht0 : t0 ∈ D.carrier)
    (alpha : ℝ → M) :
    lRegularizedLagrangian (parabolicSolution S t0 R hR ht0)
        (parabolicBackward t0 R T) (fun r => alpha ((Real.sqrt R)⁻¹ * r)) s =
      lRegularizedLagrangian S T alpha ((Real.sqrt R)⁻¹ * s) := by
  have hsqrt : Real.sqrt R ≠ 0 := (Real.sqrt_pos.mpr hR).ne'
  have htime : parabolicTime t0 R (parabolicBackward t0 R T - s ^ 2) =
      T - ((Real.sqrt R)⁻¹ * s) ^ 2 := by
    have hsq : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR.le
    unfold parabolicTime parabolicBackward
    field_simp [hR.ne', hsqrt]
    nlinarith
  have hvelocity : lVelocity (I := I) (fun r => alpha ((Real.sqrt R)⁻¹ * r)) s =
      (Real.sqrt R)⁻¹ • lVelocity (I := I) alpha ((Real.sqrt R)⁻¹ * s) := by
    exact DifferentialGeometry.Geometry.mfderiv_comp_mul_apply_one
      alpha (Real.sqrt R)⁻¹ (inv_ne_zero hsqrt) s
  unfold lRegularizedLagrangian
  rw [parabolicSolution_scalar]
  change (1 / 2 : ℝ) *
      (scaleMetric R hR (S.base.metric
        (parabolicTime t0 R (parabolicBackward t0 R T - s ^ 2)))).inner _ _ _ +
      2 * s ^ 2 * (R⁻¹ * S.scalar
        (parabolicTime t0 R (parabolicBackward t0 R T - s ^ 2))
        (alpha ((Real.sqrt R)⁻¹ * s))) = _
  rw [htime, hvelocity]
  simp only [scaleMetric_inner, map_smul, smul_apply, smul_eq_mul]
  have hsq : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR.le
  field_simp [hR.ne', hsqrt]
  rw [hsq]
  ring


theorem lRegularizedAction_parabolic
    (S : SolutionOn (I := I) (M := M) D)
    (t0 R T a b : ℝ) (hR : 0 < R) (ht0 : t0 ∈ D.carrier)
    (alpha : ℝ → M) :
    lRegularizedAction (parabolicSolution S t0 R hR ht0)
        (parabolicBackward t0 R T) (fun r => alpha ((Real.sqrt R)⁻¹ * r))
        (Real.sqrt R * a) (Real.sqrt R * b) =
      Real.sqrt R * lRegularizedAction S T alpha a b := by
  have hsqrt : Real.sqrt R ≠ 0 := (Real.sqrt_pos.mpr hR).ne'
  unfold lRegularizedAction
  simp_rw [lRegularizedLagrangian_parabolic S t0 R T _ hR ht0 alpha]
  rw [intervalIntegral.integral_comp_mul_left _ (inv_ne_zero hsqrt)]
  simp only [inv_inv, inv_mul_cancel_left₀ hsqrt, smul_eq_mul]

end DifferentialGeometry.PDE.RicciFlow.Perelman
