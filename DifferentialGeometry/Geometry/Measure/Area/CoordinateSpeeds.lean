import DifferentialGeometry.Geometry.Measure.Area.ManifoldDensity
import DifferentialGeometry.Geometry.Metric.CurveSpeedCalculus



noncomputable section

open Bundle Manifold Set DifferentialGeometry
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

set_option backward.isDefEq.respectTransparency false in


theorem riemannianCurveSpeed_affine_line (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : ℂ → M} {z : ℂ} (hu : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z)
    (w : ℂ) (a : ℝ) :
    riemannianCurveSpeed g (fun t => u (z + (t - a) • w)) a =
      Real.sqrt (g.inner (u z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z w)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z w)) := by
  have hδ : HasDerivAt (fun t : ℝ => z + (t - a) • w) w a := by
    simpa only [sub_zero, one_smul, zero_add, Pi.add_apply, id_eq] using!
      (hasDerivAt_const a z).add (((hasDerivAt_id a).sub_const a).smul_const w)
  have hu' : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u (z + (a - a) • w) := by
    simpa only [sub_self, zero_smul, add_zero] using hu
  have hs := riemannianCurveSpeed_comp g (r := u) (v := fun t : ℝ => z + (t - a) • w)
      (t := a) hu' hδ.differentiableAt
  erw [hδ.deriv, sub_self, zero_smul, add_zero] at hs
  exact hs




theorem riemannianAreaDensity_le_coordinate_speeds
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : ℂ → M) (z : ℂ) (a b : ℝ) :
    riemannianAreaDensity g u z ≤
      riemannianCurveSpeed g (fun t => u (z + (t - a) • (1 : ℂ))) a *
      riemannianCurveSpeed g (fun t => u (z + (t - b) • Complex.I)) b := by
  by_cases hu : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z
  · rw [riemannianCurveSpeed_affine_line g hu, riemannianCurveSpeed_affine_line g hu]
    exact tangentTwoJacobian_le g _ _
  · rw [riemannianAreaDensity_eq_zero_of_not_mdifferentiableAt g hu]
    exact mul_nonneg (riemannianCurveSpeed_nonneg g _ _) (riemannianCurveSpeed_nonneg g _ _)

end DifferentialGeometry.Geometry
