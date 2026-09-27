import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Ricci.Basic

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Curvature

theorem riemannOp_line_eq_zero (g : SmoothRiemannianMetric 𝓘(ℝ) ℝ)
    (t u v w : ℝ) : riemannOp (LeviCivita g) t u v w = 0 := by
  let A : ℝ →L[ℝ] ℝ →L[ℝ] ℝ →L[ℝ] ℝ := riemannOp (LeviCivita g) t
  have he : riemannOp (LeviCivita g) t (1 : ℝ) (1 : ℝ) w = 0 := by
    have hs := riemannOp_swap (LeviCivita g) t (1 : ℝ) (1 : ℝ) w
    change (show ℝ from riemannOp (LeviCivita g) t (1 : ℝ) (1 : ℝ) w) =
      -(show ℝ from riemannOp (LeviCivita g) t (1 : ℝ) (1 : ℝ) w) at hs
    change (show ℝ from riemannOp (LeviCivita g) t (1 : ℝ) (1 : ℝ) w) = 0
    linarith
  change A 1 1 w = 0 at he
  change A u v w = 0
  calc
    A u v w = A (u • (1 : ℝ)) (v • (1 : ℝ)) w := by
          simp only [smul_eq_mul, mul_one]
    _ = u • (v • A 1 1 w) := by
      rw [map_smul, smul_apply, map_smul, smul_apply, smul_apply]
      exact smul_comm v u _
    _ = 0 := by rw [he, smul_zero, smul_zero]

theorem ricciTensor_line_eq_zero (g : SmoothRiemannianMetric 𝓘(ℝ) ℝ)
    (t u v : ℝ) : ricciTensor g t u v = 0 := by
  have he : ricciEndo g t u v = 0 := by
    apply LinearMap.ext
    intro w
    exact riemannOp_line_eq_zero g t w u v
  exact (congrArg (LinearMap.trace ℝ (TangentSpace 𝓘(ℝ) t)) he).trans (map_zero _)

end DifferentialGeometry.Geometry.Curvature
