import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Geometry.Curvature.Line
import DifferentialGeometry.Geometry.Metric.Cylinder

set_option autoImplicit false
noncomputable section
open Bundle DifferentialGeometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

private theorem riemannOp_real_eq_zero (g : SmoothRiemannianMetric 𝓘(ℝ) ℝ)
    (x : ℝ) (u v w : TangentSpace 𝓘(ℝ) x) :
    riemannOp (LeviCivita g) x u v w = 0 :=
  riemannOp_line_eq_zero g x u v w

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

theorem riemannOp_cylinderMetric (g : SmoothRiemannianMetric I M)
    (x : M × ℝ) (u v w : TangentSpace (I.prod 𝓘(ℝ)) x) :
    riemannOp (LeviCivita (cylinderMetric g)) x u v w =
      (riemannOp (LeviCivita g) x.1 u.1 v.1 w.1, 0) := by
  unfold cylinderMetric
  exact (riemannOp_productMetric g _ x u v w).trans (by
    apply Prod.ext
    · rfl
    · exact riemannOp_real_eq_zero _ x.2 u.2 v.2 w.2)

theorem riemannOp_cylinderAxis_left (g : SmoothRiemannianMetric I M)
    (x : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ)) x) :
    riemannOp (LeviCivita (cylinderMetric g)) x (cylinderAxis x) v w = 0 := by
  apply (riemannOp_cylinderMetric g x _ _ _).trans
  apply Prod.ext
  · change riemannOp (LeviCivita g) x.1 (0 : TangentSpace I x.1) v.1 w.1 = 0
    rw [(riemannOp (LeviCivita g) x.1).map_zero]
    rfl
  · rfl

theorem riemannOp_cylinderAxis_middle (g : SmoothRiemannianMetric I M)
    (x : M × ℝ) (u w : TangentSpace (I.prod 𝓘(ℝ)) x) :
    riemannOp (LeviCivita (cylinderMetric g)) x u (cylinderAxis x) w = 0 := by
  apply (riemannOp_cylinderMetric g x _ _ _).trans
  apply Prod.ext
  · change riemannOp (LeviCivita g) x.1 u.1 (0 : TangentSpace I x.1) w.1 = 0
    rw [(riemannOp (LeviCivita g) x.1 u.1).map_zero]
    rfl
  · rfl

theorem riemannOp_cylinderAxis_right (g : SmoothRiemannianMetric I M)
    (x : M × ℝ) (u v : TangentSpace (I.prod 𝓘(ℝ)) x) :
    riemannOp (LeviCivita (cylinderMetric g)) x u v (cylinderAxis x) = 0 := by
  apply (riemannOp_cylinderMetric g x _ _ _).trans
  apply Prod.ext
  · change riemannOp (LeviCivita g) x.1 u.1 v.1 (0 : TangentSpace I x.1) = 0
    exact map_zero _
  · rfl

theorem inner_riemannOp_cylinderMetric (g : SmoothRiemannianMetric I M)
    (x : M × ℝ) (t u v w : TangentSpace (I.prod 𝓘(ℝ)) x) :
    (cylinderMetric g).inner x t (riemannOp (LeviCivita (cylinderMetric g)) x u v w) =
      g.inner x.1 t.1 (riemannOp (LeviCivita g) x.1 u.1 v.1 w.1) := by
  rw [riemannOp_cylinderMetric]
  have h := cylinderMetric_inner g x t
    (show TangentSpace (I.prod 𝓘(ℝ)) x from by
      exact (riemannOp (LeviCivita g) x.1 u.1 v.1 w.1, 0))
  exact h.trans (by simp)

end DifferentialGeometry.Geometry.Curvature
