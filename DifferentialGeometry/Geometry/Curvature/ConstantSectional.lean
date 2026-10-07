import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
private local instance : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)
private local instance : IsManifold I 3 M := IsManifold.of_le (n := ∞) (by decide)

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem metric_gram_isAlgCurvForm (g : SmoothRiemannianMetric I M)
    (x : M) (K : ℝ) :
    IsAlgCurvForm (fun u v w z : TangentSpace I x =>
      K * (g.inner x u z * g.inner x v w - g.inner x u w * g.inner x v z)) where
  add_left := by
    intro u u' v w z
    simp only [map_add, add_apply]
    ring
  smul_left := by
    intro c u v w z
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  anti_first := by intros; ring
  anti_last := by intros; ring
  bianchi := by
    intro u v w z
    simp only [g.symm x]
    ring

/-- The actual sectional numerator determines all four slots of a constant
curvature tensor. This algebraic identity also holds at boundary points. -/
theorem metricRm04StandardAt_eq_of_constant_sectional_numerator
    (g : SmoothRiemannianMetric I M) (x : M) (K : ℝ)
    (hsec : ∀ u v : TangentSpace I x,
      metricRm04StandardAt g x u v v u =
        K * (g.inner x u u * g.inner x v v - g.inner x u v ^ 2))
    (u v w z : TangentSpace I x) :
    metricRm04StandardAt g x u v w z =
      K * (g.inner x u z * g.inner x v w - g.inner x u w * g.inner x v z) := by
  have hAlg : IsAlgCurvForm (fun a b c d : TangentSpace I x =>
      metricRm04StandardAt g x a b c d) :=
    mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)
  apply hAlg.ext (metric_gram_isAlgCurvForm g x K) _ u v w z
  intro a b
  rw [hAlg.anti_last a b a b, hsec a b, g.symm x b a]
  ring

variable [BoundarylessManifold I M]

/-- The vector curvature operator of a constant-sectional metric, with the
repository's convention `Rm(u,v,w,z) = g(z,R(u,v)w)`. -/
theorem riemannOp_eq_of_constant_sectional_numerator
    (g : SmoothRiemannianMetric I M) (x : M) (K : ℝ)
    (hsec : ∀ u v : TangentSpace I x,
      metricRm04StandardAt g x u v v u =
        K * (g.inner x u u * g.inner x v v - g.inner x u v ^ 2))
    (u v w : TangentSpace I x) :
    riemannOp (LeviCivita g) x u v w =
      K • (g.inner x v w • u - g.inner x u w • v) := by
  apply SmoothRiemannianMetric.eq_of_inner_eq g
  intro z
  rw [g.symm x (riemannOp (LeviCivita g) x u v w) z,
    ← metricRm04StandardAt_eq_inner_riemannOp,
    metricRm04StandardAt_eq_of_constant_sectional_numerator g x K hsec]
  simp only [map_smul, smul_apply, map_sub, sub_apply, smul_eq_mul]
  ring

/-- On an orthonormal plane the norm of `R(u,v)v` is exactly the absolute
sectional curvature. The norm uses the same original metric. -/
theorem sqrt_inner_riemannOp_self_eq_abs_of_constant_sectional_numerator
    (g : SmoothRiemannianMetric I M) (x : M) (K : ℝ)
    (hsec : ∀ u v : TangentSpace I x,
      metricRm04StandardAt g x u v v u =
        K * (g.inner x u u * g.inner x v v - g.inner x u v ^ 2))
    (u v : TangentSpace I x) (hu : g.inner x u u = 1)
    (hv : g.inner x v v = 1) (huv : g.inner x u v = 0) :
    Real.sqrt (g.inner x (riemannOp (LeviCivita g) x u v v)
      (riemannOp (LeviCivita g) x u v v)) = |K| := by
  rw [riemannOp_eq_of_constant_sectional_numerator g x K hsec,
    hv, huv, one_smul, zero_smul, sub_zero,
    DifferentialGeometry.Geometry.Riemannian.sqrt_inner_smul, hu,
    Real.sqrt_one, mul_one]

end DifferentialGeometry.Geometry.Curvature
