import DifferentialGeometry.Geometry.Curvature.Algebraic.SectionalLowerBound
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis.Laplacian DifferentialGeometry.CheegerGromovCompactness

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

theorem abs_metricRm04StandardAt_sub_le_of_riemannOp_sub_le
    (g G : SmoothRiemannianMetric I M) (x : M) {delta R K : ℝ}
    (hdelta : 0 ≤ delta)
    (hmetric : ∀ u v : TangentSpace I x,
      |g.inner x u v - G.inner x u v| ≤
        delta * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v))
    (hdiff : ∀ u v w : TangentSpace I x,
      let d := riemannOp (LeviCivita g) x u v w - riemannOp (LeviCivita G) x u v w
      Real.sqrt (G.inner x d d) ≤
        R * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) *
          Real.sqrt (G.inner x w w))
    (hmodel : ∀ u v w : TangentSpace I x,
      let r := riemannOp (LeviCivita G) x u v w
      Real.sqrt (G.inner x r r) ≤
        K * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) *
          Real.sqrt (G.inner x w w))
    (u v : TangentSpace I x) :
    |metricRm04StandardAt g x u v v u - metricRm04StandardAt G x u v v u| ≤
      ((1 + delta) * R + delta * K) * G.inner x u u * G.inner x v v := by
  let N (z : TangentSpace I x) := Real.sqrt (G.inner x z z)
  let r := riemannOp (LeviCivita g) x u v v
  let r0 := riemannOp (LeviCivita G) x u v v
  let d := r - r0
  have hd : N d ≤ R * N u * N v * N v := hdiff u v v
  have hr0 : N r0 ≤ K * N u * N v * N v := hmodel u v v
  have hr : N r ≤ (R + K) * N u * N v * N v := by
    have heq : r = d + r0 := by dsimp [d]; abel
    calc
      N r = N (d + r0) := congrArg N heq
      _ ≤ N d + N r0 := sqrt_inner_add_le G x d r0
      _ ≤ R * N u * N v * N v + K * N u * N v * N v := add_le_add hd hr0
      _ = _ := by ring
  have hmet : |g.inner x u r - G.inner x u r| ≤
      delta * N u * ((R + K) * N u * N v * N v) :=
    (hmetric u r).trans (mul_le_mul_of_nonneg_left hr (mul_nonneg hdelta (Real.sqrt_nonneg _)))
  have hcurv : |G.inner x u r - G.inner x u r0| ≤
      N u * (R * N u * N v * N v) := by
    rw [← map_sub]
    exact (abs_metric_inner_le_sqrt_metric_quadratic G x u d).trans
      (mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg _))
  rw [metricRm04StandardAt_eq_inner_riemannOp, metricRm04StandardAt_eq_inner_riemannOp]
  change |g.inner x u r - G.inner x u r0| ≤ _
  calc
    _ ≤ |g.inner x u r - G.inner x u r| + |G.inner x u r - G.inner x u r0| :=
      abs_sub_le _ _ _
    _ ≤ delta * N u * ((R + K) * N u * N v * N v) +
        N u * (R * N u * N v * N v) := add_le_add hmet hcurv
    _ = ((1 + delta) * R + delta * K) * (N u) ^ 2 * (N v) ^ 2 := by ring
    _ = _ := by
      dsimp only [N]
      rw [Real.sq_sqrt (metric_inner_self_nonneg G x u),
        Real.sq_sqrt (metric_inner_self_nonneg G x v)]

theorem metricRm04StandardAt_lower_bound_of_riemannOp_sub_le
    (g G : SmoothRiemannianMetric I M) (x : M) {delta R K c c' L : ℝ}
    (hdelta : 0 ≤ delta) (hc' : 0 ≤ c') (hL : 0 ≤ L)
    (hmetric : ∀ u v : TangentSpace I x,
      |g.inner x u v - G.inner x u v| ≤
        delta * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v))
    (hdiff : ∀ u v w : TangentSpace I x,
      let d := riemannOp (LeviCivita g) x u v w - riemannOp (LeviCivita G) x u v w
      Real.sqrt (G.inner x d d) ≤
        R * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) *
          Real.sqrt (G.inner x w w))
    (hmodel : ∀ u v w : TangentSpace I x,
      let r := riemannOp (LeviCivita G) x u v w
      Real.sqrt (G.inner x r r) ≤
        K * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) *
          Real.sqrt (G.inner x w w))
    (hupper : ∀ u : TangentSpace I x, g.inner x u u ≤ L * G.inner x u u)
    (hlower : ∀ u v : TangentSpace I x,
      c * (G.inner x u u * G.inner x v v - (G.inner x u v) ^ 2) ≤
        metricRm04StandardAt G x u v v u)
    (hsmall : ((1 + delta) * R + delta * K) + c' * L ^ 2 ≤ c) :
    ∀ u v : TangentSpace I x,
      c' * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) ≤
        metricRm04StandardAt g x u v v u := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)
  let : IsManifold I 3 M := IsManifold.of_le (n := ∞) (by decide)
  have hA : IsAlgCurvForm (fun u v w z : TangentSpace I x =>
      metricRm04StandardAt g x u v w z) :=
    mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)
  let G' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    { toFun := fun u => (G.inner x u).toLinearMap
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  let g' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    { toFun := fun u => (g.inner x u).toLinearMap
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  apply hA.sectional_lower_bound_of_orthogonal G' g' (G.pos x) (g.symm x)
  intro u v huv
  change G.inner x u v = 0 at huv
  have hlow := hlower u v
  rw [huv, sq, mul_zero, sub_zero] at hlow
  have herr := abs_metricRm04StandardAt_sub_le_of_riemannOp_sub_le
    g G x hdelta hmetric hdiff hmodel u v
  have hgram : g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≤
      L ^ 2 * (G.inner x u u * G.inner x v v) := by
    have hh := mul_le_mul (hupper u) (hupper v) (metric_inner_self_nonneg g x v)
      (mul_nonneg hL (metric_inner_self_nonneg G x u))
    calc
      _ ≤ g.inner x u u * g.inner x v v := sub_le_self _ (sq_nonneg _)
      _ ≤ (L * G.inner x u u) * (L * G.inner x v v) := hh
      _ = _ := by ring
  have hsmall' := mul_le_mul_of_nonneg_right hsmall
    (mul_nonneg (metric_inner_self_nonneg G x u) (metric_inner_self_nonneg G x v))
  have herr' := (abs_le.mp herr).1
  change c' * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) ≤ _
  calc
    _ ≤ c' * (L ^ 2 * (G.inner x u u * G.inner x v v)) :=
      mul_le_mul_of_nonneg_left hgram hc'
    _ ≤ metricRm04StandardAt g x u v v u := by nlinarith

end DifferentialGeometry.Geometry.Curvature
