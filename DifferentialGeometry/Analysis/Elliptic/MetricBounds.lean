import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure
import DifferentialGeometry.Analysis.Integration.Measure.Family
import DifferentialGeometry.Tensor.RSTensor.Defs

/-!
# Pointwise and uniform bounds for the metric inner product

This file collects pointwise and uniform bounds for the metric inner
product `g.inner x : E →L[ℝ] E →L[ℝ] ℝ` of a smooth Riemannian metric
`g` on a smooth manifold `(M, g)`.

## Main results (pointwise)

* `metric_inner_self_nonneg`: $g.inner\,x\,v\,v \ge 0$.
* `abs_metric_inner_le_sqrt_metric_quadratic`: pointwise Cauchy–Schwarz
  inequality, $|g.inner\,x\,v\,w| \le \sqrt{g.inner\,x\,v\,v} \sqrt{g.inner\,x\,w\,w}$.
* `abs_metric_inner_le_metricInnerOpNorm`: pointwise operator-norm bound,
  $|g.inner\,x\,v\,w| \le \|g.inner\,x\| \cdot \|v\| \cdot \|w\|$.

The pointwise bounds suffice for many applications. Uniform bounds on a
compact manifold (e.g., a uniform constant `C > 0` such that
`‖g.inner b‖ ≤ C` for all `b ∈ M`) require additional chart-localization
machinery and are deferred to dedicated downstream files when needed.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Function
open scoped Manifold Topology ContDiff ENNReal NNReal Matrix BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

/-- Non-negativity of `g.inner x v v`. -/
lemma metric_inner_self_nonneg
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with hv0 | hv0
  · have heq : g.inner x v v = 0 := by rw [hv0]; simp
    rw [heq]
  · exact (g.pos x v hv0).le

/-- Cauchy–Schwarz inequality for the metric inner product (squared form):
$(g(v, w))^2 \le g(v, v) \cdot g(w, w)$. -/
lemma metric_inner_cauchy_schwarz_sq
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    (g.inner x v w) ^ 2 ≤ g.inner x v v * g.inner x w w := by
  classical
  set a := g.inner x v v
  set b := g.inner x w w
  set c := g.inner x v w
  have ha_nn : 0 ≤ a := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · have heq : a = 0 := by change g.inner x v v = 0; rw [hv0]; simp
      rw [heq]
    · exact (g.pos x v hv0).le
  have hb_nn : 0 ≤ b := by
    rcases eq_or_ne w 0 with hw0 | hw0
    · have heq : b = 0 := by change g.inner x w w = 0; rw [hw0]; simp
      rw [heq]
    · exact (g.pos x w hw0).le
  have hquad : ∀ t : ℝ, 0 ≤ t * t * a + 2 * t * c + b := by
    intro t
    have hpos : 0 ≤ g.inner x (t • v + w) (t • v + w) := by
      rcases eq_or_ne (t • v + w) 0 with hz | hnz
      · have heqz : g.inner x (t • v + w) (t • v + w) = 0 := by rw [hz]; simp
        rw [heqz]
      · exact (g.pos x _ hnz).le
    have h_expand : g.inner x (t • v + w) (t • v + w) =
        t * t * a + 2 * t * c + b := by
      have h1 : g.inner x (t • v + w) (t • v + w) =
          g.inner x (t • v) (t • v + w) + g.inner x w (t • v + w) := by
        rw [map_add (g.inner x), ContinuousLinearMap.add_apply]
      have h2 : g.inner x (t • v) (t • v + w) =
          g.inner x (t • v) (t • v) + g.inner x (t • v) w :=
        map_add (g.inner x (t • v)) (t • v) w
      have h3 : g.inner x w (t • v + w) =
          g.inner x w (t • v) + g.inner x w w :=
        map_add (g.inner x w) (t • v) w
      have h4 : g.inner x (t • v) (t • v) = t * (t * a) := by
        change g.inner x (t • v) (t • v) = t * (t * a)
        rw [map_smul (g.inner x), ContinuousLinearMap.smul_apply,
          map_smul (g.inner x v), smul_eq_mul, smul_eq_mul]
      have h5 : g.inner x (t • v) w = t * c := by
        change g.inner x (t • v) w = t * c
        rw [map_smul (g.inner x), ContinuousLinearMap.smul_apply, smul_eq_mul]
      have h6 : g.inner x w (t • v) = t * c := by
        change g.inner x w (t • v) = t * c
        rw [map_smul (g.inner x w), smul_eq_mul, g.symm x w v]
      rw [h1, h2, h3, h4, h5, h6]
      ring
    rw [h_expand] at hpos
    exact hpos
  rcases lt_or_eq_of_le ha_nn with ha_pos | ha_zero
  · have hroot := hquad (-c / a)
    have hsimp : -c / a * (-c / a) * a + 2 * (-c / a) * c + b = b - c^2 / a := by
      field_simp
      ring
    rw [hsimp] at hroot
    have hcsa : c ^ 2 / a ≤ b := by linarith
    have h1 : c ^ 2 = a * (c ^ 2 / a) := by field_simp
    rw [h1]
    exact mul_le_mul_of_nonneg_left hcsa ha_nn
  · have ha_eq : a = 0 := ha_zero.symm
    have hv_zero : v = 0 := by
      by_contra hne
      exact (lt_irrefl (0 : ℝ)) (ha_eq ▸ g.pos x v hne)
    have hc_eq : c = 0 := by
      change g.inner x v w = 0
      rw [hv_zero]; simp
    rw [hc_eq, ha_eq]
    simp

/-- The pointwise Cauchy–Schwarz inequality (absolute value form): $|g(v, w)|
\le \sqrt{g(v, v)} \sqrt{g(w, w)}$. -/
lemma abs_metric_inner_le_sqrt_metric_quadratic
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    |g.inner x v w| ≤ Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by
  have ha_nn : 0 ≤ g.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g x v
  have hb_nn : 0 ≤ g.inner x w w := metric_inner_self_nonneg (I := I) (M := M) g x w
  have hCS_sq := metric_inner_cauchy_schwarz_sq (I := I) (M := M) g x v w
  have h_abs_sq : |g.inner x v w| ^ 2 ≤ g.inner x v v * g.inner x w w := by
    rw [sq_abs]; exact hCS_sq
  have hsqrt_mul : Real.sqrt (g.inner x v v * g.inner x w w) =
      Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) :=
    Real.sqrt_mul ha_nn _
  have h_abs_nn : 0 ≤ |g.inner x v w| := abs_nonneg _
  have h_le_sqrt : |g.inner x v w| ≤ Real.sqrt (g.inner x v v * g.inner x w w) := by
    rw [show |g.inner x v w| = Real.sqrt (|g.inner x v w| ^ 2) from
      (Real.sqrt_sq h_abs_nn).symm]
    exact Real.sqrt_le_sqrt h_abs_sq
  rw [hsqrt_mul] at h_le_sqrt
  exact h_le_sqrt

set_option linter.unusedSectionVars false in
/-- The square root of the metric quadratic form satisfies the triangle
inequality on each tangent fibre. -/
lemma gNorm_add_le
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    Real.sqrt (g.inner x (v + w) (v + w)) ≤
      Real.sqrt (g.inner x v v) + Real.sqrt (g.inner x w w) := by
  have hv : 0 ≤ g.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g x v
  have hw : 0 ≤ g.inner x w w := metric_inner_self_nonneg (I := I) (M := M) g x w
  have hvw : g.inner x v w ≤
      Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) :=
    (le_abs_self _).trans
      (abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g x v w)
  have hexpand : g.inner x (v + w) (v + w) =
      g.inner x v v + 2 * g.inner x v w + g.inner x w w := by
    rw [map_add (g.inner x), ContinuousLinearMap.add_apply,
      map_add (g.inner x v), map_add (g.inner x w), g.symm x w v]
    ring
  have hsum : 0 ≤ Real.sqrt (g.inner x v v) + Real.sqrt (g.inner x w w) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [show Real.sqrt (g.inner x v v) + Real.sqrt (g.inner x w w) =
      Real.sqrt ((Real.sqrt (g.inner x v v) + Real.sqrt (g.inner x w w)) ^ 2) from
    (Real.sqrt_sq hsum).symm]
  refine Real.sqrt_le_sqrt ?_
  rw [hexpand, add_sq, Real.sq_sqrt hv, Real.sq_sqrt hw]
  linarith

/-- Pointwise operator norm of `g.inner x` as a bilinear form on `TangentSpace I x`. -/
noncomputable def metricInnerOpNorm
    (g : SmoothRiemannianMetric I M) (x : M) : ℝ :=
  ‖g.inner x‖

/-- The pointwise operator-norm bound: `|g.inner b v w| ≤ metricInnerOpNorm · ‖v‖ · ‖w‖`.
This uses the bilinear-CLM operator norm `ContinuousLinearMap.le_opNorm₂`. -/
lemma abs_metric_inner_le_metricInnerOpNorm
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    |g.inner x v w| ≤ metricInnerOpNorm (I := I) (M := M) g x * ‖v‖ * ‖w‖ := by
  have h := ContinuousLinearMap.le_opNorm₂ (g.inner x) v w
  rwa [Real.norm_eq_abs] at h

end Laplacian
end Analysis
end DifferentialGeometry

end
