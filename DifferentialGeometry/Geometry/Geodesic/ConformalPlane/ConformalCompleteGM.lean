import DifferentialGeometry.Geometry.Metric.CompleteMetricExists
import DifferentialGeometry.Geometry.Connection.ConformalEuclidean
import DifferentialGeometry.Geometry.Measure.Area.ManifoldEuclidean

/-!
# 共形因子有正下界 ⇒ `(ℂ, ρ̃²|dz|²)` complete（O-W-GEO-MIN G1，后缀 `_GM`）

`riemannianMetricComplete_conformal_GM`：`ρ̃ ≥ δ > 0` 处处 ⇒ `conformalEuclideanMetric (log ρ̃)` 是
`RiemannianMetricComplete`。证明：`d_{ĝ}(x, y) ≥ δ ‖x − y‖`（`le_edistOf_of_quad` 与 Euclidean 度量比较，
`riemannianEDistOf_standardEuclideanMetric`），再用 `RiemannianMetricComplete.of_properFun`，
proper 函数取 `δ ‖·‖`。于是 Hopf–Rinow 的极小测地线对**整个** `ρ̃`-加权长度极小（不只在一个开集里）。
-/

set_option autoImplicit false

noncomputable section

open Set Metric Bundle Manifold
open scoped ContDiff Manifold ENNReal

namespace DifferentialGeometry.Geometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- 下界 `ρ̃ ≥ δ > 0` 的共形度量 `ρ̃² |dz|²` 是 complete 的。 -/
theorem riemannianMetricComplete_conformal_GM {ρt : ℂ → ℝ} (hρt : ∀ z, 0 < ρt z)
    (hf : ContDiff ℝ ∞ (fun z => Real.log (ρt z))) {δ : ℝ} (hδ : 0 < δ)
    (hδρ : ∀ z, δ ≤ ρt z) :
    RiemannianMetricComplete (I := 𝓘(ℝ, ℂ))
      (conformalEuclideanMetric (fun z => Real.log (ρt z)) hf) := by
  refine RiemannianMetricComplete.of_properFun (f := fun z : ℂ => δ * ‖z‖) ?_ ?_
  · intro c
    have hsub : {x : ℂ | δ * ‖x‖ ≤ c} ⊆ closedBall 0 (c / δ) := by
      intro x hx
      rw [mem_closedBall_zero_iff, le_div_iff₀ hδ]
      have hx' : δ * ‖x‖ ≤ c := hx
      linarith
    have hcl : IsClosed {x : ℂ | δ * ‖x‖ ≤ c} :=
      isClosed_le (continuous_const.mul continuous_norm) continuous_const
    exact (isCompact_closedBall 0 (c / δ)).of_isClosed_subset hcl hsub
  · intro x y
    have hl : ∀ (z : ℂ) (v : TangentSpace 𝓘(ℝ, ℂ) z),
        δ ^ 2 * (standardEuclideanMetric ℂ).inner z v v ≤
          (conformalEuclideanMetric (fun z => Real.log (ρt z)) hf).inner z v v := by
      intro z v
      change δ ^ 2 * inner ℝ (v : ℂ) v ≤ Real.exp (2 * Real.log (ρt z)) * inner ℝ (v : ℂ) v
      have h2 : Real.exp (2 * Real.log (ρt z)) = ρt z ^ 2 := by
        rw [show 2 * Real.log (ρt z) = Real.log (ρt z) + Real.log (ρt z) by ring,
          Real.exp_add, Real.exp_log (hρt z)]
        ring
      rw [h2]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hδ.le (hδρ z) 2)
        real_inner_self_nonneg
    have h1 := le_edistOf_of_quad (standardEuclideanMetric ℂ)
      (conformalEuclideanMetric (fun z => Real.log (ρt z)) hf) (by positivity : 0 < δ ^ 2) hl x y
    rw [riemannianEDistOf_standardEuclideanMetric, Real.sqrt_sq hδ.le] at h1
    refine le_trans ?_ h1
    rw [edist_dist, dist_eq_norm, ← ENNReal.ofReal_mul hδ.le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← mul_sub, abs_mul, abs_of_pos hδ]
    exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) hδ.le

end DifferentialGeometry.Geometry
