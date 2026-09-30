import DifferentialGeometry.Geometry.Metric.SegmentLog
import DifferentialGeometry.Geometry.Comparison.FourPoint

set_option autoImplicit false

open Set Metric Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem dist_le_dist_segmentLog_of_fourPointComparison_zero
    {X : Type*} [MetricSpace X] {q : X} [HasAnglesAt q]
    (hcomp : fourPointComparison 0 (univ : Set X))
    (x y : X) (γ : Icc (0 : ℝ) (dist q x) → X)
    (τ : Icc (0 : ℝ) (dist q y) → X)
    (hγ : Isometry γ) (hτ : Isometry τ)
    (hγ0 : γ ⟨0, le_rfl, dist_nonneg⟩ = q)
    (hτ0 : τ ⟨0, le_rfl, dist_nonneg⟩ = q)
    (hγend : γ ⟨dist q x, dist_nonneg, le_rfl⟩ = x)
    (hτend : τ ⟨dist q y, dist_nonneg, le_rfl⟩ = y) :
    dist x y ≤ dist (segmentLog x γ hγ hγ0) (segmentLog y τ hτ hτ0) := by
  have hlim := dist_div_tendsto_segmentLog x y γ τ hγ hτ hγ0 hτ0
  apply ge_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  have hxt : dist q x * t ∈ Icc (0 : ℝ) (dist q x) :=
    ⟨mul_nonneg dist_nonneg ht.1.le, mul_le_of_le_one_right dist_nonneg ht.2.le⟩
  have hyt : dist q y * t ∈ Icc (0 : ℝ) (dist q y) :=
    ⟨mul_nonneg dist_nonneg ht.1.le, mul_le_of_le_one_right dist_nonneg ht.2.le⟩
  let xt := γ ⟨dist q x * t, hxt⟩
  let yt := τ ⟨dist q y * t, hyt⟩
  have hx0 : dist q xt = t * dist q x := by
    conv_lhs => rw [← hγ0, hγ.dist_eq]
    change |(0 : ℝ) - dist q x * t| = _
    rw [zero_sub, abs_neg, abs_of_nonneg hxt.1, mul_comm]
  have hy0 : dist q yt = t * dist q y := by
    conv_lhs => rw [← hτ0, hτ.dist_eq]
    change |(0 : ℝ) - dist q y * t| = _
    rw [zero_sub, abs_neg, abs_of_nonneg hyt.1, mul_comm]
  have hxend : dist xt x = (1 - t) * dist q x := by
    conv_lhs => rw [← hγend, hγ.dist_eq]
    change |dist q x * t - dist q x| = _
    rw [abs_of_nonpos (by linarith [hxt.2])]
    ring
  have hyend : dist yt y = (1 - t) * dist q y := by
    conv_lhs => rw [← hτend, hτ.dist_eq]
    change |dist q y * t - dist q y| = _
    rw [abs_of_nonpos (by linarith [hyt.2])]
    ring
  have hfirst := quadratic_side_comparison_of_fourPointComparison hcomp
    (mem_univ q) (mem_univ x) (mem_univ xt) (mem_univ yt) ⟨ht.1.le, ht.2.le⟩ hx0 hxend
  have hsecond := quadratic_side_comparison_of_fourPointComparison hcomp
    (mem_univ q) (mem_univ y) (mem_univ yt) (mem_univ x) ⟨ht.1.le, ht.2.le⟩ hy0 hyend
  rw [dist_comm yt q, hy0, dist_comm yt x, dist_comm yt xt] at hfirst
  rw [dist_comm x q] at hsecond
  have hsecond' := mul_le_mul_of_nonneg_left hsecond ht.1.le
  have hsq : (t * dist x y) ^ 2 ≤ dist xt yt ^ 2 := by nlinarith
  have hbound : t * dist x y ≤ dist xt yt :=
    (sq_le_sq₀ (mul_nonneg ht.1.le dist_nonneg) dist_nonneg).mp hsq
  rw [IccExtend_of_mem dist_nonneg γ hxt, IccExtend_of_mem dist_nonneg τ hyt]
  exact (le_div_iff₀ ht.1).mpr (by simpa [xt, yt, mul_comm] using hbound)

end DifferentialGeometry.Geometry.Comparison.Toponogov
