import DifferentialGeometry.Geometry.Metric.Approximation.ProductCollapse
import DifferentialGeometry.Geometry.Metric.Scaling.Rescale

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace GC.MetricGeometry

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace Y]

def rescaledProductFstApprox (p : E) (q : Y)
    (hY : Bornology.IsBounded (univ : Set Y)) (c : ℝ) (hc : 0 < c)
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hdiam : c * diam (univ : Set Y) < ε) :
    @PointedBallApprox (WithLp 2 (E × Y)) E
      ((inferInstance : MetricSpace (WithLp 2 (E × Y))).rescale c hc) _
      (WithLp.toLp 2 (p, q)) 0 R ε := by
  refine @PointedBallApprox.mk (WithLp 2 (E × Y)) E
    ((inferInstance : MetricSpace (WithLp 2 (E × Y))).rescale c hc) _
    (WithLp.toLp 2 (p, q)) 0 R ε hε hεR (fun x => c • (x.val.fst - p)) (by simp) ?_ ?_
  · intro x y
    change |dist (c • (x.val.fst - p)) (c • (y.val.fst - p)) - c * dist x.val y.val| < ε
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hc, dist_sub_right, ← mul_sub, abs_mul, abs_of_pos hc,
      abs_sub_comm]
    exact (mul_le_mul_of_nonneg_left
      ((WithLp.prod_dist_sub_dist_fst_le x.val y.val).trans
        (dist_le_diam_of_mem hY (mem_univ _) (mem_univ _))) hc.le).trans_lt hdiam
  · intro y hy
    let x := WithLp.toLp 2 (c⁻¹ • y + p, q)
    have hdist : c * dist x (WithLp.toLp 2 (p, q)) = dist y 0 := by
      simp [x, WithLp.prod_dist_eq_sqrt_sq_add_sq, dist_eq_norm, norm_smul,
        Real.norm_eq_abs, abs_of_pos hc, Real.sqrt_sq_eq_abs, mul_inv_cancel_left₀ hc.ne']
    refine ⟨⟨x, ?_⟩, ?_⟩
    · change c * dist x (WithLp.toLp 2 (p, q)) ≤ R
      rw [hdist]
      linarith
    · change dist y (c • (x.fst - p)) < ε
      simpa [x, smul_smul, hc.ne'] using hε

theorem pointedGHConverges_rescaled_normed_product [CompleteSpace E]
    (p : E) (q : Y) (hY : Bornology.IsBounded (univ : Set Y))
    {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) (hlim : Tendsto c atTop (𝓝 0)) :
    @PointedGHConverges (fun _ : ℕ => WithLp 2 (E × Y))
      (fun n => (inferInstance : MetricSpace (WithLp 2 (E × Y))).rescale (c n) (hc n)) E _
      (fun _ => WithLp.toLp 2 (p, q)) 0 := by
  refine ⟨inferInstance, fun R ε hε hεR => ?_⟩
  have hdlim : Tendsto (fun n => c n * diam (univ : Set Y)) atTop (𝓝 0) := by
    simpa using hlim.mul_const (diam (univ : Set Y))
  filter_upwards [hdlim.eventually (eventually_lt_nhds hε)] with n hn
  exact ⟨rescaledProductFstApprox p q hY (c n) (hc n) hε hεR hn⟩

end GC.MetricGeometry
