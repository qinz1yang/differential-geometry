import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Klein
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Horosphere
import Mathlib.Topology.Algebra.Order.Field

open scoped Topology

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem tendsto_time_atTop_of_tendsto_kleinHomeomorph
    {α : Type*} {l : Filter α} {x : α → Hyperboloid E}
    {ζ : Metric.sphere (0 : E) 1}
    (hx : Filter.Tendsto (fun i => (kleinHomeomorph (x i) : E)) l (𝓝 (ζ : E))) :
    Filter.Tendsto (fun i => (x i).time) l Filter.atTop := by
  have hr : Filter.Tendsto (fun i => Real.sqrt (1 - ‖(kleinHomeomorph (x i) : E)‖ ^ 2))
      l (𝓝 (0 : ℝ)) := by
    simpa only [norm_eq_of_mem_sphere, one_pow, sub_self, Real.sqrt_zero] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (hx.norm.pow 2)).sqrt
  have hrpos (i : α) : 0 < Real.sqrt (1 - ‖(kleinHomeomorph (x i) : E)‖ ^ 2) := by
    apply Real.sqrt_pos.mpr
    have hn : ‖(kleinHomeomorph (x i) : E)‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using (kleinHomeomorph (x i)).property
    nlinarith [norm_nonneg (kleinHomeomorph (x i) : E)]
  have hr' : Filter.Tendsto (fun i => Real.sqrt (1 - ‖(kleinHomeomorph (x i) : E)‖ ^ 2))
      l (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hr, Filter.Eventually.of_forall hrpos⟩
  have ht (i : α) : (x i).time =
      (Real.sqrt (1 - ‖(kleinHomeomorph (x i) : E)‖ ^ 2))⁻¹ := by
    simpa only [Homeomorph.symm_apply_apply] using
      kleinHomeomorph_symm_time (kleinHomeomorph (x i))
  have h := tendsto_inv_nhdsGT_zero.comp hr'
  simpa only [Function.comp_def, ht] using h

theorem tendsto_time_sub_inner_atTop_of_tendsto_kleinHomeomorph
    {α : Type*} {l : Filter α} {x : α → Hyperboloid E}
    {ζ : Metric.sphere (0 : E) 1}
    (hx : Filter.Tendsto (fun i => (kleinHomeomorph (x i) : E)) l (𝓝 (ζ : E)))
    (ξ : Metric.sphere (0 : E) 1) (hne : ζ ≠ ξ) :
    Filter.Tendsto (fun i => (x i).time - inner ℝ (x i).space (ξ : E)) l Filter.atTop := by
  have hc : 0 < 1 - inner ℝ (ζ : E) (ξ : E) := sub_pos.mpr
    ((inner_lt_one_iff_real_of_norm_eq_one (norm_eq_of_mem_sphere ζ)
      (norm_eq_of_mem_sphere ξ)).mpr (fun h => hne (Subtype.ext h)))
  have hfactor : Filter.Tendsto (fun i => 1 - inner ℝ (kleinHomeomorph (x i) : E) (ξ : E))
      l (𝓝 (1 - inner ℝ (ζ : E) (ξ : E))) :=
    tendsto_const_nhds.sub (hx.inner tendsto_const_nhds)
  have h := (tendsto_time_atTop_of_tendsto_kleinHomeomorph hx).atTop_mul_pos hc hfactor
  convert h using 1
  funext i
  rw [kleinHomeomorph_apply_coe, real_inner_smul_left, mul_sub, mul_one,
    ← mul_assoc, mul_inv_cancel₀ (x i).time_pos.ne', one_mul]

theorem ideal_limit_eq_of_time_sub_inner_bounded
    {α : Type*} {l : Filter α} [l.NeBot] {x : α → Hyperboloid E}
    {ζ : Metric.sphere (0 : E) 1}
    (hx : Filter.Tendsto (fun i => (kleinHomeomorph (x i) : E)) l (𝓝 (ζ : E)))
    (ξ : Metric.sphere (0 : E) 1) {C : ℝ}
    (hbound : ∀ᶠ i in l, (x i).time - inner ℝ (x i).space (ξ : E) ≤ C) : ζ = ξ := by
  by_contra hne
  have h := (tendsto_time_sub_inner_atTop_of_tendsto_kleinHomeomorph hx ξ hne).eventually
    (Filter.eventually_gt_atTop C)
  obtain ⟨i, hi, hle⟩ := (h.and hbound).exists
  exact (not_lt_of_ge hle) hi

end DifferentialGeometry.Hyperboloid
