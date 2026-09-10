import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.MetricSpace.Holder

set_option autoImplicit false
open Set Metric Filter
open scoped NNReal ENNReal Topology
namespace DifferentialGeometry.Calculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : E → F} {s : Set E} {K : ℝ≥0}

theorem norm_sub_le_sq_of_fderiv_eq_zero (hs : Convex ℝ s)
    (hf : ∀ z ∈ s, DifferentiableAt ℝ f z)
    (hLip : LipschitzOnWith K (fderiv ℝ f) s)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) (hz : fderiv ℝ f x = 0) :
    ‖f y - f x‖ ≤ (K : ℝ) * ‖y - x‖ ^ 2 := by
  have hseg : segment ℝ x y ⊆ s := hs.segment_subset hx hy
  have hbound (z : E) (hzm : z ∈ segment ℝ x y) :
      ‖fderiv ℝ f z‖ ≤ (K : ℝ) * ‖y - x‖ := by
    have hh := hLip.dist_le_mul z (hseg hzm) x hx
    rw [dist_eq_norm,hz,sub_zero,dist_eq_norm] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hzm) K.property)
  calc
    _ ≤ ((K : ℝ) * ‖y - x‖) * ‖y - x‖ :=
      Convex.norm_image_sub_le_of_norm_fderiv_le (fun z hz => hf z (hseg hz)) hbound
        (convex_segment x y) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
    _ = _ := by ring

theorem holderOnWith_fderiv_zeroSet (hs : Convex ℝ s)
    (hf : ∀ z ∈ s, DifferentiableAt ℝ f z)
    (hLip : LipschitzOnWith K (fderiv ℝ f) s) :
    HolderOnWith K 2 f {x ∈ s | fderiv ℝ f x = 0} := by
  intro x hx y hy
  have hh := norm_sub_le_sq_of_fderiv_eq_zero hs hf hLip hy.1 hx.1 hy.2
  rw [← dist_eq_norm,← dist_eq_norm] at hh
  rw [edist_dist,edist_dist,show ((2 : ℝ≥0) : ℝ) = 2 from rfl,ENNReal.rpow_two]
  have hcoe : (K : ℝ≥0∞) = ENNReal.ofReal (K : ℝ) := by simp
  rw [hcoe,← ENNReal.ofReal_pow (dist_nonneg : 0 ≤ dist x y)]
  erw [← ENNReal.ofReal_mul K.property]
  exact ENNReal.ofReal_le_ofReal hh

theorem exists_holderOnWith_fderiv_zeroSet_ball {x : E}
    (hf : ContDiffAt ℝ 2 f x) :
    ∃ K : ℝ≥0, ∃ r > 0,
      HolderOnWith K 2 f {y ∈ ball x r | fderiv ℝ f y = 0} := by
  obtain ⟨K, t, ht, hLip⟩ :=
    (hf.fderiv_right (m := 1) (by norm_num)).exists_lipschitzOnWith
  have hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (hf.eventually (by norm_num)).mono fun y hy => hy.differentiableAt (by norm_num)
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp (inter_mem ht hd)
  exact ⟨K, r, hr, holderOnWith_fderiv_zeroSet (convex_ball x r)
    (fun y hy => (hrt hy).2) (hLip.mono (fun y hy => (hrt hy).1))⟩

end DifferentialGeometry.Calculus
