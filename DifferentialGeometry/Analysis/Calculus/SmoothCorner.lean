import DifferentialGeometry.Analysis.Calculus.SmoothMax
import Mathlib.Analysis.Calculus.Deriv.Mul

open Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def smoothCorner (ε : ℝ) (p v w : E) (t : ℝ) : E :=
  p + t • v + Real.smoothMax ε t 0 • (w - v)

namespace smoothCorner

theorem contDiff (ε : ℝ) (p v w : E) : ContDiff ℝ ∞ (smoothCorner ε p v w) :=
  (contDiff_const.add (contDiff_id.smul contDiff_const)).add
    (((Real.smoothMax.contDiff ε).comp (contDiff_id.prodMk contDiff_const)).smul contDiff_const)

theorem hasDerivAt (ε : ℝ) (p v w : E) (t : ℝ) :
    HasDerivAt (smoothCorner ε p v w)
      ((1 - deriv (fun x => Real.smoothMax ε x 0) t) • v +
        deriv (fun x => Real.smoothMax ε x 0) t • w) t := by
  have hs : ContDiff ℝ ∞ (fun x : ℝ => Real.smoothMax ε x 0) :=
    (Real.smoothMax.contDiff ε).comp (contDiff_id.prodMk contDiff_const)
  have hd := ((hasDerivAt_id t).smul_const v).const_add p |>.add
    ((hs.differentiable (by simp) t).hasDerivAt.smul_const (w - v))
  convert hd using 1
  · rfl
  · simp only [one_smul, smul_sub, sub_smul]
    abel

theorem deriv (ε : ℝ) (p v w : E) (t : ℝ) :
    _root_.deriv (smoothCorner ε p v w) t =
      (1 - _root_.deriv (fun x => Real.smoothMax ε x 0) t) • v +
        _root_.deriv (fun x => Real.smoothMax ε x 0) t • w :=
  (hasDerivAt ε p v w t).deriv

theorem deriv_mem_segment (ε : ℝ) (p v w : E) (t : ℝ) :
    _root_.deriv (smoothCorner ε p v w) t ∈ segment ℝ v w := by
  rw [deriv, segment_eq_image_lineMap]
  exact ⟨_, Real.smoothMax.deriv_left_mem_Icc ε t 0, AffineMap.lineMap_apply_module _ _ _⟩

theorem norm_deriv_sub_le (ε : ℝ) (p v w q : E) {r : ℝ}
    (hv : ‖v - q‖ ≤ r) (hw : ‖w - q‖ ≤ r) (t : ℝ) :
    ‖_root_.deriv (smoothCorner ε p v w) t - q‖ ≤ r := by
  rw [← dist_eq_norm]
  apply (Metric.mem_closedBall.mp ?_)
  exact (convex_closedBall q r).segment_subset
    (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hv)
    (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hw)
    (deriv_mem_segment ε p v w t)

theorem eq_left {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ -ε) (p v w : E) :
    smoothCorner ε p v w t = p + t • v := by
  have ht0 : t ≤ 0 := by linarith
  rw [smoothCorner, Real.smoothMax.eq_max_of_le hε (by
    rw [sub_zero, abs_of_nonpos ht0]
    linarith), max_eq_right ht0, zero_smul, add_zero]

theorem eq_right {ε t : ℝ} (hε : 0 < ε) (ht : ε ≤ t) (p v w : E) :
    smoothCorner ε p v w t = p + t • w := by
  have ht0 : 0 ≤ t := hε.le.trans ht
  rw [smoothCorner, Real.smoothMax.eq_max_of_le hε (by
    simpa only [sub_zero, abs_of_nonneg ht0] using ht), max_eq_left ht0, smul_sub]
  abel

theorem norm_sub_le {ε : ℝ} (hε : 0 < ε) (p v w : E) (t : ℝ) :
    ‖smoothCorner ε p v w t - (if t ≤ 0 then p + t • v else p + t • w)‖ ≤
      ε * ‖w - v‖ := by
  have hid : smoothCorner ε p v w t -
      (if t ≤ 0 then p + t • v else p + t • w) =
      (Real.smoothMax ε t 0 - max t 0) • (w - v) := by
    by_cases ht : t ≤ 0
    · rw [if_pos ht, max_eq_right ht, sub_zero, smoothCorner]
      abel
    · rw [if_neg ht, max_eq_left (le_of_not_ge ht), smoothCorner]
      simp only [sub_smul, smul_sub]
      abel
  rw [hid, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.smoothMax.sub_max_mem_Icc hε t 0).1]
  exact mul_le_mul_of_nonneg_right (Real.smoothMax.sub_max_mem_Icc hε t 0).2 (norm_nonneg _)

theorem deriv_ne_zero (ε : ℝ) (p v w : E) (L : E →L[ℝ] ℝ)
    (hv : 0 < L v) (hw : 0 < L w) (t : ℝ) :
    _root_.deriv (smoothCorner ε p v w) t ≠ 0 := by
  have hd := deriv_mem_segment ε p v w t
  have hpos : 0 < L (_root_.deriv (smoothCorner ε p v w) t) :=
    ((convex_Ioi (0 : ℝ)).linear_preimage L.toLinearMap).segment_subset hv hw hd
  intro hz
  simp only [hz, map_zero, lt_self_iff_false] at hpos

theorem strictMono_comp (ε : ℝ) (p v w : E) (L : E →L[ℝ] ℝ)
    (hv : 0 < L v) (hw : 0 < L w) :
    StrictMono (fun t => L (smoothCorner ε p v w t)) := by
  apply strictMono_of_deriv_pos
  intro t
  change 0 < _root_.deriv (L ∘ smoothCorner ε p v w) t
  rw [(L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt ε p v w t)).deriv]
  have hmem := deriv_mem_segment ε p v w t
  rw [deriv] at hmem
  exact ((convex_Ioi (0 : ℝ)).linear_preimage L.toLinearMap).segment_subset hv hw hmem

theorem injective (ε : ℝ) (p v w : E) (L : E →L[ℝ] ℝ)
    (hv : 0 < L v) (hw : 0 < L w) : Function.Injective (smoothCorner ε p v w) := by
  intro s t hst
  exact (strictMono_comp ε p v w L hv hw).injective (congrArg L hst)

theorem map_affine {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →ᵃ[ℝ] F) (ε : ℝ) (p v w : E) (t : ℝ) :
    f (smoothCorner ε p v w t) =
      smoothCorner ε (f p) (f.linear v) (f.linear w) t := by
  have hmap (q : E) (u : E) : f (q + u) = f q + f.linear u := by
    simpa only [vadd_eq_add, add_comm] using f.map_vadd q u
  simp only [smoothCorner, hmap, map_smul, map_sub]

end smoothCorner
end DifferentialGeometry.Analysis
