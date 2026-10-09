import DifferentialGeometry.Topology.MetricSpace.SegmentConcatenation

set_option autoImplicit false

open Set Metric

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem metric_endpoint_of_injOn_dist_ball
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {p : X} {r : ℝ} (hr : 0 < r)
    (hinj : (ball p r).InjOn (fun x => dist p x)) :
    ∀ x y : X, dist x p + dist p y = dist x y → x = p ∨ y = p := by
  apply (metric_endpoint_iff_not_mem_segment_interior hsegments p).mpr
  intro a b σ hσ t hat htb htp
  let δ := min (r / 2) (min (((t : ℝ) - a) / 2) ((b - t) / 2))
  have hδ : 0 < δ := lt_min (half_pos hr) (lt_min (by linarith) (by linarith))
  have hδr : δ < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hδa : δ ≤ ((t : ℝ) - a) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδb : δ ≤ (b - (t : ℝ)) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  let s : Icc a b := ⟨(t : ℝ) - δ, by constructor <;> linarith⟩
  let u : Icc a b := ⟨(t : ℝ) + δ, by constructor <;> linarith⟩
  have hds : dist p (σ s) = δ := by
    calc
      dist p (σ s) = dist (σ t) (σ s) := congrArg (fun w => dist w (σ s)) htp.symm
      _ = dist t s := hσ.dist_eq _ _
      _ = δ := by simp only [Subtype.dist_eq, Real.dist_eq, s]; rw [sub_sub_cancel, abs_of_pos hδ]
  have hdu : dist p (σ u) = δ := by
    calc
      dist p (σ u) = dist (σ t) (σ u) := congrArg (fun w => dist w (σ u)) htp.symm
      _ = dist t u := hσ.dist_eq _ _
      _ = δ := by simp only [Subtype.dist_eq, Real.dist_eq, u]; rw [sub_add_cancel_left, abs_neg, abs_of_pos hδ]
  have he := hinj (show σ s ∈ ball p r by rw [mem_ball, dist_comm, hds]; exact hδr)
    (show σ u ∈ ball p r by rw [mem_ball, dist_comm, hdu]; exact hδr) (hds.trans hdu.symm)
  have hsu := congrArg Subtype.val (hσ.injective he)
  change (t : ℝ) - δ = (t : ℝ) + δ at hsu
  linarith

theorem metric_endpoint_of_pointed_half_interval_chart
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {p : X} {r : ℝ} (hr : 0 < r) (e : Ico (0 : ℝ) r ≃ᵢ ball p r)
    (he0 : (e ⟨0, le_rfl, hr⟩ : X) = p) :
    ∀ x y : X, dist x p + dist p y = dist x y → x = p ∨ y = p := by
  have hcoord (x : ball p r) : dist p (x : X) = (e.symm x : ℝ) := by
    calc
      dist p (x : X) = dist (e ⟨0, le_rfl, hr⟩) x := by rw [Subtype.dist_eq, he0]
      _ = dist (e ⟨0, le_rfl, hr⟩) (e (e.symm x)) := by rw [e.apply_symm_apply]
      _ = dist (⟨0, le_rfl, hr⟩ : Ico (0 : ℝ) r) (e.symm x) := e.dist_eq _ _
      _ = (e.symm x : ℝ) := by
        simp only [Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (e.symm x).property.1]
  apply metric_endpoint_of_injOn_dist_ball hsegments hr
  intro x hx y hy hxy
  have hc : (e.symm ⟨x, hx⟩ : ℝ) = (e.symm ⟨y, hy⟩ : ℝ) := by
    rw [← hcoord, ← hcoord]
    exact hxy
  exact congrArg Subtype.val (e.symm.injective (Subtype.ext hc))

end Metric
