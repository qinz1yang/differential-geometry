import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Metric

namespace Isometry

variable {X : Type*} [MetricSpace X] {a b : ℝ} {σ : Icc a b → X}

theorem dist_IccExtend (hσ : Isometry σ) (hab : a ≤ b)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    dist (IccExtend hab σ s) (IccExtend hab σ t) = |s - t| := by
  rw [IccExtend_of_mem hab σ hs, IccExtend_of_mem hab σ ht,
    hσ.dist_eq, Subtype.dist_eq, Real.dist_eq]

theorem IccExtend_forward_radial (hσ : Isometry σ) {h : ℝ} (hh : h ∈ Icc a b)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (b - h)) :
    dist (σ ⟨h, hh⟩) (IccExtend (hh.1.trans hh.2) σ (h + s)) = s := by
  rw [← IccExtend_of_mem (hh.1.trans hh.2) σ hh,
    hσ.dist_IccExtend _ hh ⟨by linarith [hh.1, hh.2, hs.1], by linarith [hh.1, hh.2, hs.2]⟩]
  rw [show h - (h + s) = -s by ring, abs_neg, abs_of_nonneg hs.1]

theorem IccExtend_backward_radial (hσ : Isometry σ) {h : ℝ} (hh : h ∈ Icc a b)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (h - a)) :
    dist (σ ⟨h, hh⟩) (IccExtend (hh.1.trans hh.2) σ (h - s)) = s := by
  rw [← IccExtend_of_mem (hh.1.trans hh.2) σ hh,
    hσ.dist_IccExtend _ hh ⟨by linarith [hh.1, hh.2, hs.2], by linarith [hh.1, hh.2, hs.1]⟩]
  rw [show h - (h - s) = s by ring, abs_of_nonneg hs.1]

theorem IccExtend_forward_dist (hσ : Isometry σ) {h : ℝ} (hh : h ∈ Icc a b)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) (b - h)) (ht : t ∈ Icc (0 : ℝ) (b - h)) :
    dist (IccExtend (hh.1.trans hh.2) σ (h + s))
      (IccExtend (hh.1.trans hh.2) σ (h + t)) = |s - t| := by
  rw [hσ.dist_IccExtend _ ⟨by linarith [hh.1, hh.2, hs.1], by linarith [hh.1, hh.2, hs.2]⟩
    ⟨by linarith [hh.1, hh.2, ht.1], by linarith [hh.1, hh.2, ht.2]⟩]
  congr 1
  ring

theorem IccExtend_backward_dist (hσ : Isometry σ) {h : ℝ} (hh : h ∈ Icc a b)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) (h - a)) (ht : t ∈ Icc (0 : ℝ) (h - a)) :
    dist (IccExtend (hh.1.trans hh.2) σ (h - s))
      (IccExtend (hh.1.trans hh.2) σ (h - t)) = |s - t| := by
  rw [hσ.dist_IccExtend _ ⟨by linarith [hh.1, hh.2, hs.2], by linarith [hh.1, hh.2, hs.1]⟩
    ⟨by linarith [hh.1, hh.2, ht.2], by linarith [hh.1, hh.2, ht.1]⟩,
    show h - s - (h - t) = -(s - t) by ring, abs_neg]

theorem IccExtend_opposite_dist (hσ : Isometry σ) {h : ℝ} (hh : h ∈ Icc a b)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) (b - h)) (ht : t ∈ Icc (0 : ℝ) (h - a)) :
    dist (IccExtend (hh.1.trans hh.2) σ (h + s))
      (IccExtend (hh.1.trans hh.2) σ (h - t)) = s + t := by
  rw [hσ.dist_IccExtend _ ⟨by linarith [hh.1, hh.2, hs.1], by linarith [hh.1, hh.2, hs.2]⟩
    ⟨by linarith [hh.1, hh.2, ht.2], by linarith [hh.1, hh.2, ht.1]⟩,
    show h + s - (h - t) = s + t by ring, abs_of_nonneg (add_nonneg hs.1 ht.1)]

end Isometry
