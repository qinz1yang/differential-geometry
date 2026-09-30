import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

open Set MeasureTheory

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem one_le_dimH_of_nonconstant_segment {a b : X} (hab : a ≠ b)
    {f : Icc (0 : ℝ) 1 → X}
    (hd : ∀ s t, dist (f s) (f t) = dist a b * dist s t) :
    1 ≤ dimH (univ : Set X) := by
  have hpos : 0 < dist a b := dist_pos.mpr hab
  have hanti : AntilipschitzWith ⟨(dist a b)⁻¹, by positivity⟩ f := by
    apply AntilipschitzWith.of_le_mul_dist
    intro s t
    change dist s t ≤ (dist a b)⁻¹ * dist (f s) (f t)
    rw [hd, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  have hI : dimH (Icc (0 : ℝ) 1) = 1 := by
    have hi : (interior (Icc (0 : ℝ) 1)).Nonempty := by
      rw [interior_Icc]
      exact ⟨1 / 2, by norm_num⟩
    simpa using Real.dimH_of_nonempty_interior hi
  have hsub : dimH (univ : Set (Icc (0 : ℝ) 1)) = 1 := by
    have h := (isometry_subtype_coe (s := Icc (0 : ℝ) 1)).dimH_image univ
    simpa only [image_univ, Subtype.range_coe, hI] using h.symm
  rw [← hsub]
  exact (hanti.le_dimH_image univ).trans (dimH_mono (subset_univ _))

theorem subsingleton_of_dimH_lt_one
    (hsegments : ∀ a b : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (hdim : dimH (univ : Set X) < 1) : Subsingleton X := by
  refine ⟨fun a b => ?_⟩
  by_contra hab
  obtain ⟨f, _, _, _, hd⟩ := hsegments a b
  exact (not_lt_of_ge (one_le_dimH_of_nonconstant_segment hab hd)) hdim

end Metric
