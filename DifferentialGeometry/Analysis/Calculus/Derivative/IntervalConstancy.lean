import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.DenselyOrdered

set_option autoImplicit false

noncomputable section

open Set

namespace Convex

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {f : ℝ → G} {s : Set ℝ} {a b : ℝ}

theorem is_const_of_hasDerivWithinAt_eq_zero (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasDerivWithinAt f 0 s x) (ha : a ∈ s) (hb : b ∈ s) : f a = f b := by
  have hbd : ‖f b - f a‖ ≤ (0 : ℝ) * ‖b - a‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0)
      (f' := fun _ : ℝ => (0 : G)) hf (fun x _ => by simp) hs ha hb
  have hzero : f b - f a = 0 :=
    norm_eq_zero.mp (le_antisymm (by simpa using hbd) (norm_nonneg _))
  exact (sub_eq_zero.mp hzero).symm

end Convex

namespace DifferentialGeometry

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {f : ℝ → G} {a b x y : ℝ}

theorem eq_of_hasDerivAt_zero_of_mem_Ioo
    (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b)
    (hf : ∀ z ∈ Set.Ioo a b, HasDerivAt f 0 z) : f x = f y := by
  rcases le_total x y with hxy | hyx
  · exact (convex_Icc x y).is_const_of_hasDerivWithinAt_eq_zero
      (fun z hz => (hf z ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩).hasDerivWithinAt)
      (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy)
  · exact ((convex_Icc y x).is_const_of_hasDerivWithinAt_eq_zero
      (fun z hz => (hf z ⟨lt_of_lt_of_le hy.1 hz.1, lt_of_le_of_lt hz.2 hx.2⟩).hasDerivWithinAt)
      (right_mem_Icc.mpr hyx) (left_mem_Icc.mpr hyx))

theorem eq_of_hasDerivAt_zero_on_Icc (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hf : ∀ z ∈ Set.Ioo a b, HasDerivAt f 0 z) :
    ∀ x ∈ Set.Icc a b, f x = f a := by
  rcases eq_or_lt_of_le hab with rfl | hablt
  · intro x hx
    rw [le_antisymm hx.2 hx.1]
  · have hc : (a + b) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
    have hclosed : IsClosed (Set.Icc a b ∩ f ⁻¹' {f ((a + b) / 2)}) :=
      hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hIoo : Set.Ioo a b ⊆ Set.Icc a b ∩ f ⁻¹' {f ((a + b) / 2)} := by
      intro z hz
      exact ⟨Set.Ioo_subset_Icc_self hz,
        eq_of_hasDerivAt_zero_of_mem_Ioo hz hc hf⟩
    have hclosure : Set.Icc a b = closure (Set.Ioo a b) :=
      (closure_Ioo (ne_of_lt hablt)).symm
    have hsub : Set.Icc a b ⊆ Set.Icc a b ∩ f ⁻¹' {f ((a + b) / 2)} := by
      intro x hx
      rw [hclosure] at hx
      exact closure_minimal hIoo hclosed hx
    intro x hx
    rw [(hsub hx).2, (hsub (left_mem_Icc.mpr hab)).2]

end DifferentialGeometry
