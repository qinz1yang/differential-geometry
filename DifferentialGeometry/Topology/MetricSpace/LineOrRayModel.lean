import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

open Set Metric

namespace Metric

variable {X : Type*} [MetricSpace X] [CompleteSpace X]

theorem exists_line_or_ray_isometry_of_isometry_range {f : X → ℝ} {p : X}
    (hf : Isometry f) (hfp : f p = 0)
    (hrange : Ici (0 : ℝ) ⊆ range f)
    (hcurves : ∀ x : X, ∃ c : unitInterval → X, Continuous c ∧ c 0 = p ∧ c 1 = x) :
    (∃ e : X ≃ᵢ ℝ, e p = 0 ∧ ∀ x, e x = f x) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ e : X ≃ᵢ Ici (0 : ℝ),
      (e p : ℝ) = a ∧ ∀ x, (e x : ℝ) = f x + a) := by
  classical
  let S := range f
  have hS0 : (0 : ℝ) ∈ S := ⟨p, hfp⟩
  have hclosed : IsClosed S := hf.antilipschitzWith.isClosed_range hf.uniformContinuous
  have hfill {y : X} {t : ℝ} (hty : f y ≤ t) (ht : t ≤ 0) : t ∈ S := by
    obtain ⟨c, hc, hc0, hc1⟩ := hcurves y
    obtain ⟨s, hs⟩ := intermediate_value_univ (1 : unitInterval) 0 (hf.continuous.comp hc)
      (show t ∈ Icc (f (c 1)) (f (c 0)) by rw [hc0, hc1, hfp]; exact ⟨hty, ht⟩)
    exact ⟨c s, hs⟩
  by_cases hB : BddBelow S
  · let l := sInf S
    have hlS : l ∈ S := hclosed.csInf_mem ⟨0, hS0⟩ hB
    have hl0 : l ≤ 0 := csInf_le hB hS0
    have hSl : S = Ici l := by
      apply Subset.antisymm
      · rintro t ⟨x, rfl⟩
        exact csInf_le hB (mem_range_self x)
      · intro t ht
        by_cases ht0 : 0 ≤ t
        · exact hrange ht0
        · obtain ⟨y, hy⟩ := hlS
          exact hfill (hy ▸ ht) (le_of_not_ge ht0)
    let F : X → Ici (0 : ℝ) := fun x =>
      ⟨f x - l, sub_nonneg.mpr (csInf_le hB (mem_range_self x))⟩
    have hF : Isometry F := by
      apply Isometry.of_dist_eq
      intro x y
      change |(f x - l) - (f y - l)| = dist x y
      rw [sub_sub_sub_cancel_right]
      exact hf.dist_eq x y
    have hsurj : Function.Surjective F := by
      intro t
      have htl : (t : ℝ) + l ∈ S := by
        rw [hSl]
        change l ≤ (t : ℝ) + l
        have ht0 : 0 ≤ (t : ℝ) := t.property
        linarith
      obtain ⟨x, hx⟩ := htl
      refine ⟨x, Subtype.ext ?_⟩
      change f x - l = (t : ℝ)
      linarith
    let e : X ≃ᵢ Ici (0 : ℝ) := ⟨Equiv.ofBijective F ⟨hF.injective, hsurj⟩, hF⟩
    refine Or.inr ⟨-l, neg_nonneg.mpr hl0, e, ?_, ?_⟩
    · change f p - l = -l
      rw [hfp, zero_sub]
    · intro x
      rfl
  · have hsurj : Function.Surjective f := by
      intro t
      by_cases ht : 0 ≤ t
      · exact hrange ht
      · obtain ⟨r, hr, hrt⟩ := not_bddBelow_iff.mp hB t
        obtain ⟨y, hy⟩ := hr
        exact hfill (hy ▸ hrt.le) (le_of_not_ge ht)
    let e : X ≃ᵢ ℝ := ⟨Equiv.ofBijective f ⟨hf.injective, hsurj⟩, hf⟩
    exact Or.inl ⟨e, hfp, fun _ => rfl⟩

end Metric
