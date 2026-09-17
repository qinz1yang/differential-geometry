import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas

open Set

namespace Homeomorph

theorem image_sublevel_eq_of_image_level_eq
    {X : Type*} [TopologicalSpace X] (P : ℝ → X ≃ₜ X)
    {a b c : ℝ} {f : X → ℝ} (hf : Continuous f)
    (hP : ∀ x, ContinuousOn (fun t => P t x) (Icc a b))
    (hPa : P a = Homeomorph.refl X)
    (hlevel : ∀ t ∈ Icc a b, P t '' {x | f x = c} = {x | f x = c})
    (t : ℝ) (ht : t ∈ Icc a b) :
    P t '' {x | f x ≤ c} = {x | f x ≤ c} := by
  have hmem (s : ℝ) (hs : s ∈ Icc a b) (x : X) : f (P s x) = c ↔ f x = c := by
    change P s x ∈ {y | f y = c} ↔ x ∈ {y | f y = c}
    conv_lhs => rw [← hlevel s hs]
    exact (P s).injective.mem_set_image
  have hle (x : X) : f (P t x) ≤ c ↔ f x ≤ c := by
    have hcurve : ContinuousOn (fun s => f (P s x)) (Icc a t) :=
      (hf.comp_continuousOn (hP x)).mono (Icc_subset_Icc le_rfl ht.2)
    have hstart : f (P a x) = f x := by rw [hPa]; rfl
    constructor
    · intro htx
      by_contra hx
      have hx' : c < f x := lt_of_not_ge hx
      obtain ⟨s, hs, hsc⟩ := intermediate_value_Icc' ht.1 hcurve
        (show c ∈ Icc (f (P t x)) (f (P a x)) by rw [hstart]; exact ⟨htx, hx'.le⟩)
      have hxc := (hmem s ⟨hs.1, hs.2.trans ht.2⟩ x).mp hsc
      exact (ne_of_gt hx') hxc
    · intro hx
      by_contra htx
      have ht' : c < f (P t x) := lt_of_not_ge htx
      obtain ⟨s, hs, hsc⟩ := intermediate_value_Icc ht.1 hcurve
        (show c ∈ Icc (f (P a x)) (f (P t x)) by rw [hstart]; exact ⟨hx, ht'.le⟩)
      have hxc := (hmem s ⟨hs.1, hs.2.trans ht.2⟩ x).mp hsc
      exact (ne_of_gt ht') ((hmem t ht x).mpr hxc)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hle y).mpr hy
  · intro hx
    change f x ≤ c at hx
    exact ⟨(P t).symm x, (hle ((P t).symm x)).mp (by simpa only [(P t).apply_symm_apply] using hx),
      (P t).apply_symm_apply x⟩

end Homeomorph
