import Mathlib.Topology.ContinuousOn

set_option autoImplicit false

open Set

namespace Topology.IsClosedEmbedding

universe u v w

variable {C : Type u} {X : Type v} {Y : Type w}
  [TopologicalSpace C] [TopologicalSpace X] [TopologicalSpace Y]

theorem continuous_extend_of_isOpen_image
    {c : C → X} (hc : IsClosedEmbedding c) {U : Set C}
    (hU : IsOpen (c '' U)) {f : C → Y} {g : X → Y}
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ p, p ∉ U → f p = g (c p)) :
    Continuous (Function.extend c f g) := by
  have hcomp : ContinuousOn (Function.extend c f g ∘ c) univ := by
    rw [Function.extend_comp hc.injective f g]
    exact hf.continuousOn
  have hrange : ContinuousOn (Function.extend c f g) (range c) := by
    simpa only [image_univ] using
      (hc.isInducing.continuousOn_image_iff (s := univ)).mpr hcomp
  have houtside : EqOn (Function.extend c f g) g (c '' U)ᶜ := by
    intro x hx
    by_cases hcx : x ∈ range c
    · obtain ⟨p, rfl⟩ := hcx
      rw [hc.injective.extend_apply f g p]
      exact hfg p (fun hp => hx ⟨p, hp, rfl⟩)
    · exact Function.extend_apply' f g x hcx
  have hcover : range c ∪ (c '' U)ᶜ = univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ range c
    · exact Or.inl hx
    · exact Or.inr (fun ⟨p, _, hp⟩ => hx ⟨p, hp⟩)
  have hcont := hrange.union_of_isClosed (hg.continuousOn.congr houtside)
    hc.isClosed_range hU.isClosed_compl
  rw [hcover] at hcont
  exact continuousOn_univ.mp hcont

theorem exists_continuous_extension_of_isOpen_image
    {c : C → X} (hc : IsClosedEmbedding c) {U : Set C}
    (hU : IsOpen (c '' U)) {f : C → Y} {g : X → Y}
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ p, p ∉ U → f p = g (c p)) :
    ∃ F : X → Y, Continuous F ∧ (∀ p, F (c p) = f p) ∧
      ∀ x, x ∉ range c → F x = g x := by
  exact ⟨Function.extend c f g, hc.continuous_extend_of_isOpen_image hU hf hg hfg,
    hc.injective.extend_apply f g, fun x hx => Function.extend_apply' f g x hx⟩

end Topology.IsClosedEmbedding
