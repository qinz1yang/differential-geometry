import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Connected.Clopen

noncomputable section
open Set Topology

namespace DifferentialGeometry.Topology.Covering

variable {B C : Type*} [TopologicalSpace B] [TopologicalSpace C]


theorem isOpenEmbedding_section {p : C → B} (hp : IsLocalHomeomorph p)
    (s : C(B, C)) (hs : Function.RightInverse s p) : IsOpenEmbedding s := by
  apply hp.isOpenEmbedding_of_comp _ s.continuous
  have heq : p ∘ s = id := funext hs
  rw [heq]
  exact (Homeomorph.refl B).isOpenEmbedding

theorem not_connected_of_double_cover_section [Nonempty B]
    {p : C → B} (hp : IsCoveringMap p) (τ : C → C) (hτ : Continuous τ)
    (hdeck : ∀ z, p (τ z) = p z) (hfree : ∀ z, τ z ≠ z)
    (hfiber : ∀ x y, p y = p x → y = x ∨ y = τ x)
    (s : C(B, C)) (hs : Function.RightInverse s p) : ¬ ConnectedSpace C := by
  let s' : C(B, C) := ⟨τ ∘ s, hτ.comp s.continuous⟩
  have hs' : Function.RightInverse s' p := fun b => (hdeck (s b)).trans (hs b)
  have hout (b : B) : s' b ∉ range s := by
    rintro ⟨b', hb'⟩
    have hbb : b' = b := (hs b').symm.trans ((congrArg p hb').trans (hs' b))
    subst b'
    exact hfree (s b) hb'.symm
  have hcompl : (range s)ᶜ = range s' := by
    ext z
    constructor
    · intro hz
      rcases hfiber (s (p z)) z (hs (p z)).symm with he | he
      · exact False.elim (hz ⟨p z, he.symm⟩)
      · exact ⟨p z, he.symm⟩
    · rintro ⟨b, rfl⟩
      exact hout b
  have hcl : IsClopen (range s) := by
    refine ⟨?_, (isOpenEmbedding_section hp.isLocalHomeomorph s hs).isOpen_range⟩
    rw [← isOpen_compl_iff, hcompl]
    exact (isOpenEmbedding_section hp.isLocalHomeomorph s' hs').isOpen_range
  intro hconn
  let := hconn
  let b : B := Classical.choice inferInstance
  rcases isClopen_iff.mp hcl with h | h
  · have hh : s b ∈ range s := mem_range_self b
    rw [h] at hh
    exact hh
  · exact hout b (h.symm ▸ mem_univ (s' b))

end DifferentialGeometry.Topology.Covering
