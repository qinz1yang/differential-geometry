import DifferentialGeometry.Topology.Covering.DoubleCoverComponents
import Mathlib.Data.Set.Card
import Mathlib.Topology.LocalAtTarget

noncomputable section

open Set

namespace DifferentialGeometry.Topology.Covering

variable {B C : Type*}

theorem exists_unique_ne_of_fiber_encard_eq_two {p : C → B} (x : C)
    (hcard : (p ⁻¹' {p x}).encard = 2) :
    ∃! y, p y = p x ∧ y ≠ x := by
  obtain ⟨a, b, hab, hfiber⟩ := encard_eq_two.mp hcard
  have ha : a ∈ p ⁻¹' {p x} := by
    rw [hfiber]
    exact Or.inl rfl
  have hb : b ∈ p ⁻¹' {p x} := by
    rw [hfiber]
    exact Or.inr rfl
  have hx : x ∈ ({a, b} : Set C) := by
    rw [← hfiber]
    exact rfl
  rcases hx with hxa | hxb
  · refine ⟨b, ⟨hb, ?_⟩, ?_⟩
    · intro hbx
      exact hab (hxa.symm.trans hbx.symm)
    · intro y hy
      have hyfiber : y ∈ ({a, b} : Set C) := by
        rw [← hfiber]
        exact hy.1
      rcases hyfiber with hya | hyb
      · exact False.elim (hy.2 (hya.trans hxa.symm))
      · exact hyb
  · refine ⟨a, ⟨ha, ?_⟩, ?_⟩
    · intro hax
      exact hab (hax.trans hxb)
    · intro y hy
      have hyfiber : y ∈ ({a, b} : Set C) := by
        rw [← hfiber]
        exact hy.1
      rcases hyfiber with hya | hyb
      · exact hya
      · exact False.elim (hy.2 (hyb.trans hxb.symm))

noncomputable def fiberSwap (p : C → B)
    (hcard : ∀ b, (p ⁻¹' {b}).encard = 2) (x : C) : C :=
  Classical.choose (exists_unique_ne_of_fiber_encard_eq_two x (hcard (p x)))

theorem fiberSwap_spec (p : C → B)
    (hcard : ∀ b, (p ⁻¹' {b}).encard = 2) (x : C) :
    p (fiberSwap p hcard x) = p x ∧ fiberSwap p hcard x ≠ x :=
  Classical.choose_spec (exists_unique_ne_of_fiber_encard_eq_two x (hcard (p x))) |>.1

theorem eq_or_eq_fiberSwap (p : C → B)
    (hcard : ∀ b, (p ⁻¹' {b}).encard = 2) (x y : C)
    (hpy : p y = p x) : y = x ∨ y = fiberSwap p hcard x := by
  by_cases hyx : y = x
  · exact Or.inl hyx
  · exact Or.inr
      ((Classical.choose_spec (exists_unique_ne_of_fiber_encard_eq_two x (hcard (p x)))).2
        y ⟨hpy, hyx⟩)

theorem encard_fiber_restrictPreimage (p : C → B) (J : Set B) (j : J) :
    ((J.restrictPreimage p) ⁻¹' {j}).encard = (p ⁻¹' {(j : B)}).encard := by
  let C' := p ⁻¹' J
  let F : Set C' := (J.restrictPreimage p) ⁻¹' {j}
  have himage : ((↑) : C' → C) '' F = p ⁻¹' {(j : B)} := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact congrArg Subtype.val hz
    · intro hx
      have hxJ : p x ∈ J := by
        change p x = (j : B) at hx
        rw [hx]
        exact j.2
      refine ⟨(⟨x, hxJ⟩ : C'), ?_, rfl⟩
      apply Subtype.ext
      exact hx
  calc
    F.encard = (((↑) : C' → C) '' F).encard :=
      (Subtype.val_injective.encard_image F).symm
    _ = (p ⁻¹' {(j : B)}).encard := congrArg Set.encard himage

theorem connectedSpace_or_exists_exactly_two_components
    [TopologicalSpace B] [TopologicalSpace C] [ConnectedSpace B] [Nonempty C] {p : C → B}
    (hp : IsCoveringMap p) (hclosed : IsClosedMap p)
    (hcard : ∀ b, (p ⁻¹' {b}).encard = 2) :
    ConnectedSpace C ∨
      ∃ x y : C,
        Disjoint (connectedComponent x) (connectedComponent y) ∧
        connectedComponent x ∪ connectedComponent y = univ ∧
        (∃ e : connectedComponent x ≃ₜ B, ∀ z : connectedComponent x, e z = p z) ∧
        ∃ e : connectedComponent y ≃ₜ B, ∀ z : connectedComponent y, e z = p z := by
  by_cases hconn : ConnectedSpace C
  · exact Or.inl hconn
  · exact Or.inr (exists_exactly_two_components_of_not_connected hp hclosed
      (fiberSwap p hcard) (eq_or_eq_fiberSwap p hcard) hconn)

theorem connectedSpace_or_exists_exactly_two_components_restrictPreimage
    [TopologicalSpace B] [TopologicalSpace C] {p : C → B} (J : Set B)
    [ConnectedSpace J] (hp : IsCoveringMap p) (hclosed : IsClosedMap p)
    (hcard : ∀ b, (p ⁻¹' {b}).encard = 2) :
    ConnectedSpace (p ⁻¹' J) ∨
      ∃ x y : p ⁻¹' J,
        Disjoint (connectedComponent x) (connectedComponent y) ∧
        connectedComponent x ∪ connectedComponent y = univ ∧
        (∃ e : connectedComponent x ≃ₜ J,
          ∀ z : connectedComponent x, e z = J.restrictPreimage p z) ∧
        ∃ e : connectedComponent y ≃ₜ J,
          ∀ z : connectedComponent y, e z = J.restrictPreimage p z := by
  let j : J := Classical.arbitrary J
  obtain ⟨a, _, _, hfiber⟩ := encard_eq_two.mp (hcard j)
  have ha : a ∈ p ⁻¹' {(j : B)} := by
    rw [hfiber]
    exact Or.inl rfl
  have haJ : p a ∈ J := by
    change p a = (j : B) at ha
    rw [ha]
    exact j.2
  let _ : Nonempty (p ⁻¹' J) := ⟨⟨a, haJ⟩⟩
  apply connectedSpace_or_exists_exactly_two_components
    (hp.restrictPreimage J) (hclosed.restrictPreimage J)
  intro b
  rw [encard_fiber_restrictPreimage]
  exact hcard b

end DifferentialGeometry.Topology.Covering
