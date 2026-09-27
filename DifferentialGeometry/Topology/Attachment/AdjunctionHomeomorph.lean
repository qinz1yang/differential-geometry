import DifferentialGeometry.Topology.Attachment.Basic
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

noncomputable section

open Function

namespace DifferentialGeometry.Topology

universe uA uL uR uT

variable {A : Type uA} {L : Type uL} {R : Type uR} {T : Type uT}
  [TopologicalSpace L] [TopologicalSpace R] [TopologicalSpace T]

def adjunctionHomeomorphOfFibers
    (l : A → L) (r : A → R) (F : L ⊕ R → T)
    (hF : _root_.Topology.IsQuotientMap F)
    (hleft : Injective (fun x : L => F (Sum.inl x)))
    (hright : Injective (fun y : R => F (Sum.inr y)))
    (hcross : ∀ x : L, ∀ y : R,
      F (Sum.inl x) = F (Sum.inr y) ↔ ∃ z : A, l z = x ∧ r z = y) :
    AdjunctionSpace l r ≃ₜ T := by
  have hseam (z : A) : F (Sum.inl (l z)) = F (Sum.inr (r z)) :=
    (hcross (l z) (r z)).mpr ⟨z, rfl, rfl⟩
  have hrel : ∀ x y : L ⊕ R, adjunctionRel l r x y → F x = F y := by
    rintro x y ⟨z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact hseam z
    · exact (hseam z).symm
  let G : AdjunctionSpace l r → T := Quot.lift F hrel
  have hGinjective : Injective G := by
    intro q q' hqq'
    obtain ⟨x, rfl⟩ := Quot.exists_rep q
    obtain ⟨y, rfl⟩ := Quot.exists_rep q'
    change F x = F y at hqq'
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        exact congrArg (adjunctionCell l r) (hleft hqq')
      | inr y =>
        obtain ⟨z, hzL, hzR⟩ := (hcross x y).mp hqq'
        exact Quot.sound ⟨z, Or.inl ⟨congrArg Sum.inl hzL.symm,
          congrArg Sum.inr hzR.symm⟩⟩
    | inr x =>
      cases y with
      | inl y =>
        obtain ⟨z, hzL, hzR⟩ := (hcross y x).mp hqq'.symm
        exact Quot.sound ⟨z, Or.inr ⟨congrArg Sum.inl hzL.symm,
          congrArg Sum.inr hzR.symm⟩⟩
      | inr y =>
        exact congrArg (adjunctionLower (i := l) r) (hright hqq')
  have hGquotient : _root_.Topology.IsQuotientMap G :=
    (isQuotientMap_adjunctionMk l r).of_comp_isQuotientMap hF
  exact IsHomeomorph.homeomorph G
    ((isHomeomorph_iff_isQuotientMap_injective).mpr ⟨hGquotient, hGinjective⟩)

@[simp]
theorem adjunctionHomeomorphOfFibers_apply_mk
    (l : A → L) (r : A → R) (F : L ⊕ R → T)
    (hF : _root_.Topology.IsQuotientMap F)
    (hleft : Injective (fun x : L => F (Sum.inl x)))
    (hright : Injective (fun y : R => F (Sum.inr y)))
    (hcross : ∀ x : L, ∀ y : R,
      F (Sum.inl x) = F (Sum.inr y) ↔ ∃ z : A, l z = x ∧ r z = y)
    (x : L ⊕ R) :
    adjunctionHomeomorphOfFibers l r F hF hleft hright hcross (adjunctionMk l r x) = F x :=
  rfl

@[simp]
theorem adjunctionHomeomorphOfFibers_apply_cell
    (l : A → L) (r : A → R) (F : L ⊕ R → T)
    (hF : _root_.Topology.IsQuotientMap F)
    (hleft : Injective (fun x : L => F (Sum.inl x)))
    (hright : Injective (fun y : R => F (Sum.inr y)))
    (hcross : ∀ x : L, ∀ y : R,
      F (Sum.inl x) = F (Sum.inr y) ↔ ∃ z : A, l z = x ∧ r z = y)
    (x : L) :
    adjunctionHomeomorphOfFibers l r F hF hleft hright hcross (adjunctionCell l r x) =
      F (Sum.inl x) :=
  rfl

@[simp]
theorem adjunctionHomeomorphOfFibers_apply_lower
    (l : A → L) (r : A → R) (F : L ⊕ R → T)
    (hF : _root_.Topology.IsQuotientMap F)
    (hleft : Injective (fun x : L => F (Sum.inl x)))
    (hright : Injective (fun y : R => F (Sum.inr y)))
    (hcross : ∀ x : L, ∀ y : R,
      F (Sum.inl x) = F (Sum.inr y) ↔ ∃ z : A, l z = x ∧ r z = y)
    (y : R) :
    adjunctionHomeomorphOfFibers l r F hF hleft hright hcross (adjunctionLower (i := l) r y) =
      F (Sum.inr y) :=
  rfl

end DifferentialGeometry.Topology
