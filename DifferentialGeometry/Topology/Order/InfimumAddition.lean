import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Bounds.Lattice
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.WithTop

namespace WithTop

theorem sInf_coe_image_add {R : Type*} [ConditionallyCompleteLattice R]
    [AddCommGroup R] [IsOrderedAddMonoid R] {A B : Set R} (hAbdd : BddBelow A) (hBbdd : BddBelow B) :
    sInf ((fun r : R => (r : WithTop R)) '' A) + sInf ((fun r : R => (r : WithTop R)) '' B) =
      sInf ((fun r : R => (r : WithTop R)) '' Set.image2 (fun a b : R => a + b) A B) := by
  classical
  by_cases hA : A.Nonempty
  · by_cases hB : B.Nonempty
    · have hAB := hA.image2 (f := fun a b : R => a + b) hB
      have hABbdd : BddBelow (Set.image2 (fun a b : R => a + b) A B) := by
        obtain ⟨a, ha⟩ := hAbdd
        obtain ⟨b, hb⟩ := hBbdd
        refine ⟨a + b, ?_⟩
        rintro z ⟨x, hx, y, hy, rfl⟩
        exact add_le_add (ha hx) (hb hy)
      have hInf : sInf (Set.image2 (fun a b : R => a + b) A B) = sInf A + sInf B :=
        csInf_image2_eq_csInf_csInf
          (u := fun p q : R => p + q)
          (l₁ := fun q p : R => p - q) (l₂ := fun p q : R => q - p)
          (fun _ _ _ => sub_le_iff_le_add) (fun _ _ _ => sub_le_iff_le_add')
          hA hAbdd hB hBbdd
      rw [← WithTop.coe_sInf' hA hAbdd, ← WithTop.coe_sInf' hB hBbdd,
        ← WithTop.coe_sInf' hAB hABbdd, hInf, WithTop.coe_add]
    · have hBe : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
      rw [hBe, Set.image_empty, WithTop.sInf_empty, Set.image2_empty_right,
        Set.image_empty, WithTop.sInf_empty, WithTop.add_top]
  · have hAe : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    rw [hAe, Set.image_empty, WithTop.sInf_empty, Set.image2_empty_left,
      Set.image_empty, WithTop.sInf_empty, WithTop.top_add]

end WithTop
