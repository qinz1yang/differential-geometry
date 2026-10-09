import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FiniteFreeFactors
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.GroupTheory.OrderOfElement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
namespace GC.Group

theorem finite_isFreeGroup_subsingleton (G : Type u) [Group G]
    [IsFreeGroup G] [Finite G] : Subsingleton G := by
  let e := IsFreeGroup.toFreeGroup G
  let : Finite (FreeGroup (IsFreeGroup.Generators G)) := Finite.of_equiv G e.toEquiv
  have h (x : G) : x = 1 := e.injective (by
    simpa using (isOfFinOrder_of_finite (e x)).eq_one')
  exact ⟨fun x y => (h x).trans (h y).symm⟩

theorem finite_coprodI_other_subsingleton {ι : Type u} (M : ι → Type v)
    [∀ i, Group (M i)] [Finite (Monoid.CoprodI M)]
    (i : ι) [Nontrivial (M i)] (j : ι) (hji : j ≠ i) : Subsingleton (M j) := by
  classical
  by_contra h
  let : Nontrivial (M j) := not_subsingleton_iff_nontrivial.mp h
  obtain ⟨a, ha⟩ := exists_ne (1 : M i)
  obtain ⟨b, hb⟩ := exists_ne (1 : M j)
  let := infinite_coprodI_of_two_factors M hji.symm a ha b hb
  exact not_finite (Monoid.CoprodI M)

theorem coprodI_of_surjective_of_others_trivial {ι : Type u} (M : ι → Type v)
    [∀ i, Group (M i)] (i : ι)
    (h : ∀ j, j ≠ i → Subsingleton (M j)) :
    Function.Surjective (Monoid.CoprodI.of : M i →* Monoid.CoprodI M) := by
  classical
  intro z
  induction z using Monoid.CoprodI.induction_on with
  | one => exact ⟨1, map_one _⟩
  | of j a =>
      by_cases hj : j = i
      · subst j; exact ⟨a, rfl⟩
      · let := h j hj
        have ha : a = 1 := Subsingleton.elim _ _
        exact ⟨1, by simp [ha]⟩
  | mul x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a * b, map_mul _ _ _⟩

theorem finite_coprodI_exists_surjective_factor {ι : Type u} (M : ι → Type v)
    [∀ i, Group (M i)] [Finite (Monoid.CoprodI M)] [Nontrivial (Monoid.CoprodI M)] :
    ∃ i, Nontrivial (M i) ∧
      Function.Surjective (Monoid.CoprodI.of : M i →* Monoid.CoprodI M) := by
  classical
  have hex : ∃ i, Nontrivial (M i) := by
    by_contra h
    have hs (i : ι) : Subsingleton (M i) :=
      not_nontrivial_iff_subsingleton.mp (fun hi => h ⟨i, hi⟩)
    have hz (z : Monoid.CoprodI M) : z = 1 := by
      induction z using Monoid.CoprodI.induction_on with
      | one => rfl
      | of i a =>
          let := hs i
          rw [Subsingleton.elim a 1, map_one]
      | mul x y hx hy => rw [hx, hy, one_mul]
    obtain ⟨z, hz'⟩ := exists_ne (1 : Monoid.CoprodI M)
    exact hz' (hz z)
  obtain ⟨i, hi⟩ := hex
  let := hi
  exact ⟨i, hi, coprodI_of_surjective_of_others_trivial M i
    (finite_coprodI_other_subsingleton M i)⟩

end GC.Group
