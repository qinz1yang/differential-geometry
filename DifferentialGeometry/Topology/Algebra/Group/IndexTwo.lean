import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index

namespace DifferentialGeometry.Algebra.Group

variable {G : Type*} [Group G]

noncomputable def indexTwoHom (H : Subgroup G) (hH : H.index = 2) :
    G →* Multiplicative (ZMod 2) := by
  classical
  exact
    { toFun := fun g => Multiplicative.ofAdd (if g ∈ H then 0 else 1)
      map_one' := by simp
      map_mul' := by
        intro a b
        have hmul : (1 : Multiplicative (ZMod 2)) =
            Multiplicative.ofAdd 1 * Multiplicative.ofAdd 1 := by
          change (0 : ZMod 2) = 1 + 1
          rfl
        rw [H.mul_mem_iff_of_index_two hH]
        by_cases ha : a ∈ H
        · by_cases hb : b ∈ H <;> simp [ha, hb]
        · by_cases hb : b ∈ H
          · simp [ha, hb]
          · simpa [ha, hb] using hmul }

theorem indexTwoHom_surjective (H : Subgroup G) (hH : H.index = 2) :
    Function.Surjective (indexTwoHom H hH) := by
  classical
  rcases H.index_eq_two_iff_exists_notMem_and.mp hH with ⟨a, ha, _⟩
  intro z
  fin_cases z
  · refine ⟨1, ?_⟩
    simp [indexTwoHom]
    rfl
  · refine ⟨a, ?_⟩
    simp [indexTwoHom, ha]
    rfl

theorem ker_indexTwoHom (H : Subgroup G) (hH : H.index = 2) :
    (indexTwoHom H hH).ker = H := by
  classical
  ext g
  simp [indexTwoHom]

theorem index_ker_eq_two_of_surjective
    (f : G →* Multiplicative (ZMod 2)) (hf : Function.Surjective f) :
    f.ker.index = 2 := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf, Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem exists_surjective_ker_eq_of_index_eq_two
    (H : Subgroup G) (hH : H.index = 2) :
    ∃ f : G →* Multiplicative (ZMod 2), Function.Surjective f ∧ f.ker = H :=
  ⟨indexTwoHom H hH, indexTwoHom_surjective H hH, ker_indexTwoHom H hH⟩

theorem exists_subgroup_index_eq_two_iff_exists_surjective_zmod_two :
    (∃ H : Subgroup G, H.index = 2) ↔
      ∃ f : G →* Multiplicative (ZMod 2), Function.Surjective f := by
  constructor
  · rintro ⟨H, hH⟩
    exact ⟨indexTwoHom H hH, indexTwoHom_surjective H hH⟩
  · rintro ⟨f, hf⟩
    exact ⟨f.ker, index_ker_eq_two_of_surjective f hf⟩

end DifferentialGeometry.Algebra.Group
