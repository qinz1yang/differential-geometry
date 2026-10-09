import DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoFull
import Mathlib.GroupTheory.Rank

/-!
# Rank drops strictly in a nontrivial free product

By the Grushko–Neumann theorem the rank of `A ∗ B` is `rank A + rank B`, so each nontrivial
factor of a finitely generated free product has strictly smaller rank than the product.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace GC.Group

theorem rank_lt_of_mulEquiv_coprod {G A B : Type u} [Group G] [Group A] [Group B]
    [Group.FG G] [Group.FG A] [Group.FG B] [Nontrivial A] [Nontrivial B]
    (e : G ≃* Monoid.Coprod A B) :
    Group.rank A < Group.rank G ∧ Group.rank B < Group.rank G := by
  have h : Group.rank G = Group.rank A + Group.rank B :=
    (Group.rank_congr e).trans MarshallHall.GeneralGrushko.rank_coprod_eq_add
  have hA := Group.rank_pos A
  have hB := Group.rank_pos B
  omega

end GC.Group
