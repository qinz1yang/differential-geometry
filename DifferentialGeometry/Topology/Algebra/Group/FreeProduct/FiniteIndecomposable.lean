import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FiniteProductPresentation
import DifferentialGeometry.External.GrushkoNeumannTheorem.MarshallHall.GrushkoFull
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace GC.Group

theorem rank_lt_of_nontrivial_split {G A B : Type u}
    [Group G] [Group A] [Group B] [Group.FG G] [Group.FG A] [Group.FG B]
    [Nontrivial A] [Nontrivial B] (e : G ≃* Monoid.Coprod A B) :
    Group.rank A < Group.rank G ∧ Group.rank B < Group.rank G := by
  have hr : Group.rank G = Group.rank A + Group.rank B :=
    (Group.rank_congr e).trans (MarshallHall.GeneralGrushko.rank_coprod_eq_add)
  have ha := Group.rank_pos A
  have hb := Group.rank_pos B
  omega

theorem finiteIndecomposablePresentation_of_fg (G : Type u)
    [Group G] [Group.FG G] : HasFiniteIndecomposablePresentation G := by
  classical
  have aux : ∀ n : ℕ, ∀ (X : Type u) [Group X] [Group.FG X],
      Group.rank X = n → HasFiniteIndecomposablePresentation X := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro X hX hFX hn
      by_cases hs : Subsingleton X
      · let := hs
        exact finiteIndecomposablePresentation_of_subsingleton X
      let : Nontrivial X := not_subsingleton_iff_nontrivial.mp hs
      by_cases hi : FreelyIndecomposable X
      · exact finiteIndecomposablePresentation_single X hi
      simp only [FreelyIndecomposable, not_forall, not_or] at hi
      obtain ⟨A, B, hA, hB, ⟨e⟩, ha, hb⟩ := hi
      let : Nontrivial A := not_subsingleton_iff_nontrivial.mp ha
      let : Nontrivial B := not_subsingleton_iff_nontrivial.mp hb
      obtain ⟨hFA, hFB⟩ := fg_factors_of_equiv_coprod e
      let := hFA
      let := hFB
      obtain ⟨hra, hrb⟩ := rank_lt_of_nontrivial_split e
      rw [hn] at hra hrb
      exact finiteIndecomposablePresentation_combine e
        (ih (Group.rank A) hra A rfl) (ih (Group.rank B) hrb B rfl)
  exact aux (Group.rank G) G rfl

end GC.Group
