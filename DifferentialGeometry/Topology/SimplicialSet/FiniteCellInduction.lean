import DifferentialGeometry.Topology.SimplicialSet.MaximalCell
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial

universe u

namespace DifferentialGeometry.SSet


def isInitial_of_isEmpty_nondegenerate (X : _root_.SSet.{u}) [IsEmpty X.N] : IsInitial X := by
  have hbot : (⊥ : X.Subcomplex) = ⊤ := by
    apply le_antisymm bot_le
    rw [_root_.SSet.N.subcomplex_le_iff]
    intro s
    exact isEmptyElim s
  have ht : IsInitial ((⊤ : X.Subcomplex) : _root_.SSet.{u}) := by
    rw [← hbot]
    exact _root_.SSet.Subcomplex.isInitialBot
  exact ht.ofIso (_root_.SSet.Subcomplex.topIso X)

@[elab_as_elim]
theorem finite_cell_induction (P : _root_.SSet.{u} → Prop)
    (hInitial : ∀ X, IsInitial X → P X)
    (hCell : ∀ (n : ℕ) (X Y : _root_.SSet.{u})
      (g : (_root_.SSet.boundary n : _root_.SSet) ⟶ X)
      (r : (Δ[n] : _root_.SSet) ⟶ Y) (b : X ⟶ Y),
      IsPushout (_root_.SSet.boundary n).ι g r b →
      P (_root_.SSet.boundary n) → P X → P Y)
    (X : _root_.SSet.{u}) [X.Finite] : P X := by
  suffices ∀ d : ℕ, ∀ Y : _root_.SSet.{u}, Y.Finite → Y.HasDimensionLT d → P Y by
    obtain ⟨d, hd⟩ := X.hasDimensionLT_of_finite
    exact this d X inferInstance hd
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro Y hY hd
    generalize hn : Nat.card Y.N = n
    induction n using Nat.strong_induction_on generalizing Y with
    | h n ihn =>
      cases isEmpty_or_nonempty Y.N with
      | inl he =>
        have : IsEmpty Y.N := he
        exact hInitial Y (isInitial_of_isEmpty_nondegenerate Y)
      | inr he =>
        have : Nonempty Y.N := he
        obtain ⟨s, hs⟩ := (Set.finite_univ : (Set.univ : Set Y.N).Finite).exists_maximal
          (Set.univ_nonempty)
        have hmax : IsMax s := fun t ht ↦ hs.2 (Set.mem_univ t) ht
        apply hCell s.dim (costar s) Y (costarAttachingMap s) (nondegenerateCellMap s)
          (costar s).ι (costar_cell_isPushout s hmax)
        · exact ih s.dim (Y.dim_lt_of_nonDegenerate ⟨_, s.nonDegenerate⟩ d)
            (_root_.SSet.boundary s.dim) inferInstance inferInstance
        · apply ihn (Nat.card (costar s : _root_.SSet).N)
            (by rw [← hn]; exact card_costar_nondegenerate_lt s) (costar s)
            inferInstance inferInstance rfl

end DifferentialGeometry.SSet
