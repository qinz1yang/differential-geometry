import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.InheritedFreeFactor
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FiniteIndecomposable
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace GC.Group
open GraphCoveringTheory.Kurosh

theorem finite_freeFactor_equiv_fixed_factor {ι : Type} (F : ι → Type u)
    [∀ i, Group (F i)] (hi : ∀ i, FreelyIndecomposable (F i))
    {A X : Type u} [Group A] [Group X] [Finite A] [Nontrivial A]
    (e₀ : X ≃* Monoid.CoprodI F) (h : IsFreeFactor A X) :
    ∃ i : ι, Nonempty (A ≃* F i) := by
  obtain ⟨B, hB, ⟨e⟩⟩ := h
  let q : A →* FreeProduct F := e₀.toMonoidHom.comp
    (e.symm.toMonoidHom.comp Monoid.Coprod.inl)
  have hq : Function.Injective q :=
    e₀.injective.comp (e.symm.injective.comp Monoid.Coprod.inl_injective)
  let eq := MonoidHom.ofInjective hq
  let : Finite q.range := Finite.of_equiv A eq.toEquiv
  let : Nontrivial q.range := eq.injective.nontrivial
  obtain ⟨i, g, hc⟩ := finite_subgroup_le_conjugate_factor F q.range
  let j : F i →* Monoid.Coprod A B := e.toMonoidHom.comp
    (e₀.symm.toMonoidHom.comp ((MulAut.conj g).toMonoidHom.comp (factorInclusion F i)))
  have hj : Function.Injective j := e.injective.comp
    (e₀.symm.injective.comp ((MulAut.conj g).injective.comp (factorInclusion_injective F i)))
  have hh : ∀ a : A, ∃ b : F i, j b = Monoid.Coprod.inl a := by
    intro a
    have ha := (mem_conjugateSubgroup_iff _ g (q a)).mp (hc ⟨a, rfl⟩)
    obtain ⟨b, hb⟩ := ha
    refine ⟨b, ?_⟩
    change e (e₀.symm (g * factorInclusion F i b * g⁻¹)) = Monoid.Coprod.inl a
    rw [hb]
    simp [q, mul_assoc]
  exact ⟨i, freeFactor_equiv_of_indecomposable (hi i)
    (isFreeFactor_of_injective_over_inl j hj hh)⟩

theorem exists_finite_freeFactor_order_bound {X : Type u} [Group X]
    (h : HasFiniteIndecomposablePresentation X) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ (A : Type u) [Group A] [Finite A],
      IsFreeFactor A X → Nat.card A ≤ N := by
  classical
  obtain ⟨ι, hι, F, hF, hi, ⟨e⟩⟩ := h
  let N := 1 + ∑ i : ι, Nat.card (F i)
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  intro A hA hFin hAfree
  rcases subsingleton_or_nontrivial A with hs | hn
  · let := hs
    rw [Nat.card_unique]
    dsimp [N]; omega
  · let := hn
    obtain ⟨i, ⟨a⟩⟩ := finite_freeFactor_equiv_fixed_factor F (fun i => (hi i).2.2) e hAfree
    rw [Nat.card_congr a.toEquiv]
    have hc : Nat.card (F i) ≤ ∑ j : ι, Nat.card (F j) :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (Nat.card (F j))) (Finset.mem_univ i)
    dsimp [N]; omega

theorem fg_finite_freeFactor_order_bound (X : Type u) [Group X] [Group.FG X] :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ (A : Type u) [Group A] [Finite A],
      IsFreeFactor A X → Nat.card A ≤ N :=
  exists_finite_freeFactor_order_bound (finiteIndecomposablePresentation_of_fg X)

end GC.Group
