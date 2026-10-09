import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.KuroshFreeFactors
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace GC.Group
open DifferentialGeometry.Algebra.Group

theorem isFreeFactor_of_injective_over_inl {A B S : Type u}
    [Group A] [Group B] [Group S] (f : S →* Monoid.Coprod A B)
    (hf : Function.Injective f)
    (h : ∀ a : A, ∃ s : S, f s = Monoid.Coprod.inl a) : IsFreeFactor A S := by
  let M := boolCoprodFamily A B
  let e := coprodIBoolEquivCoprod A B
  let j : S →* Monoid.CoprodI M := e.symm.toMonoidHom.comp f
  have hj : Function.Injective j := e.symm.injective.comp hf
  have hr : MonoidHom.range (GraphCoveringTheory.Kurosh.factorInclusion M false) ≤
      j.range := by
    rintro x ⟨a, rfl⟩
    obtain ⟨s, hs⟩ := h a.down
    refine ⟨s, ?_⟩
    apply e.injective
    change e (e.symm (f s)) = e (Monoid.CoprodI.of (i := false) a)
    rw [e.apply_symm_apply, coprodIBoolEquivCoprod_of_false, hs]
  exact (factor_isFreeFactor_of_range_le M j.range false hr).congr
    MulEquiv.ulift (MonoidHom.ofInjective hj).symm

theorem freeFactor_equiv_of_indecomposable {A S : Type u}
    [Group A] [Group S] [Nontrivial A]
    (hi : FreelyIndecomposable S) (h : IsFreeFactor A S) : Nonempty (A ≃* S) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := h
  rcases hi A K ⟨e⟩ with ha | hk
  · exact (not_subsingleton A ha).elim
  · let := hk
    let : Unique K := ⟨⟨1⟩, fun x => Subsingleton.elim x 1⟩
    let q : K ≃* PUnit.{u+1} := MulEquiv.ofUnique
    exact ⟨((MulEquiv.coprodPUnit A).symm.trans
      ((MulEquiv.refl A).coprodCongr q.symm)).trans e.symm⟩

end GC.Group
