import DifferentialGeometry.Topology.Algebra.Group.FreeProductAssociativity
import Mathlib.Logic.Equiv.Option
set_option autoImplicit false
noncomputable section
universe u
namespace GC.Group

def IsFreeFactor (G H : Type u) [Group G] [Group H] : Prop :=
  ∃ (K : Type u) (_ : Group K), Nonempty (H ≃* Monoid.Coprod G K)

theorem IsFreeFactor.refl (G : Type u) [Group G] : IsFreeFactor G G :=
  ⟨PUnit, inferInstance, ⟨(MulEquiv.coprodPUnit G).symm⟩⟩

theorem IsFreeFactor.trans {G H J : Type u} [Group G] [Group H] [Group J]
    (h : IsFreeFactor G H) (k : IsFreeFactor H J) : IsFreeFactor G J := by
  obtain ⟨K, hK, ⟨e⟩⟩ := h
  obtain ⟨L, hL, ⟨f⟩⟩ := k
  exact ⟨Monoid.Coprod K L, inferInstance,
    ⟨f.trans ((e.coprodCongr (MulEquiv.refl L)).trans
      (MulEquiv.coprodAssoc G K L))⟩⟩

theorem IsFreeFactor.congr {G H G' H' : Type u}
    [Group G] [Group H] [Group G'] [Group H']
    (h : IsFreeFactor G H) (e : G ≃* G') (f : H ≃* H') :
    IsFreeFactor G' H' := by
  obtain ⟨K, hK, ⟨a⟩⟩ := h
  exact ⟨K, hK, ⟨f.symm.trans (a.trans (e.coprodCongr (MulEquiv.refl K)))⟩⟩

theorem isFreeFactor_coprodI {ι : Type} (G : ι → Type u)
    [∀ i, Group (G i)] (i : ι) : IsFreeFactor (G i) (Monoid.CoprodI G) := by
  classical
  let R := fun j : {j // j ≠ i} => G j.val
  let F := DifferentialGeometry.Algebra.Group.optionFreeProductFactor R (G i)
  let e : Monoid.CoprodI F ≃* Monoid.CoprodI G :=
    DifferentialGeometry.Algebra.Group.coprodIReindexEquiv F G
      (Equiv.optionSubtypeNe i) (fun j => by
        cases j with
        | none => exact MulEquiv.refl _
        | some j => exact MulEquiv.refl _)
  exact ⟨Monoid.CoprodI R, inferInstance,
    ⟨e.symm.trans ((DifferentialGeometry.Algebra.Group.coprodIOptionEquivCoprod R (G i)).trans
      (MulEquiv.coprodComm _ _))⟩⟩

end GC.Group
