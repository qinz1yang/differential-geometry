import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FreeFactor
import Mathlib.Algebra.Group.Subgroup.Ker
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w z
namespace GC.Group

theorem isFreeFactor_of_large_coprod {G A : Type u} {B : Type v} {C : Type w}
    [Group G] [Group A] [Group B] [Group C]
    (e : Monoid.Coprod B C ≃* G) (a : B ≃* A) : IsFreeFactor A G := by
  let f : C →* G := e.toMonoidHom.comp Monoid.Coprod.inr
  have hf : Function.Injective f := e.injective.comp Monoid.Coprod.inr_injective
  let b : C ≃* f.range := MonoidHom.ofInjective hf
  exact ⟨f.range, inferInstance, ⟨e.symm.trans (a.coprodCongr b)⟩⟩

def coprodIFactorEquiv {ι : Type v} (M : ι → Type w) [∀ i, Group (M i)] (i : ι) :
    Monoid.CoprodI M ≃* Monoid.Coprod (M i)
      (Monoid.CoprodI (fun j : {j // j ≠ i} => M j.val)) := by
  classical
  let R := fun j : {j // j ≠ i} => M j.val
  let F := DifferentialGeometry.Algebra.Group.optionFreeProductFactor R (M i)
  let e : Monoid.CoprodI F ≃* Monoid.CoprodI M :=
    DifferentialGeometry.Algebra.Group.coprodIReindexEquiv F M
      (Equiv.optionSubtypeNe i) (fun j => by
        cases j with
        | none => exact MulEquiv.refl _
        | some j => exact MulEquiv.refl _)
  exact e.symm.trans ((DifferentialGeometry.Algebra.Group.coprodIOptionEquivCoprod R
    (M i)).trans (MulEquiv.coprodComm _ _))

theorem isFreeFactor_of_indexed_equiv {ι : Type v} (M : ι → Type w)
    [∀ i, Group (M i)] {G A : Type u} [Group G] [Group A]
    (e : Monoid.CoprodI M ≃* G) (i : ι) (a : M i ≃* A) : IsFreeFactor A G :=
  isFreeFactor_of_large_coprod ((coprodIFactorEquiv M i).symm.trans e) a

end GC.Group
