import Mathlib.GroupTheory.Torsion

namespace Poincare.Algebra.Group

theorem subsingleton_of_injective_hom_to_torsion_free
    {G H : Type*} [Group G] [Finite G] [Monoid H] [IsMulTorsionFree H]
    (f : G →* H) (hf : Function.Injective f) : Subsingleton G := by
  have hone (g : G) : g = 1 := by
    apply hf
    rw [map_one]
    exact (isOfFinOrder_iff_eq_one (f g)).mp
      (f.isOfFinOrder (isMulTorsion_of_finite g))
  exact ⟨fun g h ↦ (hone g).trans (hone h).symm⟩

theorem subsingleton_of_injective_comp_through_torsion_free
    {G H K : Type*} [Group G] [Group H] [Group K] [Finite K]
    [IsMulTorsionFree H] (f : G →* H) (g : H →* K)
    (hgf : Function.Injective (g.comp f)) : Subsingleton G := by
  let : Finite G := Finite.of_injective (g.comp f) hgf
  exact subsingleton_of_injective_hom_to_torsion_free f
    (Function.Injective.of_comp hgf)

end Poincare.Algebra.Group
