import Mathlib.GroupTheory.Torsion
import Mathlib.Topology.Covering.Quotient

namespace MulAction

variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]

private theorem isCancelSMul_of_torsion_free [ProperlyDiscontinuousSMul G X]
    (hG : ∀ g : G, IsOfFinOrder g → g = 1) : IsCancelSMul G X := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g x hg
  let S := stabilizer G x
  let _ : Finite S := (ProperlyDiscontinuousSMul.finite_stabilizer (Γ := G) x).to_subtype
  exact hG g (S.subtype.isOfFinOrder (isMulTorsion_of_finite (⟨g, hg⟩ : S)))

theorem isCoveringMap_quotientMk_of_torsion_free [ProperlyDiscontinuousSMul G X]
    [LocallyCompactSpace X] [T2Space X] [ContinuousConstSMul G X]
    (hG : ∀ g : G, IsOfFinOrder g → g = 1) :
    IsCoveringMap (Quotient.mk (MulAction.orbitRel G X)) := by
  let _ : IsCancelSMul G X := isCancelSMul_of_torsion_free hG
  exact (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := G)).isCoveringMap

end MulAction
