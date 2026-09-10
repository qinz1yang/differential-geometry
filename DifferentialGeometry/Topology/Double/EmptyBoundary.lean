import DifferentialGeometry.Topology.Double.ClosedCover
import Mathlib.Topology.Constructions.SumProd

set_option autoImplicit false
noncomputable section
open Set Function Topology
namespace Poincare.Topology
variable {X : Type*} [TopologicalSpace X]


def doubleEmptyHomeomorph : Double (∅ : Set X) ≃ₜ X ⊕ X where
  toFun := doubleDesc (∅ : Set X) ⟨Sum.inl, continuous_inl⟩ ⟨Sum.inr, continuous_inr⟩
    (fun b => b.property.elim)
  invFun := Sum.elim (doublePositive ∅) (doubleNegative ∅)
  left_inv z := by
    rcases double_cases (∅ : Set X) z with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;> rfl
  right_inv z := by cases z <;> rfl
  continuous_toFun := (doubleDesc (∅ : Set X) ⟨Sum.inl, continuous_inl⟩ ⟨Sum.inr, continuous_inr⟩
    (fun b => b.property.elim)).continuous
  continuous_invFun := (doublePositive ∅).continuous.sumElim (doubleNegative ∅).continuous

@[simp] theorem doubleEmptyHomeomorph_positive (x : X) :
    doubleEmptyHomeomorph (doublePositive (∅ : Set X) x) = Sum.inl x := rfl

@[simp] theorem doubleEmptyHomeomorph_negative (x : X) :
    doubleEmptyHomeomorph (doubleNegative (∅ : Set X) x) = Sum.inr x := rfl

end Poincare.Topology
