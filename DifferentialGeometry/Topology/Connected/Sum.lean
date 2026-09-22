import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Constructions.SumProd

set_option autoImplicit false
noncomputable section

open Function

namespace ConnectedComponents

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def sumEquiv : ConnectedComponents (X ⊕ Y) ≃ (ConnectedComponents X ⊕ ConnectedComponents Y) where
  toFun := (Continuous.sumElim
    (continuous_inl.comp ConnectedComponents.continuous_coe)
    (continuous_inr.comp ConnectedComponents.continuous_coe)).connectedComponentsLift
  invFun := Sum.elim continuous_inl.connectedComponentsMap continuous_inr.connectedComponentsMap
  left_inv c := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    cases x <;> rfl
  right_inv c := by
    cases c with
    | inl c => obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c; rfl
    | inr c => obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c; rfl

end ConnectedComponents
