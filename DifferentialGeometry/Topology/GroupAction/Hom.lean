import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Topology.Constructions

namespace MulActionHom

variable {M N X Y A : Type*} [SMul M X] [SMul N Y] {φ : M → N}
  [TopologicalSpace Y]

instance instTopologicalSpace : TopologicalSpace (X →ₑ[φ] Y) :=
  TopologicalSpace.induced (fun f : X →ₑ[φ] Y => (f : X → Y)) inferInstance

theorem isEmbedding_coe :
    Topology.IsEmbedding (fun f : X →ₑ[φ] Y => (f : X → Y)) :=
  ⟨⟨rfl⟩, DFunLike.coe_injective⟩

@[fun_prop]
theorem continuous_coe : Continuous (fun f : X →ₑ[φ] Y => (f : X → Y)) :=
  isEmbedding_coe.continuous

@[fun_prop]
theorem continuous_eval (x : X) : Continuous (fun f : X →ₑ[φ] Y => f x) :=
  (continuous_apply x).comp continuous_coe

theorem continuous_iff [TopologicalSpace A] {f : A → (X →ₑ[φ] Y)} :
    Continuous f ↔ ∀ x, Continuous (fun a => f a x) := by
  rw [isEmbedding_coe.isInducing.continuous_iff, continuous_pi_iff]
  rfl

end MulActionHom
