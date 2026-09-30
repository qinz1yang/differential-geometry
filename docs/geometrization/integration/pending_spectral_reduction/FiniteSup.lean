import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false

open scoped BigOperators

namespace Submodule

variable {𝕜 E A : Type*} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

theorem finrank_finset_sup_le_sum (S : Finset A) (L : A → Submodule 𝕜 E)
    [∀ i, FiniteDimensional 𝕜 (L i)] :
    Module.finrank 𝕜 (S.sup L : Submodule 𝕜 E) ≤ ∑ i ∈ S, Module.finrank 𝕜 (L i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.sup_insert, Finset.sum_insert hi]
    exact (finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)

theorem finrank_finset_sup_span_singleton_sup_le (S : Finset A)
    (L : A → Submodule 𝕜 E) [∀ i, FiniteDimensional 𝕜 (L i)] (x : A → E) :
    Module.finrank 𝕜 (S.sup (fun i => 𝕜 ∙ x i ⊔ L i) : Submodule 𝕜 E) ≤
      ∑ i ∈ S, (Module.finrank 𝕜 (L i) + 1) := by
  apply (finrank_finset_sup_le_sum S (fun i => 𝕜 ∙ x i ⊔ L i)).trans
  apply Finset.sum_le_sum
  intro i hi
  have hx : Module.finrank 𝕜 (𝕜 ∙ x i) ≤ 1 := finrank_span_le_card {x i}
  exact (finrank_add_le_finrank_add_finrank _ _).trans (by omega)

end Submodule
