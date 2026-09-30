import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

namespace Orthonormal

theorem exists_euclidean_product_coordinates {j k : ℕ}
    {ξ : Fin j → EuclideanSpace ℝ (Fin k)} (hξ : Orthonormal ℝ ξ) (hjk : j ≤ k) :
    ∃ Q : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin j) × EuclideanSpace ℝ (Fin (k - j))),
      ∀ v l, (Q v).fst l = inner ℝ v (ξ l) := by
  classical
  let ι := Fin j ⊕ Fin (k - j)
  let s : Set ι := Set.range (Sum.inl : Fin j → ι)
  let v : ι → EuclideanSpace ℝ (Fin k) := Sum.elim ξ (fun _ => 0)
  let e : Fin j ≃ s := Equiv.ofInjective Sum.inl Sum.inl_injective
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    convert hξ.comp e.symm e.symm.injective using 1
    funext i
    rcases i with ⟨i, l, rfl⟩
    change ξ l = ξ (e.symm (e l))
    rw [e.symm_apply_apply]
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = Fintype.card ι := by
    simp only [finrank_euclideanSpace_fin, ι, Fintype.card_sum, Fintype.card_fin]
    exact (Nat.add_sub_of_le hjk).symm
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq hcard
  let Q := b.repr.trans (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : ι => ℝ))
  refine ⟨Q, ?_⟩
  intro x l
  change b.repr x (Sum.inl l) = inner ℝ x (ξ l)
  rw [b.repr_apply_apply, hb _ (Set.mem_range_self l)]
  exact real_inner_comm _ _

end Orthonormal
