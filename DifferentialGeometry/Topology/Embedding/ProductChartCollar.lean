import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.UniformSpace.Real

open Set

namespace DifferentialGeometry.Topology.Embedding

theorem section_subset_interior_union_of_product_chart_collar
    {N M : Type*} [TopologicalSpace N] [TopologicalSpace M]
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens M)
    (e : O ≃ₜ V) (a c b : ℝ) (hac : a < c) (hcb : c < b)
    (hcollar : (univ : Set N) ×ˢ Icc a b ⊆ O) {A B : Set M}
    (hA : ∀ x : O, a ≤ (x : N × ℝ).2 → (x : N × ℝ).2 ≤ c → (e x : M) ∈ A)
    (hB : ∀ x : O, c ≤ (x : N × ℝ).2 → (x : N × ℝ).2 ≤ b → (e x : M) ∈ B) :
    range (fun p : N ↦ (e ⟨(p, c), hcollar ⟨mem_univ _, hac.le, hcb.le⟩⟩ : M)) ⊆
      interior (A ∪ B) := by
  let F : O → M := fun x ↦ (e x : M)
  let U : Set O := {x | a < (x : N × ℝ).2 ∧ (x : N × ℝ).2 < b}
  have hopen : IsOpen (F '' U) :=
    (V.isOpenEmbedding'.isOpenMap.comp e.isOpenMap) U
      (isOpen_Ioo.preimage (continuous_snd.comp continuous_subtype_val))
  have hsub : F '' U ⊆ A ∪ B := by
    rintro y ⟨x, hx, rfl⟩
    rcases le_total (x : N × ℝ).2 c with h | h
    · exact Or.inl (hA x hx.1.le h)
    · exact Or.inr (hB x h hx.2.le)
  rintro y ⟨p, rfl⟩
  exact mem_interior.mpr ⟨F '' U, hsub, hopen,
    ⟨⟨(p, c), hcollar ⟨mem_univ _, hac.le, hcb.le⟩⟩, ⟨hac, hcb⟩, rfl⟩⟩

end DifferentialGeometry.Topology.Embedding
