import DifferentialGeometry.Analysis.Convex.CompactFrontier

open Set

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

theorem exists_mem_frontier_apply_lt_iff {P : Set E} (hP : IsCompact P)
    (ℓ : E →L[ℝ] ℝ) (a : ℝ) :
    (∃ x ∈ frontier P, ℓ x < a) ↔ ∃ x ∈ P, ℓ x < a := by
  refine ⟨fun ⟨x, hx, hxa⟩ => ⟨x, hP.isClosed.frontier_subset hx, hxa⟩, ?_⟩
  rintro ⟨x, hx, hxa⟩
  by_contra h
  push Not at h
  have hsub : P ⊆ ℓ ⁻¹' Ici a :=
    Analysis.IsCompact.subset_of_frontier_subset_convex_closed hP
      ((convex_Ici a).linear_preimage ℓ.toLinearMap) (isClosed_Ici.preimage ℓ.continuous) h
  exact hxa.not_ge (hsub hx)

theorem exists_mem_frontier_lt_apply_iff {P : Set E} (hP : IsCompact P)
    (ℓ : E →L[ℝ] ℝ) (a : ℝ) :
    (∃ x ∈ frontier P, a < ℓ x) ↔ ∃ x ∈ P, a < ℓ x := by
  simpa only [neg_apply, neg_lt_neg_iff] using exists_mem_frontier_apply_lt_iff hP (-ℓ) (-a)

end DifferentialGeometry.Topology
