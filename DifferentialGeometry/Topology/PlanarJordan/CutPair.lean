import DifferentialGeometry.External.Schoenflies.GeneralCrosscut
import DifferentialGeometry.External.Schoenflies.FaceCyclesProof
import DifferentialGeometry.External.Schoenflies.JordanSeparates

open Set

namespace Schoenflies.IsArcBetween

private theorem subset_fst_of_mem_diff
    {C A B₀ B₁ : Set Schoenflies.Plane} {p q x : Schoenflies.Plane}
    (hA : Schoenflies.IsArcBetween A p q) (hsub : A ⊆ C)
    (hB : Schoenflies.IsCutPair C p q B₀ B₁)
    (hxA : x ∈ A) (hxB : x ∈ B₀) (hx : x ∉ ({p, q} : Set Schoenflies.Plane)) :
    A ⊆ B₀ := by
  have hxB₁ : x ∉ B₁ := fun h => hx (hB.inter_eq ▸ ⟨hxB, h⟩)
  have hcover : A \ {p, q} ⊆ B₁ᶜ ∪ B₀ᶜ := by
    intro z hz
    by_contra h
    simp only [mem_union, mem_compl_iff, not_or, not_not] at h
    exact hz.2 (hB.inter_eq ▸ ⟨h.2, h.1⟩)
  intro y hy
  by_cases hypq : y ∈ ({p, q} : Set Schoenflies.Plane)
  · rcases hypq with rfl | hypq
    · exact hB.fst.left_mem
    · rw [mem_singleton_iff] at hypq
      exact hypq ▸ hB.fst.right_mem
  by_contra hyB
  obtain ⟨z, hz, hz₁, hz₀⟩ := hA.isPreconnected_diff _ _
    hB.snd.isArc.isClosed.isOpen_compl hB.fst.isArc.isClosed.isOpen_compl
    hcover ⟨x, ⟨hxA, hx⟩, hxB₁⟩ ⟨y, ⟨hy, hypq⟩, hyB⟩
  have hzC : z ∈ B₀ ∪ B₁ := hB.union_eq.symm ▸ hsub hz.1
  exact hzC.elim hz₀ hz₁

theorem eq_fst_or_eq_snd_of_subset
    {C A B₀ B₁ : Set Schoenflies.Plane} {p q : Schoenflies.Plane}
    (hA : Schoenflies.IsArcBetween A p q) (hsub : A ⊆ C)
    (hB : Schoenflies.IsCutPair C p q B₀ B₁) :
    A = B₀ ∨ A = B₁ := by
  obtain ⟨x, hxA, hx⟩ := Set.not_subset.mp hA.not_subset_pair
  have hxC : x ∈ B₀ ∪ B₁ := hB.union_eq.symm ▸ hsub hxA
  rcases hxC with hxB | hxB
  · exact Or.inl (hB.fst.eq_of_subset hA (subset_fst_of_mem_diff hA hsub hB hxA hxB hx))
  · exact Or.inr (hB.snd.eq_of_subset hA (subset_fst_of_mem_diff hA hsub hB.symm hxA hxB hx))

end Schoenflies.IsArcBetween

namespace Schoenflies.IsCutPair

theorem eq_of_mem_diff
    {C A₀ A₁ B₀ B₁ : Set Schoenflies.Plane} {p q x : Schoenflies.Plane}
    (hA : Schoenflies.IsCutPair C p q A₀ A₁)
    (hB : Schoenflies.IsCutPair C p q B₀ B₁)
    (hxA : x ∈ A₀) (hxB : x ∈ B₀) (hx : x ∉ ({p, q} : Set Schoenflies.Plane)) :
    A₀ = B₀ ∧ A₁ = B₁ := by
  have hfirst : A₀ = B₀ := Set.Subset.antisymm
    (Schoenflies.IsArcBetween.subset_fst_of_mem_diff hA.fst hA.fst_subset hB hxA hxB hx)
    (Schoenflies.IsArcBetween.subset_fst_of_mem_diff hB.fst hB.fst_subset hA hxB hxA hx)
  refine ⟨hfirst, ?_⟩
  have hsub {D₀ D₁ E₀ E₁ : Set Schoenflies.Plane}
      (hD : Schoenflies.IsCutPair C p q D₀ D₁)
      (hE : Schoenflies.IsCutPair C p q E₀ E₁) (hDE : D₀ = E₀) : D₁ ⊆ E₁ := by
    intro y hy
    by_cases hypq : y ∈ ({p, q} : Set Schoenflies.Plane)
    · rcases hypq with rfl | hypq
      · exact hE.snd.left_mem
      · rw [mem_singleton_iff] at hypq
        exact hypq ▸ hE.snd.right_mem
    have hyC : y ∈ E₀ ∪ E₁ := hE.union_eq.symm ▸ hD.snd_subset hy
    exact hyC.resolve_left (fun h => hypq (hD.inter_eq ▸ ⟨hDE.symm ▸ h, hy⟩))
  exact Set.Subset.antisymm (hsub hA hB hfirst) (hsub hB hA hfirst.symm)

end Schoenflies.IsCutPair

namespace Schoenflies.IsJordanCurve

theorem eq_of_subset {C D : Set Plane} (hC : IsJordanCurve C) (hD : IsJordanCurve D)
    (hsub : C ⊆ D) : C = D := by
  obtain ⟨p, hp, q, hq, hpq⟩ := hC.exists_ne
  obtain ⟨A₀, A₁, hA⟩ := exists_isCutPair hC hp hq hpq
  obtain ⟨B₀, B₁, hB⟩ := exists_isCutPair hD (hsub hp) (hsub hq) hpq
  have hne : A₀ ≠ A₁ := by
    intro heq
    apply hA.fst.not_subset_pair
    intro z hz
    rw [← hA.inter_eq]
    exact ⟨hz, heq ▸ hz⟩
  rcases hA.fst.eq_fst_or_eq_snd_of_subset (hA.fst_subset.trans hsub) hB with h₀ | h₀ <;>
    rcases hA.snd.eq_fst_or_eq_snd_of_subset (hA.snd_subset.trans hsub) hB with h₁ | h₁
  · exact False.elim (hne (h₀.trans h₁.symm))
  · rw [← hA.union_eq, h₀, h₁, hB.union_eq]
  · rw [← hA.union_eq, h₀, h₁, union_comm, hB.union_eq]
  · exact False.elim (hne (h₀.trans h₁.symm))

end Schoenflies.IsJordanCurve
