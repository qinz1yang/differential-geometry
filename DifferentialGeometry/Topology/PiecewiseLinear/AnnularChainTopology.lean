/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainLocalPolyhedral

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {φ : E3 → E3} {Pt : ℤ → E3}
  {Dp Dpint J A S T S'' T'' H B Jlo Jhi : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

private theorem mem_of_mem_closure_annularChain
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (hch : IsAnnularChain H B Jlo Jhi (fun i => φ '' S i) S'' T'' P')
    {x : E3} (hxI : x ∈ I) (hx : x ∈ closure (annularChain H B P')) :
    x ∈ annularChain H B P' := by
  classical
  by_cases hxP : x = P'
  · exact Or.inr hxP
  obtain ⟨U, hU, hF⟩ := htw.locallyFinite x hxI hxP
  let F : Set ℤ := {j | ((φ '' S j) ∩ U).Nonempty}
  have hfinite (k : ℤ) : {i : ℤ | 2 * i + k ∈ F}.Finite := by
    change ((fun i : ℤ => 2 * i + k) ⁻¹' F).Finite
    apply Set.Finite.preimage (s := F) ?_ hF
    intro i _ j _ hij
    dsimp at hij
    omega
  let L : Set ℤ := {i | 2 * i ∈ F} ∪
    {i | 2 * i + 1 ∈ F} ∪ {i | 2 * i + 2 ∈ F}
  have hL : L.Finite := by
    have h₀ : {i : ℤ | 2 * i ∈ F}.Finite := by simpa using hfinite 0
    exact (h₀.union (hfinite 1)).union (hfinite 2)
  let Z : Set E3 := (⋃ i ∈ L, H i ∪ B i) ∪ {P'}
  have hZ : IsClosed Z :=
    (hL.isClosed_biUnion fun i _ =>
      (hch.half_isPolyhedron i).isClosed.union
        (hch.bridge_isPolyhedron i).isClosed).union isClosed_singleton
  have hZsub : Z ⊆ annularChain H B P' :=
    union_subset_union (iUnion₂_subset_iUnion _ _) subset_rfl
  have hlocal : interior U ∩ annularChain H B P' ⊆ Z := by
    rintro y ⟨hyU, hy | hy⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      have hiL : i ∈ L := by
        rcases hi with hiH | hiB
        · exact Or.inl (Or.inl ⟨y, hch.halfSubsetTorus i hiH, interior_subset hyU⟩)
        · rcases hch.bridgeSubset i hiB with (h₀ | h₁) | h₂
          · exact Or.inl (Or.inl ⟨y, h₀, interior_subset hyU⟩)
          · exact Or.inl (Or.inr ⟨y, h₁, interior_subset hyU⟩)
          · exact Or.inr ⟨y, h₂, interior_subset hyU⟩
      exact Or.inl (mem_biUnion hiL hi)
    · exact Or.inr hy
  exact hZsub (closure_minimal hlocal hZ
    (isOpen_interior.inter_closure ⟨mem_interior_iff_mem_nhds.mpr hU, hx⟩))

theorem IsAnnularChain.isClosed_preimage_annularChain
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (hch : IsAnnularChain H B Jlo Jhi (fun i => φ '' S i) S'' T'' P') :
    IsClosed (((↑) : I → E3) ⁻¹' annularChain H B P') := by
  refine isClosed_preimage_val.mpr fun x hx => ?_
  exact mem_of_mem_closure_annularChain htw hch hx.1
    (closure_mono inter_subset_right hx.2)

theorem IsAnnularChain.closure_annularChain_subset
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (hch : IsAnnularChain H B Jlo Jhi (fun i => φ '' S i) S'' T'' P') :
    closure (annularChain H B P') ⊆ annularChain H B P' ∪ Dbdimg := by
  have hsplit : (⋃ i, φ '' S i) =
      (⋃ i, ⋃ (_ : i ≤ (0 : ℤ)), φ '' S i) ∪
        (⋃ i, ⋃ (_ : (0 : ℤ) ≤ i), φ '' S i) := by
    ext x
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨i, hi⟩
      rcases le_total i 0 with hi₀ | h₀i
      · exact Or.inl ⟨i, hi₀, hi⟩
      · exact Or.inr ⟨i, h₀i, hi⟩
    · rintro (⟨i, -, hi⟩ | ⟨i, -, hi⟩) <;> exact ⟨i, hi⟩
  have hcover : closure (⋃ i, φ '' S i) ⊆ I ∪ Dbdimg := by
    rw [hsplit, closure_union, htw.closureLower, htw.closureUpper]
    rintro x ((hx | hx) | (hx | hx))
    · obtain ⟨i, -, hi⟩ := mem_iUnion₂.mp hx
      exact Or.inl (htw.subsetInterior i hi)
    · exact Or.inl (mem_singleton_iff.mp hx ▸ htw.centerMemInterior)
    · obtain ⟨i, -, hi⟩ := mem_iUnion₂.mp hx
      exact Or.inl (htw.subsetInterior i hi)
    · exact Or.inr hx
  have hchain : annularChain H B P' ⊆ (⋃ i, φ '' S i) ∪ {P'} := by
    rintro x (hx | hx)
    · obtain ⟨i, hi | hi⟩ := mem_iUnion.mp hx
      · exact Or.inl (mem_iUnion.mpr ⟨2 * i, hch.halfSubsetTorus i hi⟩)
      · rcases hch.bridgeSubset i hi with (h₀ | h₁) | h₂
        · exact Or.inl (mem_iUnion.mpr ⟨2 * i, h₀⟩)
        · exact Or.inl (mem_iUnion.mpr ⟨2 * i + 1, h₁⟩)
        · exact Or.inl (mem_iUnion.mpr ⟨2 * i + 2, h₂⟩)
    · exact Or.inr hx
  intro x hx
  have hxcover := closure_mono hchain hx
  rw [closure_union, closure_singleton] at hxcover
  rcases hxcover with hxS | hxP
  · rcases hcover hxS with hxI | hxrim
    · exact Or.inl (mem_of_mem_closure_annularChain htw hch hxI hx)
    · exact Or.inr hxrim
  · exact Or.inl (Or.inr hxP)

end DifferentialGeometry.Topology.PiecewiseLinear
