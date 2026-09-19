/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDerivedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInteriorDensity
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary

/-! Intrinsic boundary traces of cells outside a derived neighborhood. -/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
omit [FiniteDimensional ℝ E] in
theorem derivedNeighborhood_space_of_insert_face
    (K L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces)
    (hproper : ∀ t : Finset E, t.Nonempty → t ⊂ s → t ∈ L.faces) :
    (derivedNeighborhood K (subcomplexGeneratedBy K (insert s L.faces))).space =
      (derivedNeighborhoodCell K s).space ∪ (derivedNeighborhood K L).space := by
  classical
  have hfaces : (subcomplexGeneratedBy K (insert s L.faces)).faces = insert s L.faces := by
    ext t
    constructor
    · rintro ⟨u, ⟨_, hu⟩, htu, ht⟩
      rcases hu with hus | hu
      · subst u
        by_cases hts : t = s
        · exact Or.inl hts
        · exact Or.inr (hproper t ht (Finset.ssubset_iff_subset_ne.mpr ⟨htu, hts⟩))
      · exact Or.inr (L.down_closed hu htu ht)
    · rintro (ht | ht)
      · subst t
        exact ⟨s, ⟨hs, Or.inl rfl⟩, Finset.Subset.rfl, K.nonempty_of_mem_faces hs⟩
      · exact ⟨t, ⟨hLK ht, Or.inr ht⟩, Finset.Subset.rfl, L.nonempty_of_mem_faces ht⟩
  rw [← iUnion_derivedNeighborhoodCell_space K _ (subcomplexGeneratedBy_faces_subset K _),
    ← iUnion_derivedNeighborhoodCell_space K L hLK]
  ext x
  simp only [mem_iUnion, hfaces, mem_insert_iff, mem_union]
  aesop

open Classical in
theorem derivedNeighborhoodCell_inter_subset_boundary_derivedNeighborhood
    {n : ℕ} (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 2) K) (hLK : L.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces) (hsL : s ∉ L.faces) :
    (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhood K L).space ⊆
      (boundaryComplex (n + 2) (derivedNeighborhood K L)).space := by
  classical
  let C := derivedNeighborhoodCell K s
  let N := derivedNeighborhood K L
  let _ : Finite C.faces := (derivedNeighborhoodCell_faces_finite K s).to_subtype
  let _ : Finite N.faces := (derivedNeighborhood_faces_finite K L).to_subtype
  have hC : IsCombinatorialManifoldWithBoundary (n + 2) C :=
    (hK.isPLBall_derivedNeighborhoodCell hs).isCombinatorialManifoldWithBoundary
  have hN : IsCombinatorialManifoldWithBoundary (n + 2) N := hK.derivedNeighborhood L
  have hI : C.space ∩ N.space ⊆ (boundaryComplex (n + 2) C).space := by
    rintro x ⟨hxC, hxN⟩
    change x ∈ (derivedNeighborhood K L).space at hxN
    rw [← iUnion_derivedNeighborhoodCell_space K L hLK] at hxN
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hxN
    exact hK.derivedNeighborhoodCell_inter_subset_boundaryComplex hs (hLK ht)
      (fun h => hsL (h.symm ▸ ht)) ⟨hxC, hxt⟩
  have hCclosure : C.space ⊆ closure (K.space \ N.space) := by
    apply hC.space_subset_closure_sdiff_boundaryComplex_space.trans
    apply closure_mono
    rintro x ⟨hxC, hxB⟩
    exact ⟨derivedNeighborhoodCell_space_subset K s hxC, fun hxN => hxB (hI ⟨hxC, hxN⟩)⟩
  rintro x ⟨hxC, hxN⟩
  exact inter_closure_sdiff_subset_boundaryComplex K N hK hN
    (derivedNeighborhood_space_subset K L) ⟨hxN, hCclosure hxC⟩

end DifferentialGeometry.Topology.PiecewiseLinear
