/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodAttachments
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.LinkDimension
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGraphApproximation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem closure_space_sdiff_derivedNeighborhood_space {A K L : Geometry.SimplicialComplex ℝ E}
    [Finite K.faces] (hKA : K.faces ⊆ A.faces) (hLA : L.faces ⊆ A.faces) :
    closure (K.space \ (derivedNeighborhood K L).space) =
      ⋃ σ ∈ {σ : Finset E | σ ∈ K.faces ∧ σ ∉ L.faces},
        (derivedNeighborhoodCell K σ).space := by
  classical
  apply Subset.antisymm
  · have hclosed : IsClosed (⋃ σ ∈ {σ : Finset E | σ ∈ K.faces ∧ σ ∉ L.faces},
        (derivedNeighborhoodCell K σ).space) := by
      refine Set.Finite.isClosed_biUnion ((Set.toFinite K.faces).subset fun σ hσ => hσ.1)
        fun σ _ => ?_
      have := (derivedNeighborhoodCell_faces_finite K σ).to_subtype
      exact (SimplicialComplex.isCompact_geometricSpace _).isClosed
    refine closure_minimal ?_ hclosed
    rintro y ⟨hyK, hyN⟩
    have hyK2 : y ∈ (secondDerived K).space := by
      rw [(secondDerived_isSubdivision K).space_eq]
      exact hyK
    obtain ⟨u, hu, hyu⟩ := exists_face_mem_openSimplex (secondDerived K) hyK2
    obtain ⟨D, hD, hDne, rfl⟩ := hu
    have hDN : ¬ ∀ e ∈ D, ∃ τ ∈ L.faces, τ.centroid ℝ id ∈ e := fun hall =>
      hyN ((derivedNeighborhood K L).convexHull_subset_space
        ((mem_derivedNeighborhood_faces_iff_of_flag hD hDne).mpr hall)
        (openSimplex_subset_convexHull _ hyu))
    obtain ⟨e₀, he₀, hbot⟩ := hD.exists_bot hDne
    obtain ⟨d₀, hd₀, hd₀ne, rfl⟩ := hD.1 e₀ he₀
    obtain ⟨σ, hσ, -⟩ := hd₀.exists_bot hd₀ne
    have hσK : σ ∈ K.faces := hd₀.1 σ hσ
    have hσe₀ : σ.centroid ℝ id ∈ d₀.image fun s => s.centroid ℝ id := Finset.mem_image_of_mem _ hσ
    have hσL : σ ∉ L.faces := fun hσL => hDN fun e he => ⟨σ, hσL, hbot e he hσe₀⟩
    refine mem_iUnion₂.mpr ⟨σ, ⟨hσK, hσL⟩, (derivedNeighborhoodCell K σ).convexHull_subset_space
      ?_ (openSimplex_subset_convexHull _ hyu)⟩
    exact (mem_derivedNeighborhoodCell_faces_iff_of_flag hσK hD hDne).mpr fun e he => hbot e he hσe₀
  · refine iUnion₂_subset fun σ hσ x hx => ?_
    obtain ⟨u, hu, hxu⟩ := (derivedNeighborhoodCell K σ).mem_space_iff.mp hx
    obtain ⟨D, hD, hDne, rfl⟩ := derivedNeighborhoodCell_faces_subset K σ hu
    have hcond := (mem_derivedNeighborhoodCell_faces_iff_of_flag hσ.1 hD hDne).mp hu
    have hσsd := singleton_centroid_mem_barycentricSubdivision K hσ.1
    have hD' : IsFlag (barycentricSubdivision K) (insert {σ.centroid ℝ id} D) := by
      refine ⟨fun e he => ?_, fun e he f hf => ?_⟩
      · rcases Finset.mem_insert.mp he with rfl | he
        · exact hσsd
        · exact hD.1 e he
      · rcases Finset.mem_insert.mp he with rfl | he <;>
          rcases Finset.mem_insert.mp hf with rfl | hf
        · exact Or.inl subset_rfl
        · exact Or.inl (Finset.singleton_subset_iff.mpr (hcond f hf))
        · exact Or.inr (Finset.singleton_subset_iff.mpr (hcond e he))
        · exact hD.2 e he f hf
    have hD'ne : (insert {σ.centroid ℝ id} D).Nonempty := Finset.insert_nonempty _ _
    set u' := (insert {σ.centroid ℝ id} D).image fun e => e.centroid ℝ id
    have hu'sd : u' ∈ (secondDerived K).faces := ⟨_, hD', hD'ne, rfl⟩
    have hu'N : u' ∉ (derivedNeighborhood K L).faces := by
      intro hN
      obtain ⟨τ, hτ, hτσ⟩ := (mem_derivedNeighborhood_faces_iff_of_flag hD' hD'ne).mp hN
        {σ.centroid ℝ id} (Finset.mem_insert_self _ _)
      have heq : τ = σ := injOn_faces_of_mem_openSimplex A
        (centroid_mem_openSimplex_of_mem_faces A) (hLA hτ) (hKA hσ.1)
        (Finset.mem_singleton.mp hτσ)
      exact hσ.2 (heq ▸ hτ)
    have hopen : openSimplex u' ⊆ K.space \ (derivedNeighborhood K L).space := by
      intro z hz
      refine ⟨?_, fun hzN => hu'N ?_⟩
      · rw [← (secondDerived_isSubdivision K).space_eq]
        exact (secondDerived K).convexHull_subset_space hu'sd (openSimplex_subset_convexHull _ hz)
      · exact mem_faces_of_mem_openSimplex_of_mem_space (derivedNeighborhood_faces_subset K L)
          hu'sd hz hzN
    have hsub : (D.image fun e => e.centroid ℝ id) ⊆ u' :=
      Finset.image_subset_image (Finset.subset_insert _ _)
    have hu'ne : u'.Nonempty := hD'ne.image _
    exact closure_mono hopen (convexHull_subset_closure_openSimplex hu'ne
      (convexHull_mono (Finset.coe_subset.mpr hsub) hxu))

open Classical in
theorem closure_convexHull_sdiff_derivedNeighborhood_space {A L : Geometry.SimplicialComplex ℝ E}
    [Finite A.faces] (hLA : L.faces ⊆ A.faces) {s : Finset E} (hs : s ∈ A.faces) :
    closure (convexHull ℝ (s : Set E) \ (derivedNeighborhood A L).space) =
      ⋃ σ ∈ {σ : Finset E | σ ⊆ s ∧ σ.Nonempty ∧ σ ∉ L.faces},
        (derivedNeighborhoodCell (restrict A (convexHull ℝ (s : Set E))) σ).space := by
  classical
  set S := restrict A (convexHull ℝ (s : Set E))
  have : Finite S.faces := (restrict_faces_finite A _).to_subtype
  have hSA : S.faces ⊆ A.faces := restrict_faces_subset A _
  have hSsp : S.space = convexHull ℝ (s : Set E) := restrict_convexHull_space hs
  have hset : convexHull ℝ (s : Set E) \ (derivedNeighborhood A L).space =
      S.space \ (derivedNeighborhood S L).space := by
    rw [← derivedNeighborhood_space_inter_subcomplex A S L hSA, hSsp]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  have hfaces : ∀ σ : Finset E, σ ∈ S.faces ↔ σ ⊆ s ∧ σ.Nonempty := by
    intro σ
    constructor
    · intro hσ
      have hne := S.nonempty_of_mem_faces hσ
      exact ⟨face_subset_of_mem_openSimplex_of_mem_convexHull A (hSA hσ) hs
        (centroid_mem_openSimplex hne) (hσ.2 (openSimplex_subset_convexHull σ
          (centroid_mem_openSimplex hne))), hne⟩
    · rintro ⟨hσs, hne⟩
      exact ⟨A.down_closed hs hσs hne, convexHull_mono (Finset.coe_subset.mpr hσs)⟩
  rw [hset, closure_space_sdiff_derivedNeighborhood_space hSA hLA]
  ext x
  simp only [mem_iUnion, mem_ofPred_eq, exists_prop, hfaces, and_assoc]

end Generic

section Compact

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Geometry.SimplicialComplex ℝ E3} {C : Set E3}

theorem vertices_eq_setOf_restrict_section34CompactGraphSkeleton
    {K : Geometry.SimplicialComplex ℝ E3} :
    K.vertices = {v | {v} ∈ (restrict K (section34CompactGraphSkeleton K)).faces} := by
  ext v
  exact ⟨fun hv => ⟨hv, convexHull_subset_section34CompactGraphSkeleton hv (by simp)⟩,
    fun hv => hv.1⟩

theorem mem_restrict_section34CompactGraphSkeleton_iff {K : Geometry.SimplicialComplex ℝ E3}
    {s σ : Finset E3} (hs : s ∈ K.faces) (hσs : σ ⊆ s) (hne : σ.Nonempty) :
    σ ∈ (restrict K (section34CompactGraphSkeleton K)).faces ↔ σ.card ≤ 2 := by
  have hσ : σ ∈ K.faces := K.down_closed hs hσs hne
  exact ⟨card_le_two_of_mem_restrict_section34CompactGraphSkeleton,
    fun hcard => ⟨hσ, convexHull_subset_section34CompactGraphSkeleton hσ hcard⟩⟩

open Classical in
theorem closure_convexHull_sdiff_iUnion_graphDualCell_of_card_eq_three [Finite M.faces]
    (s : Section34CompactSimplexIndex (restrict M C) 3) :
    closure (convexHull ℝ (s.1 : Set E3) \ ⋃ v ∈ (restrict M C).vertices,
      (graphDualCell M (restrict (restrict M C) (section34CompactGraphSkeleton (restrict M C)))
        v).space) =
    (derivedNeighborhoodCell (restrict M (convexHull ℝ (s.1 : Set E3))) s.1).space := by
  have hLM : (restrict (restrict M C) (section34CompactGraphSkeleton (restrict M C))).faces ⊆
      M.faces := (restrict_faces_subset _ _).trans (restrict_faces_subset M C)
  have hsM : s.1 ∈ M.faces := s.2.1.1
  have h := closure_convexHull_sdiff_derivedNeighborhood_space hLM hsM
  rw [← iUnion_graphDualCell_space M _ hLM,
    ← vertices_eq_setOf_restrict_section34CompactGraphSkeleton] at h
  rw [h]
  apply Subset.antisymm
  · refine iUnion₂_subset fun σ hσ => ?_
    have hσs : σ = s.1 := by
      by_contra hne
      have hlt : σ.card < s.1.card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hσ.1, hne⟩)
      exact hσ.2.2 ((mem_restrict_section34CompactGraphSkeleton_iff s.2.1 hσ.1 hσ.2.1).mpr
        (by rw [s.2.2] at hlt; omega))
    subst hσs
    exact subset_rfl
  · exact subset_biUnion_of_mem (u := fun σ => (derivedNeighborhoodCell
      (restrict M (convexHull ℝ (s.1 : Set E3))) σ).space)
      ⟨subset_rfl, (restrict M C).nonempty_of_mem_faces s.2.1, fun hmem => by
        have := card_le_two_of_mem_restrict_section34CompactGraphSkeleton hmem
        rw [s.2.2] at this
        omega⟩

open Classical in
theorem closure_convexHull_sdiff_iUnion_graphDualCell_of_card_eq_four [Finite M.faces]
    (t : Section34CompactSimplexIndex (restrict M C) 4) :
    closure (convexHull ℝ (t.1 : Set E3) \ ⋃ v ∈ (restrict M C).vertices,
      (graphDualCell M (restrict (restrict M C) (section34CompactGraphSkeleton (restrict M C)))
        v).space) =
    (derivedNeighborhoodCell (restrict M (convexHull ℝ (t.1 : Set E3))) t.1).space ∪
      ⋃ s ∈ t.1.powersetCard 3,
        (derivedNeighborhoodCell (restrict M (convexHull ℝ (t.1 : Set E3))) s).space := by
  have hLM : (restrict (restrict M C) (section34CompactGraphSkeleton (restrict M C))).faces ⊆
      M.faces := (restrict_faces_subset _ _).trans (restrict_faces_subset M C)
  have htM : t.1 ∈ M.faces := t.2.1.1
  have h := closure_convexHull_sdiff_derivedNeighborhood_space hLM htM
  rw [← iUnion_graphDualCell_space M _ hLM,
    ← vertices_eq_setOf_restrict_section34CompactGraphSkeleton] at h
  rw [h]
  apply Subset.antisymm
  · refine iUnion₂_subset fun σ hσ => ?_
    have hcard : 3 ≤ σ.card := by
      by_contra hlt
      exact hσ.2.2 ((mem_restrict_section34CompactGraphSkeleton_iff t.2.1 hσ.1 hσ.2.1).mpr
        (by omega))
    have hle : σ.card ≤ 4 := t.2.2 ▸ Finset.card_le_card hσ.1
    rcases Nat.lt_or_ge σ.card 4 with h3 | h4
    · refine subset_union_of_subset_right (subset_biUnion_of_mem (u := fun s =>
        (derivedNeighborhoodCell (restrict M (convexHull ℝ (t.1 : Set E3))) s).space) ?_) _
      exact Finset.mem_powersetCard.mpr ⟨hσ.1, by omega⟩
    · have hσt : σ = t.1 := Finset.eq_of_subset_of_card_le hσ.1 (by rw [t.2.2]; exact h4)
      subst hσt
      exact subset_union_left
  · refine union_subset ?_ (iUnion₂_subset fun s hs => ?_)
    · exact subset_biUnion_of_mem (u := fun σ => (derivedNeighborhoodCell
        (restrict M (convexHull ℝ (t.1 : Set E3))) σ).space)
        ⟨subset_rfl, (restrict M C).nonempty_of_mem_faces t.2.1, fun hmem => by
          have := card_le_two_of_mem_restrict_section34CompactGraphSkeleton hmem
          rw [t.2.2] at this
          omega⟩
    · obtain ⟨hst, hcard⟩ := Finset.mem_powersetCard.mp hs
      exact subset_biUnion_of_mem (u := fun σ => (derivedNeighborhoodCell
        (restrict M (convexHull ℝ (t.1 : Set E3))) σ).space)
        ⟨hst, Finset.card_pos.mp (by omega), fun hmem => by
          have := card_le_two_of_mem_restrict_section34CompactGraphSkeleton hmem
          omega⟩

theorem isPLBall_derivedNeighborhoodCell_restrict_of_card_eq_three [Finite M.faces]
    {s : Finset E3} (hs : s ∈ M.faces) (hcard : s.card = 3) :
    IsPLBall 2 (derivedNeighborhoodCell (restrict M (convexHull ℝ (s : Set E3))) s).space := by
  have : Finite (restrict M (convexHull ℝ (s : Set E3))).faces :=
    (restrict_faces_finite M _).to_subtype
  have hball : IsPLBall (1 + 1) (restrict M (convexHull ℝ (s : Set E3))).space := by
    rw [restrict_convexHull_space hs]
    exact isPLBall_convexHull_of_affineIndependent s (M.indep hs) hcard
  exact hball.isCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhoodCell
    ⟨hs, subset_rfl⟩

theorem isPLBall_residualCell_of_card_eq_four [Finite M.faces] {t : Finset E3}
    (ht : t ∈ M.faces) (hcard : t.card = 4) :
    IsPLBall 3 ((derivedNeighborhoodCell (restrict M (convexHull ℝ (t : Set E3))) t).space ∪
      ⋃ s ∈ t.powersetCard 3,
        (derivedNeighborhoodCell (restrict M (convexHull ℝ (t : Set E3))) s).space) := by
  have : Finite (restrict M (convexHull ℝ (t : Set E3))).faces :=
    (restrict_faces_finite M _).to_subtype
  have hball : IsPLBall (2 + 1) (restrict M (convexHull ℝ (t : Set E3))).space := by
    rw [restrict_convexHull_space ht]
    exact isPLBall_convexHull_of_affineIndependent t (M.indep ht) hcard
  exact hball.isCombinatorialManifoldWithBoundary.isPLBall_union_derivedNeighborhoodCells_of_card
    ⟨ht, subset_rfl⟩ (t.powersetCard 3) (k := 3) (by norm_num) (by omega)
    (fun s hs => (Finset.mem_powersetCard.mp hs).1) (fun s hs => (Finset.mem_powersetCard.mp hs).2)

end Compact

end DifferentialGeometry.Topology.PiecewiseLinear
