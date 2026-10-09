/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Combinatorial
import DifferentialGeometry.Topology.PiecewiseLinear.ExhaustionGeneral
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteSplittingDisks

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

open Classical in
theorem LocallyFinitePLPieceIn.starComplex_faces_finite
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    {Y : Set X} (T : LocallyFinitePLPieceIn E n X Y) {v : E}
    (hv : ({v} : Finset E) ∈ T.complex.faces) :
    (starComplex T.complex v).faces.Finite := by
  let P : Set (Finset E) := {s | s ∈ T.complex.faces ∧ ({v} : Finset E) ⊆ s}
  have hP : P.Finite := by
    refine (T.cofaces_finite hv).image (fun s : T.complex.faces => (s : Finset E)) |>.subset ?_
    rintro s ⟨hs, hvs⟩
    exact ⟨⟨s, hs⟩, hvs, rfl⟩
  refine (hP.union (hP.image fun s => s.erase v)).subset ?_
  intro s hs
  rw [mem_starComplex_faces_iff] at hs
  by_cases hvs : v ∈ s
  · exact Or.inl ⟨hs.1, Finset.singleton_subset_iff.mpr hvs⟩
  · refine Or.inr ⟨insert v s,
      ⟨hs.2, Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)⟩, ?_⟩
    exact Finset.erase_insert hvs

open Classical in
theorem LocallyFinitePLPieceIn.closedStar_mem_nhdsWithin
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    {Y : Set X} (T : LocallyFinitePLPieceIn E n X Y) {v : E}
    (hv : ({v} : Finset E) ∈ T.complex.faces) :
    closedStar T.complex v ∈ 𝓝[T.complex.space] v := by
  let F : T.complex.faces → Set T.complex.space := fun s =>
    (Subtype.val : T.complex.space → E) ⁻¹' convexHull ℝ ((s : Finset E) : Set E)
  let I := {s : T.complex.faces // v ∉ (s : Finset E)}
  have hFclosed (s : T.complex.faces) : IsClosed (F s) := by
    exact (s.1.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed.preimage
      continuous_subtype_val
  have hFloc : LocallyFinite F := by
    simpa only [F] using T.locallyFinite
  have hWclosed : IsClosed (⋃ i : I, F i.val) :=
    (hFloc.comp_injective Subtype.val_injective).isClosed_iUnion fun i => hFclosed i.val
  have hvspace : v ∈ T.complex.space :=
    T.complex.convexHull_subset_space hv (subset_convexHull ℝ _ (by simp))
  have hvnot : (⟨v, hvspace⟩ : T.complex.space) ∉ ⋃ i : I, F i.val := by
    intro h
    obtain ⟨i, hi⟩ := mem_iUnion.mp h
    change v ∈ convexHull ℝ ((i.val : Finset E) : Set E) at hi
    exact i.property (mem_of_mem_convexHull_of_singleton_mem T.complex hv i.val.property hi)
  have hpre : (Subtype.val : T.complex.space → E) ⁻¹' closedStar T.complex v ∈
      𝓝 (⟨v, hvspace⟩ : T.complex.space) := by
    refine Filter.mem_of_superset (hWclosed.isOpen_compl.mem_nhds hvnot) ?_
    intro z hz
    obtain ⟨s, hs, hzs⟩ := T.complex.mem_space_iff.mp z.property
    have hvs : v ∈ s := by
      by_contra hvs
      apply hz
      refine mem_iUnion.mpr ⟨⟨⟨s, hs⟩, hvs⟩, ?_⟩
      exact hzs
    exact mem_iUnion₂.mpr
      ⟨s, ⟨hs, subset_convexHull ℝ _ (Finset.mem_coe.mpr hvs)⟩, hzs⟩
  exact preimage_coe_mem_nhds_subtype.mp hpre

section

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] {U : Set M₁}

theorem isCombinatorialManifold_of_locallyFinitePLPieceIn [T2Space M₁]
    (hU : IsOpen U) (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U) :
    IsCombinatorialManifold 3 𝒦.complex := by
  classical
  intro v hv
  let L := starComplex 𝒦.complex v
  have hLfin : L.faces.Finite := 𝒦.starComplex_faces_finite hv
  let _ : Finite L.faces := hLfin.to_subtype
  have hLsub : L.space ⊆ 𝒦.complex.space :=
    space_mono_of_faces_subset (starComplex_faces_subset 𝒦.complex v)
  have hvspace : v ∈ 𝒦.complex.space :=
    𝒦.complex.convexHull_subset_space hv (subset_convexHull ℝ _ (by simp))
  have hsource : closedStar 𝒦.complex v ∈ 𝓝[𝒦.complex.space] v :=
    𝒦.closedStar_mem_nhdsWithin hv
  have himage : 𝒦.map '' L.space ∈ 𝓝 (𝒦.map v) := by
    have hpre : Set.preimage (Subtype.val : 𝒦.complex.space → Ea)
        (closedStar 𝒦.complex v) ∈
        𝓝 (⟨v, hvspace⟩ : 𝒦.complex.space) :=
      preimage_coe_mem_nhds_subtype.mpr hsource
    have hwithin := 𝒦.isEmbedding.isInducing.image_mem_nhdsWithin hpre
    have hrange : Set.range (fun x : 𝒦.complex.space => 𝒦.map x) = U := by
      change Set.range (𝒦.map ∘ Subtype.val) = U
      rw [Set.range_comp, Subtype.range_val, 𝒦.bijOn.image_eq]
    have hset : (fun x : 𝒦.complex.space => 𝒦.map x) ''
        Set.preimage (Subtype.val : 𝒦.complex.space → Ea) (closedStar 𝒦.complex v) =
        𝒦.map '' closedStar 𝒦.complex v := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, closedStar_subset_space 𝒦.complex v hz⟩, hz, rfl⟩
    have hmapstar : 𝒦.map '' closedStar 𝒦.complex v ∈ 𝓝[U] (𝒦.map v) := by
      simpa only [hset, hrange] using hwithin
    have hmapv : 𝒦.map v ∈ U := 𝒦.bijOn.mapsTo hvspace
    rw [nhdsWithin_eq_nhds.mpr (hU.mem_nhds hmapv)] at hmapstar
    rwa [starComplex_space 𝒦.complex v hv]
  let T : PLPieceIn Ea 3 M₁ (𝒦.map '' L.space) := by
    refine ⟨L, hLfin, 𝒦.map, (𝒦.bijOn.injOn.mono hLsub).bijOn_image,
      𝒦.continuousOn.mono hLsub, ?_, ?_⟩
    · intro e he
      have h := (𝒦.isPiecewiseAffineOn_chart e he).inter_of_isPolyhedron
        (PiecewiseLinear.isPolyhedron_space L)
      have heq : (𝒦.complex.space ∩ 𝒦.map ⁻¹' e.source) ∩ L.space =
          L.space ∩ 𝒦.map ⁻¹' e.source := by
        ext x
        constructor
        · rintro ⟨⟨hxK, hxe⟩, hxL⟩
          exact ⟨hxL, hxe⟩
        · rintro ⟨hxL, hxe⟩
          exact ⟨⟨hLsub hxL, hxe⟩, hxL⟩
      rwa [heq] at h
    · intro e he
      have h := (𝒦.isPiecewiseAffineOn_chart_symm e he).inter_preimage_of_isPolyhedron
        (PiecewiseLinear.isPolyhedron_space L)
      have heq : (e.target ∩ e.symm ⁻¹' U) ∩
          (Function.invFunOn 𝒦.map 𝒦.complex.space ∘ e.symm) ⁻¹' L.space =
          e.target ∩ e.symm ⁻¹' (𝒦.map '' L.space) := by
        ext y
        constructor
        · rintro ⟨⟨hy, hyU⟩, hyL⟩
          exact ⟨hy, Function.invFunOn 𝒦.map 𝒦.complex.space (e.symm y), hyL,
            𝒦.bijOn.invOn_invFunOn.2 hyU⟩
        · rintro ⟨hy, z, hz, hzy⟩
          refine ⟨⟨hy, ?_⟩, ?_⟩
          · change e.symm y ∈ U
            rw [← hzy]
            exact 𝒦.bijOn.mapsTo (hLsub hz)
          · change Function.invFunOn 𝒦.map 𝒦.complex.space (e.symm y) ∈ L.space
            rw [← hzy, 𝒦.bijOn.invOn_invFunOn.1 (hLsub hz)]
            exact hz
      rw [heq] at h
      refine h.congr fun y hy => ?_
      have hmem := (𝒦.bijOn.injOn.mono hLsub).bijOn_image.surjOn.mapsTo_invFunOn hy.2
      have hUmem := (image_mono hLsub).trans 𝒦.bijOn.mapsTo.image_subset hy.2
      exact 𝒦.bijOn.injOn (hLsub hmem) (𝒦.bijOn.surjOn.mapsTo_invFunOn hUmem)
        (((𝒦.bijOn.injOn.mono hLsub).bijOn_image.invOn_invFunOn.2 hy.2).trans
          (𝒦.bijOn.invOn_invFunOn.2 hUmem).symm)
  have hvL : ({v} : Finset Ea) ∈ L.faces := singleton_mem_starComplex 𝒦.complex v hv
  obtain ⟨L', hL', hL'fin, hstars⟩ :=
    exists_isSubdivision_closedStar_subset (n := 3) L T.continuousOn
  let _ : Finite L'.faces := hL'fin.to_subtype
  have hvL' : ({v} : Finset Ea) ∈ L'.faces := hL'.singleton_mem hvL
  obtain ⟨e, he, hstar⟩ := hstars v hvL'
  let T' := T.subdivide L' hL' hL'fin
  have hvT' : v ∈ T'.complex.space :=
    T'.complex.convexHull_subset_space hvL' (subset_convexHull ℝ _ (by simp))
  have hnhds : T'.map '' closedStar T'.complex v ∈ 𝓝 (T'.map v) := by
    change T.map '' closedStar L' v ∈ 𝓝 (T.map v)
    exact T'.image_mem_nhds_of_mem_nhds hvT' himage (closedStar_mem_nhdsWithin L' v)
  have hlink : IsPLSphere 2 (SimplicialComplex.geometricLink L' {v}).space :=
    T'.isPLSphere_geometricLink_of_image_mem_nhds hvL' e he hstar hnhds
  rw [isPLSphere_geometricLink_iff_of_isSubdivision hL' hvL,
    geometricLink_starComplex] at hlink
  exact hlink

end

end DifferentialGeometry.Topology.PiecewiseLinear
