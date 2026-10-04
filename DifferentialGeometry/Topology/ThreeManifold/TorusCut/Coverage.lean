import DifferentialGeometry.Topology.ThreeManifold.TorusCut.Decomposition

set_option autoImplicit false

/-!
# Cut-piece coverage for torus systems

For a torus gluing `G` of a compact carrier `C` with component system `D`, the images of the open
piece interiors under the quotient map are pairwise disjoint and cover exactly the complement of
the union of the glued tori. The images of two distinct compact pieces meet only along tori. The
same statements are transported to a torus decomposition of a closed oriented 3-manifold `M`
through its reconstruction diffeomorphism, where two compact pieces meet only along tori whose
two sides are owned by those pieces.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

namespace GC.Endpoint.TorusGluing
universe u
variable {C : CompactCarrier.{u}}

private theorem mem_boundary_of_mem_block (G : TorusGluing C) {k : Fin G.count} {x : C.Carrier}
    (hx : x ∈ G.gluing.block k) : x ∈ C.model.boundary C.Carrier := by
  rw [G.boundary_exhausted]
  exact Set.mem_iUnion.mpr ⟨k, hx⟩

theorem quotientMap_mem_range_torusMap (G : TorusGluing C) {k : Fin G.count} {x : C.Carrier}
    (hx : x ∈ G.gluing.block k) : G.quotientMap x ∈ Set.range (G.torusMap k) := by
  rcases hx with hl | hr
  · refine ⟨(G.leftParam k).symm ⟨x, hl⟩, ?_⟩
    change G.quotientMap ((G.leftParam k) ((G.leftParam k).symm ⟨x, hl⟩)).val = G.quotientMap x
    rw [Homeomorph.apply_symm_apply]
  · let b := (G.gluing.attaching k).symm ⟨x, hr⟩
    refine ⟨(G.leftParam k).symm b, ?_⟩
    change G.quotientMap ((G.leftParam k) ((G.leftParam k).symm b)).val = G.quotientMap x
    rw [Homeomorph.apply_symm_apply]
    have h : G.quotientMap (G.gluing.attaching k b) = G.quotientMap b :=
      Quotient.sound' (G.gluing.rel_of_attaching k b)
    simpa only [b, Homeomorph.apply_symm_apply] using h.symm

private theorem eq_of_mem_piece (D : C.Components) {a b : Fin D.count} {x : C.Carrier}
    (ha : x ∈ D.piece a) (hb : x ∈ D.piece b) : a = b := by
  by_contra h
  exact (D.disjoint h).le_bot ⟨ha, hb⟩

theorem disjoint_image_pieceInterior (G : TorusGluing C) (D : C.Components)
    {i j : Fin D.count} (hij : i ≠ j) :
    Disjoint (G.quotientMap '' (C.pieceInterior (D.piece i) : Set C.Carrier))
      (G.quotientMap '' (C.pieceInterior (D.piece j) : Set C.Carrier)) := by
  rw [Set.disjoint_left]
  rintro q ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  obtain rfl := G.interior_fiber_singleton hx.2 hxy.symm
  exact hij (eq_of_mem_piece D hx.1 hy.1)

theorem image_piece_inter_subset (G : TorusGluing C) (D : C.Components)
    {i j : Fin D.count} (hij : i ≠ j) :
    G.quotientMap '' (D.piece i : Set C.Carrier) ∩
        G.quotientMap '' (D.piece j : Set C.Carrier) ⊆
      ⋃ k, Set.range (G.torusMap k) := by
  rintro q ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
  rcases (G.quotientMap_eq_iff y x).mp hxy with rfl | ⟨k, hyk, -⟩
  · exact (hij (eq_of_mem_piece D hx hy)).elim
  · rw [← hxy]
    exact Set.mem_iUnion.mpr ⟨k, G.quotientMap_mem_range_torusMap hyk⟩

theorem iUnion_image_pieceInterior (G : TorusGluing C) (D : C.Components) :
    ⋃ i, G.quotientMap '' (C.pieceInterior (D.piece i) : Set C.Carrier) =
      (⋃ k, Set.range (G.torusMap k))ᶜ := by
  ext q
  constructor
  · rintro hq
    obtain ⟨i, x, hx, rfl⟩ := Set.mem_iUnion.mp hq
    rintro hk
    obtain ⟨k, t, ht⟩ := Set.mem_iUnion.mp hk
    have he : G.quotientMap x = G.quotientMap (G.leftParam k t).val := ht.symm
    obtain rfl := G.interior_fiber_singleton hx.2 he
    exact C.model.disjoint_interior_boundary.le_bot
      ⟨hx.2, G.mem_boundary_of_mem_block (Or.inl (G.leftParam k t).property)⟩
  · intro hq
    rcases G.interior_or_torus q with ⟨x, rfl⟩ | ⟨k, t, rfl⟩
    · have hx : x.val ∈ ⋃ i, (D.piece i : Set C.Carrier) := D.covers ▸ Set.mem_univ _
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨i, x.val, ⟨hi, x.property⟩, rfl⟩
    · exact (hq (Set.mem_iUnion.mpr ⟨k, t, rfl⟩)).elim

end GC.Endpoint.TorusGluing

namespace GC.Topology.TorusDecomposition
universe u
variable {M : ConnectedClosedOrientedManifold.{u} 3}

private theorem disjoint_image_comp {X Y Z : Type*} {f : Y → Z} (hf : Function.Injective f)
    {g : X → Y} {s t : Set X} (h : Disjoint (g '' s) (g '' t)) :
    Disjoint ((f ∘ g) '' s) ((f ∘ g) '' t) := by
  rw [Set.image_comp, Set.image_comp]
  exact (Set.disjoint_image_iff hf).mpr h

private theorem iUnion_image_comp_eq_compl {X Y Z ι κ : Type*} {f : Y → Z}
    (hf : Function.Bijective f) {g : X → Y} {s : ι → Set X} {t : κ → Set Y}
    (h : ⋃ i, g '' s i = (⋃ k, t k)ᶜ) : ⋃ i, (f ∘ g) '' s i = (⋃ k, f '' t k)ᶜ := by
  simp only [Set.image_comp]
  rw [← Set.image_iUnion, h, ← Set.image_iUnion, Set.image_compl_eq hf]

private theorem range_torusInPrime (D : TorusDecomposition M) (k : Fin D.boundary.count) :
    Set.range (D.reconstructionAtlas.torusInPrime D.reconstruction k) =
      D.reconstruction.val '' Set.range (D.boundary.torusMap k) := by
  rw [SmoothAssembly.torusInPrime, ContinuousMap.coe_comp, Set.range_comp]
  rfl

theorem disjoint_image_pieceInterior (D : TorusDecomposition M)
    {i j : Fin D.components.count} (hij : i ≠ j) :
    Disjoint
      ((⇑D.reconstruction.val ∘ D.boundary.quotientMap) ''
        (D.carrier.pieceInterior (D.components.piece i) : Set D.carrier.Carrier))
      ((⇑D.reconstruction.val ∘ D.boundary.quotientMap) ''
        (D.carrier.pieceInterior (D.components.piece j) : Set D.carrier.Carrier)) := by
  exact disjoint_image_comp D.reconstruction.val.injective
    (D.boundary.disjoint_image_pieceInterior D.components hij)

theorem image_piece_inter_subset (D : TorusDecomposition M)
    {i j : Fin D.components.count} (hij : i ≠ j) :
    (⇑D.reconstruction.val ∘ D.boundary.quotientMap) ''
        (D.components.piece i : Set D.carrier.Carrier) ∩
      (⇑D.reconstruction.val ∘ D.boundary.quotientMap) ''
        (D.components.piece j : Set D.carrier.Carrier) ⊆
      ⋃ (k) (_ : D.leftPiece k = i ∧ D.rightPiece k = j ∨
          D.leftPiece k = j ∧ D.rightPiece k = i),
        Set.range (D.reconstructionAtlas.torusInPrime D.reconstruction k) := by
  rintro q ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
  have hq : D.boundary.quotientMap y = D.boundary.quotientMap x :=
    D.reconstruction.val.injective hxy
  rcases (D.boundary.quotientMap_eq_iff y x).mp hq with rfl | ⟨k, hyk, hxk⟩
  · exact (hij (TorusGluing.eq_of_mem_piece D.components hx hy)).elim
  refine Set.mem_iUnion₂.mpr ⟨k, ?_, ?_⟩
  · rcases hyk with hl | hr
    · rw [D.boundary.gluing.flip_of_mem_left hl] at hxk
      have hxr : x ∈ D.boundary.gluing.right k := hxk ▸ (D.boundary.gluing.attaching k _).2
      exact Or.inr ⟨TorusGluing.eq_of_mem_piece D.components (D.left_owned k hl) hy,
        TorusGluing.eq_of_mem_piece D.components (D.right_owned k hxr) hx⟩
    · rw [D.boundary.gluing.flip_of_mem_right hr] at hxk
      have hxl : x ∈ D.boundary.gluing.left k :=
        hxk ▸ ((D.boundary.gluing.attaching k).symm _).2
      exact Or.inl ⟨TorusGluing.eq_of_mem_piece D.components (D.left_owned k hxl) hx,
        TorusGluing.eq_of_mem_piece D.components (D.right_owned k hr) hy⟩
  · rw [range_torusInPrime]
    obtain ⟨t, ht⟩ := D.boundary.quotientMap_mem_range_torusMap hyk
    exact ⟨D.boundary.torusMap k t, ⟨t, rfl⟩, by rw [ht, hq]; rfl⟩

theorem iUnion_image_pieceInterior (D : TorusDecomposition M) :
    ⋃ i, (⇑D.reconstruction.val ∘ D.boundary.quotientMap) ''
        (D.carrier.pieceInterior (D.components.piece i) : Set D.carrier.Carrier) =
      (⋃ k, Set.range (D.reconstructionAtlas.torusInPrime D.reconstruction k))ᶜ := by
  simp only [range_torusInPrime]
  exact iUnion_image_comp_eq_compl D.reconstruction.val.bijective
    (D.boundary.iUnion_image_pieceInterior D.components)

end GC.Topology.TorusDecomposition
