import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSeamFacesBase
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GTraceRows

/-!
# FC39 GROUP G, target `stub_exists_seams_faces` (lane FC39-G-SF): disjointness of the faces

Step G8 of the lane sheet (`build-logs/resume/sheet-FC39-G-SF.md`): two distinct catalogue faces
meet only when they are the two sides of one seam (`catImage_disjoint_GSF`, the `face_disjoint`
field of the face layer). Route, at the level of the rows:

* faces of different rows meet only along a shared face, with the two rows its slim owner and its
  neighbour (`rowBoundary_meet_GSF`): rows of the same kind have disjoint ranges (`disjoint`,
  `zero_cusp_disjoint`); a face of a slim piece is an end (`endFace_exhausted`); a cusp external face
  lies in `∂W`, every slim end in `W.interior`; a slim end meeting a neighbour face is the registered
  shared end of that face (`neighbourSet_disjoint_GSAFE`, `endSet_disjoint_GSAFE`), except possibly a
  NEW end against an UNREGISTERED neighbour face, two residual faces of different owners:
* `newEnd_disjoint_residualNeighbour_GSF` — they are disjoint: a new end lies in `M₂`
  (`slim_M2`), and `M₂ ⊆ R ∪ P` (`region_eq`); on the circle region a point lies on at most one
  residual face (the trace-atlas lemma `residualFace_eq_of_mem_region_GTR` of the common pack, draft
  58 §二 F2, HH), on the edge piece a residual face is the union of its registered end disks
  (`edge_faces`) and distinct end disks are disjoint;
* for catalogue entries, equal vertices force equal faces (`catalogue_eq_of_meet_GSF`), and the two
  sides of a shared face are the seam entries `sEntry_GSF` / `tEntry_GSF`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

namespace FC39RowsV2

variable (Rw : FC39RowsV2 W E)

/-- The image of the model boundary of the row piece of an index. -/
def rowBoundary_GSF (a : Rw.slim.RowIndex) : Set W.Carrier :=
  (Rw.rowPiece a).map '' (𝓡∂ 3).boundary (Rw.rowPiece a).Piece

/-! ## The new ends against the unregistered neighbour faces -/

/-- `M₂ ⊆ R ∪ P` (`region_eq`). -/
theorem regionM2_subset_GSF : regionM2 Rw.slim ⊆ Rw.circle.region ∪ Rw.edge.edgePiece := by
  intro x hx
  by_cases h : x ∈ relInt (regionM2 Rw.slim) Rw.edge.edgePiece
  · right
    obtain ⟨y, hy, rfl⟩ := h
    exact (interior_subset hy : y ∈ Subtype.val ⁻¹' Rw.edge.edgePiece)
  · left
    rw [← Rw.junctions.region_eq]
    exact ⟨hx, h⟩

/-- A new end lies in `M₂` (`slim_M2`). -/
theorem newEndSet_subset_regionM2_GSF (e : Rw.slim.NewEnd) :
    Rw.slim.endSet e.1 ⊆ regionM2 Rw.slim := by
  intro x hx
  have h : x ∈ ⋃ e : Rw.slim.NewEnd, Rw.slim.endSet e.1 := mem_iUnion.2 ⟨e, hx⟩
  rw [← Rw.junctions.slim_M2] at h
  exact h.2

/-- **G8-HARD.** A new end and an unregistered neighbour face (two residual faces of different
owners) are disjoint. -/
theorem newEnd_disjoint_residualNeighbour_GSF (e : Rw.slim.NewEnd)
    (F : {F : NeighbourFace Rw.zero Rw.cusp // ∀ e, Rw.slim.endKind e ≠ some F}) :
    Disjoint (Rw.slim.endSet e.1) (neighbourSet F.1) := by
  refine Set.disjoint_left.2 fun x hxe hxF => ?_
  let G : Rw.slim.ResidualFace := Sum.inr e
  let G' : Rw.slim.ResidualFace := Sum.inl F
  have hGG : G ≠ G' := Sum.inr_ne_inl
  have hxe' : x ∈ Rw.slim.residualSet G := hxe
  have hxF' : x ∈ Rw.slim.residualSet G' := hxF
  rcases Rw.regionM2_subset_GSF (Rw.newEndSet_subset_regionM2_GSF e hxe) with hR | hP
  · exact hGG (Rw.residualFace_eq_of_mem_region_GTR hR hxe' hxF')
  · have h1 : x ∈ Rw.edge.edgePiece ∩ Rw.slim.residualSet G := ⟨hP, hxe'⟩
    have h2 : x ∈ Rw.edge.edgePiece ∩ Rw.slim.residualSet G' := ⟨hP, hxF'⟩
    rw [Rw.junctions.edge_faces] at h1 h2
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 h1
    obtain ⟨c', hc', hxc'⟩ := mem_iUnion₂.1 h2
    have hcc : c = c' := by
      by_contra hne
      exact Set.disjoint_left.1 (Rw.edge.disk_disjoint fun h => hne (Subtype.ext h)) hxc hxc'
    subst hcc
    exact hGG (hc.symm.trans hc')

/-! ## Faces of the rows -/

/-- A slim end lies in `W.interior` (shared: through its neighbour; new: in `endNear`). -/
theorem endSet_subset_interior_GSF (e : Rw.slim.End) : Rw.slim.endSet e ⊆ W.interior := by
  rcases h : Rw.slim.endKind e with _ | F
  · intro x hx
    have hx' : x ∈ {x | x ∈ Rw.slim.endNear ⟨e, h⟩ ∧ Rw.slim.endFn ⟨e, h⟩ x = 0} := by
      rw [← Rw.slim.endFn_level ⟨e, h⟩]
      exact hx
    exact Rw.slim.endNear_interior ⟨e, h⟩ hx'.1
  · have hs : (Rw.slim.endKind e).isSome := by rw [h]; rfl
    exact Rw.sharedSet_subset_interior_GSF ⟨e, hs⟩

/-- A point of the model boundary image of a slim piece lies on one of its ends. -/
theorem exists_end_of_mem_slimBoundary_GSF {j : Fin Rw.slim.count} {x : W.Carrier}
    (hx : x ∈ Rw.rowBoundary_GSF (.inr (.inr j))) :
    ∃ e : Rw.slim.End, e.1.1 = j ∧ x ∈ Rw.slim.endSet e := by
  obtain ⟨q, hq, rfl⟩ := hx
  obtain ⟨β, hβ, hF⟩ := Rw.slim.endFace_exhausted j (ActualComponent.of hq)
  let e : Rw.slim.End := ⟨(j, β), hβ⟩
  refine ⟨e, rfl, q, ?_, rfl⟩
  have hq' : q ∈ (Rw.slim.endFace e).1 := by
    change q ∈ (Rw.slim.endFace ⟨(j, β), hβ⟩).1
    rw [hF]
    exact mem_connectedComponentIn hq
  rw [Rw.slim.endFace_eq e] at hq'
  exact hq'

/-- A slim end meeting a neighbour face is the registered shared end of that face. -/
theorem exists_shared_of_end_meet_GSF (e : Rw.slim.End) (F : NeighbourFace Rw.zero Rw.cusp)
    {x : W.Carrier} (hxe : x ∈ Rw.slim.endSet e) (hxF : x ∈ neighbourSet F) :
    ∃ σ : Rw.SharedFace, σ.1 = e ∧ Rw.sharedNeighbour σ = F := by
  rcases h : Rw.slim.endKind e with _ | G
  · exfalso
    by_cases hreg : ∃ e', Rw.slim.endKind e' = some F
    · obtain ⟨e', he'⟩ := hreg
      have hee : e ≠ e' := by
        intro hee
        rw [hee, he'] at h
        cases h
      rw [← Rw.junctions.shared_eq e' F he'] at hxF
      exact Set.disjoint_left.1 (Rw.slim.endSet_disjoint_GSAFE hee) hxe hxF
    · push Not at hreg
      exact Set.disjoint_left.1 (Rw.newEnd_disjoint_residualNeighbour_GSF ⟨e, h⟩ ⟨F, hreg⟩)
        hxe hxF
  · have hs : (Rw.slim.endKind e).isSome := by rw [h]; rfl
    refine ⟨⟨e, hs⟩, rfl, ?_⟩
    have hG : Rw.sharedNeighbour ⟨e, hs⟩ = G := by
      change (Rw.slim.endKind e).get hs = G
      simp only [h, Option.get_some]
    rw [hG]
    by_contra hne
    rw [Rw.junctions.shared_eq e G h] at hxe
    exact Set.disjoint_left.1 (Rw.neighbourSet_disjoint_GSAFE hne) hxe hxF

/-- A point of the model boundary image of a zero domain lies on one of its neighbour faces. -/
theorem exists_zeroFace_of_mem_GSF {i : Fin Rw.zero.count} {x : W.Carrier}
    (hx : x ∈ Rw.rowBoundary_GSF (.inl i)) :
    ∃ A : ModelBoundaryFace (Rw.zero.piece i),
      x ∈ neighbourSet (Sum.inl ⟨i, A⟩ : NeighbourFace Rw.zero Rw.cusp) := by
  obtain ⟨q, hq, rfl⟩ := hx
  exact ⟨ActualComponent.of hq, q, mem_connectedComponentIn hq, rfl⟩

/-- A point of the model boundary image of a cusp core lies on its internal face or on its
external torus. -/
theorem cuspFace_cases_GSF {b : Fin n} {x : W.Carrier}
    (hx : x ∈ Rw.rowBoundary_GSF (.inr (.inl b))) :
    x ∈ neighbourSet (Sum.inr ⟨b, Rw.cusp.internalModelFace b, rfl⟩ :
      NeighbourFace Rw.zero Rw.cusp) ∨ x ∈ range (E.torusMap b) := by
  obtain ⟨q, hq, rfl⟩ := hx
  have hqC : q ∈ (ActualComponent.of hq : ModelBoundaryFace (Rw.cusp.piece b)).1 :=
    mem_connectedComponentIn hq
  rcases Rw.cusp.modelFace_cases b (ActualComponent.of hq) with h | h
  · left
    rw [h] at hqC
    exact ⟨q, hqC, rfl⟩
  · right
    rw [h, Rw.cusp.externalModelFace_eq] at hqC
    obtain ⟨t, rfl⟩ := hqC
    exact ⟨t, (Rw.cusp.external_end b t).symm⟩

/-- Faces of a slim piece and of a non-slim row meet only along a shared face. -/
theorem slim_meet_GSF {j : Fin Rw.slim.count} {a : Rw.slim.RowIndex}
    (ha : ∀ j', a ≠ .inr (.inr j')) {x : W.Carrier}
    (hx : x ∈ Rw.rowBoundary_GSF (.inr (.inr j))) (hx' : x ∈ Rw.rowBoundary_GSF a) :
    ∃ σ : Rw.SharedFace, x ∈ Rw.sharedSet σ ∧ Rw.slimIndex σ = .inr (.inr j) ∧
      Rw.neighbourIndex (Rw.sharedNeighbour σ) = a := by
  obtain ⟨e, hej, hxe⟩ := Rw.exists_end_of_mem_slimBoundary_GSF hx
  have hfin : ∀ F : NeighbourFace Rw.zero Rw.cusp, x ∈ neighbourSet F →
      Rw.neighbourIndex F = a → ∃ σ : Rw.SharedFace, x ∈ Rw.sharedSet σ ∧
        Rw.slimIndex σ = .inr (.inr j) ∧ Rw.neighbourIndex (Rw.sharedNeighbour σ) = a := by
    intro F hxF hFa
    obtain ⟨σ, hσe, hσF⟩ := Rw.exists_shared_of_end_meet_GSF e F hxe hxF
    refine ⟨σ, ?_, ?_, ?_⟩
    · change x ∈ Rw.slim.endSet σ.1
      rw [hσe]
      exact hxe
    · change Sum.inr (Sum.inr σ.1.1.1) = _
      rw [hσe, hej]
    · rw [hσF, hFa]
  rcases a with i | b | j'
  · obtain ⟨A, hA⟩ := Rw.exists_zeroFace_of_mem_GSF hx'
    exact hfin _ hA rfl
  · rcases Rw.cuspFace_cases_GSF hx' with h | h
    · exact hfin _ h rfl
    · exact (Set.disjoint_left.1 (W.model.disjoint_interior_boundary (M := W.Carrier))
        (Rw.endSet_subset_interior_GSF e hxe) (Rw.range_torusMap_subset_boundary_GSF b h)).elim
  · exact (ha j' rfl).elim

/-- **G8, rows.** Faces of two different rows meet only along a shared face, the two rows being its
slim owner and its neighbour. -/
theorem rowBoundary_meet_GSF {a a' : Rw.slim.RowIndex} (haa : a ≠ a') {x : W.Carrier}
    (hx : x ∈ Rw.rowBoundary_GSF a) (hx' : x ∈ Rw.rowBoundary_GSF a') :
    ∃ σ : Rw.SharedFace, x ∈ Rw.sharedSet σ ∧
      ((a = Rw.slimIndex σ ∧ a' = Rw.neighbourIndex (Rw.sharedNeighbour σ)) ∨
        (a' = Rw.slimIndex σ ∧ a = Rw.neighbourIndex (Rw.sharedNeighbour σ))) := by
  have hrange : ∀ c : Rw.slim.RowIndex, Rw.rowBoundary_GSF c ⊆ Rw.slim.rowSet c := by
    rintro (i | b | j) _ ⟨q, -, rfl⟩ <;> exact ⟨q, rfl⟩
  rcases a with i | b | j <;> rcases a' with i' | b' | j'
  · have hii : i ≠ i' := fun h => haa (by rw [h])
    exact (Set.disjoint_left.1 (Rw.zero.disjoint hii) (hrange _ hx) (hrange _ hx')).elim
  · exact (Set.disjoint_left.1 (Rw.junctions.zero_cusp_disjoint i b') (hrange _ hx)
      (hrange _ hx')).elim
  · obtain ⟨σ, h1, h2, h3⟩ := Rw.slim_meet_GSF (fun _ h => by cases h) hx' hx
    exact ⟨σ, h1, Or.inr ⟨h2.symm, h3.symm⟩⟩
  · exact (Set.disjoint_left.1 (Rw.junctions.zero_cusp_disjoint i' b) (hrange _ hx')
      (hrange _ hx)).elim
  · have hbb : b ≠ b' := fun h => haa (by rw [h])
    exact (Set.disjoint_left.1 (Rw.cusp.disjoint hbb) (hrange _ hx) (hrange _ hx')).elim
  · obtain ⟨σ, h1, h2, h3⟩ := Rw.slim_meet_GSF (fun _ h => by cases h) hx' hx
    exact ⟨σ, h1, Or.inr ⟨h2.symm, h3.symm⟩⟩
  · obtain ⟨σ, h1, h2, h3⟩ := Rw.slim_meet_GSF (fun _ h => by cases h) hx hx'
    exact ⟨σ, h1, Or.inl ⟨h2.symm, h3.symm⟩⟩
  · obtain ⟨σ, h1, h2, h3⟩ := Rw.slim_meet_GSF (fun _ h => by cases h) hx hx'
    exact ⟨σ, h1, Or.inl ⟨h2.symm, h3.symm⟩⟩
  · have hjj : j ≠ j' := fun h => haa (by rw [h])
    exact (Set.disjoint_left.1 (Rw.slim.disjoint hjj) (hrange _ hx) (hrange _ hx')).elim

end FC39RowsV2

/-! ## G8 for the catalogue -/

section Catalogue

variable (Rw : FC39RowsV2 W E) (V : VertexLayer W) (vlink : VertexModelLink Rw V)

theorem catImage_subset_rowBoundary_GSF (p : Catalogue_GSF V) :
    catImage_GSF p ⊆ Rw.rowBoundary_GSF (vlink.index p.1) := by
  have h := catImage_subset_boundaryImage_GSF p
  have hb : (V.vertex p.1).boundaryImage = Rw.rowBoundary_GSF (vlink.index p.1) := by
    unfold Vertex.boundaryImage FC39RowsV2.rowBoundary_GSF
    rw [vlink.vertex_piece]
  exact hb ▸ h

/-- The catalogue entry of a vertex whose image meets a shared face from the side `b` is the side
entry. -/
theorem eq_sideEntry_GSF {p : Catalogue_GSF V} {σ : Rw.SharedFace} {b : Bool}
    (hp : vlink.index p.1 = Rw.sideIndex_GSF σ b) {x : W.Carrier} (hx : x ∈ catImage_GSF p)
    (hσ : x ∈ Rw.sharedSet σ) :
    p = ⟨sideVertex_GSF Rw V vlink σ b, sideFace_GSF Rw V vlink σ b⟩ := by
  refine catalogue_eq_of_meet_GSF ?_ ⟨x, hx, ?_⟩
  · change p.1 = vlink.index.symm (Rw.sideIndex_GSF σ b)
    rw [← hp, Equiv.symm_apply_apply]
  · change x ∈ (V.vertex (sideVertex_GSF Rw V vlink σ b)).piece.map ''
      (sideFace_GSF Rw V vlink σ b).1
    rw [sideFace_image_GSF]
    exact hσ

/-- **G8.** Two distinct catalogue faces that are not the two sides of one seam are disjoint. -/
theorem catImage_disjoint_GSF {p p' : Catalogue_GSF V} (hne : p ≠ p')
    (hs : ∀ c b, ¬ (p = sEntry_GSF Rw V vlink c b ∧ p' = sEntry_GSF Rw V vlink c (!b)))
    (ht : ∀ c b, ¬ (p = tEntry_GSF Rw V vlink c b ∧ p' = tEntry_GSF Rw V vlink c (!b))) :
    Disjoint (catImage_GSF p) (catImage_GSF p') := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  by_cases hk : p.1 = p'.1
  · exact hne (catalogue_eq_of_meet_GSF hk ⟨x, hx, hx'⟩)
  have haa : vlink.index p.1 ≠ vlink.index p'.1 := fun h => hk (vlink.index.injective h)
  obtain ⟨σ, hσ, hcase⟩ := Rw.rowBoundary_meet_GSF haa
    (catImage_subset_rowBoundary_GSF Rw V vlink p hx)
    (catImage_subset_rowBoundary_GSF Rw V vlink p' hx')
  -- the side `b` of `p` and `!b` of `p'`
  obtain ⟨b, hb, hb'⟩ : ∃ b, vlink.index p.1 = Rw.sideIndex_GSF σ b ∧
      vlink.index p'.1 = Rw.sideIndex_GSF σ (!b) := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨false, h1, h2⟩
    · exact ⟨true, h2, h1⟩
  have hp := eq_sideEntry_GSF Rw V vlink hb hx hσ
  have hp' := eq_sideEntry_GSF Rw V vlink hb' hx' hσ
  rcases hsh : Rw.sharedShape σ with _ | _
  · let c := Rw.sphereEquiv_GSF.symm ⟨σ, hsh⟩
    have hc : (Rw.sphereEquiv_GSF c).1 = σ := by
      change (Rw.sphereEquiv_GSF (Rw.sphereEquiv_GSF.symm ⟨σ, hsh⟩)).1 = σ
      rw [Equiv.apply_symm_apply]
    refine hs c b ⟨?_, ?_⟩
    · rw [hp]
      unfold sEntry_GSF
      rw [hc]
    · rw [hp']
      unfold sEntry_GSF
      rw [hc]
  · let c := Rw.torusEquiv_GSF.symm ⟨σ, hsh⟩
    have hc : (Rw.torusEquiv_GSF c).1 = σ := by
      change (Rw.torusEquiv_GSF (Rw.torusEquiv_GSF.symm ⟨σ, hsh⟩)).1 = σ
      rw [Equiv.apply_symm_apply]
    refine ht c b ⟨?_, ?_⟩
    · rw [hp]
      unfold tEntry_GSF
      rw [hc]
    · rw [hp']
      unfold tEntry_GSF
      rw [hc]

end Catalogue

end GC.GraphManifold.Assembly.FC39P0
