import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlug

/-!
Two actual connected cut pieces meeting across a genuine seam have connected reconstructed
carrier; in particular the physical bounded fibre plug is connected.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.TorusPresentation

theorem connected_of_two_pieces {W : CompactCarrier.{u}} (T : TorusPresentation W)
    (hc : T.components.count = 2) (j : Fin T.pairing.count)
    (hne : T.leftPiece j ≠ T.rightPiece j) : ConnectedSpace W.Carrier := by
  have hleft : (T.leftPiece j).val < 2 := hc ▸ (T.leftPiece j).isLt
  have hright : (T.rightPiece j).val < 2 := hc ▸ (T.rightPiece j).isLt
  have hvals : (T.leftPiece j).val ≠ (T.rightPiece j).val := fun h => hne (Fin.ext h)
  have hindex (i : Fin T.components.count) : i = T.leftPiece j ∨ i = T.rightPiece j := by
    have hi : i.val < 2 := hc ▸ i.isLt
    have hv : i.val = (T.leftPiece j).val ∨ i.val = (T.rightPiece j).val := by omega
    exact hv.imp Fin.ext Fin.ext
  let f : T.components.piece (T.leftPiece j) → W.Carrier := fun x => T.cutMap x.val
  let g : T.components.piece (T.rightPiece j) → W.Carrier := fun x => T.cutMap x.val
  have hmap : Continuous T.cutMap :=
    T.reconstruction.continuous.comp T.pairing.quotientMap.continuous
  have hfc : IsConnected (range f) := by
    let := T.components.connected (T.leftPiece j)
    exact isConnected_range (hmap.comp continuous_subtype_val)
  have hgc : IsConnected (range g) := by
    let := T.components.connected (T.rightPiece j)
    exact isConnected_range (hmap.comp continuous_subtype_val)
  have hcov : range f ∪ range g = univ := by
    apply eq_univ_of_forall
    intro q
    obtain ⟨x, hx⟩ := Quotient.exists_rep (T.reconstruction.symm q)
    have hq : T.cutMap x = q := by
      change T.reconstruction (Quotient.mk'' x) = q
      exact (congrArg T.reconstruction hx).trans (T.reconstruction.apply_symm_apply q)
    have hcover : x ∈ ⋃ i, (T.components.piece i : Set T.cutCarrier.Carrier) := by
      rw [T.components.covers]
      exact mem_univ x
    obtain ⟨i, hi⟩ := mem_iUnion.mp hcover
    rcases hindex i with rfl | rfl
    · exact Or.inl ⟨⟨x, hi⟩, hq⟩
    · exact Or.inr ⟨⟨x, hi⟩, hq⟩
  let x := T.pairing.leftParam j 1
  let y := T.pairing.rightParam j (T.pairing.matching j 1)
  have hx : x.val ∈ T.components.piece (T.leftPiece j) := T.left_owned j x.property
  have hy : y.val ∈ T.components.piece (T.rightPiece j) := T.right_owned j y.property
  have hxy : T.cutMap x.val = T.cutMap y.val := by
    apply congrArg T.reconstruction
    apply Quotient.sound
    have hrel := T.pairing.gluing.rel_of_mem_left x.property
    have he := congrArg Subtype.val (T.pairing.matching_eq j 1)
    exact he ▸ hrel
  have hinter : (range f ∩ range g).Nonempty :=
    ⟨T.cutMap x.val, ⟨⟨x.val, hx⟩, rfl⟩, ⟨⟨y.val, hy⟩, hxy.symm⟩⟩
  exact connectedSpace_iff_univ.mpr (hcov ▸ hfc.union hinter hgc)

end GC.Seifert.TorusPresentation

namespace GC.GraphManifold

theorem exists_connectedFibrePlug :
    ∃ (W : CompactCarrier.{u}) (E : ElementaryPresentation W)
      (j : Fin E.toTorus.pairing.count),
      ConnectedSpace W.Carrier ∧ W.kind = .withBoundary ∧
      E.toTorus.components.count = 2 ∧ E.toTorus.pairing.count = 1 ∧
      E.toTorus.externalCount = 2 ∧ E.IsSplitSeam j true ∧ E.IsLinearSeam j := by
  obtain ⟨W, E, j, hW, hC, hP, hE, h, hlin⟩ := exists_fibrePlug.{u}
  have hne : E.toTorus.leftPiece j ≠ E.toTorus.rightPiece j := by
    simpa [ElementaryPresentation.seamPiece, ElementaryPresentation.hostPiece] using
      E.seamPiece_ne_hostPiece h
  exact ⟨W, E, j, E.toTorus.connected_of_two_pieces hC j hne, hW, hC, hP, hE, h, hlin⟩

end GC.GraphManifold
