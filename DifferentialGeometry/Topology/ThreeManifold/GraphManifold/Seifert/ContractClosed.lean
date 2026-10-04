import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveAbsorb
import DifferentialGeometry.Topology.Manifold.ConnectedInterior

/-!
# Seam connectivity and closed contraction

The seam graph discharges the connectivity condition of contraction. Piece interiors are
connected and dense in the pieces, including their external boundary points.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)
  (S : Finset (Fin T.components.count))

theorem hext_of_externalCount_eq_zero (h : T.externalCount = 0) :
    ∀ i, T.externalPiece i ∉ S := by
  intro i
  exact Fin.elim0 (i.cast h)

theorem kind_eq_withBoundary_of_pairing_count_pos (h : 0 < T.pairing.count) :
    T.cutCarrier.kind = .withBoundary := T.cutCarrier_kind_of_pos h

def SeamAdjacent (a b : Fin T.components.count) : Prop :=
  a ∈ S ∧ b ∈ S ∧ ∃ k,
    (T.leftPiece k = a ∧ T.rightPiece k = b) ∨
      (T.leftPiece k = b ∧ T.rightPiece k = a)

def SeamConnected : Prop :=
  S.Nonempty ∧ ∀ a ∈ S, ∀ b ∈ S, Relation.ReflTransGen (T.SeamAdjacent S) a b

private theorem piece_subset_closure_pieceInterior (i : Fin T.components.count) :
    (T.components.piece i : Set T.cutCarrier.Carrier) ⊆
      closure (T.cutCarrier.pieceInterior (T.components.piece i) :
        Set T.cutCarrier.Carrier) := by
  have h := Manifold.dense_manifold_interior (I := T.cutCarrier.model)
    (M := T.cutCarrier.Carrier)
  have hd := h.open_subset_closure_inter (T.components.piece i).isOpen
  exact hd

private theorem isConnected_pieceImage_diff_crossing (i : Fin T.components.count) (hi : i ∈ S) :
    IsConnected (T.cutMap '' (T.components.piece i : Set T.cutCarrier.Carrier) \
      T.crossingSurface S) := by
  have hc : Continuous T.cutMap :=
    T.reconstruction.continuous.comp T.pairing.quotientMap.continuous
  have hU := (isConnected_iff_connectedSpace.mpr
    (T.components.interior_connected i)).image T.cutMap hc.continuousOn
  refine hU.subset_closure ?_ ?_
  · intro y hy
    exact ⟨Set.image_mono (fun x hx => hx.1) hy,
      (T.cutMap_pieceInterior_subset_region S hi hy).2⟩
  · exact Set.Subset.trans Set.sdiff_subset
      ((Set.image_mono (T.piece_subset_closure_pieceInterior i)).trans
        (image_closure_subset_closure_image hc))

private theorem seamTorus_not_mem_crossing_of_internal {k : Fin T.pairing.count}
    (hl : T.leftPiece k ∈ S) (hr : T.rightPiece k ∈ S) (t : Torus) :
    T.seamTorus k t ∉ T.crossingSurface S := by
  intro h
  obtain ⟨j, hj, hsurf⟩ := Set.mem_iUnion₂.mp h
  have hne : j ≠ k := by
    intro heq
    subst j
    rcases hj with ⟨hj, hn⟩ | ⟨hj, hn⟩
    · exact hn hr
    · exact hn hl
  exact (T.seam_disjoint hne).le_bot
    ⟨T.seamSurface_subset_seamCollar j hsurf,
      T.seamSurface_subset_seamCollar k ⟨t, rfl⟩⟩

private theorem pieceImage_inter_nonempty_of_seamAdjacent
    {a b : Fin T.components.count} (h : T.SeamAdjacent S a b) :
    ((T.cutMap '' (T.components.piece a : Set T.cutCarrier.Carrier) \ T.crossingSurface S) ∩
      (T.cutMap '' (T.components.piece b : Set T.cutCarrier.Carrier) \
        T.crossingSurface S)).Nonempty := by
  obtain ⟨ha, hb, k, hleft | hright⟩ := h
  · obtain ⟨rfl, rfl⟩ := hleft
    have hn := T.seamTorus_not_mem_crossing_of_internal S ha hb (1 : Torus)
    refine ⟨T.seamTorus k 1, ⟨?_, hn⟩, ⟨?_, hn⟩⟩
    · exact ⟨(T.pairing.leftParam k 1).val,
        T.left_owned k (T.pairing.leftParam k 1).property, (T.seamTorus_eq_cutMap k 1).symm⟩
    · refine ⟨(T.pairing.rightParam k (T.pairing.matching k 1)).val,
        T.right_owned k (T.pairing.rightParam k (T.pairing.matching k 1)).property, ?_⟩
      rw [← T.seamTorus_eq_cutMap_right]
  · obtain ⟨rfl, rfl⟩ := hright
    have hn := T.seamTorus_not_mem_crossing_of_internal S hb ha (1 : Torus)
    refine ⟨T.seamTorus k 1, ⟨?_, hn⟩, ⟨?_, hn⟩⟩
    · refine ⟨(T.pairing.rightParam k (T.pairing.matching k 1)).val,
        T.right_owned k (T.pairing.rightParam k (T.pairing.matching k 1)).property, ?_⟩
      rw [← T.seamTorus_eq_cutMap_right]
    · exact ⟨(T.pairing.leftParam k 1).val,
        T.left_owned k (T.pairing.leftParam k 1).property, (T.seamTorus_eq_cutMap k 1).symm⟩

theorem isConnected_of_seamConnected (hS : T.SeamConnected S) :
    IsConnected (Set.range (T.restrictMap S) \ T.crossingSurface S) := by
  have heq : Set.range (T.restrictMap S) \ T.crossingSurface S =
      ⋃ i ∈ (S : Set (Fin T.components.count)),
        T.cutMap '' (T.components.piece i : Set T.cutCarrier.Carrier) \
          T.crossingSurface S := by
    ext y
    constructor
    · rintro ⟨hy, hn⟩
      rw [T.range_restrictMap] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨i, hi, hxi⟩ := (T.mem_subPiece S).mp hx
      exact Set.mem_iUnion₂.mpr ⟨i, hi, ⟨⟨x, hxi, rfl⟩, hn⟩⟩
    · intro hy
      obtain ⟨i, hi, ⟨x, hx, rfl⟩, hn⟩ := Set.mem_iUnion₂.mp hy
      exact ⟨T.cutMap_mem_range_of_mem S (T.piece_subset_subPiece S hi hx), hn⟩
  rw [heq]
  refine IsConnected.biUnion_of_reflTransGen hS.1
    (fun i hi => T.isConnected_pieceImage_diff_crossing S i hi) ?_
  intro a ha b hb
  exact Relation.ReflTransGen.mono
    (fun x y hxy => ⟨T.pieceImage_inter_nonempty_of_seamAdjacent S hxy, hxy.1⟩)
    a b (hS.2 a ha b hb)

def contractOfSeamConnected (h0 : T.externalCount = 0) (hp : 0 < T.pairing.count)
    (hS : T.SeamConnected S) : TorusPresentation W :=
  T.contract S (T.hext_of_externalCount_eq_zero S h0)
    (T.kind_eq_withBoundary_of_pairing_count_pos hp) (T.isConnected_of_seamConnected S hS)

theorem contractOfSeamConnected_components_count (h0 : T.externalCount = 0)
    (hp : 0 < T.pairing.count) (hS : T.SeamConnected S) :
    (T.contractOfSeamConnected S h0 hp hS).components.count =
      T.components.count - S.card + 1 :=
  T.contract_components_count S (T.hext_of_externalCount_eq_zero S h0)
    (T.kind_eq_withBoundary_of_pairing_count_pos hp) (T.isConnected_of_seamConnected S hS)

theorem contractOfSeamConnected_pairing_count (h0 : T.externalCount = 0)
    (hp : 0 < T.pairing.count) (hS : T.SeamConnected S) :
    (T.contractOfSeamConnected S h0 hp hS).pairing.count = T.pairing.count -
      (Finset.univ.filter fun k => T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S).card :=
  T.contract_pairing_count S (T.hext_of_externalCount_eq_zero S h0)
    (T.kind_eq_withBoundary_of_pairing_count_pos hp) (T.isConnected_of_seamConnected S hS)

end GC.Seifert.TorusPresentation
