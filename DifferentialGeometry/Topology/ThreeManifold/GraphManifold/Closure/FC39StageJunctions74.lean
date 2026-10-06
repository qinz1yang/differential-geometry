import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageGeometryH74

/-!
# Draft 74, package J0 (part 1): `JunctionsV2` from the stage geometry `A`, the cut `D`, the cut
geometry `H`

Lane S-JUNCTIONS (suffix `_JN74`). `junctions_of_actual_decomposition74 A D H` builds the
`JunctionsV2` of the rows `(A.zero, A.cusp, H.rows.slim, H.rows.edge, H.rows.circle)`:

* DERIVED from the cut facts (FDC04 and the relative interiors of §5.7):
  `cover` (`W = Z ∪ C ∪ slimSet ∪ M₂` and `M₂ ⊆ M^edge ∪ M₃`), `interiors_disjoint` (the slim set
  lies in `M₁`, the edge piece in `M₂`, the region is `M₃ ⊆ M₂ ∖ int_{M₂} M^edge`; `int A ⊆ int_S A`
  for `A ⊆ S`), `region_eq` (`M₃` of the rows is the cut's `M₃`, the circle region by saturation);
* TRANSPORTED along `S.union = slimSet`, `P.edgePiece = M^edge`, `R.region = M₃`,
  `regionM2 S = M₂`: the face facts, the rim facts and the shared-end classification of `H`.
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

/-! ## Relative interiors -/

theorem relInt_subset_JN74 {X : Type*} [TopologicalSpace X] {A S : Set X} : relInt A S ⊆ S := by
  rintro _ ⟨x, hx, rfl⟩
  exact interior_subset (s := Subtype.val ⁻¹' S) hx

theorem interior_subset_relInt_JN74 {X : Type*} [TopologicalSpace X] {A S : Set X}
    (h : S ⊆ A) : interior S ⊆ relInt A S := by
  intro x hx
  refine ⟨⟨x, h (interior_subset hx)⟩, ?_, rfl⟩
  exact mem_interior.2 ⟨Subtype.val ⁻¹' interior S,
    fun y (hy : (y : X) ∈ interior S) => interior_subset (s := S) hy,
    isOpen_interior.preimage continuous_subtype_val, hx⟩

/-! ## The slim pieces fill the slim set; the rows' regions are the cut's -/

namespace SlimCutPieces74

variable {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A} (S : SlimCutPieces74 A D)

/-- The union of the slim pieces is `f₃⁻¹(D₃)`. -/
theorem union_eq : S.pieces.union = D.slimSet := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.1 hx
    obtain ⟨h, hmem⟩ := (S.piece_range j ▸ hj : x ∈ _)
    exact ⟨h, (S.componentEquiv j).subset hmem⟩
  · rintro ⟨h, hd⟩
    refine mem_iUnion.2 ⟨S.componentEquiv.symm (ActualComponent.of hd), ?_⟩
    rw [S.piece_range]
    refine ⟨h, ?_⟩
    rw [S.componentEquiv.apply_symm_apply]
    exact mem_connectedComponentIn hd

end SlimCutPieces74

namespace StageCutRows74

variable {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A} (R : StageCutRows74 A D)

theorem edgePiece_eq : R.edge.edgePiece = D.edgeSet :=
  D.edgePiece_edgeBundle74 R.edgeFacts

theorem regionM2_eq : regionM2 R.slimPieces = D.M₂ := by
  change regionM1 A.zero A.cusp \ relInt (regionM1 A.zero A.cusp) R.slimPieces.union = _
  rw [R.slim.union_eq]
  rfl

theorem regionM3_eq : regionM3 R.slimPieces R.edge = D.M₃ := by
  change regionM2 R.slimPieces \ relInt (regionM2 R.slimPieces) R.edge.edgePiece = _
  rw [R.regionM2_eq, R.edgePiece_eq]
  rfl

end StageCutRows74

/-! ## The pieces of the decomposition and their position in `M₁ ⊇ M₂ ⊇ M₃` -/

section Pieces

variable {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A} (H : StageCutGeometry74 A D)

theorem slimRange_subset_slimSet_JN74 (j : Fin H.rows.slimPieces.count) :
    range (H.rows.slimPieces.piece j).map ⊆ D.slimSet := by
  rw [← H.rows.slim.union_eq]
  exact subset_iUnion (fun j => range (H.rows.slimPieces.piece j).map) j

theorem edgePiece_subset_M₂_JN74 : H.rows.edge.edgePiece ⊆ D.M₂ := by
  rw [H.rows.edgePiece_eq]
  exact H.cover.edgeSet_subset_M₂

theorem region_eq_M₃_JN74 : H.rows.circle.region = D.M₃ :=
  D.region_circleBundle74_eq_M₃ H.rows.circleFacts

theorem region_subset_M₂_JN74 : H.rows.circle.region ⊆ D.M₂ := by
  rw [region_eq_M₃_JN74 H]
  exact D.M₃_subset_M₂

/-- A set inside `M₁` has interior-disjoint position with the zero domain `i`. -/
theorem disjoint_zero_interior_JN74 (i : Fin A.zero.count) {Y : Set W.Carrier}
    (hY : Y ⊆ regionM1 A.zero A.cusp) : Disjoint (interior (range (A.zero.piece i).map)) Y := by
  refine Set.disjoint_left.2 fun x hx hxY => ?_
  refine hY hxY (interior_mono ?_ hx)
  exact (subset_iUnion (fun i => range (A.zero.piece i).map) i).trans subset_union_left

/-- A set inside `M₁` has interior-disjoint position with the cusp core `b`. -/
theorem disjoint_cusp_interior_JN74 (b : Fin n) {Y : Set W.Carrier}
    (hY : Y ⊆ regionM1 A.zero A.cusp) : Disjoint (interior (range (A.cusp.piece b).map)) Y := by
  refine Set.disjoint_left.2 fun x hx hxY => ?_
  refine hY hxY (interior_mono ?_ hx)
  exact (subset_iUnion (fun b => range (A.cusp.piece b).map) b).trans subset_union_right

/-- A set inside `M₂` is disjoint from the interior of the slim piece `j` (relative interior in
`M₁` of the slim set). -/
theorem disjoint_slim_interior_JN74 (j : Fin H.rows.slimPieces.count) {Y : Set W.Carrier}
    (hY : Y ⊆ D.M₂) : Disjoint (interior (range (H.rows.slimPieces.piece j).map)) Y := by
  refine Set.disjoint_left.2 fun x hx hxY => (hY hxY).2 ?_
  exact interior_subset_relInt_JN74 H.cover.slimSet_subset_M₁
    (interior_mono (slimRange_subset_slimSet_JN74 H j) hx)

/-- A set inside `M₃` is disjoint from the interior of the edge piece (relative interior in `M₂`
of the edge piece). -/
theorem disjoint_edge_interior_JN74 {Y : Set W.Carrier} (hY : Y ⊆ D.M₃) :
    Disjoint (interior H.rows.edge.edgePiece) Y := by
  refine Set.disjoint_left.2 fun x hx hxY => (hY hxY).2 ?_
  rw [H.rows.edgePiece_eq] at hx
  exact interior_subset_relInt_JN74 H.cover.edgeSet_subset_M₂ hx

end Pieces

/-! ## The junctions -/

section Junctions

variable {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A} (H : StageCutGeometry74 A D)

/-- **FDC04**: the pieces of the decomposition cover `W`. -/
theorem cover_JN74 : (⋃ a, allPieces H.rows.slimPieces H.rows.edge H.rows.circle a) = univ := by
  refine eq_univ_of_univ_subset fun x _ => ?_
  have hx : x ∈ (((⋃ i, range (A.zero.piece i).map) ∪ ⋃ b, range (A.cusp.piece b).map) ∪
      D.slimSet) ∪ D.M₂ := by
    rw [H.cover.cover]
    trivial
  rcases hx with ((hz | hc) | hs) | hm
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hz
    exact mem_iUnion.2 ⟨Sum.inl (Sum.inl i), hi⟩
  · obtain ⟨b, hb⟩ := mem_iUnion.1 hc
    exact mem_iUnion.2 ⟨Sum.inl (Sum.inr (Sum.inl b)), hb⟩
  · rw [← H.rows.slim.union_eq] at hs
    obtain ⟨j, hj⟩ := mem_iUnion.1 hs
    exact mem_iUnion.2 ⟨Sum.inl (Sum.inr (Sum.inr j)), hj⟩
  · by_cases hrel : x ∈ relInt D.M₂ D.edgeSet
    · refine mem_iUnion.2 ⟨Sum.inr true, ?_⟩
      change x ∈ H.rows.edge.edgePiece
      rw [H.rows.edgePiece_eq]
      exact relInt_subset_JN74 hrel
    · refine mem_iUnion.2 ⟨Sum.inr false, ?_⟩
      change x ∈ H.rows.circle.region
      rw [region_eq_M₃_JN74 H]
      exact ⟨hm, hrel⟩

/-- **FDC04**: the interiors of distinct pieces are disjoint. -/
theorem interiors_disjoint_JN74 : Pairwise fun a a' =>
    Disjoint (interior (allPieces H.rows.slimPieces H.rows.edge H.rows.circle a))
      (interior (allPieces H.rows.slimPieces H.rows.edge H.rows.circle a')) := by
  have hSlM1 : ∀ j, range (H.rows.slimPieces.piece j).map ⊆ regionM1 A.zero A.cusp :=
    fun j => (slimRange_subset_slimSet_JN74 H j).trans H.cover.slimSet_subset_M₁
  have hEdM2 := edgePiece_subset_M₂_JN74 H
  have hReM2 := region_subset_M₂_JN74 H
  have hM2M1 : D.M₂ ⊆ regionM1 A.zero A.cusp := D.M₂_subset_M₁
  have hReM3 : H.rows.circle.region ⊆ D.M₃ := (region_eq_M₃_JN74 H).subset
  intro a a' hne
  rcases a with ((i | b | j) | c) <;> rcases a' with ((i' | b' | j') | c')
  · exact (A.zero.disjoint (fun h => hne (congrArg (fun k => Sum.inl (Sum.inl k)) h))).mono
      interior_subset interior_subset
  · exact (H.cover.zero_cusp_disjoint i b').mono interior_subset interior_subset
  · exact (disjoint_zero_interior_JN74 i (hSlM1 j')).mono_right interior_subset
  · rcases c' with _ | _
    · exact (disjoint_zero_interior_JN74 i (hReM2.trans hM2M1)).mono_right interior_subset
    · exact (disjoint_zero_interior_JN74 i (hEdM2.trans hM2M1)).mono_right interior_subset
  · exact ((H.cover.zero_cusp_disjoint i' b).mono interior_subset interior_subset).symm
  · exact (A.cusp.disjoint (fun h => hne (congrArg (fun k => Sum.inl (Sum.inr (Sum.inl k)))
      h))).mono interior_subset interior_subset
  · exact (disjoint_cusp_interior_JN74 b (hSlM1 j')).mono_right interior_subset
  · rcases c' with _ | _
    · exact (disjoint_cusp_interior_JN74 b (hReM2.trans hM2M1)).mono_right interior_subset
    · exact (disjoint_cusp_interior_JN74 b (hEdM2.trans hM2M1)).mono_right interior_subset
  · exact ((disjoint_zero_interior_JN74 i' (hSlM1 j)).mono_right interior_subset).symm
  · exact ((disjoint_cusp_interior_JN74 b' (hSlM1 j)).mono_right interior_subset).symm
  · exact (H.rows.slimPieces.disjoint (fun h => hne (congrArg (fun k =>
      Sum.inl (Sum.inr (Sum.inr k))) h))).mono interior_subset interior_subset
  · rcases c' with _ | _
    · exact (disjoint_slim_interior_JN74 H j hReM2).mono_right interior_subset
    · exact (disjoint_slim_interior_JN74 H j hEdM2).mono_right interior_subset
  · rcases c with _ | _
    · exact ((disjoint_zero_interior_JN74 i' (hReM2.trans hM2M1)).mono_right
        interior_subset).symm
    · exact ((disjoint_zero_interior_JN74 i' (hEdM2.trans hM2M1)).mono_right
        interior_subset).symm
  · rcases c with _ | _
    · exact ((disjoint_cusp_interior_JN74 b' (hReM2.trans hM2M1)).mono_right
        interior_subset).symm
    · exact ((disjoint_cusp_interior_JN74 b' (hEdM2.trans hM2M1)).mono_right
        interior_subset).symm
  · rcases c with _ | _
    · exact ((disjoint_slim_interior_JN74 H j' hReM2).mono_right interior_subset).symm
    · exact ((disjoint_slim_interior_JN74 H j' hEdM2).mono_right interior_subset).symm
  · rcases c with _ | _ <;> rcases c' with _ | _
    · exact (hne rfl).elim
    · exact ((disjoint_edge_interior_JN74 H hReM3).mono_right interior_subset).symm
    · exact (disjoint_edge_interior_JN74 H hReM3).mono_right interior_subset
    · exact (hne rfl).elim

/-- **J0 (`junctions_of_actual_decomposition74`)**: the `JunctionsV2` of the rows of the cut. -/
def junctions_of_actual_decomposition74 (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A)
    (H : StageCutGeometry74 A D) :
    JunctionsV2 W E A.zero A.cusp H.rows.slimPieces H.rows.edge H.rows.circle where
  cover := cover_JN74 H
  interiors_disjoint := interiors_disjoint_JN74 H
  shared_eq := H.rows.slim.shared_eq
  zero_cusp_disjoint := H.cover.zero_cusp_disjoint
  horizontal := H.faces.horizontal
  horizontal_disk := H.faces.horizontal_disk
  edge_faces := fun F => by
    rw [H.rows.edgePiece_eq]
    exact H.faces.edge_faces F
  rimBase := H.rims.rimBase
  rimBase_smooth := H.rims.rimBase_smooth
  rim_fibre := H.rims.rim_fibre
  edge_region := by
    rw [H.rows.edgePiece_eq, region_eq_M₃_JN74 H]
    exact H.rims.edge_region
  local_faces := H.rims.local_faces
  region_eq := by
    rw [H.rows.regionM3_eq, region_eq_M₃_JN74 H]
  frontier_M2 := by
    rw [H.rows.regionM2_eq]
    exact H.faces.frontier_M2
  region_boundary := by
    rw [region_eq_M₃_JN74 H]
    exact H.faces.region_boundary
  slim_M2 := by
    rw [H.rows.slim.union_eq, H.rows.regionM2_eq]
    exact H.faces.slim_M2
  shared_removed := fun σ => by
    rw [H.rows.slim.union_eq]
    exact H.faces.shared_removed σ

end Junctions

end GC.GraphManifold.Assembly.FC39P0
