import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportSlim74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportEdge74

/-!
# Draft 74, D74-6: faces of the transported rows (bridge for junctions and tubes)

Lane C14-REG-CHAIN (by S-REG-CHAIN), G23 (first file of the "faces / junctions / tubes" half of
`FC39RowsV2.transport74`). Along a carrier diffeomorphism `e` between carriers of the same kind,
the faces of `∂M₂` of the transported rows (`SlimPiecesV2.ResidualFace` of
`S.mapCarrier74 e`) are the original residual faces: `SlimPiecesV2.residualEquiv74`. Their
ambient sets, defining functions, neighbourhoods and owners are the transported ones
(`residualSet_mapCarrier74`, `residualFn_mapCarrier74`, `residualNear_mapCarrier74`,
`residualOwner_mapCarrier74`, `rowSet_mapCarrier74`), `neighbourSet_mapCarrier74`,
`endSet_mapCarrier74`; the regions `M₁`, `M₂`, `M₃`, the boundary `∂M₂` and the union of all
pieces are the `e`-images (`regionM1_mapCarrier74` … `boundaryM2_mapCarrier74`,
`allPieces_mapCarrier74`); the circle tubes and the edge disks / rims / verticals / whole
components are the `e`-images (`CircleBundle.mapCarrier74_tube`,
`EdgeBundle.mapCarrier74_disk` …).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

attribute [local instance] diskChartsBase_FC39P0

variable {W₀ W₁ : CompactCarrier.{u}} {n : ℕ}
  (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)

/-! ## Neighbour faces and ends -/

/-- The ambient image of a neighbour face of the transported rows is the image. -/
theorem neighbourSet_mapCarrier74 {E : BoundaryTori W₀ n} {Z : ZeroDomains W₀}
    {C : CuspCores W₀ E} (F : NeighbourFace Z C) :
    neighbourSet (Z := Z.mapCarrier74 e) (C := C.mapCarrier74 e) F = e '' neighbourSet F := by
  cases F with
  | inl F => exact image_comp e (Z.piece F.1).map F.2.1
  | inr F => exact image_comp e (C.piece F.1).map F.2.1.1

/-- The ends of the original slim models are the ends of the transported ones. -/
def slimEndToMap74 {count : ℕ} {piece : Fin count → PieceEmbedding W₀}
    (model : ∀ j, SlimModel (piece j)) (x : SlimEnd model) :
    SlimEnd (fun j => (model j).mapCarrier74 e) :=
  ⟨x.1, (slimModelIsInterval_mapCarrier74 e (m := model x.1.1)).mpr x.2⟩

/-- The two end conversions are inverse (transported ends back to the original). -/
theorem slimEndOfMap74_toMap {count : ℕ} {piece : Fin count → PieceEmbedding W₀}
    (model : ∀ j, SlimModel (piece j)) (x : SlimEnd model) :
    slimEndOfMap74 e model (slimEndToMap74 e model x) = x :=
  rfl

/-- The two end conversions are inverse (original ends back to the transported). -/
theorem slimEndToMap74_ofMap {count : ℕ} {piece : Fin count → PieceEmbedding W₀}
    (model : ∀ j, SlimModel (piece j)) (x : SlimEnd (fun j => (model j).mapCarrier74 e)) :
    slimEndToMap74 e model (slimEndOfMap74 e model x) = x :=
  rfl

section Slim

variable {E : BoundaryTori W₀ n} {Z : ZeroDomains W₀} {C : CuspCores W₀ E}
  (S : SlimPiecesV2 W₀ Z C)

/-- The end set of a transported end is the image of the end set. -/
theorem endSet_mapCarrier74 (x : S.End) :
    (S.mapCarrier74 e).endSet (slimEndToMap74 e S.model x) = e '' S.endSet x := by
  unfold SlimPiecesV2.endSet
  have h := slimModelEnd_mapCarrier74 e (S.model x.1.1) x.1.2
  exact (congrArg (fun s : Set (S.piece x.1.1).Piece => (e ∘ (S.piece x.1.1).map) '' s) h).trans
    (image_comp e _ _)

/-- The end set of a transported end (stated on the transported end). -/
theorem endSet_mapCarrier74_of (x : (S.mapCarrier74 e).End) :
    (S.mapCarrier74 e).endSet x = e '' S.endSet (slimEndOfMap74 e S.model x) :=
  endSet_mapCarrier74 e S (slimEndOfMap74 e S.model x)

/-- The residual faces of the original rows as residual faces of the transported rows. -/
def SlimPiecesV2.resToMap74 : S.ResidualFace → (S.mapCarrier74 e).ResidualFace
  | .inl ⟨F, h⟩ => .inl ⟨F, fun x hx => h (slimEndOfMap74 e S.model x) hx⟩
  | .inr x => .inr ⟨slimEndToMap74 e S.model x.1, x.2⟩

/-- The residual faces of the transported rows as residual faces of the original rows. -/
def SlimPiecesV2.resOfMap74 : (S.mapCarrier74 e).ResidualFace → S.ResidualFace
  | .inl ⟨F, h⟩ => .inl ⟨F, fun x hx => h (slimEndToMap74 e S.model x) hx⟩
  | .inr x => .inr ⟨slimEndOfMap74 e S.model x.1, x.2⟩

/-- **The faces of `∂M₂` are unchanged by the transport** (an equivalence of the face types). -/
def SlimPiecesV2.residualEquiv74 : S.ResidualFace ≃ (S.mapCarrier74 e).ResidualFace where
  toFun := S.resToMap74 e
  invFun := S.resOfMap74 e
  left_inv F := by
    cases F with
    | inl F => rfl
    | inr x => rfl
  right_inv F := by
    cases F with
    | inl F => rfl
    | inr x => rfl

/-- The ambient set of a transported residual face is the image. -/
theorem residualSet_mapCarrier74 (F : S.ResidualFace) :
    (S.mapCarrier74 e).residualSet (S.resToMap74 e F) = e '' S.residualSet F := by
  cases F with
  | inl F => exact neighbourSet_mapCarrier74 e F.1
  | inr x => exact endSet_mapCarrier74 e S x.1

/-- The defining function of a transported residual face is the pulled-back one. -/
theorem residualFn_mapCarrier74 (F : S.ResidualFace) :
    (S.mapCarrier74 e).residualFn (S.resToMap74 e F) = S.residualFn F ∘ e.symm := by
  rcases F with ⟨F | F, h⟩ | x
  · rfl
  · rfl
  · rfl

/-- The face neighbourhood of a transported residual face is the image. -/
theorem residualNear_mapCarrier74 (F : S.ResidualFace) :
    ((S.mapCarrier74 e).residualNear (S.resToMap74 e F) : Set W₁.Carrier) =
      e '' S.residualNear F := by
  rcases F with ⟨F | F, h⟩ | x
  · rfl
  · rfl
  · rfl

/-- The vertex owner of a transported residual face is the original owner. -/
theorem residualOwner_mapCarrier74 (F : S.ResidualFace) :
    (S.mapCarrier74 e).residualOwner (S.resToMap74 e F) = S.residualOwner F := by
  rcases F with ⟨F | F, h⟩ | x
  · rfl
  · rfl
  · rfl

/-- The image of the row piece of an index is transported. -/
theorem rowSet_mapCarrier74 (i : S.RowIndex) :
    (S.mapCarrier74 e).rowSet i = e '' S.rowSet i := by
  rcases i with i | b | j
  · exact PieceEmbedding.range_mapCarrier74 e (Z.piece i)
  · exact PieceEmbedding.range_mapCarrier74 e (C.piece b)
  · exact PieceEmbedding.range_mapCarrier74 e (S.piece j)

/-- `∂M₂` of the transported rows is the image of `∂M₂`. -/
theorem boundaryM2_mapCarrier74 :
    (S.mapCarrier74 e).boundaryM2 = e '' S.boundaryM2 := by
  rw [SlimPiecesV2.boundaryM2, SlimPiecesV2.boundaryM2, image_iUnion,
    ← (S.residualEquiv74 e).surjective.iUnion_comp]
  exact iUnion_congr fun F => residualSet_mapCarrier74 e S F

/-- The union of the new ends of the transported rows is the image. -/
theorem iUnion_newEnd_mapCarrier74 :
    (⋃ x : (S.mapCarrier74 e).NewEnd, (S.mapCarrier74 e).endSet x.1) =
      e '' ⋃ x : S.NewEnd, S.endSet x.1 := by
  rw [image_iUnion]
  have hs : Surjective fun x : S.NewEnd =>
      (⟨slimEndToMap74 e S.model x.1, x.2⟩ : (S.mapCarrier74 e).NewEnd) :=
    fun y => ⟨⟨slimEndOfMap74 e S.model y.1, y.2⟩, rfl⟩
  rw [← hs.iUnion_comp]
  exact iUnion_congr fun x => endSet_mapCarrier74 e S x.1

end Slim

/-- A point lies in an image iff its `e⁻¹`-preimage lies in the set. -/
theorem mem_image_iff_symm_R74 {e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier}
    {A : Set W₀.Carrier} {y : W₁.Carrier} : y ∈ e '' A ↔ e.symm y ∈ A :=
  ⟨fun ⟨x, hx, hxy⟩ => by rw [← hxy, e.symm_apply_apply]; exact hx,
    fun h => ⟨e.symm y, h, e.apply_symm_apply y⟩⟩

/-! ## Regions -/

section Regions

variable {E : BoundaryTori W₀ n} {Z : ZeroDomains W₀} {C : CuspCores W₀ E}

/-- The union of the transported cusp cores is the image. -/
theorem CuspCores.mapCarrier74_union (C : CuspCores W₀ E) :
    (⋃ b, range ((C.mapCarrier74 e).piece b).map) = e '' ⋃ b, range (C.piece b).map := by
  rw [image_iUnion]
  exact iUnion_congr fun b => (C.mapCarrier74_range e b).1

/-- A carrier diffeomorphism is bijective. -/
theorem carrier_bijective_R74 : Bijective (e : W₀.Carrier → W₁.Carrier) :=
  e.toEquiv.bijective

/-- A carrier diffeomorphism is injective (as a function, for `rw`). -/
theorem carrier_injective_R74 : Injective (e : W₀.Carrier → W₁.Carrier) :=
  e.toEquiv.injective

/-- `M₁` of the transported rows is the image of `M₁`. -/
theorem regionM1_mapCarrier74 (Z : ZeroDomains W₀) (C : CuspCores W₀ E) :
    regionM1 (Z.mapCarrier74 e) (C.mapCarrier74 e) = e '' regionM1 Z C := by
  unfold regionM1
  rw [Z.mapCarrier74_union e, C.mapCarrier74_union e, ← image_union, ← image_interior_R74 e,
    image_compl_eq (carrier_bijective_R74 e)]

/-- `M₂` of the transported rows is the image of `M₂`. -/
theorem regionM2_mapCarrier74 (S : SlimPiecesV2 W₀ Z C) :
    regionM2 (S.mapCarrier74 e) = e '' regionM2 S := by
  unfold regionM2
  rw [regionM1_mapCarrier74, S.mapCarrier74_union e, relInt_image_R74,
    image_sdiff (carrier_injective_R74 e)]

/-- `M₃` of the transported rows is the image of `M₃`. -/
theorem regionM3_mapCarrier74 (hk : W₀.kind = W₁.kind) (S : SlimPiecesV2 W₀ Z C)
    (P : EdgeBundle W₀) :
    regionM3 (S.mapCarrier74 e) (P.mapCarrier74 e hk) = e '' regionM3 S P := by
  unfold regionM3
  rw [regionM2_mapCarrier74, EdgeBundle.mapCarrier74_edgePiece, relInt_image_R74,
    image_sdiff (carrier_injective_R74 e)]

end Regions

/-! ## Circle tubes and edge disks -/

/-- The saturated tube over a set of the base is the image of the saturated tube. -/
theorem CircleBundle.mapCarrier74_tube (R : CircleBundle W₀) (V : Set R.Base) :
    (R.mapCarrier74 e).tube V = e '' R.tube V :=
  e.image_restrictOpens74 R.domain (fun y => R.proj y ∈ V)

/-- The whole disk over `c` is transported. -/
theorem EdgeBundle.mapCarrier74_disk (hk : W₀.kind = W₁.kind) (P : EdgeBundle W₀) (c : P.Base) :
    (P.mapCarrier74 e hk).disk c = e '' P.disk c :=
  e.image_restrictOpens74 P.source (fun y => P.proj y = c ∧ P.height y ≤ P.level)

/-- The boundary circle of the disk over `c` is transported. -/
theorem EdgeBundle.mapCarrier74_rim (hk : W₀.kind = W₁.kind) (P : EdgeBundle W₀) (c : P.Base) :
    (P.mapCarrier74 e hk).rim c = e '' P.rim c :=
  e.image_restrictOpens74 P.source (fun y => P.proj y = c ∧ P.height y = P.level)

/-- The vertical face is transported. -/
theorem EdgeBundle.mapCarrier74_vertical (hk : W₀.kind = W₁.kind) (P : EdgeBundle W₀) :
    (P.mapCarrier74 e hk).vertical = e '' P.vertical :=
  e.image_restrictOpens74 P.source (fun y => P.proj y ∈ P.cbase ∧ P.height y = P.level)

/-- The whole inverse image of a base component below the level is transported. -/
theorem EdgeBundle.mapCarrier74_wholeComponent (hk : W₀.kind = W₁.kind) (P : EdgeBundle W₀)
    (C : P.EdgeBaseComponent) :
    (P.mapCarrier74 e hk).wholeComponent C = e '' P.wholeComponent C :=
  e.image_restrictOpens74 P.source (fun y => P.proj y ∈ C.1 ∧ P.height y ≤ P.level)

/-- The vertical face of a base component is transported. -/
theorem EdgeBundle.mapCarrier74_wholeVertical (hk : W₀.kind = W₁.kind) (P : EdgeBundle W₀)
    (C : P.EdgeBaseComponent) :
    (P.mapCarrier74 e hk).wholeVertical C = e '' P.wholeVertical C :=
  e.image_restrictOpens74 P.source (fun y => P.proj y ∈ C.1 ∧ P.height y = P.level)

/-- The union of the horizontal disks is transported. -/
theorem EdgeBundle.mapCarrier74_horizontalDisks (hk : W₀.kind = W₁.kind) (P : EdgeBundle W₀) :
    (P.mapCarrier74 e hk).horizontalDisks = e '' P.horizontalDisks := by
  rw [EdgeBundle.horizontalDisks, EdgeBundle.horizontalDisks, image_iUnion]
  exact iUnion_congr fun x => EdgeBundle.mapCarrier74_disk e hk P x.1

/-- **The labels of the circle-base faces are unchanged by the transport** (an equivalence). -/
def labelEquiv74 (hk : W₀.kind = W₁.kind) {E : BoundaryTori W₀ n} {Z : ZeroDomains W₀}
    {C : CuspCores W₀ E} (S : SlimPiecesV2 W₀ Z C) (P : EdgeBundle W₀) :
    CircleFaceLabel S.ResidualFace P.EdgeBaseComponent ≃
      CircleFaceLabel (S.mapCarrier74 e).ResidualFace (P.mapCarrier74 e hk).EdgeBaseComponent where
  toFun := fun
    | .horizontal F => .horizontal (S.resToMap74 e F)
    | .vertical c => .vertical c
  invFun := fun
    | .horizontal F => .horizontal (S.resOfMap74 e F)
    | .vertical c => .vertical c
  left_inv f := by
    cases f with
    | horizontal F => exact congrArg CircleFaceLabel.horizontal ((S.residualEquiv74 e).left_inv F)
    | vertical c => rfl
  right_inv f := by
    cases f with
    | horizontal F => exact congrArg CircleFaceLabel.horizontal ((S.residualEquiv74 e).right_inv F)
    | vertical c => rfl

/-- The ambient set of a transported circle-base face is the image. -/
theorem circleFaceSet_mapCarrier74 (hk : W₀.kind = W₁.kind) {E : BoundaryTori W₀ n}
    {Z : ZeroDomains W₀} {C : CuspCores W₀ E} (S : SlimPiecesV2 W₀ Z C) (P : EdgeBundle W₀)
    (f : CircleFaceLabel S.ResidualFace P.EdgeBaseComponent) :
    circleFaceSet (S.mapCarrier74 e) (P.mapCarrier74 e hk) (labelEquiv74 e hk S P f) =
      e '' circleFaceSet S P f := by
  cases f with
  | horizontal F => exact residualSet_mapCarrier74 e S F
  | vertical c => exact EdgeBundle.mapCarrier74_wholeVertical e hk P c

/-- **All pieces of the transported decomposition are the images of the original pieces.** -/
theorem allPieces_mapCarrier74 (hk : W₀.kind = W₁.kind) {E : BoundaryTori W₀ n}
    {Z : ZeroDomains W₀} {C : CuspCores W₀ E} (S : SlimPiecesV2 W₀ Z C) (P : EdgeBundle W₀)
    (R : CircleBundle W₀) (a : S.RowIndex ⊕ Bool) :
    allPieces (S.mapCarrier74 e) (P.mapCarrier74 e hk) (R.mapCarrier74 e) a =
      e '' allPieces S P R a := by
  rcases a with i | b
  · exact rowSet_mapCarrier74 e S i
  · cases b
    · exact R.mapCarrier74_region e
    · exact EdgeBundle.mapCarrier74_edgePiece e hk P

end GC.GraphManifold.Assembly.FC39P0
