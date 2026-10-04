import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Gluing

/-!
# Restricting a torus presentation to a set of pieces

Chapter 6, K22a (sub-presentations, first half of K22). For a torus presentation `T` of `W` and
a finset `S` of pieces, `subPiece S` is the union of the pieces in `S`, open and closed in the cut
carrier, so `subCarrier S` is a compact carrier with the restricted charts and orientation, as
`componentCarrier` is for one piece. Its components are the pieces of `S`, indexed by
`Fin S.card` along `S.orderIsoOfFin` (`subComponents`, `subIndex`, `subIndexOf`).

A seam is kept (`KeptSeam`) when both of its sides lie in `S`. `restrictPairing S` pairs the kept
seams in `subCarrier S` with the same blocks, parameters, matchings and collars (`subCollar`
corestricts a side collar to `subPiece S`); its boundary reversal is that of `T`, because the
corestriction changes neither derivatives nor orientations (`reversesBoundaryOrientation_sub`).
The remaining sides of pieces of `S` (`RestrictSide`: external sides on `S` and the `S`-side of
every crossing seam) give `restrictBoundaryTori S`. They exhaust the boundary together with the
kept blocks (`subCarrier_boundary`), are disjoint from them (`restrict_external_disjoint`), and are
owned through `restrictLeftPiece`, `restrictRightPiece`, `restrictExternalPiece`. Counts: `S.card`
pieces, the kept seams (`restrictPairing_count_eq_card_filter`), and the external tori on `S` plus
the crossing seams (`card_restrictSide`).

`cutMap` descends to `restrictMap S` on the quotient by the kept seams, a closed embedding into
`W` (`isClosedEmbedding_restrictMap`, `restrictHomeomorph`) onto the image of the pieces of `S`
(`range_restrictMap`), sending kept collars to the seams of `T` (`restrictMap_leftCollar`). If `j`
is the only crossing seam and its left side is in `S`, then `j` separates
(`isSeparating_of_restrict`), the interior of the image is the image minus the seam torus
(`interior_range_restrictMap`), and when this set is preconnected it is K09's `leftSide j`, so the
image with the seam collar is `leftRegion j` (`range_union_seamCollar_eq_leftRegion`).

With no kept seam the restriction is a torus presentation of `subCarrier S` itself
(`restrictOfNoKeptSeam`, generalizing `ofPiece`). In general the reconstructed space is the
quotient by the kept seams, not `subCarrier S`; a compact carrier structure on it (charts of the
cut carrier off the kept blocks, signed seam collars on them) is the part of K22 not done here.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

def preimageValHomeomorph {X : Type*} [TopologicalSpace X] (U : Set X) (A : Set X)
    (h : A ⊆ U) : (Subtype.val ⁻¹' A : Set U) ≃ₜ A where
  toFun x := ⟨x.1.1, x.2⟩
  invFun y := ⟨⟨y.1, h y.2⟩, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

@[simp]
theorem preimageValHomeomorph_apply {X : Type*} [TopologicalSpace X] (U : Set X) (A : Set X)
    (h : A ⊆ U) (x : (Subtype.val ⁻¹' A : Set U)) :
    (preimageValHomeomorph U A h x : X) = x.1.1 := rfl

@[simp]
theorem preimageValHomeomorph_symm_apply {X : Type*} [TopologicalSpace X] (U : Set X)
    (A : Set X) (h : A ⊆ U) (y : A) :
    ((preimageValHomeomorph U A h).symm y : X) = y.1 := rfl

namespace TorusPresentation
variable {W : CompactCarrier.{u}} (T : TorusPresentation W)
  (S : Finset (Fin T.components.count))

def subPiece : TopologicalSpace.Opens T.cutCarrier.Carrier :=
  ⟨⋃ i ∈ S, (T.components.piece i : Set T.cutCarrier.Carrier),
    isOpen_biUnion fun i _ => (T.components.piece i).isOpen⟩

theorem mem_subPiece {x : T.cutCarrier.Carrier} :
    x ∈ T.subPiece S ↔ ∃ i ∈ S, x ∈ T.components.piece i := by
  change x ∈ ⋃ i ∈ S, (T.components.piece i : Set T.cutCarrier.Carrier) ↔ _
  simp only [Set.mem_iUnion, exists_prop, SetLike.mem_coe]

theorem piece_subset_subPiece {i : Fin T.components.count} (hi : i ∈ S) :
    (T.components.piece i : Set T.cutCarrier.Carrier) ⊆ T.subPiece S :=
  fun _ hx => (T.mem_subPiece S).mpr ⟨i, hi, hx⟩

theorem mem_of_mem_subPiece {x : T.cutCarrier.Carrier} (hx : x ∈ T.subPiece S)
    {i : Fin T.components.count} (hi : x ∈ T.components.piece i) : i ∈ S := by
  obtain ⟨i', hi', hx'⟩ := (T.mem_subPiece S).mp hx
  by_cases h : i = i'
  · exact h ▸ hi'
  · exact ((T.components.disjoint h).le_bot ⟨hi, hx'⟩).elim

theorem isClosed_subPiece : IsClosed (T.subPiece S : Set T.cutCarrier.Carrier) :=
  isClosed_biUnion_finset fun i _ => T.components.closed i

def subCarrier : CompactCarrier.{u} where
  kind := T.cutCarrier.kind
  Carrier := T.subPiece S
  compact := isCompact_iff_compactSpace.mp (T.isClosed_subPiece S).isCompact
  orientation := T.cutCarrier.orientation.restrictOpen (T.subPiece S)

def subIndex (j : Fin S.card) : Fin T.components.count := (S.orderIsoOfFin rfl j).val

theorem subIndex_mem (j : Fin S.card) : T.subIndex S j ∈ S := (S.orderIsoOfFin rfl j).property

def subIndexOf {i : Fin T.components.count} (hi : i ∈ S) : Fin S.card :=
  (S.orderIsoOfFin rfl).symm ⟨i, hi⟩

@[simp]
theorem subIndex_subIndexOf {i : Fin T.components.count} (hi : i ∈ S) :
    T.subIndex S (T.subIndexOf S hi) = i := by
  simp [subIndex, subIndexOf]

@[simp]
theorem subIndexOf_subIndex (j : Fin S.card) : T.subIndexOf S (T.subIndex_mem S j) = j :=
  (S.orderIsoOfFin rfl).symm_apply_apply j

theorem subIndex_injective : Function.Injective (T.subIndex S) := fun _ _ h =>
  (S.orderIsoOfFin rfl).injective (Subtype.ext h)

def subPieceOf (j : Fin S.card) : TopologicalSpace.Opens (T.subCarrier S).Carrier :=
  ⟨Subtype.val ⁻¹' (T.components.piece (T.subIndex S j) : Set T.cutCarrier.Carrier),
    (T.components.piece _).isOpen.preimage continuous_subtype_val⟩

def subPieceOfHomeomorph (j : Fin S.card) :
    T.subPieceOf S j ≃ₜ T.components.piece (T.subIndex S j) :=
  preimageValHomeomorph (T.subPiece S : Set T.cutCarrier.Carrier) _
    (T.piece_subset_subPiece S (T.subIndex_mem S j))

def subPieceInteriorHomeomorph (j : Fin S.card) :
    (T.subCarrier S).pieceInterior (T.subPieceOf S j) ≃ₜ
      T.cutCarrier.pieceInterior (T.components.piece (T.subIndex S j)) where
  toFun x := ⟨x.val.val, x.property.1,
    (ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val (I := T.cutCarrier.model)
      (u := T.subPiece S) (x := x.val)).mp x.property.2⟩
  invFun y := ⟨⟨y.val, T.piece_subset_subPiece S (T.subIndex_mem S j) y.property.1⟩,
    y.property.1,
    (ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val (I := T.cutCarrier.model)
      (u := T.subPiece S)
      (x := ⟨y.val, T.piece_subset_subPiece S (T.subIndex_mem S j) y.property.1⟩)).mpr
      y.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact continuous_subtype_val

def subComponents (hS : S.Nonempty) : (T.subCarrier S).Components where
  count := S.card
  count_pos := Finset.card_pos.mpr hS
  piece := T.subPieceOf S
  closed j := (T.components.closed _).preimage continuous_subtype_val
  connected j := (T.subPieceOfHomeomorph S j).connectedSpace_iff.mpr
    (T.components.connected (T.subIndex S j))
  disjoint i j h := (T.components.disjoint
    fun e => h (T.subIndex_injective S e)).preimage Subtype.val
  covers := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨i, hi, hx⟩ := (T.mem_subPiece S).mp x.property
    refine Set.mem_iUnion.mpr ⟨T.subIndexOf S hi, ?_⟩
    change x.val ∈ T.components.piece (T.subIndex S (T.subIndexOf S hi))
    rw [subIndex_subIndexOf]
    exact hx
  interior_connected j := (T.subPieceInteriorHomeomorph S j).connectedSpace_iff.mpr
    (T.components.interior_connected (T.subIndex S j))


theorem sideCollar_target_subset_subPiece {s : T.Side} (hs : T.sidePiece s ∈ S) :
    (T.sideCollar s).target ⊆ T.subPiece S :=
  (T.sideCollar_target_subset s).trans (T.piece_subset_subPiece S hs)

theorem sideCollar_zero_mem_subPiece {s : T.Side} (hs : T.sidePiece s ∈ S) (t : Torus) :
    T.sideCollar s (t, halfZero) ∈ T.subPiece S :=
  T.piece_subset_subPiece S hs (T.sideCollar_zero_mem s t).2

def subCollar (s : T.Side) (hs : T.sidePiece s ∈ S) :
    PartialDiffeomorph halfCollarModel (T.subCarrier S).model (Torus × EuclideanHalfSpace 1)
      (T.subCarrier S).Carrier ∞ :=
  (codRestrictOpens (T.sideCollar s) (T.subPiece S)
    ⟨⟨_, T.sideCollar_zero_mem_subPiece S hs 1⟩⟩ :
    PartialDiffeomorph halfCollarModel T.cutCarrier.model (Torus × EuclideanHalfSpace 1)
      (T.subPiece S) ∞)

theorem subCollar_source (s : T.Side) (hs : T.sidePiece s ∈ S) :
    (T.subCollar S s hs).source = halfCollarSource :=
  (codRestrictOpens_source (J := T.cutCarrier.model) (T.sideCollar s) (T.subPiece S)
    ⟨⟨_, T.sideCollar_zero_mem_subPiece S hs 1⟩⟩
    (T.sideCollar_target_subset_subPiece S hs)).trans (T.sideCollar_source s)

theorem subCollar_target (s : T.Side) (hs : T.sidePiece s ∈ S) :
    (T.subCollar S s hs).target = Subtype.val ⁻¹' (T.sideCollar s).target :=
  codRestrictOpens_target (J := T.cutCarrier.model) (T.sideCollar s) (T.subPiece S)
    ⟨⟨_, T.sideCollar_zero_mem_subPiece S hs 1⟩⟩

theorem subCollar_apply (s : T.Side) (hs : T.sidePiece s ∈ S)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    (T.subCollar S s hs p).val = T.sideCollar s p :=
  codRestrictOpens_apply (J := T.cutCarrier.model) (T.sideCollar s) (T.subPiece S)
    ⟨⟨_, T.sideCollar_zero_mem_subPiece S hs 1⟩⟩ (T.sideCollar_target_subset_subPiece S hs
    ((T.sideCollar s).map_source' ((T.sideCollar_source s).symm ▸ hp)))

private theorem isOpen_halfCollarSource_of_side (s : T.Side) : IsOpen halfCollarSource :=
  T.sideCollar_source s ▸ (T.sideCollar s).open_source

theorem eventuallyEq_subCollar (s : T.Side) (hs : T.sidePiece s ∈ S)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    (fun q => (T.subCollar S s hs q).val) =ᶠ[𝓝 p] T.sideCollar s :=
  Filter.eventuallyEq_of_mem ((T.isOpen_halfCollarSource_of_side s).mem_nhds hp)
    fun _ hq => T.subCollar_apply S s hs hq

theorem reversesBoundaryOrientation_sub
    {l r : Torus × EuclideanHalfSpace 1 → T.cutCarrier.Carrier}
    {l' r' : Torus × EuclideanHalfSpace 1 → (T.subCarrier S).Carrier}
    (hl : ∀ t, (fun q => (l' q).val) =ᶠ[𝓝 (t, halfZero)] l)
    (hr : ∀ t, (fun q => (r' q).val) =ᶠ[𝓝 (t, halfZero)] r)
    (h : ReversesBoundaryOrientation T.cutCarrier l r) :
    ReversesBoundaryOrientation (T.subCarrier S) l' r' := by
  intro t
  obtain ⟨L, R, hL, hR, ho⟩ := h t
  have hl0 : (l' (t, halfZero)).val = l (t, halfZero) := (hl t).eq_of_nhds
  have hr0 : (r' (t, halfZero)).val = r (t, halfZero) := (hr t).eq_of_nhds
  have dl := DifferentialGeometry.mfderiv_subtypeVal_comp (I := halfCollarModel)
    (J := T.cutCarrier.model) (U := T.subPiece S) l' (t, halfZero)
  have dr := DifferentialGeometry.mfderiv_subtypeVal_comp (I := halfCollarModel)
    (J := T.cutCarrier.model) (U := T.subPiece S) r' (t, halfZero)
  have el : ∀ v, mfderiv halfCollarModel (T.subCarrier S).model l' (t, halfZero) v =
      mfderiv halfCollarModel T.cutCarrier.model l (t, halfZero) v := by
    intro v
    have h1 := congrArg (fun A => A v) dl
    have h2 := congrArg (fun A => A v)
      (Filter.EventuallyEq.mfderiv_eq (I := halfCollarModel) (I' := T.cutCarrier.model) (hl t))
    exact h1.symm.trans h2
  have er : ∀ v, mfderiv halfCollarModel (T.subCarrier S).model r' (t, halfZero) v =
      mfderiv halfCollarModel T.cutCarrier.model r (t, halfZero) v := by
    intro v
    have h1 := congrArg (fun A => A v) dr
    have h2 := congrArg (fun A => A v)
      (Filter.EventuallyEq.mfderiv_eq (I := halfCollarModel) (I' := T.cutCarrier.model) (hr t))
    exact h1.symm.trans h2
  refine ⟨L, R, fun v => (hL v).trans (el v).symm, fun v => (hR v).trans (er v).symm, ?_⟩
  · change Orientation.map (Fin 3) L.symm
        (T.cutCarrier.orientation.orientation (l' (t, halfZero)).val) =
      -Orientation.map (Fin 3) R.symm
        (T.cutCarrier.orientation.orientation (r' (t, halfZero)).val)
    rw [hl0, hr0]
    exact ho

abbrev KeptSeam := {k : Fin T.pairing.count // T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S}

def keptSeam (j : Fin (Fintype.card (T.KeptSeam S))) : T.KeptSeam S :=
  (Fintype.equivFin _).symm j

@[simp]
theorem keptSeam_equivFin (a : T.KeptSeam S) : T.keptSeam S (Fintype.equivFin _ a) = a :=
  (Fintype.equivFin _).symm_apply_apply a

theorem left_subset_subPiece (j : Fin (Fintype.card (T.KeptSeam S))) :
    T.pairing.gluing.left (T.keptSeam S j).val ⊆ T.subPiece S :=
  (T.left_owned _).trans (T.piece_subset_subPiece S (T.keptSeam S j).property.1)

theorem right_subset_subPiece (j : Fin (Fintype.card (T.KeptSeam S))) :
    T.pairing.gluing.right (T.keptSeam S j).val ⊆ T.subPiece S :=
  (T.right_owned _).trans (T.piece_subset_subPiece S (T.keptSeam S j).property.2)

def restrictGluing :
    BoundaryGluing (T.subCarrier S).Carrier (Fin (Fintype.card (T.KeptSeam S))) where
  left j := Subtype.val ⁻¹' T.pairing.gluing.left (T.keptSeam S j).val
  right j := Subtype.val ⁻¹' T.pairing.gluing.right (T.keptSeam S j).val
  attaching j := (preimageValHomeomorph _ _ (T.left_subset_subPiece S j)).trans
    ((T.pairing.gluing.attaching _).trans
      (preimageValHomeomorph _ _ (T.right_subset_subPiece S j)).symm)
  isClosed_left j := (T.pairing.gluing.isClosed_left (T.keptSeam S j).val).preimage
    continuous_subtype_val
  isClosed_right j := (T.pairing.gluing.isClosed_right (T.keptSeam S j).val).preimage
    continuous_subtype_val
  disjoint_left_right j :=
    (T.pairing.gluing.disjoint_left_right (T.keptSeam S j).val).preimage Subtype.val
  disjoint_blocks i j h := (T.pairing.gluing.disjoint_blocks (T.keptSeam S i).val
    (T.keptSeam S j).val
    fun e => h ((Fintype.equivFin _).symm.injective (Subtype.ext e))).preimage Subtype.val

def restrictPairing : TorusPairing (T.subCarrier S) where
  count := Fintype.card (T.KeptSeam S)
  gluing := T.restrictGluing S
  leftParam j := (T.pairing.leftParam (T.keptSeam S j).val).trans
    (preimageValHomeomorph _ _ (T.left_subset_subPiece S j)).symm
  rightParam j := (T.pairing.rightParam (T.keptSeam S j).val).trans
    (preimageValHomeomorph _ _ (T.right_subset_subPiece S j)).symm
  matching j := T.pairing.matching (T.keptSeam S j).val
  matching_eq j t := by
    have h := congrArg Subtype.val (T.pairing.matching_eq (T.keptSeam S j).val t)
    apply Subtype.ext
    apply Subtype.ext
    exact h
  leftCollar j := T.subCollar S (.inl (T.keptSeam S j).val) (T.keptSeam S j).property.1
  rightCollar j := T.subCollar S (.inr (.inl (T.keptSeam S j).val)) (T.keptSeam S j).property.2
  left_source j := T.subCollar_source S _ _
  right_source j := T.subCollar_source S _ _
  left_zero j t := Subtype.ext ((T.subCollar_apply S _ _ (zero_mem_halfCollarSource t)).trans
    (T.pairing.left_zero _ t))
  right_zero j t := Subtype.ext ((T.subCollar_apply S _ _ (zero_mem_halfCollarSource t)).trans
    (T.pairing.right_zero _ t))
  reversing j := T.reversesBoundaryOrientation_sub S
    (fun t => T.eventuallyEq_subCollar S _ _ (zero_mem_halfCollarSource t))
    (fun t => (T.eventuallyEq_subCollar S (.inr (.inl (T.keptSeam S j).val))
      (T.keptSeam S j).property.2 (p := (T.pairing.matching _ t, halfZero))
      (zero_mem_halfCollarSource _)).comp_tendsto
      ((((T.pairing.matching _).continuous.comp continuous_fst).prodMk
        continuous_snd).tendsto (t, halfZero)))
    (T.pairing.reversing (T.keptSeam S j).val)

theorem restrictPairing_count : (T.restrictPairing S).count = Fintype.card (T.KeptSeam S) :=
  rfl

theorem restrictPairing_left (j : Fin (T.restrictPairing S).count) :
    (T.restrictPairing S).gluing.left j =
      Subtype.val ⁻¹' T.pairing.gluing.left (T.keptSeam S j).val := rfl

theorem restrictPairing_right (j : Fin (T.restrictPairing S).count) :
    (T.restrictPairing S).gluing.right j =
      Subtype.val ⁻¹' T.pairing.gluing.right (T.keptSeam S j).val := rfl

theorem restrictPairing_matching (j : Fin (T.restrictPairing S).count) :
    (T.restrictPairing S).matching j = T.pairing.matching (T.keptSeam S j).val := rfl

theorem restrictPairing_leftCollar_apply (j : Fin (T.restrictPairing S).count)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    ((T.restrictPairing S).leftCollar j p).val = T.pairing.leftCollar (T.keptSeam S j).val p :=
  T.subCollar_apply S (.inl (T.keptSeam S j).val) (T.keptSeam S j).property.1 hp

theorem restrictPairing_rightCollar_apply (j : Fin (T.restrictPairing S).count)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    ((T.restrictPairing S).rightCollar j p).val =
      T.pairing.rightCollar (T.keptSeam S j).val p :=
  T.subCollar_apply S (.inr (.inl (T.keptSeam S j).val)) (T.keptSeam S j).property.2 hp

def IsKeptSide : T.Side → Prop
  | .inl k => T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S
  | .inr (.inl k) => T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S
  | .inr (.inr _) => False

instance : DecidablePred (T.IsKeptSide S)
  | .inl k => inferInstanceAs (Decidable (T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S))
  | .inr (.inl k) => inferInstanceAs (Decidable (T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S))
  | .inr (.inr _) => inferInstanceAs (Decidable False)

abbrev RestrictSide := {s : T.Side // T.sidePiece s ∈ S ∧ ¬ T.IsKeptSide S s}

def restrictSide (j : Fin (Fintype.card (T.RestrictSide S))) : T.RestrictSide S :=
  (Fintype.equivFin _).symm j

@[simp]
theorem restrictSide_equivFin (a : T.RestrictSide S) :
    T.restrictSide S (Fintype.equivFin _ a) = a :=
  (Fintype.equivFin _).symm_apply_apply a

def restrictBoundaryTori : BoundaryTori (T.subCarrier S) (Fintype.card (T.RestrictSide S)) where
  collar j := T.subCollar S (T.restrictSide S j).val (T.restrictSide S j).property.1
  source_eq j := T.subCollar_source S _ _
  boundary_zero j t := by
    refine (ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val (I := T.cutCarrier.model)
      (u := T.subPiece S)).mpr ?_
    rw [T.subCollar_apply S _ (T.restrictSide S j).property.1 (zero_mem_halfCollarSource t)]
    exact (T.sideCollar_zero_mem _ t).1
  disjoint j j' h := by
    change Disjoint (T.subCollar S _ _).target (T.subCollar S _ _).target
    rw [T.subCollar_target, T.subCollar_target]
    exact (T.sideCollar_disjoint fun e =>
      h ((Fintype.equivFin _).symm.injective (Subtype.ext e))).preimage _

theorem restrictBoundaryTori_torusMap (j : Fin (Fintype.card (T.RestrictSide S))) (t : Torus) :
    ((T.restrictBoundaryTori S).torusMap j t).val =
      T.sideCollar (T.restrictSide S j).val (t, halfZero) :=
  T.subCollar_apply S _ (T.restrictSide S j).property.1 (zero_mem_halfCollarSource t)

theorem restrictBoundaryTori_collar_apply (j : Fin (Fintype.card (T.RestrictSide S)))
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    ((T.restrictBoundaryTori S).collar j p).val = T.sideCollar (T.restrictSide S j).val p :=
  T.subCollar_apply S _ (T.restrictSide S j).property.1 hp

theorem left_subset_leftCollar_target (k : Fin T.pairing.count) :
    T.pairing.gluing.left k ⊆ (T.pairing.leftCollar k).target := by
  intro x hx
  have h : T.pairing.leftCollar k ((T.pairing.leftParam k).symm ⟨x, hx⟩, halfZero) = x := by
    rw [T.pairing.left_zero, Homeomorph.apply_symm_apply]
  rw [← h]
  exact (T.pairing.leftCollar k).map_source'
    (T.pairing.left_source k ▸ zero_mem_halfCollarSource _)

theorem right_subset_rightCollar_target (k : Fin T.pairing.count) :
    T.pairing.gluing.right k ⊆ (T.pairing.rightCollar k).target := by
  intro x hx
  have h : T.pairing.rightCollar k ((T.pairing.rightParam k).symm ⟨x, hx⟩, halfZero) = x := by
    rw [T.pairing.right_zero, Homeomorph.apply_symm_apply]
  rw [← h]
  exact (T.pairing.rightCollar k).map_source'
    (T.pairing.right_source k ▸ zero_mem_halfCollarSource _)

private theorem mem_boundary_of_mem_block' {k : Fin T.pairing.count}
    {x : T.cutCarrier.Carrier} (hx : x ∈ T.pairing.gluing.block k) :
    x ∈ T.cutCarrier.model.boundary T.cutCarrier.Carrier := by
  rw [T.cut_boundary_exhausted]
  exact Or.inl (Set.mem_iUnion.mpr ⟨k, hx⟩)

theorem subCarrier_boundary :
    (T.subCarrier S).model.boundary (T.subCarrier S).Carrier =
      (⋃ j, (T.restrictPairing S).gluing.block j) ∪ (T.restrictBoundaryTori S).image := by
  ext x
  constructor
  · intro hx
    have hx' : x.val ∈ T.cutCarrier.model.boundary T.cutCarrier.Carrier :=
      (ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val (I := T.cutCarrier.model)
        (u := T.subPiece S)).mp hx
    obtain ⟨s, t, hst⟩ := T.exists_sideCollar_zero_eq hx'
    have hsS : T.sidePiece s ∈ S :=
      T.mem_of_mem_subPiece S x.property (hst ▸ (T.sideCollar_zero_mem s t).2)
    by_cases hk : T.IsKeptSide S s
    · left
      rcases s with k | k | k
      · refine Set.mem_iUnion.mpr ⟨Fintype.equivFin (T.KeptSeam S) ⟨k, hk⟩, Or.inl ?_⟩
        change x.val ∈ T.pairing.gluing.left (T.keptSeam S (Fintype.equivFin _ ⟨k, hk⟩)).val
        rw [keptSeam_equivFin, ← hst]
        change T.pairing.leftCollar k (t, halfZero) ∈ _
        rw [T.pairing.left_zero]
        exact (T.pairing.leftParam k t).property
      · refine Set.mem_iUnion.mpr ⟨Fintype.equivFin (T.KeptSeam S) ⟨k, hk⟩, Or.inr ?_⟩
        change x.val ∈ T.pairing.gluing.right (T.keptSeam S (Fintype.equivFin _ ⟨k, hk⟩)).val
        rw [keptSeam_equivFin, ← hst]
        change T.pairing.rightCollar k (t, halfZero) ∈ _
        rw [T.pairing.right_zero]
        exact (T.pairing.rightParam k t).property
      · exact hk.elim
    · right
      refine Set.mem_iUnion.mpr
        ⟨Fintype.equivFin (T.RestrictSide S) ⟨s, hsS, hk⟩, t, Subtype.ext ?_⟩
      rw [restrictBoundaryTori_torusMap, restrictSide_equivFin]
      exact hst
  · rintro (hx | hx)
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      exact (ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val (I := T.cutCarrier.model)
        (u := T.subPiece S)).mpr (T.mem_boundary_of_mem_block' hj)
    · obtain ⟨j, t, rfl⟩ := Set.mem_iUnion.mp hx
      exact (T.restrictBoundaryTori S).boundary_zero j t

theorem restrict_external_disjoint :
    Disjoint (⋃ j, (T.restrictPairing S).gluing.block j) (T.restrictBoundaryTori S).image := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  obtain ⟨j', t, rfl⟩ := Set.mem_iUnion.mp hx'
  have hmem : ((T.restrictBoundaryTori S).torusMap j' t).val ∈
      (T.sideCollar (T.restrictSide S j').val).target := by
    rw [restrictBoundaryTori_torusMap]
    exact (T.sideCollar _).map_source' (T.zero_mem_sideCollar_source _ t)
  have hkept := (T.keptSeam S j).property
  have hnot := (T.restrictSide S j').property.2
  rcases hj with hl | hr
  · have hne : (T.restrictSide S j').val ≠ .inl (T.keptSeam S j).val := fun e =>
      hnot (by rw [e]; exact hkept)
    exact (T.sideCollar_disjoint hne).le_bot
      ⟨hmem, T.left_subset_leftCollar_target _ hl⟩
  · have hne : (T.restrictSide S j').val ≠ .inr (.inl (T.keptSeam S j).val) := fun e =>
      hnot (by rw [e]; exact hkept)
    exact (T.sideCollar_disjoint hne).le_bot
      ⟨hmem, T.right_subset_rightCollar_target _ hr⟩

def restrictLeftPiece (j : Fin (T.restrictPairing S).count) : Fin S.card :=
  T.subIndexOf S (T.keptSeam S j).property.1

def restrictRightPiece (j : Fin (T.restrictPairing S).count) : Fin S.card :=
  T.subIndexOf S (T.keptSeam S j).property.2

def restrictExternalPiece (j : Fin (Fintype.card (T.RestrictSide S))) : Fin S.card :=
  T.subIndexOf S (T.restrictSide S j).property.1

theorem restrict_left_owned (hS : S.Nonempty) (j : Fin (T.restrictPairing S).count) :
    (T.restrictPairing S).gluing.left j ⊆
      (T.subComponents S hS).piece (T.restrictLeftPiece S j) := by
  intro x hx
  change x.val ∈ T.components.piece (T.subIndex S (T.subIndexOf S _))
  rw [subIndex_subIndexOf]
  exact T.left_owned _ hx

theorem restrict_right_owned (hS : S.Nonempty) (j : Fin (T.restrictPairing S).count) :
    (T.restrictPairing S).gluing.right j ⊆
      (T.subComponents S hS).piece (T.restrictRightPiece S j) := by
  intro x hx
  change x.val ∈ T.components.piece (T.subIndex S (T.subIndexOf S _))
  rw [subIndex_subIndexOf]
  exact T.right_owned _ hx

theorem restrict_external_owned (hS : S.Nonempty) (j : Fin (Fintype.card (T.RestrictSide S))) :
    Set.range ((T.restrictBoundaryTori S).torusMap j) ⊆
      (T.subComponents S hS).piece (T.restrictExternalPiece S j) := by
  rintro _ ⟨t, rfl⟩
  change ((T.restrictBoundaryTori S).torusMap j t).val ∈
    T.components.piece (T.subIndex S (T.subIndexOf S _))
  rw [subIndex_subIndexOf, restrictBoundaryTori_torusMap]
  exact (T.sideCollar_zero_mem _ t).2

@[simp]
theorem subComponents_count (hS : S.Nonempty) : (T.subComponents S hS).count = S.card := rfl

theorem restrictPairing_count_eq_card_filter :
    (T.restrictPairing S).count =
      (Finset.univ.filter fun k => T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S).card := by
  rw [restrictPairing_count]
  exact Fintype.card_subtype _

theorem card_restrictSide :
    Fintype.card (T.RestrictSide S) =
      (Finset.univ.filter fun k => T.externalPiece k ∈ S).card +
        (Finset.univ.filter fun k => (T.leftPiece k ∈ S ∧ T.rightPiece k ∉ S) ∨
          (T.rightPiece k ∈ S ∧ T.leftPiece k ∉ S)).card := by
  have e : T.RestrictSide S ≃
      {k : Fin T.pairing.count // T.leftPiece k ∈ S ∧ T.rightPiece k ∉ S} ⊕
        ({k : Fin T.pairing.count // T.rightPiece k ∈ S ∧ T.leftPiece k ∉ S} ⊕
          {k : Fin T.externalCount // T.externalPiece k ∈ S}) := by
    refine Equiv.subtypeSum.trans (Equiv.sumCongr (Equiv.subtypeEquivRight fun k => ?_)
      (Equiv.subtypeSum.trans (Equiv.sumCongr (Equiv.subtypeEquivRight fun k => ?_)
        (Equiv.subtypeEquivRight fun k => ?_))))
    · change T.leftPiece k ∈ S ∧ ¬(T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) ↔ _
      tauto
    · change T.rightPiece k ∈ S ∧ ¬(T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) ↔ _
      tauto
    · change T.externalPiece k ∈ S ∧ ¬False ↔ _
      tauto
  rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_sum, Fintype.card_subtype,
    Fintype.card_subtype, Fintype.card_subtype, Finset.filter_or,
    Finset.card_union_of_disjoint
      (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2.2 h1.1)]
  omega

theorem restrictGluing_flip_val (j : Fin (T.restrictPairing S).count)
    (x : (T.subCarrier S).Carrier) :
    ((T.restrictGluing S).flip j x).val =
      T.pairing.gluing.flip (T.keptSeam S j).val x.val := by
  by_cases hl : x ∈ (T.restrictGluing S).left j
  · have hl' : x.val ∈ T.pairing.gluing.left (T.keptSeam S j).val := hl
    rw [BoundaryGluing.flip_of_mem_left _ hl, BoundaryGluing.flip_of_mem_left _ hl']
    rfl
  · by_cases hr : x ∈ (T.restrictGluing S).right j
    · have hr' : x.val ∈ T.pairing.gluing.right (T.keptSeam S j).val := hr
      rw [BoundaryGluing.flip_of_mem_right _ hr, BoundaryGluing.flip_of_mem_right _ hr']
      rfl
    · have hb : x.val ∉ T.pairing.gluing.block (T.keptSeam S j).val := fun h => h.elim hl hr
      rw [BoundaryGluing.flip_of_notMem _ (fun h => h.elim hl hr),
        BoundaryGluing.flip_of_notMem _ hb]

theorem restrictGluing_rel_val {x y : (T.subCarrier S).Carrier}
    (h : (T.restrictGluing S).rel x y) : T.pairing.gluing.rel x.val y.val := by
  rcases h with rfl | ⟨j, hx, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨(T.keptSeam S j).val, hx, T.restrictGluing_flip_val S j x⟩

theorem restrictGluing_rel_of_val {x y : (T.subCarrier S).Carrier}
    (h : T.pairing.gluing.rel x.val y.val) : (T.restrictGluing S).rel x y := by
  rcases h with h | ⟨k, hx, hy⟩
  · exact Or.inl (Subtype.ext h)
  have hk : T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S := by
    rcases hx with hl | hr
    · have hyr : y.val ∈ T.pairing.gluing.right k := by
        rw [hy, T.pairing.gluing.flip_of_mem_left hl]
        exact (T.pairing.gluing.attaching k ⟨x.val, hl⟩).property
      exact ⟨T.mem_of_mem_subPiece S x.property (T.left_owned k hl),
        T.mem_of_mem_subPiece S y.property (T.right_owned k hyr)⟩
    · have hyl : y.val ∈ T.pairing.gluing.left k := by
        rw [hy, T.pairing.gluing.flip_of_mem_right hr]
        exact ((T.pairing.gluing.attaching k).symm ⟨x.val, hr⟩).property
      exact ⟨T.mem_of_mem_subPiece S y.property (T.left_owned k hyl),
        T.mem_of_mem_subPiece S x.property (T.right_owned k hr)⟩
  refine Or.inr ⟨Fintype.equivFin (T.KeptSeam S) ⟨k, hk⟩, ?_, Subtype.ext ?_⟩
  · change x.val ∈ T.pairing.gluing.block (T.keptSeam S (Fintype.equivFin _ ⟨k, hk⟩)).val
    rw [keptSeam_equivFin]
    exact hx
  · have h2 := T.restrictGluing_flip_val S (Fintype.equivFin (T.KeptSeam S) ⟨k, hk⟩) x
    rw [keptSeam_equivFin] at h2
    exact hy.trans h2.symm

def restrictMap : (T.restrictPairing S).QuotientSpace → W.Carrier :=
  Quotient.lift (fun x : (T.subCarrier S).Carrier => T.cutMap x.val) fun _ _ h =>
    congrArg T.reconstruction (Quotient.sound' (T.restrictGluing_rel_val S h))

theorem restrictMap_quotientMap (x : (T.subCarrier S).Carrier) :
    T.restrictMap S ((T.restrictPairing S).quotientMap x) = T.cutMap x.val := rfl

theorem continuous_restrictMap : Continuous (T.restrictMap S) :=
  continuous_quot_lift _ (T.reconstruction.continuous.comp
    (T.pairing.quotientMap.continuous.comp continuous_subtype_val))

theorem restrictMap_injective : Function.Injective (T.restrictMap S) := by
  intro a b h
  obtain ⟨x, rfl⟩ := Quotient.exists_rep a
  obtain ⟨y, rfl⟩ := Quotient.exists_rep b
  have h1 : T.pairing.quotientMap x.val = T.pairing.quotientMap y.val :=
    T.reconstruction.injective h
  exact Quotient.sound' (T.restrictGluing_rel_of_val S
    ((Quotient.eq' (s₁ := T.pairing.gluing.setoid)).mp h1))

theorem isClosedEmbedding_restrictMap : _root_.Topology.IsClosedEmbedding (T.restrictMap S) :=
  (T.continuous_restrictMap S).isClosedEmbedding (T.restrictMap_injective S)

theorem range_restrictMap :
    Set.range (T.restrictMap S) = T.cutMap '' (T.subPiece S : Set T.cutCarrier.Carrier) := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨x, rfl⟩ := Quotient.exists_rep a
    exact ⟨x.val, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(T.restrictPairing S).quotientMap ⟨x, hx⟩, rfl⟩

def restrictHomeomorph :
    (T.restrictPairing S).QuotientSpace ≃ₜ Set.range (T.restrictMap S) :=
  (T.isClosedEmbedding_restrictMap S).isEmbedding.toHomeomorph

theorem restrictHomeomorph_apply (q : (T.restrictPairing S).QuotientSpace) :
    (T.restrictHomeomorph S q : W.Carrier) = T.restrictMap S q := rfl

theorem restrictMap_leftParam (j : Fin (T.restrictPairing S).count) (t : Torus) :
    T.restrictMap S ((T.restrictPairing S).quotientMap ((T.restrictPairing S).leftParam j t)) =
      T.seam (T.keptSeam S j).val (t, 0) :=
  (T.seam_zero _ t).symm

theorem restrictMap_leftCollar (j : Fin (T.restrictPairing S).count)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    T.restrictMap S ((T.restrictPairing S).quotientMap ((T.restrictPairing S).leftCollar j p)) =
      T.seam (T.keptSeam S j).val (p.1, -(p.2.val 0)) := by
  rw [restrictMap_quotientMap, T.restrictPairing_leftCollar_apply S j hp]
  exact T.cutMap_leftCollar _ hp

theorem restrictMap_rightCollar (j : Fin (T.restrictPairing S).count)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    T.restrictMap S ((T.restrictPairing S).quotientMap ((T.restrictPairing S).rightCollar j p)) =
      T.seam (T.keptSeam S j).val
        ((T.pairing.matching (T.keptSeam S j).val).symm p.1, p.2.val 0) := by
  rw [restrictMap_quotientMap, T.restrictPairing_rightCollar_apply S j hp]
  exact T.cutMap_rightCollar _ hp

theorem restrictMap_boundaryCollar (j : Fin (Fintype.card (T.RestrictSide S)))
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    T.restrictMap S ((T.restrictPairing S).quotientMap ((T.restrictBoundaryTori S).collar j p)) =
      T.cutMap (T.sideCollar (T.restrictSide S j).val p) := by
  rw [restrictMap_quotientMap, T.restrictBoundaryTori_collar_apply S j hp]

theorem seam_target_subset_range_restrictMap (j : Fin (T.restrictPairing S).count) :
    (T.seam (T.keptSeam S j).val).target ⊆ Set.range (T.restrictMap S) := by
  rw [range_restrictMap]
  intro z hz
  have hs : (T.seam (T.keptSeam S j).val).symm z ∈ signedCollarSource :=
    T.seam_source _ ▸ (T.seam _).map_target' hz
  have hz' : T.seam (T.keptSeam S j).val ((T.seam (T.keptSeam S j).val).symm z) = z :=
    (T.seam _).right_inv' hz
  generalize (T.seam (T.keptSeam S j).val).symm z = p at hs hz'
  obtain ⟨t, a⟩ := p
  rcases le_total a 0 with ha | ha
  · rw [T.seam_negative _ t a ha hs.1] at hz'
    refine ⟨_, T.sideCollar_target_subset_subPiece S (s := .inl (T.keptSeam S j).val)
      (T.keptSeam S j).property.1 ((T.pairing.leftCollar _).map_source' ?_), hz'⟩
    rw [T.pairing.left_source]
    change -a < 1
    linarith [hs.1]
  · rw [T.seam_positive _ t a ha hs.2] at hz'
    refine ⟨_, T.sideCollar_target_subset_subPiece S (s := .inr (.inl (T.keptSeam S j).val))
      (T.keptSeam S j).property.2 ((T.pairing.rightCollar _).map_source' ?_), hz'⟩
    rw [T.pairing.right_source]
    exact hs.2

theorem iUnion_restrict_block_eq_empty
    (hk : ∀ k, ¬(T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)) :
    ⋃ j, (T.restrictPairing S).gluing.block j = ∅ := by
  have : IsEmpty (Fin (T.restrictPairing S).count) := by
    rw [restrictPairing_count, Fintype.card_eq_zero_iff.mpr ⟨fun a => hk a.val a.property⟩]
    infer_instance
  exact Set.iUnion_of_empty _

theorem subCarrier_boundary_of_noKeptSeam
    (hk : ∀ k, ¬(T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)) :
    (T.subCarrier S).model.boundary (T.subCarrier S).Carrier =
      (T.restrictBoundaryTori S).image := by
  rw [T.subCarrier_boundary S, T.iUnion_restrict_block_eq_empty S hk, Set.empty_union]

def restrictOfNoKeptSeam (hS : S.Nonempty)
    (hk : ∀ k, ¬(T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)) :
    TorusPresentation (T.subCarrier S) where
  cutCarrier := T.subCarrier S
  components := T.subComponents S hS
  pairing := emptyTorusPairing _
  externalCount := Fintype.card (T.RestrictSide S)
  external := T.restrictBoundaryTori S
  cutExternal := T.restrictBoundaryTori S
  external_exhausted := T.subCarrier_boundary_of_noKeptSeam S hk
  cut_boundary_exhausted := by
    rw [iUnion_block_emptyTorusPairing, Set.empty_union]
    exact T.subCarrier_boundary_of_noKeptSeam S hk
  external_disjoint := by
    rw [iUnion_block_emptyTorusPairing]
    exact Set.empty_disjoint _
  reconstruction := emptyTorusPairingHomeomorph _
  quotient_smooth := contMDiff_id
  quotient_oriented x := by
    refine ⟨LinearEquiv.refl ℝ _, fun v => ?_, ?_⟩
    · change v = mfderiv _ _ (id : (T.subCarrier S).Carrier → _) x v
      rw [mfderiv_id]
      rfl
    · change Orientation.map (Fin 3) (LinearEquiv.refl ℝ (TangentSpace _ x))
          ((T.subCarrier S).orientation.orientation x) =
        (T.subCarrier S).orientation.orientation x
      rw [Orientation.map_refl]
      rfl
  interiorImage := (T.subCarrier S).interior
  interiorDiffeomorph := Diffeomorph.refl _ _ _
  interior_map _ := rfl
  seam k := k.elim0
  seam_source k := k.elim0
  seam_zero k := k.elim0
  seam_positive k := k.elim0
  seam_negative k := k.elim0
  seam_interior k := k.elim0
  seam_disjoint k := k.elim0
  marked_collar _ _ _ := rfl
  external_seam_disjoint _ k := k.elim0
  leftPiece k := k.elim0
  rightPiece k := k.elim0
  left_owned k := k.elim0
  right_owned k := k.elim0
  externalPiece := T.restrictExternalPiece S
  external_owned := T.restrict_external_owned S hS

section NoKeptSeam
variable (hS : S.Nonempty) (hk : ∀ k, ¬(T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S))

@[simp]
theorem restrictOfNoKeptSeam_components_count :
    (T.restrictOfNoKeptSeam S hS hk).components.count = S.card := rfl

@[simp]
theorem restrictOfNoKeptSeam_pairing_count :
    (T.restrictOfNoKeptSeam S hS hk).pairing.count = 0 := rfl

theorem restrictOfNoKeptSeam_externalCount :
    (T.restrictOfNoKeptSeam S hS hk).externalCount =
      (Finset.univ.filter fun k => T.externalPiece k ∈ S).card +
        (Finset.univ.filter fun k => (T.leftPiece k ∈ S ∧ T.rightPiece k ∉ S) ∨
          (T.rightPiece k ∈ S ∧ T.leftPiece k ∉ S)).card :=
  T.card_restrictSide S

theorem restrictOfNoKeptSeam_external :
    (T.restrictOfNoKeptSeam S hS hk).external = T.restrictBoundaryTori S := rfl

end NoKeptSeam

section Side
variable (j : Fin T.pairing.count)

def complImage : Set W.Carrier := T.cutMap '' (T.subPiece S : Set T.cutCarrier.Carrier)ᶜ

private theorem continuous_cutMap_aux : Continuous T.cutMap :=
  T.reconstruction.continuous.comp T.pairing.quotientMap.continuous

theorem isClosed_range_restrictMap : IsClosed (Set.range (T.restrictMap S)) :=
  (T.isClosedEmbedding_restrictMap S).isClosed_range

theorem isClosed_complImage : IsClosed (T.complImage S) :=
  ((T.subPiece S).isOpen.isClosed_compl.isCompact.image (T.continuous_cutMap_aux)).isClosed

theorem range_union_complImage : Set.range (T.restrictMap S) ∪ T.complImage S = Set.univ := by
  rw [range_restrictMap, complImage, ← Set.image_union, Set.union_compl_self, Set.image_univ,
    Set.range_eq_univ]
  intro w
  obtain ⟨x, hx⟩ := Quotient.exists_rep (T.reconstruction.symm w)
  refine ⟨x, ?_⟩
  change T.reconstruction (Quotient.mk _ x) = w
  rw [hx, Homeomorph.apply_symm_apply]

private theorem cutMap_mem_seamSurface_of_block {x : T.cutCarrier.Carrier}
    (hx : x ∈ T.pairing.gluing.block j) : T.cutMap x ∈ T.seamSurface j := by
  rcases hx with hx | hx
  · refine ⟨(T.pairing.leftParam j).symm ⟨x, hx⟩, ?_⟩
    rw [seamTorus_eq_cutMap, Homeomorph.apply_symm_apply]
  · refine ⟨(T.pairing.matching j).symm ((T.pairing.rightParam j).symm ⟨x, hx⟩), ?_⟩
    rw [seamTorus_eq_cutMap_right, Diffeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

theorem range_inter_complImage_subset
    (hother : ∀ k, k ≠ j → (T.leftPiece k ∈ S ↔ T.rightPiece k ∈ S)) :
    Set.range (T.restrictMap S) ∩ T.complImage S ⊆ T.seamSurface j := by
  rw [range_restrictMap]
  rintro w ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
  rcases Quotient.exact (T.reconstruction.injective hxy) with h | ⟨k, hk, hxk⟩
  · exact (hy (h ▸ hx)).elim
  by_cases hkj : k = j
  · subst hkj
    rw [← hxy]
    exact T.cutMap_mem_seamSurface_of_block _ hk
  · exfalso
    rcases hk with hl | hr
    · have hxr : x ∈ T.pairing.gluing.right k := by
        rw [hxk, T.pairing.gluing.flip_of_mem_left hl]
        exact (T.pairing.gluing.attaching k ⟨y, hl⟩).property
      have hR := T.mem_of_mem_subPiece S hx (T.right_owned k hxr)
      exact hy (T.piece_subset_subPiece S ((hother k hkj).mpr hR) (T.left_owned k hl))
    · have hxl : x ∈ T.pairing.gluing.left k := by
        rw [hxk, T.pairing.gluing.flip_of_mem_right hr]
        exact ((T.pairing.gluing.attaching k).symm ⟨y, hr⟩).property
      have hL := T.mem_of_mem_subPiece S hx (T.left_owned k hxl)
      exact hy (T.piece_subset_subPiece S ((hother k hkj).mp hL) (T.right_owned k hr))

theorem leftPoint_mem_range (hj : T.leftPiece j ∈ S) :
    T.leftPoint j ∈ Set.range (T.restrictMap S) := by
  have hp : ((1, 1), halfPoint 2⁻¹ (by norm_num)) ∈ halfCollarSource := by
    change (2 : ℝ)⁻¹ < 1
    norm_num
  rw [range_restrictMap]
  refine ⟨T.pairing.leftCollar j ((1, 1), halfPoint 2⁻¹ (by norm_num)),
    T.sideCollar_target_subset_subPiece S (s := .inl j) hj
      ((T.pairing.leftCollar j).map_source (by rw [T.pairing.left_source]; exact hp)), ?_⟩
  rw [T.cutMap_leftCollar j hp]
  rfl

theorem seam_mem_complImage (hj' : T.rightPiece j ∉ S) (t : Torus) {a : ℝ} (ha : 0 ≤ a)
    (ha' : a < 1) : T.seam j (t, a) ∈ T.complImage S := by
  have hp : (T.pairing.matching j t, halfPoint a ha) ∈ halfCollarSource := ha'
  refine ⟨T.pairing.rightCollar j (T.pairing.matching j t, halfPoint a ha), fun hmem =>
    hj' (T.mem_of_mem_subPiece S hmem (T.sideCollar_target_subset (.inr (.inl j))
      ((T.pairing.rightCollar j).map_source (by rw [T.pairing.right_source]; exact hp)))), ?_⟩
  rw [T.cutMap_rightCollar j hp, Diffeomorph.symm_apply_apply]
  rfl

theorem rightPoint_mem_complImage (hj' : T.rightPiece j ∉ S) :
    T.rightPoint j ∈ T.complImage S :=
  T.seam_mem_complImage S j hj' (1, 1) (by norm_num) (by norm_num)

theorem pathComponentIn_subset_range
    (hother : ∀ k, k ≠ j → (T.leftPiece k ∈ S ↔ T.rightPiece k ∈ S)) {p : W.Carrier}
    (hp : p ∈ Set.range (T.restrictMap S)) (hpS : p ∉ T.seamSurface j) :
    pathComponentIn (T.seamSurface j)ᶜ p ⊆ Set.range (T.restrictMap S) := by
  have hS := T.range_inter_complImage_subset S j hother
  have hcover : pathComponentIn (T.seamSurface j)ᶜ p ⊆
      Set.range (T.restrictMap S) ∪ T.complImage S := by
    rw [T.range_union_complImage S]
    exact Set.subset_univ _
  have hempty : pathComponentIn (T.seamSurface j)ᶜ p ∩
      (Set.range (T.restrictMap S) ∩ T.complImage S) = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun w hw => pathComponentIn_subset hw.1 (hS hw.2)
  rcases isPreconnected_iff_subset_of_disjoint_closed.1
    (isPathConnected_pathComponentIn hpS).isConnected.isPreconnected _ _
    (T.isClosed_range_restrictMap S) (T.isClosed_complImage S) hcover hempty with h | h
  · exact h
  · exact (hpS (hS ⟨hp, h (mem_pathComponentIn_self hpS)⟩)).elim

theorem leftSide_subset_range (hj : T.leftPiece j ∈ S)
    (hother : ∀ k, k ≠ j → (T.leftPiece k ∈ S ↔ T.rightPiece k ∈ S)) :
    T.leftSide j ⊆ Set.range (T.restrictMap S) :=
  T.pathComponentIn_subset_range S j hother (T.leftPoint_mem_range S j hj)
    (T.leftPoint_mem_compl j)

theorem isSeparating_of_restrict (hj : T.leftPiece j ∈ S) (hj' : T.rightPiece j ∉ S)
    (hother : ∀ k, k ≠ j → (T.leftPiece k ∈ S ↔ T.rightPiece k ∈ S)) : T.IsSeparating j := by
  rw [isSeparating_iff]
  intro h
  exact T.rightPoint_mem_compl j (T.range_inter_complImage_subset S j hother
    ⟨T.leftSide_subset_range S j hj hother h, T.rightPoint_mem_complImage S j hj'⟩)

theorem range_diff_seamSurface_eq
    (hother : ∀ k, k ≠ j → (T.leftPiece k ∈ S ↔ T.rightPiece k ∈ S)) :
    Set.range (T.restrictMap S) \ T.seamSurface j = (T.complImage S ∪ T.seamSurface j)ᶜ := by
  ext x
  constructor
  · rintro ⟨hx, hs⟩ (hc | hc)
    · exact hs (T.range_inter_complImage_subset S j hother ⟨hx, hc⟩)
    · exact hs hc
  · intro hx
    have hx' : x ∈ Set.range (T.restrictMap S) ∪ T.complImage S := by
      rw [T.range_union_complImage S]
      exact Set.mem_univ x
    rcases hx' with h | h
    · exact ⟨h, fun hs => hx (Or.inr hs)⟩
    · exact (hx (Or.inl h)).elim

theorem isOpen_range_diff_seamSurface
    (hother : ∀ k, k ≠ j → (T.leftPiece k ∈ S ↔ T.rightPiece k ∈ S)) :
    IsOpen (Set.range (T.restrictMap S) \ T.seamSurface j) := by
  rw [T.range_diff_seamSurface_eq S j hother]
  exact ((T.isClosed_complImage S).union (T.isClosed_seamSurface j)).isOpen_compl

private theorem snd_eq_zero_of_mem_seamSurface' {p : Torus × ℝ} (hp : p ∈ signedCollarSource)
    (h : T.seam j p ∈ T.seamSurface j) : p.2 = 0 := by
  obtain ⟨t, ht⟩ := h
  rw [← (T.seam j).toPartialEquiv.injOn
    (T.mem_seam_source j ⟨by norm_num, by norm_num⟩) (T.mem_seam_source j hp) ht]

theorem interior_range_restrictMap (hj' : T.rightPiece j ∉ S)
    (hother : ∀ k, k ≠ j → (T.leftPiece k ∈ S ↔ T.rightPiece k ∈ S)) :
    interior (Set.range (T.restrictMap S)) = Set.range (T.restrictMap S) \ T.seamSurface j := by
  refine Set.Subset.antisymm (fun x hx => ⟨interior_subset hx, fun hs => ?_⟩)
    (interior_maximal Set.sdiff_subset (T.isOpen_range_diff_seamSurface S j hother))
  obtain ⟨t, rfl⟩ := hs
  have hc : ContinuousAt (fun a : ℝ => T.seam j (t, a)) 0 :=
    ((T.continuousOn_seam j).continuousAt ((T.seam j).open_source.mem_nhds
      (T.mem_seam_source j ⟨by norm_num, by norm_num⟩))).comp
      (Continuous.prodMk_right t).continuousAt
  have hn := hc.preimage_mem_nhds (isOpen_interior.mem_nhds hx)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  set a := min (ε / 2) 2⁻¹ with ha
  have ha0 : 0 < a := lt_min (half_pos hε) (by norm_num)
  have ha1 : a < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have haε : a ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ha0]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hin : T.seam j (t, a) ∈ Set.range (T.restrictMap S) := interior_subset (hball haε)
  have hsurf := T.range_inter_complImage_subset S j hother
    ⟨hin, T.seam_mem_complImage S j hj' t ha0.le ha1⟩
  have := T.snd_eq_zero_of_mem_seamSurface' j
    ⟨lt_trans (by norm_num) ha0, ha1⟩ hsurf
  exact ha0.ne' this

theorem leftSide_eq_range_diff (hj : T.leftPiece j ∈ S)
    (hother : ∀ k, k ≠ j → (T.leftPiece k ∈ S ↔ T.rightPiece k ∈ S))
    (hconn : IsPreconnected (Set.range (T.restrictMap S) \ T.seamSurface j)) :
    T.leftSide j = Set.range (T.restrictMap S) \ T.seamSurface j := by
  refine Set.Subset.antisymm (fun x hx => ⟨T.leftSide_subset_range S j hj hother hx,
    pathComponentIn_subset hx⟩) ?_
  have := Manifold.locallyPathConnectedSpace_of_modelWithCorners (M := W.Carrier) W.model
  have hmem : T.leftPoint j ∈ Set.range (T.restrictMap S) \ T.seamSurface j :=
    ⟨T.leftPoint_mem_range S j hj, T.leftPoint_mem_compl j⟩
  have hpc := ((T.isOpen_range_diff_seamSurface S j hother).isConnected_iff_isPathConnected).mp
    ⟨⟨_, hmem⟩, hconn⟩
  exact hpc.subset_pathComponentIn hmem (Set.sdiff_subset_compl _ _)

theorem range_union_seamCollar_eq_leftRegion (hj : T.leftPiece j ∈ S)
    (hother : ∀ k, k ≠ j → (T.leftPiece k ∈ S ↔ T.rightPiece k ∈ S))
    (hconn : IsPreconnected (Set.range (T.restrictMap S) \ T.seamSurface j)) :
    Set.range (T.restrictMap S) ∪ T.seamCollar j = T.leftRegion j := by
  rw [leftRegion, T.leftSide_eq_range_diff S j hj hother hconn]
  ext x
  constructor
  · rintro (hx | hx)
    · by_cases hs : x ∈ T.seamSurface j
      · exact Or.inr (T.seamSurface_subset_seamCollar j hs)
      · exact Or.inl ⟨hx, hs⟩
    · exact Or.inr hx
  · rintro (hx | hx)
    · exact Or.inl hx.1
    · exact Or.inr hx

theorem interior_range_eq_leftSide (hj : T.leftPiece j ∈ S) (hj' : T.rightPiece j ∉ S)
    (hother : ∀ k, k ≠ j → (T.leftPiece k ∈ S ↔ T.rightPiece k ∈ S))
    (hconn : IsPreconnected (Set.range (T.restrictMap S) \ T.seamSurface j)) :
    interior (Set.range (T.restrictMap S)) = T.leftSide j := by
  rw [T.interior_range_restrictMap S j hj' hother, T.leftSide_eq_range_diff S j hj hother hconn]

end Side

end TorusPresentation

end GC.Seifert
