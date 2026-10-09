import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Contract
import Mathlib.Topology.LocalAtTarget

/-!
# Selected-seam contraction foundations

The selected pairing on the pieces of S glues exactly K. Its compact Hausdorff quotient
retains both sides of every omitted seam, including internal seams. The ambient fold is
continuous but need not be injective. This module constructs the compact Hausdorff quotient
foundations used by the boundary atlas and the final selected contraction presentation.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)
  (S : Finset (Fin T.components.count)) (K : Finset (Fin T.pairing.count))

def alongSeam (j : Fin K.card) : {k : Fin T.pairing.count // k ∈ K} :=
  K.orderIsoOfFin rfl j

theorem alongSeam_injective : Function.Injective (T.alongSeam K) :=
  (K.orderIsoOfFin rfl).injective

def alongKeptIndex (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (j : Fin K.card) : Fin (Fintype.card (T.KeptSeam S)) :=
  Fintype.equivFin (T.KeptSeam S)
    ⟨(T.alongSeam K j).val, hK (T.alongSeam K j).val (T.alongSeam K j).property⟩

theorem keptSeam_alongKeptIndex
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) (j : Fin K.card) :
    (T.keptSeam S (T.alongKeptIndex S K hK j)).val = (T.alongSeam K j).val := by
  rw [alongKeptIndex, keptSeam_equivFin]

theorem alongKeptIndex_injective
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) :
    Function.Injective (T.alongKeptIndex S K hK) := by
  intro i j hij
  apply T.alongSeam_injective K
  apply Subtype.ext
  have he := congrArg (fun n => (T.keptSeam S n).val) hij
  simpa only [keptSeam_alongKeptIndex] using he

def restrictAlongGluing
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) :
    BoundaryGluing (T.subCarrier S).Carrier (Fin K.card) where
  left j := (T.restrictGluing S).left (T.alongKeptIndex S K hK j)
  right j := (T.restrictGluing S).right (T.alongKeptIndex S K hK j)
  attaching j := (T.restrictGluing S).attaching (T.alongKeptIndex S K hK j)
  isClosed_left j := (T.restrictGluing S).isClosed_left (T.alongKeptIndex S K hK j)
  isClosed_right j := (T.restrictGluing S).isClosed_right (T.alongKeptIndex S K hK j)
  disjoint_left_right j :=
    (T.restrictGluing S).disjoint_left_right (T.alongKeptIndex S K hK j)
  disjoint_blocks i j hij := (T.restrictGluing S).disjoint_blocks
    (T.alongKeptIndex S K hK i) (T.alongKeptIndex S K hK j)
    (fun he => hij (T.alongKeptIndex_injective S K hK he))

def restrictAlongPairing
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) :
    TorusPairing (T.subCarrier S) where
  count := K.card
  gluing := T.restrictAlongGluing S K hK
  leftParam j := (T.restrictPairing S).leftParam (T.alongKeptIndex S K hK j)
  rightParam j := (T.restrictPairing S).rightParam (T.alongKeptIndex S K hK j)
  matching j := (T.restrictPairing S).matching (T.alongKeptIndex S K hK j)
  matching_eq j t := (T.restrictPairing S).matching_eq (T.alongKeptIndex S K hK j) t
  leftCollar j := (T.restrictPairing S).leftCollar (T.alongKeptIndex S K hK j)
  rightCollar j := (T.restrictPairing S).rightCollar (T.alongKeptIndex S K hK j)
  left_source j := (T.restrictPairing S).left_source (T.alongKeptIndex S K hK j)
  right_source j := (T.restrictPairing S).right_source (T.alongKeptIndex S K hK j)
  left_zero j t := (T.restrictPairing S).left_zero (T.alongKeptIndex S K hK j) t
  right_zero j t := (T.restrictPairing S).right_zero (T.alongKeptIndex S K hK j) t
  reversing j := (T.restrictPairing S).reversing (T.alongKeptIndex S K hK j)

theorem restrictAlong_rel_closed
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) :
    IsClosed {p : (T.subCarrier S).Carrier × (T.subCarrier S).Carrier |
      (T.restrictAlongGluing S K hK).rel p.1 p.2} :=
  (T.restrictAlongGluing S K hK).isClosed_setOf_rel

theorem restrictAlong_t2Space
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) :
    T2Space (T.restrictAlongPairing S K hK).QuotientSpace :=
  DifferentialGeometry.Topology.t2Space_quotient_of_isClosed_rel
    (T.restrictAlong_rel_closed S K hK)

theorem restrictAlong_compactSpace
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) :
    CompactSpace (T.restrictAlongPairing S K hK).QuotientSpace := inferInstance

theorem restrictAlongPairing_count
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) :
    (T.restrictAlongPairing S K hK).count = K.card := rfl

theorem restrictAlongGluing_flip
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) (j : Fin K.card)
    (x : (T.subCarrier S).Carrier) :
    (T.restrictAlongGluing S K hK).flip j x =
      (T.restrictGluing S).flip (T.alongKeptIndex S K hK j) x := rfl

theorem restrictAlongGluing_rel
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    {x y : (T.subCarrier S).Carrier} (h : (T.restrictAlongGluing S K hK).rel x y) :
    (T.restrictGluing S).rel x y := by
  rcases h with rfl | ⟨j, hx, hy⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨T.alongKeptIndex S K hK j, hx, hy⟩

def restrictAlongMap
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) :
    (T.restrictAlongPairing S K hK).QuotientSpace → W.Carrier :=
  Quotient.lift (fun x : (T.subCarrier S).Carrier => T.cutMap x.val)
    (fun x y h => show T.cutMap x.val = T.cutMap y.val from
      congrArg T.reconstruction (Quotient.sound'
        (T.restrictGluing_rel_val S (T.restrictAlongGluing_rel S K hK h))))

theorem restrictAlongMap_quotientMap
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (x : (T.subCarrier S).Carrier) :
    T.restrictAlongMap S K hK ((T.restrictAlongPairing S K hK).quotientMap x) =
      T.cutMap x.val := rfl

theorem continuous_restrictAlongMap
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) :
    Continuous (T.restrictAlongMap S K hK) :=
  continuous_quot_lift _ (T.reconstruction.continuous.comp
    (T.pairing.quotientMap.continuous.comp continuous_subtype_val))

theorem range_restrictAlongMap
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) :
    Set.range (T.restrictAlongMap S K hK) = Set.range (T.restrictMap S) := by
  rw [T.range_restrictMap S]
  ext w
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    exact ⟨x.val, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(T.restrictAlongPairing S K hK).quotientMap ⟨x, hx⟩, rfl⟩

abbrev AlongUnpairedSeam := {k : Fin T.pairing.count // k ∉ K}

theorem alongUnpairedSeam_card : Fintype.card (T.AlongUnpairedSeam K) =
    T.pairing.count - K.card := by
  classical
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype]
  simp

def alongPieceIndex (i : Fin T.components.count) : Fin (Sᶜ.card + 1) := by
  classical
  exact if hi : i ∈ S then Fin.last Sᶜ.card
    else (T.subIndexOf Sᶜ (Finset.mem_compl.mpr hi)).castSucc

theorem alongPieceIndex_of_mem {i : Fin T.components.count} (hi : i ∈ S) :
    T.alongPieceIndex S i = Fin.last Sᶜ.card := by
  classical
  simp [alongPieceIndex, hi]

theorem alongPieceIndex_internal {k : Fin T.pairing.count}
    (hl : T.leftPiece k ∈ S) (hr : T.rightPiece k ∈ S) :
    T.alongPieceIndex S (T.leftPiece k) = Fin.last Sᶜ.card ∧
      T.alongPieceIndex S (T.rightPiece k) = Fin.last Sᶜ.card :=
  ⟨T.alongPieceIndex_of_mem S hl, T.alongPieceIndex_of_mem S hr⟩

theorem alongPieceIndex_count : Sᶜ.card + 1 = T.components.count - S.card + 1 := by
  rw [Finset.card_compl, Fintype.card_fin]

theorem restrictAlongGluing_block_val
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (j : Fin K.card) (x : (T.subCarrier S).Carrier) :
    x ∈ (T.restrictAlongGluing S K hK).block j ↔
      x.val ∈ T.pairing.gluing.block (T.alongSeam K j).val := by
  change x.val ∈ T.pairing.gluing.block
    (T.keptSeam S (T.alongKeptIndex S K hK j)).val ↔ _
  rw [keptSeam_alongKeptIndex]

theorem restrictAlong_quotientMap_inj_of_omitted_block
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    {k : Fin T.pairing.count} (hk : k ∉ K) {x y : (T.subCarrier S).Carrier}
    (hx : x.val ∈ T.pairing.gluing.block k)
    (he : (T.restrictAlongPairing S K hK).quotientMap x =
      (T.restrictAlongPairing S K hK).quotientMap y) : x = y := by
  apply (T.restrictAlongGluing S K hK).eq_of_rel_of_notMem
    (fun j hj => ?_) (Quotient.exact he)
  have hblock := (T.restrictAlongGluing_block_val S K hK j x).mp hj
  have heq := T.block_unique hx hblock
  exact hk (heq ▸ (T.alongSeam K j).property)

def alongOmittedLeft (k : Fin T.pairing.count) (hl : T.leftPiece k ∈ S)
    (t : Torus) : (T.subCarrier S).Carrier :=
  ⟨(T.pairing.leftParam k t).val,
    T.piece_subset_subPiece S hl (T.left_owned k (T.pairing.leftParam k t).property)⟩

def alongOmittedRight (k : Fin T.pairing.count) (hr : T.rightPiece k ∈ S)
    (t : Torus) : (T.subCarrier S).Carrier :=
  ⟨(T.pairing.rightParam k t).val,
    T.piece_subset_subPiece S hr (T.right_owned k (T.pairing.rightParam k t).property)⟩

theorem alongOmittedSides_distinct
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    {k : Fin T.pairing.count} (hk : k ∉ K)
    (hl : T.leftPiece k ∈ S) (hr : T.rightPiece k ∈ S) (t t' : Torus) :
    (T.restrictAlongPairing S K hK).quotientMap (T.alongOmittedLeft S k hl t) ≠
      (T.restrictAlongPairing S K hK).quotientMap (T.alongOmittedRight S k hr t') := by
  intro he
  have hxy := T.restrictAlong_quotientMap_inj_of_omitted_block S K hK hk
    (Or.inl (T.pairing.leftParam k t).property) he
  have hval := congrArg Subtype.val hxy
  exact (T.pairing.gluing.disjoint_left_right k).le_bot
    ⟨(T.pairing.leftParam k t).property, hval ▸ (T.pairing.rightParam k t').property⟩

theorem restrictAlongMap_not_injective_of_omitted_internal
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    {k : Fin T.pairing.count} (hk : k ∉ K)
    (hl : T.leftPiece k ∈ S) (hr : T.rightPiece k ∈ S) :
    ¬ Function.Injective (T.restrictAlongMap S K hK) := by
  intro hinj
  apply T.alongOmittedSides_distinct S K hK hk hl hr (1 : Torus) (T.pairing.matching k 1)
  apply hinj
  change T.cutMap (T.pairing.leftParam k 1).val =
    T.cutMap (T.pairing.rightParam k (T.pairing.matching k 1)).val
  rw [← T.seamTorus_eq_cutMap k 1, ← T.seamTorus_eq_cutMap_right k 1]

instance restrictAlongQuotient_compact
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) :
    CompactSpace (T.restrictAlongPairing S K hK).QuotientSpace := inferInstance

instance restrictAlongQuotient_t2
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) :
    T2Space (T.restrictAlongPairing S K hK).QuotientSpace := inferInstance

abbrev AlongBoundarySide :=
  {s : T.Side // T.sidePiece s ∈ S ∧
    match s with
    | .inl k => k ∉ K
    | .inr (.inl k) => k ∉ K
    | .inr (.inr i) => i ∈ Finset.univ}

instance alongBoundarySide_fintype : Fintype (T.AlongBoundarySide S K) := by
  classical
  exact Fintype.ofFinite (T.AlongBoundarySide S K)

def alongBoundarySide (j : Fin (Fintype.card (T.AlongBoundarySide S K))) :
    T.AlongBoundarySide S K := (Fintype.equivFin (T.AlongBoundarySide S K)).symm j

def restrictAlongBoundaryTori :
    BoundaryTori (T.subCarrier S) (Fintype.card (T.AlongBoundarySide S K)) where
  collar j := T.subCollar S (T.alongBoundarySide S K j).val
    (T.alongBoundarySide S K j).property.1
  source_eq j := T.subCollar_source S (T.alongBoundarySide S K j).val
    (T.alongBoundarySide S K j).property.1
  boundary_zero j t := by
    refine (ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val (I := T.cutCarrier.model)
      (u := T.subPiece S)).mpr ?_
    rw [T.subCollar_apply S (T.alongBoundarySide S K j).val
      (T.alongBoundarySide S K j).property.1 (zero_mem_halfCollarSource t)]
    exact (T.sideCollar_zero_mem (T.alongBoundarySide S K j).val t).1
  disjoint i j hij := by
    change Disjoint (T.subCollar S (T.alongBoundarySide S K i).val
      (T.alongBoundarySide S K i).property.1).target
      (T.subCollar S (T.alongBoundarySide S K j).val
        (T.alongBoundarySide S K j).property.1).target
    rw [T.subCollar_target, T.subCollar_target]
    exact (T.sideCollar_disjoint (fun he => hij
      ((Fintype.equivFin (T.AlongBoundarySide S K)).symm.injective
        (Subtype.ext he)))).preimage Subtype.val

theorem restrictAlongBoundaryTori_collar_apply
    (j : Fin (Fintype.card (T.AlongBoundarySide S K)))
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    ((T.restrictAlongBoundaryTori S K).collar j p).val =
      T.sideCollar (T.alongBoundarySide S K j).val p :=
  T.subCollar_apply S (T.alongBoundarySide S K j).val
    (T.alongBoundarySide S K j).property.1 hp

theorem alongSeam_surjective : Function.Surjective (T.alongSeam K) :=
  (K.orderIsoOfFin rfl).surjective

theorem restrictAlongGluing_rel_of_all
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hAll : ∀ k, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S → k ∈ K)
    {x y : (T.subCarrier S).Carrier} (h : (T.restrictGluing S).rel x y) :
    (T.restrictAlongGluing S K hK).rel x y := by
  rcases h with rfl | ⟨j, hx, hy⟩
  · exact Or.inl rfl
  · obtain ⟨n, hn⟩ := T.alongSeam_surjective K
      ⟨(T.keptSeam S j).val, hAll (T.keptSeam S j).val (T.keptSeam S j).property⟩
    have hi : T.alongKeptIndex S K hK n = j := by
      apply (Fintype.equivFin (T.KeptSeam S)).symm.injective
      apply Subtype.ext
      change (T.keptSeam S (T.alongKeptIndex S K hK n)).val = (T.keptSeam S j).val
      rw [keptSeam_alongKeptIndex]
      exact congrArg Subtype.val hn
    refine Or.inr ⟨n, ?_, ?_⟩
    · change x ∈ (T.restrictGluing S).block (T.alongKeptIndex S K hK n)
      rwa [hi]
    · rw [restrictAlongGluing_flip, hi]
      exact hy

theorem restrictAlongMap_injective_of_all
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hAll : ∀ k, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S → k ∈ K) :
    Function.Injective (T.restrictAlongMap S K hK) := by
  intro q r he
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  obtain ⟨y, rfl⟩ := Quotient.exists_rep r
  apply Quotient.sound
  apply T.restrictAlongGluing_rel_of_all S K hK hAll
  apply T.restrictGluing_rel_of_val S
  exact Quotient.exact (T.reconstruction.injective he)

theorem restrictAlongMap_injective_iff_all
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) :
    Function.Injective (T.restrictAlongMap S K hK) ↔
      ∀ k, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S → k ∈ K := by
  constructor
  · intro hinj k hInt
    by_contra hk
    exact T.restrictAlongMap_not_injective_of_omitted_internal S K hK hk hInt.1 hInt.2 hinj
  · exact T.restrictAlongMap_injective_of_all S K hK

def restrictAlongHomeomorph_of_all
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hAll : ∀ k, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S → k ∈ K) :
    (T.restrictAlongPairing S K hK).QuotientSpace ≃ₜ Set.range (T.restrictMap S) :=
  ((T.continuous_restrictAlongMap S K hK).isClosedEmbedding
    (T.restrictAlongMap_injective_of_all S K hK hAll)).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (T.range_restrictAlongMap S K hK))

theorem alongBoundarySide_equivFin (a : T.AlongBoundarySide S K) :
    T.alongBoundarySide S K (Fintype.equivFin (T.AlongBoundarySide S K) a) = a :=
  (Fintype.equivFin (T.AlongBoundarySide S K)).symm_apply_apply a

theorem subCarrier_boundary_along
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) :
    (T.subCarrier S).model.boundary (T.subCarrier S).Carrier =
      (⋃ j, (T.restrictAlongPairing S K hK).gluing.block j) ∪
        (T.restrictAlongBoundaryTori S K).image := by
  classical
  ext x
  constructor
  · intro hx
    have hb : T.cutCarrier.model.IsBoundaryPoint x.val :=
      (ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val (I := T.cutCarrier.model)
        (u := T.subPiece S)).mp hx
    obtain ⟨s, t, hst⟩ := T.exists_sideCollar_zero_eq hb
    have hs : T.sidePiece s ∈ S :=
      T.mem_of_mem_subPiece S x.property (hst ▸ (T.sideCollar_zero_mem s t).2)
    have omitted (s' : T.Side)
        (hn : match s' with
          | .inl k => k ∉ K
          | .inr (.inl k) => k ∉ K
          | .inr (.inr i) => i ∈ Finset.univ)
        (hs' : T.sidePiece s' ∈ S) (he : T.sideCollar s' (t, halfZero) = x.val) :
        x ∈ (T.restrictAlongBoundaryTori S K).image := by
      let a : T.AlongBoundarySide S K := ⟨s', hs', hn⟩
      refine Set.mem_iUnion.mpr ⟨Fintype.equivFin (T.AlongBoundarySide S K) a, t, ?_⟩
      apply Subtype.ext
      change ((T.restrictAlongBoundaryTori S K).collar
        (Fintype.equivFin (T.AlongBoundarySide S K) a) (t, halfZero)).val = x.val
      rw [T.restrictAlongBoundaryTori_collar_apply S K
        (Fintype.equivFin (T.AlongBoundarySide S K) a) (zero_mem_halfCollarSource t),
        alongBoundarySide_equivFin]
      exact he
    rcases s with k | k | i
    · by_cases hk : k ∈ K
      · obtain ⟨j, hj⟩ := T.alongSeam_surjective K ⟨k, hk⟩
        refine Or.inl (Set.mem_iUnion.mpr ⟨j, ?_⟩)
        apply (T.restrictAlongGluing_block_val S K hK j x).mpr
        rw [congrArg Subtype.val hj]
        left
        rw [← hst]
        exact (T.pairing.left_zero k t) ▸ (T.pairing.leftParam k t).property
      · exact Or.inr (omitted (.inl k) hk hs hst)
    · by_cases hk : k ∈ K
      · obtain ⟨j, hj⟩ := T.alongSeam_surjective K ⟨k, hk⟩
        refine Or.inl (Set.mem_iUnion.mpr ⟨j, ?_⟩)
        apply (T.restrictAlongGluing_block_val S K hK j x).mpr
        rw [congrArg Subtype.val hj]
        right
        rw [← hst]
        exact (T.pairing.right_zero k t) ▸ (T.pairing.rightParam k t).property
      · exact Or.inr (omitted (.inr (.inl k)) hk hs hst)
    · exact Or.inr (omitted (.inr (.inr i)) (Finset.mem_univ i) hs hst)
  · rintro (hx | hx)
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      apply (ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val
        (I := T.cutCarrier.model) (u := T.subPiece S)).mpr
      change x.val ∈ T.cutCarrier.model.boundary T.cutCarrier.Carrier
      rw [T.cut_boundary_exhausted]
      exact Or.inl (Set.mem_iUnion.mpr
        ⟨(T.alongSeam K j).val, (T.restrictAlongGluing_block_val S K hK j x).mp hj⟩)
    · obtain ⟨j, t, rfl⟩ := Set.mem_iUnion.mp hx
      exact (T.restrictAlongBoundaryTori S K).boundary_zero j t

theorem isOpenEmbedding_restrictAlong_quotientMap
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (U : TopologicalSpace.Opens (T.subCarrier S).Carrier)
    (hU : ∀ x ∈ U, ∀ j, x ∉ (T.restrictAlongGluing S K hK).block j) :
    _root_.Topology.IsOpenEmbedding
      (fun x : U => (T.restrictAlongPairing S K hK).quotientMap x.val) := by
  apply _root_.Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact (T.restrictAlongPairing S K hK).quotientMap.continuous.comp continuous_subtype_val
  · intro x y hxy
    apply Subtype.ext
    exact (T.restrictAlongGluing S K hK).eq_of_rel_of_notMem
      (hU x.val x.property) (Quotient.exact hxy)
  · intro A hA
    have ho : IsOpen (Subtype.val '' A : Set (T.subCarrier S).Carrier) :=
      U.isOpen.isOpenMap_subtype_val A hA
    have hsat : ∀ x y, (T.restrictAlongGluing S K hK).setoid x y →
        (x ∈ Subtype.val '' A ↔ y ∈ Subtype.val '' A) := by
      intro x y hxy
      constructor
      · rintro ⟨z, hz, rfl⟩
        have he := (T.restrictAlongGluing S K hK).eq_of_rel_of_notMem
          (hU z.val z.property) hxy
        exact ⟨z, hz, he⟩
      · rintro ⟨z, hz, rfl⟩
        have he := (T.restrictAlongGluing S K hK).eq_of_rel_of_notMem
          (hU z.val z.property) ((T.restrictAlongGluing S K hK).setoid.symm hxy)
        exact ⟨z, hz, he⟩
    have hopen := isOpen_quotient_mk_image_of_saturated hsat ho
    change IsOpen ((fun x : U =>
      @Quotient.mk' _ (T.restrictAlongGluing S K hK).setoid x.val) '' A)
    simpa only [Set.image_image, Function.comp_def] using hopen

private theorem alongCutMap_mem_seamSurface {k : Fin T.pairing.count}
    {x : T.cutCarrier.Carrier} (hx : x ∈ T.pairing.gluing.block k) :
    T.cutMap x ∈ T.seamSurface k := by
  rcases hx with hx | hx
  · refine ⟨(T.pairing.leftParam k).symm ⟨x, hx⟩, ?_⟩
    rw [seamTorus_eq_cutMap, Homeomorph.apply_symm_apply]
  · refine ⟨(T.pairing.matching k).symm ((T.pairing.rightParam k).symm ⟨x, hx⟩), ?_⟩
    rw [seamTorus_eq_cutMap_right, Diffeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

theorem restrictAlongMap_injOn_seamCollar
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    {k : Fin T.pairing.count} (hk : k ∈ K) :
    Set.InjOn (T.restrictAlongMap S K hK)
      ((T.restrictAlongMap S K hK) ⁻¹' (T.seam k).target) := by
  intro q hq r hr he
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  obtain ⟨y, rfl⟩ := Quotient.exists_rep r
  apply Quotient.sound
  rcases Quotient.exact (T.reconstruction.injective he) with hxy | ⟨j, hxj, hyj⟩
  · exact Or.inl (Subtype.ext hxy)
  · have hsurf := T.alongCutMap_mem_seamSurface hxj
    have hjk : j = k := by
      by_contra hne
      exact (T.seam_disjoint hne).le_bot
        ⟨T.seamSurface_subset_seamCollar j hsurf, hq⟩
    subst j
    obtain ⟨i, hi⟩ := T.alongSeam_surjective K ⟨k, hk⟩
    have hib : x ∈ (T.restrictAlongGluing S K hK).block i := by
      apply (T.restrictAlongGluing_block_val S K hK i x).mpr
      rw [congrArg Subtype.val hi]
      exact hxj
    refine Or.inr ⟨i, hib, ?_⟩
    apply Subtype.ext
    change y.val = ((T.restrictAlongGluing S K hK).flip i x).val
    have hf := T.restrictGluing_flip_val S (T.alongKeptIndex S K hK i) x
    rw [keptSeam_alongKeptIndex, congrArg Subtype.val hi] at hf
    exact hyj.trans hf.symm

def restrictAlongSeamHomeomorph
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    {k : Fin T.pairing.count} (hk : k ∈ K) :
    ((T.restrictAlongMap S K hK) ⁻¹' (T.seam k).target) ≃ₜ (T.seam k).target := by
  let f := T.restrictAlongMap S K hK
  let U := (T.seam k).target
  have hinj : Function.Injective (U.restrictPreimage f) := by
    intro q r he
    apply Subtype.ext
    exact T.restrictAlongMap_injOn_seamCollar S K hK hk q.property r.property
      (congrArg Subtype.val he)
  have hsurj : Function.Surjective (U.restrictPreimage f) := by
    intro y
    obtain ⟨j, hj⟩ := T.alongSeam_surjective K ⟨k, hk⟩
    have hkept := T.seam_target_subset_range_restrictMap S (T.alongKeptIndex S K hK j)
    rw [keptSeam_alongKeptIndex, congrArg Subtype.val hj] at hkept
    have hy := hkept y.property
    rw [← T.range_restrictAlongMap S K hK] at hy
    obtain ⟨q, hq⟩ := hy
    refine ⟨⟨q, ?_⟩, Subtype.ext hq⟩
    change T.restrictAlongMap S K hK q ∈ U
    rw [hq]
    exact y.property
  exact (Equiv.ofBijective (U.restrictPreimage f) ⟨hinj, hsurj⟩).toHomeomorphOfContinuousClosed
    (T.continuous_restrictAlongMap S K hK).restrictPreimage
      ((T.continuous_restrictAlongMap S K hK).isClosedMap.restrictPreimage U)

theorem alongBoundaryCollar_avoids_selected
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (a : T.AlongBoundarySide S K) {x : (T.subCarrier S).Carrier}
    (hx : x.val ∈ (T.sideCollar a.val).target) (j : Fin K.card) :
    x ∉ (T.restrictAlongGluing S K hK).block j := by
  intro hj
  have hb := (T.restrictAlongGluing_block_val S K hK j x).mp hj
  have hnleft : a.val ≠ .inl (T.alongSeam K j).val := by
    intro he
    have hn := a.property.2
    rw [he] at hn
    exact hn (T.alongSeam K j).property
  have hnright : a.val ≠ .inr (.inl (T.alongSeam K j).val) := by
    intro he
    have hn := a.property.2
    rw [he] at hn
    exact hn (T.alongSeam K j).property
  rcases hb with hl | hr
  · exact (T.sideCollar_disjoint hnleft).le_bot
      ⟨hx, T.left_subset_leftCollar_target (T.alongSeam K j).val hl⟩
  · exact (T.sideCollar_disjoint hnright).le_bot
      ⟨hx, T.right_subset_rightCollar_target (T.alongSeam K j).val hr⟩

theorem isOpenEmbedding_alongBoundaryCollar
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (a : T.AlongBoundarySide S K) :
    _root_.Topology.IsOpenEmbedding
      (fun x : ((T.subCollar S a.val a.property.1).target) =>
        (T.restrictAlongPairing S K hK).quotientMap x.val) := by
  apply T.isOpenEmbedding_restrictAlong_quotientMap S K hK
    ⟨(T.subCollar S a.val a.property.1).target,
      (T.subCollar S a.val a.property.1).open_target⟩
  intro x hx j
  apply T.alongBoundaryCollar_avoids_selected S K hK a
  have ht := congrArg (fun A : Set (T.subCarrier S).Carrier => x ∈ A)
    (T.subCollar_target S a.val a.property.1)
  exact ht.mp hx

def alongOmittedSurface : Set W.Carrier := ⋃ k ∈ Kᶜ, T.seamSurface k

def alongInteriorRange : Set W.Carrier :=
  (Set.range (T.restrictMap S) \ T.crossingSurface S) \ T.alongOmittedSurface K

theorem isOpen_alongInteriorRange : IsOpen (T.alongInteriorRange S K) := by
  classical
  exact (T.isOpen_range_diff_crossingSurface S).sdiff
    (isClosed_biUnion_finset (fun k hk => T.isClosed_seamSurface k))

theorem restrictAlongMap_injOn_away_omitted
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) :
    Set.InjOn (T.restrictAlongMap S K hK)
      ((T.restrictAlongMap S K hK) ⁻¹' (T.alongOmittedSurface K)ᶜ) := by
  classical
  intro q hq r hr he
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  obtain ⟨y, rfl⟩ := Quotient.exists_rep r
  apply Quotient.sound
  rcases Quotient.exact (T.reconstruction.injective he) with hxy | ⟨k, hxk, hyk⟩
  · exact Or.inl (Subtype.ext hxy)
  · have hk : k ∈ K := by
      by_contra hnot
      exact hq (Set.mem_iUnion₂.mpr ⟨k, Finset.mem_compl.mpr hnot,
        T.alongCutMap_mem_seamSurface hxk⟩)
    obtain ⟨i, hi⟩ := T.alongSeam_surjective K ⟨k, hk⟩
    have hib : x ∈ (T.restrictAlongGluing S K hK).block i := by
      apply (T.restrictAlongGluing_block_val S K hK i x).mpr
      rw [congrArg Subtype.val hi]
      exact hxk
    refine Or.inr ⟨i, hib, ?_⟩
    apply Subtype.ext
    have hf := T.restrictGluing_flip_val S (T.alongKeptIndex S K hK i) x
    rw [keptSeam_alongKeptIndex, congrArg Subtype.val hi] at hf
    exact hyk.trans hf.symm

def restrictAlongInteriorHomeomorph
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) :
    ((T.restrictAlongMap S K hK) ⁻¹' T.alongInteriorRange S K) ≃ₜ
      T.alongInteriorRange S K := by
  let f := T.restrictAlongMap S K hK
  let U := T.alongInteriorRange S K
  have hinj : Function.Injective (U.restrictPreimage f) := by
    intro q r he
    apply Subtype.ext
    exact T.restrictAlongMap_injOn_away_omitted S K hK q.property.2 r.property.2
      (congrArg Subtype.val he)
  have hsurj : Function.Surjective (U.restrictPreimage f) := by
    intro y
    have hy := y.property.1.1
    rw [← T.range_restrictAlongMap S K hK] at hy
    obtain ⟨q, hq⟩ := hy
    refine ⟨⟨q, ?_⟩, Subtype.ext hq⟩
    change T.restrictAlongMap S K hK q ∈ U
    rw [hq]
    exact y.property
  exact (Equiv.ofBijective (U.restrictPreimage f) ⟨hinj, hsurj⟩).toHomeomorphOfContinuousClosed
    (T.continuous_restrictAlongMap S K hK).restrictPreimage
      ((T.continuous_restrictAlongMap S K hK).isClosedMap.restrictPreimage U)

theorem alongMem_block_of_cutMap_mem_seamSurface {k : Fin T.pairing.count}
    {x : T.cutCarrier.Carrier} (hx : T.cutMap x ∈ T.seamSurface k) :
    x ∈ T.pairing.gluing.block k := by
  obtain ⟨t, ht⟩ := hx
  rw [seamTorus_eq_cutMap] at ht
  rcases Quotient.exact (T.reconstruction.injective ht) with he | ⟨j, hj, hxj⟩
  · exact Or.inl (he ▸ (T.pairing.leftParam k t).property)
  · have hb := T.pairing.gluing.flip_mem_block hj
    have hk : k = j := (T.block_unique (k := k) (k' := j)
      (Or.inl (T.pairing.leftParam k t).property) hj).symm
    subst j
    exact hxj ▸ hb

theorem crossingSurface_subset_alongOmittedSurface
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) :
    T.crossingSurface S ⊆ T.alongOmittedSurface K := by
  classical
  intro w hw
  obtain ⟨k, hk, hs⟩ := Set.mem_iUnion₂.mp hw
  have hnot : k ∉ K := by
    intro hmem
    rcases hk with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · exact hr (hK k hmem).2
    · exact hl (hK k hmem).1
  exact Set.mem_iUnion₂.mpr ⟨k, Finset.mem_compl.mpr hnot, hs⟩

end GC.Seifert.TorusPresentation
