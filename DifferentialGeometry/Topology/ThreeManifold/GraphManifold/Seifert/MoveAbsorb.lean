import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Normalize
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Contract

/-!
# The absorb move M3 of the (S⁺) normalization

Lane N3, for `MoveAbsorb` of `Seifert/Normalize.lean`. An absorb seam `j` with side `b` joins a
solid torus `V = seamPiece j b` to an annulus piece `A = hostPiece j b`. The presentation
surgery is the contraction of P2a (`Seifert/Contract.lean`) along `seamPair j = {V, A}`, whose
three side conditions are discharged here. The cut carrier has boundary as soon as there is a
seam (`cutCarrier_kind_of_pos`). The pieces own no external torus (automatic on a closed
carrier). The region interior is connected (`isConnected_region_seamPair`): it is the union of
the images of the piece interiors of `V` and `A` and of the open collar of `j`, which meets both
(`isInteriorPoint_sideCollar_pairSide`), as soon as `j` is the only seam with both sides in the
pair. For an absorb seam this holds by counting ports (`IsAbsorbSeam.eq_of_internal`): `V`
owns one side and `A` two, so a second internal seam would give `A` three sides.

So `absorbContraction` is a torus presentation of the same carrier with one seam fewer
(`absorbContraction_pairing_count`) and one piece fewer (`absorbContraction_components_count`).
Its seams are the old seams other than `j` (`absorbSeamEquiv`), with the same seam charts and
matchings (`absorbContraction_seam`, `absorbContraction_matching`). The merged piece is the last
one (`absorbLast`) and owns exactly one side, the crossing side of the other port of `A`
(`absorbContraction_card_ownedSide_last`, through the lift `contractLiftSide` of the contracted
sides). `absorbPresentation` is the closed case.

The merged piece does not in general inherit a `SolidTorusPiece` from the contracted collar.
`ProductFibredPiece.collar_eq` is an equality on the whole half collar. If the distance between
the meridian of `V` and the fibre of `A` is not `1`, the fibres of any product structure wind
around the annulus near that port. This is impossible when the annulus collar accumulates on a
continuum carrying no essential loop, such as a Warsaw circle. So the presentation has to be
recollared, and tier 3 is stated conditionally.
`moveAbsorb_of_absorbContractionElementary` derives `MoveAbsorb` from the single named input
`AbsorbContractionElementary` (the absorb contraction admits an elementary presentation of the
same carrier with as many seams). That input follows from two finer ones
(`absorbContractionElementary_of_mergedSolidTorus_of_contractionRecollar`).
`MergedSolidTorus` is the geometric core: the merged piece is diffeomorphic to the solid torus
`V`, since a solid torus with a collar `T² × I` glued to its boundary is a solid torus.
`ContractionRecollar` is presentation bookkeeping shared with the merge move. A contraction of
an elementary presentation whose merged piece is a product over a planar base with as many
boundary circles as it owns sides admits an elementary presentation with the same seam count.
Its proof is collar straightening, shrinking and reparametrizing the seams.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

theorem kind_eq_withBoundary_of_isBoundaryPoint {C : CompactCarrier.{u}} {x : C.Carrier}
    (hx : C.model.IsBoundaryPoint x) : C.kind = .withBoundary := by
  cases C with
  | mk k X =>
    cases k with
    | closed =>
      exact absurd hx ((ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint _).mp
        BoundarylessManifold.isInteriorPoint)
    | withBoundary => rfl

namespace TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)

theorem cutCarrier_kind_of_pos (h : 0 < T.pairing.count) :
    T.cutCarrier.kind = .withBoundary := by
  refine kind_eq_withBoundary_of_isBoundaryPoint (x := (T.pairing.leftParam ⟨0, h⟩ 1).val) ?_
  have hb : (T.pairing.leftParam ⟨0, h⟩ 1).val ∈
      T.cutCarrier.model.boundary T.cutCarrier.Carrier := by
    rw [T.cut_boundary_exhausted]
    exact Or.inl (Set.mem_iUnion.mpr ⟨⟨0, h⟩, Or.inl (T.pairing.leftParam ⟨0, h⟩ 1).property⟩)
  exact hb

def pairSide (j : Fin T.pairing.count) : Bool → T.Side
  | true => .inl j
  | false => .inr (.inl j)

theorem pairSide_ne_not (j : Fin T.pairing.count) (b : Bool) :
    T.pairSide j b ≠ T.pairSide j !b := by
  cases b <;> simp [pairSide]

theorem pairSide_ne_of_ne {j k : Fin T.pairing.count} (h : j ≠ k) (b c : Bool) :
    T.pairSide j b ≠ T.pairSide k c := by
  cases b <;> cases c <;> simp [pairSide, h]

theorem cutMap_mem_seamSurface_block {k : Fin T.pairing.count}
    {x : T.cutCarrier.Carrier} (hx : x ∈ T.pairing.gluing.block k) :
    T.cutMap x ∈ T.seamSurface k := by
  rcases hx with hx | hx
  · refine ⟨(T.pairing.leftParam k).symm ⟨x, hx⟩, ?_⟩
    rw [seamTorus_eq_cutMap, Homeomorph.apply_symm_apply]
  · refine ⟨(T.pairing.matching k).symm ((T.pairing.rightParam k).symm ⟨x, hx⟩), ?_⟩
    rw [seamTorus_eq_cutMap_right, Diffeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

theorem eq_of_cutMap_eq_of_interior {y x : T.cutCarrier.Carrier}
    (hy : T.cutCarrier.model.IsInteriorPoint y) (h : T.cutMap y = T.cutMap x) : y = x := by
  refine T.pairing.gluing.eq_of_rel_of_notMem (fun i hi => ?_)
    (Quotient.exact (T.reconstruction.injective h))
  have hb : y ∈ T.cutCarrier.model.boundary T.cutCarrier.Carrier := by
    rw [T.cut_boundary_exhausted]
    exact Or.inl (Set.mem_iUnion.mpr ⟨i, hi⟩)
  exact (T.cutCarrier.model.isInteriorPoint_iff_not_isBoundaryPoint y).mp hy hb

theorem cutMap_sideCollar_pairSide (j : Fin T.pairing.count) (b : Bool)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    ∃ t, T.cutMap (T.sideCollar (T.pairSide j b) p) =
      T.seam j (t, if b then -(p.2.val 0) else p.2.val 0) := by
  cases b
  · exact ⟨_, T.cutMap_rightCollar j hp⟩
  · exact ⟨_, T.cutMap_leftCollar j hp⟩

theorem isInteriorPoint_sideCollar_pairSide (j : Fin T.pairing.count) (b : Bool)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) (hpos : 0 < p.2.val 0) :
    T.cutCarrier.model.IsInteriorPoint (T.sideCollar (T.pairSide j b) p) := by
  obtain ⟨t, ht⟩ := T.cutMap_sideCollar_pairSide j b hp
  have hp1 : p.2.val 0 < 1 := hp
  have hq : (t, if b then -(p.2.val 0) else p.2.val 0) ∈ signedCollarSource := by
    cases b <;> constructor <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  have hne : (if b then -(p.2.val 0) else p.2.val 0) ≠ 0 := by
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> intro h0 <;> linarith
  have hmem : T.seam j (t, if b then -(p.2.val 0) else p.2.val 0) ∈ (T.seam j).target :=
    (T.seam j).map_source' (T.mem_seam_source j hq)
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint]
  intro hb
  have hb' : T.sideCollar (T.pairSide j b) p ∈
      T.cutCarrier.model.boundary T.cutCarrier.Carrier := hb
  rw [T.cut_boundary_exhausted] at hb'
  rcases hb' with hb' | hb'
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hb'
    have hs := T.cutMap_mem_seamSurface_block hk
    rw [ht] at hs
    by_cases hkj : k = j
    · subst hkj
      obtain ⟨t', ht'⟩ := hs
      have he := (T.seam k).toPartialEquiv.injOn
        (T.mem_seam_source k (show (t', (0 : ℝ)) ∈ signedCollarSource from
          ⟨by norm_num, by norm_num⟩)) (T.mem_seam_source k hq) ht'
      exact hne (congrArg Prod.snd he).symm
    · exact (T.seam_disjoint hkj).le_bot ⟨T.seamSurface_subset_seamCollar k hs, hmem⟩
  · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hb'
    obtain ⟨t', ht'⟩ := he
    have hx : T.cutMap (T.sideCollar (T.pairSide j b) p) ∈ (T.external.collar e).target := by
      rw [← ht']
      change T.reconstruction (T.pairing.quotientMap (T.cutExternal.collar e (t', halfZero))) ∈ _
      rw [T.marked_collar e _ (zero_mem_halfCollarSource t')]
      exact (T.external.collar e).map_source' ((T.external.source_eq e).symm ▸
        zero_mem_halfCollarSource t')
    rw [ht] at hx
    exact (T.external_seam_disjoint e j).le_bot ⟨hx, hmem⟩

def seamPair (j : Fin T.pairing.count) : Finset (Fin T.components.count) :=
  {T.leftPiece j, T.rightPiece j}

theorem left_mem_seamPair (j : Fin T.pairing.count) : T.leftPiece j ∈ T.seamPair j :=
  Finset.mem_insert_self _ _

theorem right_mem_seamPair (j : Fin T.pairing.count) : T.rightPiece j ∈ T.seamPair j :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem eq_or_eq_of_mem_seamPair {j : Fin T.pairing.count} {i : Fin T.components.count}
    (hi : i ∈ T.seamPair j) : i = T.leftPiece j ∨ i = T.rightPiece j := by
  simpa only [seamPair, Finset.mem_insert, Finset.mem_singleton] using hi

theorem not_isCrossing_seamPair (j : Fin T.pairing.count) : ¬ T.IsCrossing (T.seamPair j) j := by
  rintro (⟨-, h⟩ | ⟨-, h⟩)
  · exact h (T.right_mem_seamPair j)
  · exact h (T.left_mem_seamPair j)

theorem cutMap_pieceInterior_subset_region (S : Finset (Fin T.components.count))
    {i : Fin T.components.count} (hi : i ∈ S) :
    T.cutMap '' (T.cutCarrier.pieceInterior (T.components.piece i) : Set T.cutCarrier.Carrier) ⊆
      Set.range (T.restrictMap S) \ T.crossingSurface S := by
  intro y hy
  obtain ⟨x, ⟨hxi, hx⟩, rfl⟩ := hy
  refine ⟨?_, fun hc => ?_⟩
  · rw [range_restrictMap]
    exact ⟨x, T.piece_subset_subPiece S hi hxi, rfl⟩
  · obtain ⟨k, -, t, ht⟩ := Set.mem_iUnion₂.mp hc
    rw [seamTorus_eq_cutMap] at ht
    have he := T.eq_of_cutMap_eq_of_interior hx ht.symm
    apply (T.cutCarrier.model.isInteriorPoint_iff_not_isBoundaryPoint x).mp hx
    change x ∈ T.cutCarrier.model.boundary T.cutCarrier.Carrier
    rw [T.cut_boundary_exhausted, he]
    exact Or.inl (Set.mem_iUnion.mpr ⟨k, Or.inl (T.pairing.leftParam k t).property⟩)

theorem seamCollar_subset_region (j : Fin T.pairing.count) :
    T.seamCollar j ⊆
      Set.range (T.restrictMap (T.seamPair j)) \ T.crossingSurface (T.seamPair j) := by
  intro y hy
  have hq : (T.seam j).symm y ∈ signedCollarSource := T.seam_source j ▸ (T.seam j).map_target' hy
  have hyq : T.seam j ((T.seam j).symm y) = y := (T.seam j).right_inv' hy
  refine ⟨?_, fun hc => ?_⟩
  · rw [← hyq]
    rcases le_total ((T.seam j).symm y).2 0 with h | h
    · exact T.seam_mem_range_of_nonpos _ j (T.left_mem_seamPair j) hq h
    · exact T.seam_mem_range_of_nonneg _ j (T.right_mem_seamPair j) hq h
  · obtain ⟨k, hk, hs⟩ := Set.mem_iUnion₂.mp hc
    have hkj : k ≠ j := fun e => T.not_isCrossing_seamPair j (e ▸ hk)
    exact (T.seam_disjoint hkj).le_bot ⟨T.seamSurface_subset_seamCollar k hs, hy⟩

theorem region_subset_of_internal (j : Fin T.pairing.count)
    (hint : ∀ k, T.leftPiece k ∈ T.seamPair j → T.rightPiece k ∈ T.seamPair j → k = j)
    (hext : ∀ i, T.externalPiece i ∉ T.seamPair j) :
    Set.range (T.restrictMap (T.seamPair j)) \ T.crossingSurface (T.seamPair j) ⊆
      T.cutMap '' (T.cutCarrier.pieceInterior (T.components.piece (T.leftPiece j)) :
        Set T.cutCarrier.Carrier) ∪ T.seamCollar j ∪
      T.cutMap '' (T.cutCarrier.pieceInterior (T.components.piece (T.rightPiece j)) :
        Set T.cutCarrier.Carrier) := by
  rintro y ⟨hy, hyc⟩
  rw [range_restrictMap] at hy
  obtain ⟨x, hxS, rfl⟩ := hy
  obtain ⟨i, hi, hxi⟩ := (T.mem_subPiece _).mp hxS
  by_cases hx : T.cutCarrier.model.IsInteriorPoint x
  · rcases T.eq_or_eq_of_mem_seamPair hi with rfl | rfl
    · exact Or.inl (Or.inl ⟨x, ⟨hxi, hx⟩, rfl⟩)
    · exact Or.inr ⟨x, ⟨hxi, hx⟩, rfl⟩
  have hb : x ∈ T.cutCarrier.model.boundary T.cutCarrier.Carrier := by
    by_contra hb
    exact hx ((T.cutCarrier.model.isInteriorPoint_iff_not_isBoundaryPoint x).mpr hb)
  rw [T.cut_boundary_exhausted] at hb
  rcases hb with hb | hb
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hb
    have hsk := T.cutMap_mem_seamSurface_block hk
    have hside : T.leftPiece k ∈ T.seamPair j ∨ T.rightPiece k ∈ T.seamPair j := by
      rcases hk with hk | hk
      · exact Or.inl (T.mem_of_mem_subPiece _ hxS (T.left_owned k hk))
      · exact Or.inr (T.mem_of_mem_subPiece _ hxS (T.right_owned k hk))
    by_cases hboth : T.leftPiece k ∈ T.seamPair j ∧ T.rightPiece k ∈ T.seamPair j
    · rw [hint k hboth.1 hboth.2] at hsk
      exact Or.inl (Or.inr (T.seamSurface_subset_seamCollar j hsk))
    · refine (hyc (Set.mem_iUnion₂.mpr ⟨k, ?_, hsk⟩)).elim
      rcases hside with hl | hr
      · exact Or.inl ⟨hl, fun hr => hboth ⟨hl, hr⟩⟩
      · exact Or.inr ⟨hr, fun hl => hboth ⟨hl, hr⟩⟩
  · obtain ⟨e, t, ht⟩ : ∃ e t, T.cutExternal.torusMap e t = x := by
      obtain ⟨e, he⟩ := Set.mem_iUnion.mp hb
      obtain ⟨t, ht⟩ := he
      exact ⟨e, t, ht⟩
    exact (hext e (T.mem_of_mem_subPiece _ hxS (T.external_owned e ⟨t, ht⟩))).elim

theorem isConnected_region_seamPair (j : Fin T.pairing.count)
    (hint : ∀ k, T.leftPiece k ∈ T.seamPair j → T.rightPiece k ∈ T.seamPair j → k = j)
    (hext : ∀ i, T.externalPiece i ∉ T.seamPair j) :
    IsConnected (Set.range (T.restrictMap (T.seamPair j)) \ T.crossingSurface (T.seamPair j)) := by
  have hcont : Continuous T.cutMap :=
    T.reconstruction.continuous.comp T.pairing.quotientMap.continuous
  have hU : ∀ i, IsConnected (T.cutMap ''
      (T.cutCarrier.pieceInterior (T.components.piece i) : Set T.cutCarrier.Carrier)) :=
    fun i => (isConnected_iff_connectedSpace.mpr (T.components.interior_connected i)).image _
      hcont.continuousOn
  have hK : IsConnected (T.seamCollar j) := (T.isPathConnected_seamCollar j).isConnected
  have hp : ((1 : Torus), halfPoint (1 / 2) (by norm_num)) ∈ halfCollarSource := by
    change (1 / 2 : ℝ) < 1
    norm_num
  have hmeet : ∀ c : Bool, (T.cutMap '' (T.cutCarrier.pieceInterior
      (T.components.piece (T.sidePiece (T.pairSide j c))) : Set T.cutCarrier.Carrier) ∩
        T.seamCollar j).Nonempty := by
    intro c
    have hmem := (T.sideCollar (T.pairSide j c)).map_source'
      ((T.sideCollar_source _).symm ▸ hp)
    refine ⟨_, ⟨_, ⟨T.sideCollar_target_subset _ hmem,
      T.isInteriorPoint_sideCollar_pairSide j c hp (by change (0 : ℝ) < 1 / 2; norm_num)⟩,
      rfl⟩, ?_⟩
    have h := T.cutMap_mem_sideRegion (T.pairSide j c) hmem
    cases c <;> exact h
  have hsub := T.region_subset_of_internal j hint hext
  have hsup : T.cutMap '' (T.cutCarrier.pieceInterior (T.components.piece (T.leftPiece j)) :
        Set T.cutCarrier.Carrier) ∪ T.seamCollar j ∪
      T.cutMap '' (T.cutCarrier.pieceInterior (T.components.piece (T.rightPiece j)) :
        Set T.cutCarrier.Carrier) ⊆
      Set.range (T.restrictMap (T.seamPair j)) \ T.crossingSurface (T.seamPair j) :=
    Set.union_subset (Set.union_subset
      (T.cutMap_pieceInterior_subset_region _ (T.left_mem_seamPair j))
      (T.seamCollar_subset_region j))
      (T.cutMap_pieceInterior_subset_region _ (T.right_mem_seamPair j))
  rw [Set.Subset.antisymm hsub hsup]
  obtain ⟨y, hy1, hy2⟩ := hmeet false
  exact ((hU _).union (hmeet true) hK).union ⟨y, Or.inr hy2, hy1⟩ (hU _)

section ContractSides

variable (S : Finset (Fin T.components.count)) (hext : ∀ i, T.externalPiece i ∉ S)
  (hk : T.cutCarrier.kind = .withBoundary)
  (hconn : IsConnected (Set.range (T.restrictMap S) \ T.crossingSurface S))

def contractLast : Fin (T.contract S hext hk hconn).components.count :=
  Fin.last (Sᶜ.card)

def contractLiftSide : (T.contract S hext hk hconn).Side → T.Side
  | .inl k => .inl (T.nonInternal S k).val
  | .inr (.inl k) => .inr (.inl (T.nonInternal S k).val)
  | .inr (.inr e) => .inr (.inr e)

theorem contractLiftSide_injective :
    Function.Injective (T.contractLiftSide S hext hk hconn) := by
  rintro (k | k | e) (k' | k' | e') h <;>
    simp only [contractLiftSide, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq] at h
  · obtain rfl : k = k' :=
      (Fintype.equivFin (T.NonInternal S)).symm.injective (Subtype.ext h)
    rfl
  · obtain rfl : k = k' :=
      (Fintype.equivFin (T.NonInternal S)).symm.injective (Subtype.ext h)
    rfl
  · obtain rfl : e = e' := Sum.inr_injective h
    rfl

theorem contract_sidePiece_eq_last_iff (s : (T.contract S hext hk hconn).Side) :
    (T.contract S hext hk hconn).sidePiece s = T.contractLast S hext hk hconn ↔
      T.sidePiece (T.contractLiftSide S hext hk hconn s) ∈ S := by
  rcases s with k | k | e
  · change T.contractLeftPiece S k = Fin.last _ ↔ T.leftPiece (T.nonInternal S k).val ∈ S
    unfold contractLeftPiece
    split_ifs with hl
    · exact iff_of_true rfl hl
    · exact iff_of_false (Fin.castSucc_lt_last _).ne hl
  · change T.contractRightPiece S k = Fin.last _ ↔ T.rightPiece (T.nonInternal S k).val ∈ S
    unfold contractRightPiece
    split_ifs with hr
    · exact iff_of_true rfl hr
    · exact iff_of_false (Fin.castSucc_lt_last _).ne hr
  · exact iff_of_false (Fin.castSucc_lt_last _).ne (hext e)

theorem contractLiftSide_ne_pairSide {j : Fin T.pairing.count}
    (hj : T.leftPiece j ∈ S ∧ T.rightPiece j ∈ S) (s : (T.contract S hext hk hconn).Side)
    (c : Bool) : T.contractLiftSide S hext hk hconn s ≠ T.pairSide j c := by
  have hne : ∀ k : Fin (Fintype.card (T.NonInternal S)), (T.nonInternal S k).val ≠ j :=
    fun k e => (T.nonInternal S k).property (e ▸ hj)
  rcases s with k | k | e <;> cases c <;>
    simp only [contractLiftSide, pairSide, ne_eq, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq,
      not_false_eq_true]
  · exact hne k
  · exact hne k

theorem exists_contractLiftSide_eq (s : T.Side)
    (hs : ∀ k c, T.leftPiece k ∈ S → T.rightPiece k ∈ S → s ≠ T.pairSide k c) :
    ∃ s', T.contractLiftSide S hext hk hconn s' = s := by
  rcases s with k | k | e
  · have hk' : ¬(T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) := fun h => hs k true h.1 h.2 rfl
    let k'' : Fin (T.contract S hext hk hconn).pairing.count :=
      Fintype.equivFin (T.NonInternal S) ⟨k, hk'⟩
    refine ⟨.inl k'', ?_⟩
    change Sum.inl (T.nonInternal S (Fintype.equivFin (T.NonInternal S) ⟨k, hk'⟩)).val = _
    rw [nonInternal_equivFin]
  · have hk' : ¬(T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) := fun h => hs k false h.1 h.2 rfl
    let k'' : Fin (T.contract S hext hk hconn).pairing.count :=
      Fintype.equivFin (T.NonInternal S) ⟨k, hk'⟩
    refine ⟨.inr (.inl k''), ?_⟩
    change Sum.inr (Sum.inl (T.nonInternal S
      (Fintype.equivFin (T.NonInternal S) ⟨k, hk'⟩)).val) = _
    rw [nonInternal_equivFin]
  · exact ⟨.inr (.inr e), rfl⟩

end ContractSides

end TorusPresentation

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)

theorem card_ownedSide_eq_kind (i : Fin E.toTorus.components.count) :
    Fintype.card (E.toTorus.OwnedSide i) = E.kind i :=
  (E.piece i).card_ownedSide

theorem sidePiece_pairSide (j : Fin E.toTorus.pairing.count) (b : Bool) :
    E.toTorus.sidePiece (E.toTorus.pairSide j b) = E.seamPiece j b := by
  cases b <;> rfl

theorem mem_seamPair_iff (j : Fin E.toTorus.pairing.count) (b : Bool)
    (i : Fin E.toTorus.components.count) :
    i ∈ E.toTorus.seamPair j ↔ i = E.seamPiece j b ∨ i = E.hostPiece j b := by
  simp only [TorusPresentation.seamPair, Finset.mem_insert, Finset.mem_singleton]
  cases b
  · simp only [hostPiece, seamPiece, Bool.not_false]
    tauto
  · simp only [hostPiece, seamPiece, Bool.not_true]

variable {E}

theorem IsAbsorbSeam.seamPiece_ne_hostPiece {j : Fin E.toTorus.pairing.count} {b : Bool}
    (h : E.IsAbsorbSeam j b) : E.seamPiece j b ≠ E.hostPiece j b := by
  intro he
  have h2 := h.2
  rw [← he, h.1] at h2
  exact absurd h2 (by decide)

theorem IsAbsorbSeam.leftPiece_ne_rightPiece {j : Fin E.toTorus.pairing.count} {b : Bool}
    (h : E.IsAbsorbSeam j b) : E.toTorus.leftPiece j ≠ E.toTorus.rightPiece j := by
  have := h.seamPiece_ne_hostPiece
  cases b
  · exact this.symm
  · exact this

theorem IsAbsorbSeam.eq_seamSide {j : Fin E.toTorus.pairing.count} {b : Bool}
    (h : E.IsAbsorbSeam j b) {s : E.toTorus.Side}
    (hs : E.toTorus.sidePiece s = E.seamPiece j b) : s = E.toTorus.pairSide j b := by
  have hc : Fintype.card (E.toTorus.OwnedSide (E.seamPiece j b)) ≤ 1 := by
    rw [E.card_ownedSide_eq_kind, h.1]
  exact congrArg Subtype.val (Fintype.card_le_one_iff.mp hc ⟨s, hs⟩ ⟨_, E.sidePiece_pairSide j b⟩)

theorem IsAbsorbSeam.eq_of_internal {j : Fin E.toTorus.pairing.count} {b : Bool}
    (h : E.IsAbsorbSeam j b) {k : Fin E.toTorus.pairing.count}
    (hl : E.toTorus.leftPiece k ∈ E.toTorus.seamPair j)
    (hr : E.toTorus.rightPiece k ∈ E.toTorus.seamPair j) : k = j := by
  by_contra hkj
  have hA : ∀ c : Bool, E.toTorus.sidePiece (E.toTorus.pairSide k c) = E.hostPiece j b := by
    intro c
    have hmem : E.toTorus.sidePiece (E.toTorus.pairSide k c) ∈ E.toTorus.seamPair j := by
      cases c
      · exact hr
      · exact hl
    exact ((E.mem_seamPair_iff j b _).mp hmem).resolve_left fun hc =>
      E.toTorus.pairSide_ne_of_ne hkj c b (h.eq_seamSide hc)
  have hc : Fintype.card (E.toTorus.OwnedSide (E.hostPiece j b)) = 2 := by
    rw [E.card_ownedSide_eq_kind, h.2]
  let a : E.toTorus.OwnedSide (E.hostPiece j b) := ⟨_, E.sidePiece_pairSide j !b⟩
  let a1 : E.toTorus.OwnedSide (E.hostPiece j b) := ⟨_, hA true⟩
  let a2 : E.toTorus.OwnedSide (E.hostPiece j b) := ⟨_, hA false⟩
  have h3 : ({a, a1, a2} : Finset (E.toTorus.OwnedSide (E.hostPiece j b))).card = 3 := by
    rw [Finset.card_eq_three]
    refine ⟨a, a1, a2, fun he => ?_, fun he => ?_, fun he => ?_, rfl⟩
    · exact E.toTorus.pairSide_ne_of_ne (Ne.symm hkj) (!b) true (congrArg Subtype.val he)
    · exact E.toTorus.pairSide_ne_of_ne (Ne.symm hkj) (!b) false (congrArg Subtype.val he)
    · exact E.toTorus.pairSide_ne_not k true (congrArg Subtype.val he)
  have := Finset.card_le_univ ({a, a1, a2} : Finset (E.toTorus.OwnedSide (E.hostPiece j b)))
  omega

theorem IsAbsorbSeam.exists_otherSide {j : Fin E.toTorus.pairing.count} {b : Bool}
    (h : E.IsAbsorbSeam j b) :
    ∃ s : E.toTorus.Side, E.toTorus.sidePiece s = E.hostPiece j b ∧
      s ≠ E.toTorus.pairSide j !b ∧ ∀ s', E.toTorus.sidePiece s' = E.hostPiece j b →
        s' = E.toTorus.pairSide j !b ∨ s' = s := by
  have hc : Fintype.card (E.toTorus.OwnedSide (E.hostPiece j b)) = 2 := by
    rw [E.card_ownedSide_eq_kind, h.2]
  let a : E.toTorus.OwnedSide (E.hostPiece j b) := ⟨_, E.sidePiece_pairSide j !b⟩
  obtain ⟨a₁, ha₁⟩ := Fintype.exists_ne_of_one_lt_card (by omega) a
  refine ⟨a₁.val, a₁.property, fun he => ha₁ (Subtype.ext he), fun s' hs' => ?_⟩
  by_contra hne
  push Not at hne
  let a₂ : E.toTorus.OwnedSide (E.hostPiece j b) := ⟨s', hs'⟩
  have h3 : ({a, a₁, a₂} : Finset (E.toTorus.OwnedSide (E.hostPiece j b))).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨a, a₁, a₂, ha₁.symm, fun he => hne.1 (congrArg Subtype.val he).symm,
      fun he => hne.2 (congrArg Subtype.val he).symm, rfl⟩
  have := Finset.card_le_univ ({a, a₁, a₂} : Finset (E.toTorus.OwnedSide (E.hostPiece j b)))
  omega

theorem IsAbsorbSeam.filter_internal {j : Fin E.toTorus.pairing.count} {b : Bool}
    (h : E.IsAbsorbSeam j b) :
    (Finset.univ.filter fun k => E.toTorus.leftPiece k ∈ E.toTorus.seamPair j ∧
      E.toTorus.rightPiece k ∈ E.toTorus.seamPair j) = {j} := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨hl, hr⟩
    exact h.eq_of_internal hl hr
  · rintro rfl
    exact ⟨E.toTorus.left_mem_seamPair k, E.toTorus.right_mem_seamPair k⟩

theorem IsAbsorbSeam.isConnected_region {j : Fin E.toTorus.pairing.count} {b : Bool}
    (h : E.IsAbsorbSeam j b) (hext : ∀ i, E.toTorus.externalPiece i ∉ E.toTorus.seamPair j) :
    IsConnected (Set.range (E.toTorus.restrictMap (E.toTorus.seamPair j)) \
      E.toTorus.crossingSurface (E.toTorus.seamPair j)) :=
  E.toTorus.isConnected_region_seamPair j (fun k hl hr => h.eq_of_internal (k := k) hl hr) hext

variable (E)

def absorbContraction (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsAbsorbSeam j b)
    (hext : ∀ i, E.toTorus.externalPiece i ∉ E.toTorus.seamPair j) : TorusPresentation W :=
  E.toTorus.contract (E.toTorus.seamPair j) hext (E.toTorus.cutCarrier_kind_of_pos j.pos)
    (h.isConnected_region hext)

section Absorb

variable (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsAbsorbSeam j b)
  (hext : ∀ i, E.toTorus.externalPiece i ∉ E.toTorus.seamPair j)

theorem absorbContraction_pairing_count :
    (E.absorbContraction j b h hext).pairing.count + 1 = E.complexity := by
  rw [absorbContraction, TorusPresentation.contract_pairing_count, h.filter_internal,
    Finset.card_singleton]
  have := j.pos
  unfold complexity
  omega

theorem absorbContraction_components_count :
    (E.absorbContraction j b h hext).components.count + 1 = E.toTorus.components.count := by
  rw [absorbContraction, TorusPresentation.contract_components_count,
    TorusPresentation.seamPair, Finset.card_pair h.leftPiece_ne_rightPiece]
  have := Finset.card_le_univ ({E.toTorus.leftPiece j, E.toTorus.rightPiece j} :
    Finset (Fin E.toTorus.components.count))
  rw [Finset.card_pair h.leftPiece_ne_rightPiece, Fintype.card_fin] at this
  omega

def absorbLast : Fin (E.absorbContraction j b h hext).components.count :=
  E.toTorus.contractLast _ hext (E.toTorus.cutCarrier_kind_of_pos j.pos) (h.isConnected_region hext)

theorem absorbContraction_externalCount :
    (E.absorbContraction j b h hext).externalCount = E.toTorus.externalCount := rfl

theorem absorbContraction_seam (k : Fin (E.absorbContraction j b h hext).pairing.count) :
    (E.absorbContraction j b h hext).seam k =
      E.toTorus.seam (E.toTorus.nonInternal (E.toTorus.seamPair j) k).val := rfl

theorem absorbContraction_matching (k : Fin (E.absorbContraction j b h hext).pairing.count) :
    (E.absorbContraction j b h hext).pairing.matching k =
      E.toTorus.pairing.matching (E.toTorus.nonInternal (E.toTorus.seamPair j) k).val := rfl

theorem absorb_nonInternal_ne (k : Fin (E.absorbContraction j b h hext).pairing.count) :
    (E.toTorus.nonInternal (E.toTorus.seamPair j) k).val ≠ j := by
  intro e
  apply (E.toTorus.nonInternal (E.toTorus.seamPair j) k).property
  rw [e]
  exact ⟨E.toTorus.left_mem_seamPair j, E.toTorus.right_mem_seamPair j⟩

def absorbSeamEquiv :
    Fin (E.absorbContraction j b h hext).pairing.count ≃
      {k : Fin E.toTorus.pairing.count // k ≠ j} :=
  (Fintype.equivFin (E.toTorus.NonInternal (E.toTorus.seamPair j))).symm.trans
    (Equiv.subtypeEquivRight fun k => ⟨fun hk e => hk (by
      rw [e]
      exact ⟨E.toTorus.left_mem_seamPair j, E.toTorus.right_mem_seamPair j⟩),
      fun hk hb => hk (h.eq_of_internal hb.1 hb.2)⟩)

theorem absorbSeamEquiv_val (k : Fin (E.absorbContraction j b h hext).pairing.count) :
    (E.absorbSeamEquiv j b h hext k).val = (E.toTorus.nonInternal (E.toTorus.seamPair j) k).val :=
  rfl

theorem absorbContraction_card_ownedSide_last :
    Fintype.card ((E.absorbContraction j b h hext).OwnedSide (E.absorbLast j b h hext)) = 1 := by
  have hj : E.toTorus.leftPiece j ∈ E.toTorus.seamPair j ∧
      E.toTorus.rightPiece j ∈ E.toTorus.seamPair j :=
    ⟨E.toTorus.left_mem_seamPair j, E.toTorus.right_mem_seamPair j⟩
  obtain ⟨s₁, hs₁, hs₁ne, hs₁u⟩ := h.exists_otherSide
  have hAS : E.hostPiece j b ∈ E.toTorus.seamPair j := (E.mem_seamPair_iff j b _).mpr (Or.inr rfl)
  have hs₁j : ∀ k c, E.toTorus.leftPiece k ∈ E.toTorus.seamPair j →
      E.toTorus.rightPiece k ∈ E.toTorus.seamPair j → s₁ ≠ E.toTorus.pairSide k c := by
    intro k c hl hr he
    obtain rfl := h.eq_of_internal hl hr
    by_cases hc : c = b
    · subst hc
      rw [he, E.sidePiece_pairSide] at hs₁
      exact h.seamPiece_ne_hostPiece hs₁
    · have hc' : c = !b := by cases c <;> cases b <;> simp_all
      subst hc'
      exact hs₁ne he
  have hk := E.toTorus.cutCarrier_kind_of_pos j.pos
  have hconn := h.isConnected_region hext
  obtain ⟨s₁', hs₁'⟩ := E.toTorus.exists_contractLiftSide_eq (E.toTorus.seamPair j) hext hk hconn
    s₁ hs₁j
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨s₁', ?_⟩, ?_⟩
  · change (E.toTorus.contract (E.toTorus.seamPair j) hext hk hconn).sidePiece s₁' =
      E.toTorus.contractLast _ hext hk hconn
    rw [TorusPresentation.contract_sidePiece_eq_last_iff, hs₁', hs₁]
    exact hAS
  · rintro ⟨s', hs'⟩
    apply Subtype.ext
    change s' = s₁'
    apply E.toTorus.contractLiftSide_injective (E.toTorus.seamPair j) hext hk hconn
    rw [hs₁']
    have hmem := (E.toTorus.contract_sidePiece_eq_last_iff (E.toTorus.seamPair j) hext hk hconn
      s').mp hs'
    rcases (E.mem_seamPair_iff j b _).mp hmem with hV | hA
    · exact absurd (h.eq_seamSide hV)
        (E.toTorus.contractLiftSide_ne_pairSide _ hext hk hconn hj s' b)
    · rcases hs₁u _ hA with h1 | h1
      · exact absurd h1 (E.toTorus.contractLiftSide_ne_pairSide _ hext hk hconn hj s' !b)
      · exact h1

end Absorb

def absorbPresentation {Q : ConnectedClosedOrientedManifold.{u} 3}
    (E : ElementaryPresentation (NoCuts.carrier Q)) (j : Fin E.toTorus.pairing.count) (b : Bool)
    (h : E.IsAbsorbSeam j b) : TorusPresentation (NoCuts.carrier Q) :=
  E.absorbContraction j b h (TorusPresentation.externalPiece_not_mem_of_closed _ _)

theorem absorbPresentation_pairing_count {Q : ConnectedClosedOrientedManifold.{u} 3}
    (E : ElementaryPresentation (NoCuts.carrier Q)) (j : Fin E.toTorus.pairing.count) (b : Bool)
    (h : E.IsAbsorbSeam j b) : (E.absorbPresentation j b h).pairing.count + 1 = E.complexity :=
  E.absorbContraction_pairing_count j b h _

end ElementaryPresentation

open ElementaryPresentation

def AbsorbContractionElementary : Prop :=
  ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsAbsorbSeam j b),
      ∃ E' : ElementaryPresentation (NoCuts.carrier Q),
        E'.complexity = (E.absorbPresentation j b h).pairing.count

theorem moveAbsorb_of_absorbContractionElementary (hA : AbsorbContractionElementary.{u}) :
    MoveAbsorb.{u} := by
  intro Q E j b h
  obtain ⟨E', hE'⟩ := hA Q E j b h
  exact ⟨E', by rw [hE']; exact E.absorbPresentation_pairing_count j b h⟩

def MergedSolidTorus : Prop :=
  ∀ (W : CompactCarrier.{u}) (E : ElementaryPresentation W) (j : Fin E.toTorus.pairing.count)
    (b : Bool) (h : E.IsAbsorbSeam j b)
    (hext : ∀ i, E.toTorus.externalPiece i ∉ E.toTorus.seamPair j),
      Nonempty ((E.absorbContraction j b h hext).components.piece (E.absorbLast j b h hext) ≃ₘ⟮
        (E.absorbContraction j b h hext).cutCarrier.model, E.toTorus.cutCarrier.model⟯
          E.toTorus.components.piece (E.seamPiece j b))

def ContractionRecollar : Prop :=
  ∀ (W : CompactCarrier.{u}) (E : ElementaryPresentation W)
    (S : Finset (Fin E.toTorus.components.count)) (hext : ∀ i, E.toTorus.externalPiece i ∉ S)
    (hk : E.toTorus.cutCarrier.kind = .withBoundary)
    (hconn : IsConnected (Set.range (E.toTorus.restrictMap S) \ E.toTorus.crossingSurface S))
    (k : ℕ), k ∈ ({1, 2, 3} : Finset ℕ) →
      Fintype.card ((E.toTorus.contract S hext hk hconn).OwnedSide
        (E.toTorus.contractLast S hext hk hconn)) = k →
      ∀ B : PlanarBase.{u} k, Nonempty ((B.surface.Carrier × Circle) ≃ₘ⟮
        (SurfaceModel.model B.surface.kind).prod (𝓡 1),
          (E.toTorus.contract S hext hk hconn).cutCarrier.model⟯
            (E.toTorus.contract S hext hk hconn).components.piece
              (E.toTorus.contractLast S hext hk hconn)) →
        ∃ E' : ElementaryPresentation W,
          E'.complexity = (E.toTorus.contract S hext hk hconn).pairing.count

theorem absorbContractionElementary_of_mergedSolidTorus_of_contractionRecollar
    (hM : MergedSolidTorus.{u}) (hR : ContractionRecollar.{u}) :
    AbsorbContractionElementary.{u} := by
  intro Q E j b h
  have hext := TorusPresentation.externalPiece_not_mem_of_closed E.toTorus (E.toTorus.seamPair j)
  obtain ⟨e⟩ := hM _ E j b h hext
  exact hR _ E (E.toTorus.seamPair j) hext (E.toTorus.cutCarrier_kind_of_pos j.pos)
    (h.isConnected_region hext) (E.kind (E.seamPiece j b)) (E.kind_mem _)
    ((absorbContraction_card_ownedSide_last E j b h hext).trans h.1.symm)
    (E.piece (E.seamPiece j b)).base ⟨(E.piece (E.seamPiece j b)).trivialization.trans e.symm⟩

theorem moveAbsorb_of_mergedSolidTorus_of_contractionRecollar (hM : MergedSolidTorus.{u})
    (hR : ContractionRecollar.{u}) : MoveAbsorb.{u} :=
  moveAbsorb_of_absorbContractionElementary
    (absorbContractionElementary_of_mergedSolidTorus_of_contractionRecollar hM hR)

end GC.Seifert
