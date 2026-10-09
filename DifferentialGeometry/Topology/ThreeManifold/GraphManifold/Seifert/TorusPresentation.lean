import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Presentation
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Piece
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Transport
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Opposite

/-!
# Torus presentations

Chapter 6, S2. A `TorusPresentation W` has every field of `RawGraphPresentation W` except
`fibration`, under the same names. No other raw field mentions the fibration, so nothing else is
dropped. `RawGraphPresentation.toTorusPresentation` forgets the fibration. A raw presentation is
its torus presentation together with a circle fibration of every piece (`withFibration`,
`toTorusPresentation_injective_on_fibration`). The forgetful map is not required to be
invertible: the pieces of a torus presentation (the filled Seifert blocks of S4) need not carry a
circle fibration, and raw certificates are recovered by flattening (K21), not by inverting it.

The raw constructors read the fibration (`ofPiece` restricts it to the piece, `transport` and
`opposite` carry it along), so they are re-implemented here with the same signatures and proofs,
together with the sides, collars and boundary tori of a piece used by `ofPiece`; the raw
constructors are unchanged. The ports commute with the forgetful map definitionally
(`toTorusPresentation_ofPiece`, `toTorusPresentation_transport`, `toTorusPresentation_opposite`)
and the side maps by cases on the side. The raw side maps are definitions by `match`, which the
elaborator does not unfold, so `toTorusPresentation_ofPiece` is checked with `smartUnfolding` off.
`torusPresentation_of_diffeomorph` mirrors `rawGraphPresentation_of_diffeomorph`.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

structure TorusPresentation (W : CompactCarrier.{u}) where
  cutCarrier : CompactCarrier.{u}
  components : cutCarrier.Components
  pairing : TorusPairing cutCarrier
  externalCount : ℕ
  external : BoundaryTori W externalCount
  cutExternal : BoundaryTori cutCarrier externalCount
  external_exhausted : W.model.boundary W.Carrier = external.image
  cut_boundary_exhausted : cutCarrier.model.boundary cutCarrier.Carrier =
    (⋃ i, pairing.gluing.block i) ∪ cutExternal.image
  external_disjoint : Disjoint (⋃ i, pairing.gluing.block i) cutExternal.image
  reconstruction : pairing.QuotientSpace ≃ₜ W.Carrier
  quotient_smooth : ContMDiff cutCarrier.model W.model ∞
    (reconstruction ∘ pairing.quotientMap)
  quotient_oriented : ∀ x : cutCarrier.Carrier,
    ∃ L : TangentSpace cutCarrier.model x ≃ₗ[ℝ]
        TangentSpace W.model (reconstruction (pairing.quotientMap x)),
      (∀ v, L v = mfderiv cutCarrier.model W.model
        (reconstruction ∘ pairing.quotientMap) x v) ∧
      Orientation.map (Fin 3) L (cutCarrier.orientation.orientation x) =
        W.orientation.orientation (reconstruction (pairing.quotientMap x))
  interiorImage : TopologicalSpace.Opens W.Carrier
  interiorDiffeomorph : cutCarrier.interior ≃ₘ⟮cutCarrier.model, W.model⟯ interiorImage
  interior_map : ∀ x : cutCarrier.interior,
    (interiorDiffeomorph x).val = reconstruction (pairing.quotientMap x.val)
  seam : Fin pairing.count →
    PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞
  seam_source : ∀ i, (seam i).source = signedCollarSource
  seam_zero : ∀ i t, seam i (t, 0) =
    reconstruction (pairing.quotientMap (pairing.leftParam i t))
  seam_positive : ∀ i t s (hs : 0 ≤ s), s < 1 → seam i (t, s) =
    reconstruction (pairing.quotientMap (pairing.rightCollar i
      (pairing.matching i t, halfPoint s hs)))
  seam_negative : ∀ i t s (hs : s ≤ 0), -1 < s → seam i (t, s) =
    reconstruction (pairing.quotientMap (pairing.leftCollar i
      (t, halfPoint (-s) (neg_nonneg.mpr hs))))
  seam_interior : ∀ i, (seam i).target ⊆ W.interior
  seam_disjoint : Pairwise (fun i j => Disjoint (seam i).target (seam j).target)
  marked_collar : ∀ i p, p ∈ halfCollarSource →
    reconstruction (pairing.quotientMap (cutExternal.collar i p)) = external.collar i p
  external_seam_disjoint : ∀ i j, Disjoint (external.collar i).target (seam j).target
  leftPiece : Fin pairing.count → Fin components.count
  rightPiece : Fin pairing.count → Fin components.count
  left_owned : ∀ i, pairing.gluing.left i ⊆ components.piece (leftPiece i)
  right_owned : ∀ i, pairing.gluing.right i ⊆ components.piece (rightPiece i)
  externalPiece : Fin externalCount → Fin components.count
  external_owned : ∀ i, Set.range (cutExternal.torusMap i) ⊆
    components.piece (externalPiece i)

namespace TorusPresentation
variable {W : CompactCarrier.{u}}

abbrev Fibration (G : TorusPresentation W) :=
  (i : Fin G.components.count) → CircleFibration G.cutCarrier (G.components.piece i)

def withFibration (G : TorusPresentation W) (F : G.Fibration) : RawGraphPresentation W where
  cutCarrier := G.cutCarrier
  components := G.components
  fibration := F
  pairing := G.pairing
  externalCount := G.externalCount
  external := G.external
  cutExternal := G.cutExternal
  external_exhausted := G.external_exhausted
  cut_boundary_exhausted := G.cut_boundary_exhausted
  external_disjoint := G.external_disjoint
  reconstruction := G.reconstruction
  quotient_smooth := G.quotient_smooth
  quotient_oriented := G.quotient_oriented
  interiorImage := G.interiorImage
  interiorDiffeomorph := G.interiorDiffeomorph
  interior_map := G.interior_map
  seam := G.seam
  seam_source := G.seam_source
  seam_zero := G.seam_zero
  seam_positive := G.seam_positive
  seam_negative := G.seam_negative
  seam_interior := G.seam_interior
  seam_disjoint := G.seam_disjoint
  marked_collar := G.marked_collar
  external_seam_disjoint := G.external_seam_disjoint
  leftPiece := G.leftPiece
  rightPiece := G.rightPiece
  left_owned := G.left_owned
  right_owned := G.right_owned
  externalPiece := G.externalPiece
  external_owned := G.external_owned

abbrev Side (G : TorusPresentation W) :=
  Fin G.pairing.count ⊕ Fin G.pairing.count ⊕ Fin G.externalCount

def sidePiece (G : TorusPresentation W) : G.Side → Fin G.components.count
  | .inl k => G.leftPiece k
  | .inr (.inl k) => G.rightPiece k
  | .inr (.inr k) => G.externalPiece k

def sideCollar (G : TorusPresentation W) : G.Side →
    PartialDiffeomorph halfCollarModel G.cutCarrier.model (Torus × EuclideanHalfSpace 1)
      G.cutCarrier.Carrier ∞
  | .inl k => G.pairing.leftCollar k
  | .inr (.inl k) => G.pairing.rightCollar k
  | .inr (.inr k) => G.cutExternal.collar k

theorem sideCollar_source (G : TorusPresentation W) :
    ∀ s, (G.sideCollar s).source = halfCollarSource
  | .inl k => G.pairing.left_source k
  | .inr (.inl k) => G.pairing.right_source k
  | .inr (.inr k) => G.cutExternal.source_eq k

theorem zero_mem_sideCollar_source (G : TorusPresentation W) (s : G.Side) (t : Torus) :
    (t, halfZero) ∈ (G.sideCollar s).source := by
  rw [G.sideCollar_source]
  exact zero_mem_halfCollarSource t

private theorem mem_boundary_of_mem_block (G : TorusPresentation W)
    {k : Fin G.pairing.count} {x : G.cutCarrier.Carrier} (hx : x ∈ G.pairing.gluing.block k) :
    x ∈ G.cutCarrier.model.boundary G.cutCarrier.Carrier := by
  rw [G.cut_boundary_exhausted]
  exact Or.inl (Set.mem_iUnion.mpr ⟨k, hx⟩)

theorem sideCollar_zero_mem (G : TorusPresentation W) :
    ∀ (s : G.Side) (t : Torus),
      G.sideCollar s (t, halfZero) ∈ G.cutCarrier.model.boundary G.cutCarrier.Carrier ∧
        G.sideCollar s (t, halfZero) ∈ G.components.piece (G.sidePiece s)
  | .inl k, t => by
    change G.pairing.leftCollar k (t, halfZero) ∈ _ ∧ G.pairing.leftCollar k (t, halfZero) ∈ _
    rw [G.pairing.left_zero k t]
    exact ⟨G.mem_boundary_of_mem_block (Or.inl (G.pairing.leftParam k t).property),
      G.left_owned k (G.pairing.leftParam k t).property⟩
  | .inr (.inl k), t => by
    change G.pairing.rightCollar k (t, halfZero) ∈ _ ∧
      G.pairing.rightCollar k (t, halfZero) ∈ _
    rw [G.pairing.right_zero k t]
    exact ⟨G.mem_boundary_of_mem_block (Or.inr (G.pairing.rightParam k t).property),
      G.right_owned k (G.pairing.rightParam k t).property⟩
  | .inr (.inr k), t => ⟨G.cutExternal.boundary_zero k t, G.external_owned k ⟨t, rfl⟩⟩

theorem sideCollar_target_subset (G : TorusPresentation W) (s : G.Side) :
    (G.sideCollar s).target ⊆ G.components.piece (G.sidePiece s) :=
  target_subset_piece_of_source_eq _ _ (G.sideCollar_source s)
    (G.zero_mem_sideCollar_source s 1) (G.sideCollar_zero_mem s 1).2

def cutMap (G : TorusPresentation W) : G.cutCarrier.Carrier → W.Carrier :=
  fun x => G.reconstruction (G.pairing.quotientMap x)

theorem cutMap_leftCollar (G : TorusPresentation W) (k : Fin G.pairing.count)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    G.cutMap (G.pairing.leftCollar k p) = G.seam k (p.1, -(p.2.val 0)) := by
  rw [G.seam_negative k p.1 _ (neg_nonpos.mpr p.2.property) (neg_lt_neg hp),
    halfPoint_eq_self p.2 _ (neg_neg _)]
  rfl

theorem cutMap_rightCollar (G : TorusPresentation W) (k : Fin G.pairing.count)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    G.cutMap (G.pairing.rightCollar k p) =
      G.seam k ((G.pairing.matching k).symm p.1, p.2.val 0) := by
  rw [G.seam_positive k _ _ p.2.property hp, Diffeomorph.apply_symm_apply,
    halfPoint_eq_self p.2 _ rfl]
  rfl

private theorem neg_mem_signedCollarSource {a : ℝ} (t : Torus) (h0 : 0 ≤ a) (h1 : a < 1) :
    (t, -a) ∈ signedCollarSource :=
  ⟨neg_lt_neg h1, lt_of_le_of_lt (neg_nonpos.mpr h0) one_pos⟩

private theorem mem_signedCollarSource {a : ℝ} (t : Torus) (h0 : 0 ≤ a) (h1 : a < 1) :
    (t, a) ∈ signedCollarSource :=
  ⟨lt_of_lt_of_le (neg_lt_zero.mpr one_pos) h0, h1⟩

def sideIndex (G : TorusPresentation W) : G.Side → Fin G.pairing.count ⊕ Fin G.externalCount
  | .inl k => .inl k
  | .inr (.inl k) => .inl k
  | .inr (.inr k) => .inr k

def sideRegion (G : TorusPresentation W) :
    Fin G.pairing.count ⊕ Fin G.externalCount → Set W.Carrier
  | .inl k => (G.seam k).target
  | .inr k => (G.external.collar k).target

theorem pairwise_disjoint_sideRegion (G : TorusPresentation W) :
    Pairwise (fun a b => Disjoint (G.sideRegion a) (G.sideRegion b))
  | .inl _, .inl _, h => G.seam_disjoint fun e => h (congrArg _ e)
  | .inl k, .inr k', _ => (G.external_seam_disjoint k' k).symm
  | .inr k, .inl k', _ => G.external_seam_disjoint k k'
  | .inr _, .inr _, h => G.external.disjoint fun e => h (congrArg _ e)

theorem cutMap_mem_sideRegion (G : TorusPresentation W) :
    ∀ (s : G.Side) {x : G.cutCarrier.Carrier}, x ∈ (G.sideCollar s).target →
      G.cutMap x ∈ G.sideRegion (G.sideIndex s)
  | .inl k, x, hx => by
    obtain ⟨p, hp, rfl⟩ :=
      exists_eq_of_mem_target_of_source_eq _ (G.pairing.left_source k) hx
    change G.cutMap (G.pairing.leftCollar k p) ∈ (G.seam k).target
    rw [G.cutMap_leftCollar k hp]
    exact (G.seam k).map_source' (G.seam_source k ▸ neg_mem_signedCollarSource _ p.2.2 hp)
  | .inr (.inl k), x, hx => by
    obtain ⟨p, hp, rfl⟩ :=
      exists_eq_of_mem_target_of_source_eq _ (G.pairing.right_source k) hx
    change G.cutMap (G.pairing.rightCollar k p) ∈ (G.seam k).target
    rw [G.cutMap_rightCollar k hp]
    exact (G.seam k).map_source' (G.seam_source k ▸ mem_signedCollarSource _ p.2.2 hp)
  | .inr (.inr k), x, hx => by
    obtain ⟨p, hp, rfl⟩ :=
      exists_eq_of_mem_target_of_source_eq _ (G.cutExternal.source_eq k) hx
    change G.cutMap (G.cutExternal.collar k p) ∈ (G.external.collar k).target
    rw [cutMap, G.marked_collar k p hp]
    exact (G.external.collar k).map_source' ((G.external.source_eq k).symm ▸ hp)

theorem disjoint_leftCollar_rightCollar (G : TorusPresentation W) (k : Fin G.pairing.count) :
    Disjoint (G.pairing.leftCollar k).target (G.pairing.rightCollar k).target := by
  rw [Set.disjoint_left]
  intro x hl hr
  obtain ⟨⟨t, a⟩, hp, rfl⟩ :=
    exists_eq_of_mem_target_of_source_eq _ (G.pairing.left_source k) hl
  obtain ⟨⟨t', a'⟩, hq, hpq⟩ :=
    exists_eq_of_mem_target_of_source_eq _ (G.pairing.right_source k) hr
  have he : G.seam k (t, -(a.val 0)) = G.seam k ((G.pairing.matching k).symm t', a'.val 0) := by
    rw [← G.cutMap_leftCollar k hp, ← G.cutMap_rightCollar k hq, hpq]
  have h2 := congrArg Prod.snd ((G.seam k).toPartialEquiv.injOn
    (G.seam_source k ▸ neg_mem_signedCollarSource t a.2 hp)
    (G.seam_source k ▸ mem_signedCollarSource _ a'.2 hq) he)
  have h0 : a.val 0 = 0 := by
    have := a.2
    have := a'.2
    simp only at h2
    linarith
  have h0' : a'.val 0 = 0 := by
    simp only at h2
    linarith
  have ha : a = halfZero := (halfPoint_eq_self a le_rfl h0.symm).symm
  have ha' : a' = halfZero := (halfPoint_eq_self a' le_rfl h0'.symm).symm
  subst ha ha'
  rw [G.pairing.left_zero] at hpq
  rw [G.pairing.right_zero] at hpq
  refine (G.pairing.gluing.disjoint_left_right k).le_bot
    ⟨(G.pairing.leftParam k t).property, ?_⟩
  rw [← hpq]
  exact (G.pairing.rightParam k t').property

theorem sideCollar_disjoint (G : TorusPresentation W) :
    Pairwise (fun s s' : G.Side => Disjoint (G.sideCollar s).target (G.sideCollar s').target) := by
  intro s s' hss'
  by_cases hidx : G.sideIndex s = G.sideIndex s'
  · rcases s with k | k | k <;> rcases s' with k' | k' | k' <;>
      simp only [sideIndex, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at hidx
    · exact (hss' (congrArg Sum.inl hidx)).elim
    · subst hidx
      exact G.disjoint_leftCollar_rightCollar k
    · subst hidx
      exact (G.disjoint_leftCollar_rightCollar k).symm
    · exact (hss' (by rw [hidx])).elim
    · exact (hss' (by rw [hidx])).elim
  · rw [Set.disjoint_left]
    intro x hx hx'
    exact (G.pairwise_disjoint_sideRegion hidx).le_bot
      ⟨G.cutMap_mem_sideRegion s hx, G.cutMap_mem_sideRegion s' hx'⟩

abbrev OwnedSide (G : TorusPresentation W) (i : Fin G.components.count) :=
  {s : G.Side // G.sidePiece s = i}

def pieceCollar (G : TorusPresentation W) (i : Fin G.components.count) (s : G.OwnedSide i) :
    PartialDiffeomorph halfCollarModel G.cutCarrier.model (Torus × EuclideanHalfSpace 1)
      (G.components.piece i) ∞ :=
  codRestrictOpens (G.sideCollar s.val) (G.components.piece i)
    (G.components.connected i).toNonempty

theorem sideCollar_target_subset_of_owned (G : TorusPresentation W)
    (i : Fin G.components.count) (s : G.OwnedSide i) :
    (G.sideCollar s.val).target ⊆ G.components.piece i :=
  by simpa only [s.property] using G.sideCollar_target_subset s.val

theorem pieceCollar_source (G : TorusPresentation W) (i : Fin G.components.count)
    (s : G.OwnedSide i) : (G.pieceCollar i s).source = halfCollarSource :=
  (codRestrictOpens_source _ _ _ (G.sideCollar_target_subset_of_owned i s)).trans
    (G.sideCollar_source s.val)

theorem pieceCollar_target (G : TorusPresentation W) (i : Fin G.components.count)
    (s : G.OwnedSide i) :
    (G.pieceCollar i s).target = Subtype.val ⁻¹' (G.sideCollar s.val).target :=
  codRestrictOpens_target _ _ _

theorem pieceCollar_apply (G : TorusPresentation W) (i : Fin G.components.count)
    (s : G.OwnedSide i) {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    (G.pieceCollar i s p : G.cutCarrier.Carrier) = G.sideCollar s.val p :=
  codRestrictOpens_apply _ _ _ (G.sideCollar_target_subset_of_owned i s
    ((G.sideCollar s.val).map_source' ((G.sideCollar_source s.val).symm ▸ hp)))

def pieceBoundaryTori (G : TorusPresentation W) (i : Fin G.components.count) :
    BoundaryTori (componentCarrier G.cutCarrier G.components i)
      (Fintype.card (G.OwnedSide i)) where
  collar j := G.pieceCollar i ((Fintype.equivFin _).symm j)
  source_eq j := G.pieceCollar_source i _
  boundary_zero j t := by
    refine (ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val (I := G.cutCarrier.model)
      (u := G.components.piece i)).mpr ?_
    have h := (G.sideCollar_zero_mem ((Fintype.equivFin _).symm j).val t).1
    rw [← G.pieceCollar_apply i _ (zero_mem_halfCollarSource t)] at h
    exact h
  disjoint j j' h := by
    change Disjoint (G.pieceCollar i _).target (G.pieceCollar i _).target
    rw [G.pieceCollar_target, G.pieceCollar_target]
    exact (G.sideCollar_disjoint fun e =>
      h ((Fintype.equivFin _).symm.injective (Subtype.ext e))).preimage _

theorem pieceBoundaryTori_torusMap (G : TorusPresentation W) (i : Fin G.components.count)
    (j : Fin (Fintype.card (G.OwnedSide i))) (t : Torus) :
    ((G.pieceBoundaryTori i).torusMap j t).val =
      G.sideCollar ((Fintype.equivFin _).symm j).val (t, halfZero) :=
  G.pieceCollar_apply i _ (zero_mem_halfCollarSource t)

theorem exists_sideCollar_zero_eq (G : TorusPresentation W) {x : G.cutCarrier.Carrier}
    (hx : x ∈ G.cutCarrier.model.boundary G.cutCarrier.Carrier) :
    ∃ (s : G.Side) (t : Torus), G.sideCollar s (t, halfZero) = x := by
  rw [G.cut_boundary_exhausted] at hx
  rcases hx with hx | hx
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    rcases hk with hl | hr
    · refine ⟨.inl k, (G.pairing.leftParam k).symm ⟨x, hl⟩, ?_⟩
      change G.pairing.leftCollar k _ = x
      rw [G.pairing.left_zero, Homeomorph.apply_symm_apply]
    · refine ⟨.inr (.inl k), (G.pairing.rightParam k).symm ⟨x, hr⟩, ?_⟩
      change G.pairing.rightCollar k _ = x
      rw [G.pairing.right_zero, Homeomorph.apply_symm_apply]
  · obtain ⟨k, t, ht⟩ := Set.mem_iUnion.mp hx
    exact ⟨.inr (.inr k), t, ht⟩

theorem pieceBoundaryTori_image (G : TorusPresentation W) (i : Fin G.components.count) :
    (componentCarrier G.cutCarrier G.components i).model.boundary
        (componentCarrier G.cutCarrier G.components i).Carrier =
      (G.pieceBoundaryTori i).image := by
  ext x
  constructor
  · intro hx
    have hx' : x.val ∈ G.cutCarrier.model.boundary G.cutCarrier.Carrier :=
      (ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val (I := G.cutCarrier.model)
        (u := G.components.piece i)).mp hx
    obtain ⟨s, t, hst⟩ := G.exists_sideCollar_zero_eq hx'
    have hsi : G.sidePiece s = i := by
      by_contra hne
      exact (G.components.disjoint hne).le_bot
        ⟨hst ▸ (G.sideCollar_zero_mem s t).2, x.property⟩
    refine Set.mem_iUnion.mpr ⟨Fintype.equivFin _ ⟨s, hsi⟩, t, Subtype.ext ?_⟩
    rw [pieceBoundaryTori_torusMap, Equiv.symm_apply_apply]
    exact hst
  · intro hx
    obtain ⟨j, t, rfl⟩ := Set.mem_iUnion.mp hx
    exact (G.pieceBoundaryTori i).boundary_zero j t

def ofPiece (G : TorusPresentation W) (i : Fin G.components.count) :
    TorusPresentation (componentCarrier G.cutCarrier G.components i) where
  cutCarrier := componentCarrier G.cutCarrier G.components i
  components := componentComponents G.cutCarrier G.components i
  pairing := emptyTorusPairing _
  externalCount := Fintype.card (G.OwnedSide i)
  external := G.pieceBoundaryTori i
  cutExternal := G.pieceBoundaryTori i
  external_exhausted := G.pieceBoundaryTori_image i
  cut_boundary_exhausted := by
    rw [iUnion_block_emptyTorusPairing, Set.empty_union]
    exact G.pieceBoundaryTori_image i
  external_disjoint := by
    rw [iUnion_block_emptyTorusPairing]
    exact Set.empty_disjoint _
  reconstruction := emptyTorusPairingHomeomorph _
  quotient_smooth := contMDiff_id
  quotient_oriented x := by
    refine ⟨LinearEquiv.refl ℝ _, fun v => ?_, ?_⟩
    · change v =
        mfderiv _ _ (id : (componentCarrier G.cutCarrier G.components i).Carrier → _) x v
      rw [mfderiv_id]
      rfl
    · change Orientation.map (Fin 3) (LinearEquiv.refl ℝ (TangentSpace _ x))
          ((componentCarrier G.cutCarrier G.components i).orientation.orientation x) =
        (componentCarrier G.cutCarrier G.components i).orientation.orientation x
      rw [Orientation.map_refl]
      rfl
  interiorImage := (componentCarrier G.cutCarrier G.components i).interior
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
  externalPiece _ := ⟨0, Nat.one_pos⟩
  external_owned _ := Set.subset_univ _

@[simp]
theorem ofPiece_components_count (G : TorusPresentation W) (i : Fin G.components.count) :
    (G.ofPiece i).components.count = 1 := rfl

@[simp]
theorem ofPiece_pairing_count (G : TorusPresentation W) (i : Fin G.components.count) :
    (G.ofPiece i).pairing.count = 0 := rfl

@[simp]
theorem ofPiece_externalCount (G : TorusPresentation W) (i : Fin G.components.count) :
    (G.ofPiece i).externalCount = Fintype.card (G.OwnedSide i) := rfl

theorem ofPiece_external (G : TorusPresentation W) (i : Fin G.components.count) :
    (G.ofPiece i).external = G.pieceBoundaryTori i := rfl

private def openImageDiffeomorph {W W' : CompactCarrier.{u}}
    (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier) (U : TopologicalSpace.Opens W.Carrier) :
    U ≃ₘ⟮W.model, W'.model⟯
      (⟨e '' U, e.toHomeomorph.isOpenMap _ U.isOpen⟩ : TopologicalSpace.Opens W'.Carrier) where
  toFun x := ⟨e x, Set.mem_image_of_mem e x.property⟩
  invFun y := ⟨e.symm y, by
    obtain ⟨x, hx, he⟩ := y.property
    rw [← he, e.symm_apply_apply]
    exact hx⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  contMDiff_toFun :=
    (ContMDiff.subtypeVal_comp_iff _ _).mp (e.contMDiff.comp contMDiff_subtype_val)
  contMDiff_invFun :=
    (ContMDiff.subtypeVal_comp_iff _ _).mp (e.symm.contMDiff.comp contMDiff_subtype_val)

def transport {W W' : CompactCarrier.{u}}
    (G : TorusPresentation W) (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (he : e.preservesOrientation W.orientation W'.orientation) : TorusPresentation W' where
  cutCarrier := G.cutCarrier
  components := G.components
  pairing := G.pairing
  externalCount := G.externalCount
  external := G.external.transport e
  cutExternal := G.cutExternal
  external_exhausted := by
    rw [← e.image_boundary (by simp), G.external_exhausted]
    ext x
    simp only [BoundaryTori.image, Set.mem_image, Set.mem_iUnion, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨i, y, rfl⟩, rfl⟩
      exact ⟨i, y, rfl⟩
    · rintro ⟨i, y, rfl⟩
      exact ⟨G.external.torusMap i y, ⟨i, y, rfl⟩, rfl⟩
  cut_boundary_exhausted := G.cut_boundary_exhausted
  external_disjoint := G.external_disjoint
  reconstruction := G.reconstruction.trans e.toHomeomorph
  quotient_smooth := e.contMDiff.comp G.quotient_smooth
  quotient_oriented := by
    intro x
    obtain ⟨L, hL, ho⟩ := G.quotient_oriented x
    let R := (e.mfderivToContinuousLinearEquiv (by simp)
      (G.reconstruction (G.pairing.quotientMap x))).toLinearEquiv
    refine ⟨L.trans R, ?_, ?_⟩
    · intro v
      change R (L v) = mfderiv G.cutCarrier.model W'.model
        (e ∘ (G.reconstruction ∘ G.pairing.quotientMap)) x v
      rw [mfderiv_comp (I' := W.model) x (e.mdifferentiable (by simp) _)
        (G.quotient_smooth.mdifferentiable (by simp) x)]
      rw [hL]
      rfl
    · have hmap : Orientation.map (Fin 3) (L.trans R) (G.cutCarrier.orientation.orientation x) =
          Orientation.map (Fin 3) R
            (Orientation.map (Fin 3) L (G.cutCarrier.orientation.orientation x)) := by
        generalize G.cutCarrier.orientation.orientation x = o
        induction o using Module.Ray.ind with
        | h v hv => rfl
      exact hmap.trans ((congrArg (fun o => Orientation.map (Fin 3) R o) ho).trans (he _))
  interiorImage := ⟨e '' G.interiorImage, e.toHomeomorph.isOpenMap _ G.interiorImage.isOpen⟩
  interiorDiffeomorph := G.interiorDiffeomorph.trans (openImageDiffeomorph e G.interiorImage)
  interior_map x := congrArg e (G.interior_map x)
  seam i := (G.seam i).trans e.toPartialDiffeomorph
  seam_source i := by
    change (G.seam i).source ∩ (G.seam i) ⁻¹' Set.univ = signedCollarSource
    simpa using G.seam_source i
  seam_zero i t := congrArg e (G.seam_zero i t)
  seam_positive i t s hs h := congrArg e (G.seam_positive i t s hs h)
  seam_negative i t s hs h := congrArg e (G.seam_negative i t s hs h)
  seam_interior := by
    intro i x hx
    have hi : e.symm x ∈ (G.seam i).target := hx.2
    have := (e.isLocalDiffeomorph (e.symm x)).isInteriorPoint_iff (by simp) |>.mp
      (G.seam_interior i hi)
    change W'.model.IsInteriorPoint x
    simpa only [e.apply_symm_apply] using this
  seam_disjoint := by
    intro i j hij
    have ht (k : Fin G.pairing.count) : ((G.seam k).trans e.toPartialDiffeomorph).target =
        e.symm ⁻¹' (G.seam k).target := by
      ext x
      change (x ∈ (Set.univ : Set W'.Carrier) ∧ e.symm x ∈ (G.seam k).target) ↔
        e.symm x ∈ (G.seam k).target
      simp only [Set.mem_univ, true_and]
    rw [ht, ht]
    exact (G.seam_disjoint hij).preimage _
  marked_collar i p hp := congrArg e (G.marked_collar i p hp)
  external_seam_disjoint := by
    intro i j
    change Disjoint ((G.external.collar i).trans e.toPartialDiffeomorph).target
      ((G.seam j).trans e.toPartialDiffeomorph).target
    change Disjoint (Set.univ ∩ e.symm ⁻¹' (G.external.collar i).target)
      (Set.univ ∩ e.symm ⁻¹' (G.seam j).target)
    simpa only [Set.univ_inter] using
      (G.external_seam_disjoint i j).preimage (fun x => e.symm x)
  leftPiece := G.leftPiece
  rightPiece := G.rightPiece
  left_owned := G.left_owned
  right_owned := G.right_owned
  externalPiece := G.externalPiece
  external_owned := G.external_owned

def opposite (G : TorusPresentation W) : TorusPresentation W.opposite where
  cutCarrier := G.cutCarrier.opposite
  components := G.components.opposite
  pairing := G.pairing.opposite
  externalCount := G.externalCount
  external := G.external.opposite
  cutExternal := G.cutExternal.opposite
  external_exhausted := G.external_exhausted
  cut_boundary_exhausted := G.cut_boundary_exhausted
  external_disjoint := G.external_disjoint
  reconstruction := G.reconstruction
  quotient_smooth := G.quotient_smooth
  quotient_oriented := by
    intro x
    obtain ⟨L, hL, ho⟩ := G.quotient_oriented x
    exact ⟨L, hL, (Orientation.map_neg _ _).trans (congrArg Neg.neg ho)⟩
  interiorImage := G.interiorImage
  interiorDiffeomorph := G.interiorDiffeomorph
  interior_map := G.interior_map
  seam := G.seam
  seam_source := G.seam_source
  seam_zero := G.seam_zero
  seam_positive := G.seam_positive
  seam_negative := G.seam_negative
  seam_interior := G.seam_interior
  seam_disjoint := G.seam_disjoint
  marked_collar := G.marked_collar
  external_seam_disjoint := G.external_seam_disjoint
  leftPiece := G.leftPiece
  rightPiece := G.rightPiece
  left_owned := G.left_owned
  right_owned := G.right_owned
  externalPiece := G.externalPiece
  external_owned := G.external_owned

section Opposite
variable (G : TorusPresentation W)

@[simp] theorem opposite_cutCarrier : G.opposite.cutCarrier = G.cutCarrier.opposite := rfl

@[simp] theorem opposite_components : G.opposite.components = G.components.opposite := rfl

@[simp] theorem opposite_pairing : G.opposite.pairing = G.pairing.opposite := rfl

@[simp] theorem opposite_externalCount : G.opposite.externalCount = G.externalCount := rfl

@[simp] theorem opposite_external : G.opposite.external = G.external.opposite := rfl

@[simp] theorem opposite_cutExternal : G.opposite.cutExternal = G.cutExternal.opposite := rfl

@[simp] theorem opposite_interiorImage : G.opposite.interiorImage = G.interiorImage := rfl

@[simp] theorem opposite_leftPiece : G.opposite.leftPiece = G.leftPiece := rfl

@[simp] theorem opposite_rightPiece : G.opposite.rightPiece = G.rightPiece := rfl

@[simp] theorem opposite_externalPiece : G.opposite.externalPiece = G.externalPiece := rfl

theorem opposite_reconstruction_apply (q : G.pairing.QuotientSpace) :
    G.opposite.reconstruction q = G.reconstruction q := rfl

theorem opposite_seam_apply (i : Fin G.pairing.count) (p : Torus × ℝ) :
    G.opposite.seam i p = G.seam i p := rfl

theorem opposite_transport {W' : CompactCarrier.{u}}
    (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (he : e.preservesOrientation W.orientation W'.orientation) :
    (G.transport e he).opposite =
      G.opposite.transport (W' := W'.opposite) e
        (Diffeomorph.preservesOrientation_opposite he) := rfl

end Opposite

end TorusPresentation

theorem torusPresentation_of_diffeomorph {M N : ConnectedClosedOrientedManifold.{u} 3}
    (G : TorusPresentation (NoCuts.carrier M))
    (f : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ N.Carrier) :
    Nonempty (TorusPresentation (NoCuts.carrier N)) := by
  rcases f.preservesOrientation_or_preservesOrientation_opposite
    M.orientation N.orientation with hf | hf
  · exact ⟨G.transport f hf⟩
  · have hp : f.preservesOrientation M.orientation.opposite N.orientation := by
      simpa only [ManifoldOrientation.opposite_opposite] using
        Diffeomorph.preservesOrientation_opposite hf
    exact ⟨G.opposite.transport (W' := NoCuts.carrier N) f hp⟩

end GC.Seifert

namespace GC.GraphManifold.RawGraphPresentation
open GC.Seifert
variable {W : CompactCarrier.{u}}

def toTorusPresentation (G : RawGraphPresentation W) : TorusPresentation W where
  cutCarrier := G.cutCarrier
  components := G.components
  pairing := G.pairing
  externalCount := G.externalCount
  external := G.external
  cutExternal := G.cutExternal
  external_exhausted := G.external_exhausted
  cut_boundary_exhausted := G.cut_boundary_exhausted
  external_disjoint := G.external_disjoint
  reconstruction := G.reconstruction
  quotient_smooth := G.quotient_smooth
  quotient_oriented := G.quotient_oriented
  interiorImage := G.interiorImage
  interiorDiffeomorph := G.interiorDiffeomorph
  interior_map := G.interior_map
  seam := G.seam
  seam_source := G.seam_source
  seam_zero := G.seam_zero
  seam_positive := G.seam_positive
  seam_negative := G.seam_negative
  seam_interior := G.seam_interior
  seam_disjoint := G.seam_disjoint
  marked_collar := G.marked_collar
  external_seam_disjoint := G.external_seam_disjoint
  leftPiece := G.leftPiece
  rightPiece := G.rightPiece
  left_owned := G.left_owned
  right_owned := G.right_owned
  externalPiece := G.externalPiece
  external_owned := G.external_owned

section Forget
variable (G : RawGraphPresentation W)

@[simp] theorem toTorusPresentation_cutCarrier : G.toTorusPresentation.cutCarrier = G.cutCarrier :=
  rfl

@[simp] theorem toTorusPresentation_components :
    G.toTorusPresentation.components = G.components := rfl

@[simp] theorem toTorusPresentation_pairing : G.toTorusPresentation.pairing = G.pairing := rfl

@[simp] theorem toTorusPresentation_externalCount :
    G.toTorusPresentation.externalCount = G.externalCount := rfl

@[simp] theorem toTorusPresentation_external : G.toTorusPresentation.external = G.external := rfl

@[simp] theorem toTorusPresentation_cutExternal :
    G.toTorusPresentation.cutExternal = G.cutExternal := rfl

@[simp] theorem toTorusPresentation_reconstruction :
    G.toTorusPresentation.reconstruction = G.reconstruction := rfl

@[simp] theorem toTorusPresentation_interiorImage :
    G.toTorusPresentation.interiorImage = G.interiorImage := rfl

@[simp] theorem toTorusPresentation_seam : G.toTorusPresentation.seam = G.seam := rfl

@[simp] theorem toTorusPresentation_leftPiece :
    G.toTorusPresentation.leftPiece = G.leftPiece := rfl

@[simp] theorem toTorusPresentation_rightPiece :
    G.toTorusPresentation.rightPiece = G.rightPiece := rfl

@[simp] theorem toTorusPresentation_externalPiece :
    G.toTorusPresentation.externalPiece = G.externalPiece := rfl

@[simp] theorem withFibration_toTorusPresentation :
    G.toTorusPresentation.withFibration G.fibration = G := rfl

theorem toTorusPresentation_injective_on_fibration :
    Function.Injective (fun G : RawGraphPresentation W =>
      (⟨G.toTorusPresentation, G.fibration⟩ : Σ T : TorusPresentation W, T.Fibration)) :=
  fun _ _ h =>
    congrArg (fun p : Σ T : TorusPresentation W, T.Fibration => p.1.withFibration p.2) h

theorem toTorusPresentation_side : G.toTorusPresentation.Side = G.Side := rfl

theorem toTorusPresentation_sidePiece : G.toTorusPresentation.sidePiece = G.sidePiece := by
  funext s
  rcases s with k | k | k <;> rfl

theorem toTorusPresentation_sideCollar : G.toTorusPresentation.sideCollar = G.sideCollar := by
  funext s
  rcases s with k | k | k <;> rfl

theorem toTorusPresentation_cutMap : G.toTorusPresentation.cutMap = G.cutMap := rfl

theorem toTorusPresentation_sideIndex : G.toTorusPresentation.sideIndex = G.sideIndex := by
  funext s
  rcases s with k | k | k <;> rfl

theorem toTorusPresentation_sideRegion : G.toTorusPresentation.sideRegion = G.sideRegion := by
  funext a
  rcases a with k | k <;> rfl

theorem toTorusPresentation_ownedSide (i : Fin G.components.count) :
    G.toTorusPresentation.OwnedSide i = G.OwnedSide i := by
  change {s : G.Side // G.toTorusPresentation.sidePiece s = i} = _
  rw [toTorusPresentation_sidePiece]
  rfl

set_option smartUnfolding false in
theorem toTorusPresentation_ofPiece (i : Fin G.components.count) :
    (G.ofPiece i).toTorusPresentation = G.toTorusPresentation.ofPiece i := rfl

theorem toTorusPresentation_transport {W' : CompactCarrier.{u}}
    (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (he : e.preservesOrientation W.orientation W'.orientation) :
    (G.transport e he).toTorusPresentation = G.toTorusPresentation.transport e he := rfl

theorem toTorusPresentation_opposite :
    G.opposite.toTorusPresentation = G.toTorusPresentation.opposite := rfl

end Forget

end GC.GraphManifold.RawGraphPresentation

namespace GC.Seifert.TorusPresentation
variable {W : CompactCarrier.{u}}

@[simp] theorem toTorusPresentation_withFibration (G : TorusPresentation W) (F : G.Fibration) :
    (G.withFibration F).toTorusPresentation = G := rfl

end GC.Seifert.TorusPresentation
