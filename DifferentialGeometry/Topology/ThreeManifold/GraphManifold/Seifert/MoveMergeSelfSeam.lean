import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveMergeProduct
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.EmbeddedPieces

/-!
# Reconstructing a self-seam after a single filling

The two original pieces have exactly the filling seam and one host self-seam. Identifying only
that filling seam leaves the two sides of the self-seam as distinct boundary tori. Their original
matching may be any orientation-reversing torus diffeomorphism. The reconstruction uses a single
piece and a single seam, and a bare annulus product identification supplies elementarity after
recollaring. The original admitted merge declarations are never used.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.ElementaryPresentation

variable {Q : ConnectedClosedOrientedManifold.{u} 3}
  (E : ElementaryPresentation (NoCuts.carrier Q))
  (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
  (k : Fin E.toTorus.pairing.count)
  (hl : E.toTorus.leftPiece k = E.hostPiece j b)
  (hr : E.toTorus.rightPiece k = E.hostPiece j b)

include h hl hr in
theorem selfSeam_numbers : E.kind (E.hostPiece j b) = 3 ∧
    E.toTorus.components.count = 2 ∧ E.complexity = 2 :=
  ⟨(h.host_sides hl hr).1, h.components_count_of_selfSeam hl hr,
    h.complexity_of_selfSeam hl hr⟩

include h hl hr in
theorem mergeSelfSeam_all_seams (r : Fin E.toTorus.pairing.count) : r = j ∨ r = k := by
  classical
  have hne : j ≠ k := (h.ne_of_selfSeam hl hr).symm
  have hcard : E.toTorus.pairing.count = 2 := h.complexity_of_selfSeam hl hr
  have hall : ({j, k} : Finset (Fin E.toTorus.pairing.count)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne, Fintype.card_fin, hcard]
  have hm : r ∈ ({j, k} : Finset (Fin E.toTorus.pairing.count)) := by
    rw [hall]
    exact Finset.mem_univ r
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hm

def mergeSelfSeamBoundarySide (c : Bool) :
    E.toTorus.AlongBoundarySide (E.toTorus.seamPair j) {j} :=
  ⟨E.toTorus.pairSide k c, h.mem_seamPair_of_selfSeam hl hr _, by
    have hn : k ∉ ({j} : Finset (Fin E.toTorus.pairing.count)) := by
      simpa only [Finset.mem_singleton] using h.ne_of_selfSeam hl hr
    cases c <;> exact hn⟩

theorem mergeSelfSeamBoundarySide_bijective :
    Function.Bijective (mergeSelfSeamBoundarySide E j b h k hl hr) := by
  constructor
  · intro c c' he
    have hv := congrArg Subtype.val he
    change E.toTorus.pairSide k c = E.toTorus.pairSide k c' at hv
    cases c <;> cases c' <;> simp_all [TorusPresentation.pairSide]
  · intro a
    rcases a with ⟨s, hs, hn⟩
    rcases s with r | r | r
    · rcases E.mergeSelfSeam_all_seams j b h k hl hr r with he | he
      · exact (hn (Finset.mem_singleton.mpr he)).elim
      · subst r
        exact ⟨true, rfl⟩
    · rcases E.mergeSelfSeam_all_seams j b h k hl hr r with he | he
      · exact (hn (Finset.mem_singleton.mpr he)).elim
      · subst r
        exact ⟨false, rfl⟩
    · have hz := E.toTorus.externalCount_eq_zero
      exact (Nat.not_lt_zero r.val (hz ▸ r.isLt)).elim

def selfSeamPortEquiv : Fin 2 ≃
    E.toTorus.AlongBoundarySide (E.toTorus.seamPair j) {j} :=
  finTwoEquiv.trans (Equiv.ofBijective _ (E.mergeSelfSeamBoundarySide_bijective j b h k hl hr))

def selfSeamCollar (i : Fin 2) :
    PartialDiffeomorph halfCollarModel (fillingProductCarrier E j).model
      (Torus × EuclideanHalfSpace 1) (fillingProductCarrier E j).Carrier ∞ :=
  fillingProductCollar E j (E.selfSeamPortEquiv j b h k hl hr i)

theorem selfSeamCollar_source (i : Fin 2) :
    (E.selfSeamCollar j b h k hl hr i).source = halfCollarSource :=
  fillingProductCollar_source E j _

theorem selfSeamCollar_disjoint : Pairwise fun i i' : Fin 2 =>
    Disjoint (E.selfSeamCollar j b h k hl hr i).target
      (E.selfSeamCollar j b h k hl hr i').target := by
  intro i i' hi
  exact fillingProductCollar_disjoint E j
    (fun he => hi ((E.selfSeamPortEquiv j b h k hl hr).injective he))

theorem selfSeam_boundary_exhausted :
    (fillingProductCarrier E j).model.boundary (fillingProductCarrier E j).Carrier =
      ⋃ i : Fin 2, Set.range fun t => E.selfSeamCollar j b h k hl hr i (t, halfZero) := by
  ext x
  change (fillingProductCarrier E j).model.IsBoundaryPoint x ↔ _
  rw [fillingProduct_boundary_iff]
  constructor
  · rintro ⟨a, t, he⟩
    obtain ⟨i, rfl⟩ := (E.selfSeamPortEquiv j b h k hl hr).surjective a
    exact Set.mem_iUnion.mpr ⟨i, t, he.symm⟩
  · intro hx
    obtain ⟨i, t, he⟩ := Set.mem_iUnion.mp hx
    exact ⟨E.selfSeamPortEquiv j b h k hl hr i, t, he.symm⟩

include h hl hr in
theorem selfSeamFold_surjective : Function.Surjective (fillingProductFold E j) := by
  intro w
  have hw : w ∈ ⋃ i, Set.range (fun x : E.toTorus.components.piece i =>
      E.toTorus.cutMap x.val) := E.toTorus.covers_cutMap.symm ▸ Set.mem_univ w
  obtain ⟨i, x, hx⟩ := Set.mem_iUnion.mp hw
  let y : (E.toTorus.subCarrier (E.toTorus.seamPair j)).Carrier :=
    ⟨x.val, E.toTorus.piece_subset_subPiece _ (h.mem_seamPair_of_selfSeam hl hr i) x.property⟩
  exact ⟨(E.toTorus.restrictAlongPairing _ {j} (fillingProduct_internal E j)).quotientMap y, hx⟩

include h hl hr in
theorem selfSeamFold_overlap (x y : (fillingProductCarrier E j).Carrier)
    (he : fillingProductFold E j x = fillingProductFold E j y) :
    x = y ∨ ∃ t : Torus, fillingProductFold E j x = E.toTorus.seam k (t, 0) := by
  obtain ⟨x', rfl⟩ := Quotient.exists_rep x
  obtain ⟨y', rfl⟩ := Quotient.exists_rep y
  have hrel : E.toTorus.pairing.gluing.rel x'.val y'.val :=
    Quotient.exact (E.toTorus.reconstruction.injective he)
  rcases hrel with hv | ⟨r, hx, hy⟩
  · exact Or.inl (congrArg _ (Subtype.ext hv))
  · rcases E.mergeSelfSeam_all_seams j b h k hl hr r with hj | hk
    · subst r
      exact Or.inl (Quotient.sound
        (E.toTorus.restrictAlongGluing_rel_of_selected_flip _ {j}
          (fillingProduct_internal E j) (Finset.mem_singleton_self j) hx hy))
    · subst r
      right
      rcases hx with hx | hx
      · refine ⟨(E.toTorus.pairing.leftParam k).symm ⟨x'.val, hx⟩, ?_⟩
        change E.toTorus.cutMap x'.val = _
        rw [E.toTorus.seam_zero]
        exact congrArg E.toTorus.cutMap
          (congrArg Subtype.val
            ((E.toTorus.pairing.leftParam k).apply_symm_apply ⟨x'.val, hx⟩)).symm
      · refine ⟨(E.toTorus.pairing.matching k).symm
          ((E.toTorus.pairing.rightParam k).symm ⟨x'.val, hx⟩), ?_⟩
        change E.toTorus.cutMap x'.val = _
        change E.toTorus.cutMap x'.val = E.toTorus.seamTorus k
          ((E.toTorus.pairing.matching k).symm
            ((E.toTorus.pairing.rightParam k).symm ⟨x'.val, hx⟩))
        rw [E.toTorus.seamTorus_eq_cutMap_right, Diffeomorph.apply_symm_apply]
        exact congrArg E.toTorus.cutMap
          (congrArg Subtype.val
            ((E.toTorus.pairing.rightParam k).apply_symm_apply ⟨x'.val, hx⟩)).symm

def selfSeamCutSystem (B : PlanarBase.{u} 2)
    (e : (B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
      (fillingProductCarrier E j).model⟯ (fillingProductCarrier E j).Carrier) :
    EmbeddedCutSystem (NoCuts.carrier Q) .withBoundary := by
  let C := fillingProductCarrier E j
  letI : ConnectedSpace C.Carrier := e.surjective.connectedSpace e.contMDiff_toFun.continuous
  refine {
    count := 1
    count_pos := by norm_num
    Piece := fun i => C.Carrier
    topology := fun i => C.topology
    charts := fun i => C.charts
    manifold := fun i => C.smooth
    compact := fun i => C.compact
    hausdorff := fun i => C.hausdorff
    secondCountable := fun i => C.secondCountable
    connected := fun i => inferInstance
    map := fun i => fillingProductFold E j
    smooth := fun i => fillingProductFold_smooth E j
    mfderiv_bijective := fun i => fillingProductFold_mfderiv E j
    covers := ?_
    torusCount := fun i => 2
    collar := fun i => E.selfSeamCollar j b h k hl hr
    collar_source := fun i => E.selfSeamCollar_source j b h k hl hr
    collar_disjoint := fun i => E.selfSeamCollar_disjoint j b h k hl hr
    boundary_exhausted := fun i => E.selfSeam_boundary_exhausted j b h k hl hr
    seamCount := 1
    side := fun c d => ⟨c, finTwoEquiv.symm d⟩
    externalCount := 0
    externalSide := Fin.elim0
    sides_bijective := ?_
    matching := fun c => E.toTorus.pairing.matching k
    seam := fun c => E.toTorus.seam k
    seam_source := fun c => E.toTorus.seam_source k
    seam_neg := ?_
    seam_pos := ?_
    seam_interior := fun c => E.toTorus.seam_interior k
    external_local := ?_
    overlap := ?_ }
  · simp only [Set.iUnion_const, Set.range_eq_univ.mpr
      (E.selfSeamFold_surjective j b h k hl hr)]
  · constructor
    · intro a a' he
      rcases a with ⟨c, d⟩ | a
      · rcases a' with ⟨c', d'⟩ | a'
        · apply congrArg Sum.inl
          apply Prod.ext
          · exact congrArg Sigma.fst he
          · exact finTwoEquiv.symm.injective (congrArg Sigma.snd he)
        · exact a'.elim0
      · exact a.elim0
    · rintro ⟨c, d⟩
      exact ⟨.inl (c, finTwoEquiv d), by simp⟩
  · intro c t s hs hlt
    change E.toTorus.seam k (t, s) = fillingProductFold E j
      (fillingProductCollar E j
        (E.selfSeamPortEquiv j b h k hl hr (finTwoEquiv.symm true))
          (t, halfPoint (-s) (neg_nonneg.2 hs)))
    rw [show E.selfSeamPortEquiv j b h k hl hr (finTwoEquiv.symm true) =
      E.mergeSelfSeamBoundarySide j b h k hl hr true by simp [selfSeamPortEquiv]]
    rw [fillingProductFold_collar E j _ (by
      change -s < 1
      linarith)]
    exact E.toTorus.seam_negative k t s hs hlt
  · intro c t s hs hlt
    change E.toTorus.seam k (t, s) = fillingProductFold E j
      (fillingProductCollar E j
        (E.selfSeamPortEquiv j b h k hl hr (finTwoEquiv.symm false))
          (E.toTorus.pairing.matching k t, halfPoint s hs))
    rw [show E.selfSeamPortEquiv j b h k hl hr (finTwoEquiv.symm false) =
      E.mergeSelfSeamBoundarySide j b h k hl hr false by simp [selfSeamPortEquiv]]
    rw [fillingProductFold_collar E j _ (by exact hlt)]
    exact E.toTorus.seam_positive k t s hs hlt
  · intro i
    exact i.elim0
  · intro i i' x y he
    rcases E.selfSeamFold_overlap j b h k hl hr x y he with hxy | ⟨t, ht⟩
    · left
      cases Subsingleton.elim i i'
      exact congrArg (Sigma.mk i) hxy
    · exact Or.inr ⟨0, t, ht⟩

theorem selfSeamCutSystem_pairing_count (B : PlanarBase.{u} 2)
    (e : (B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
      (fillingProductCarrier E j).model⟯ (fillingProductCarrier E j).Carrier) :
    (E.selfSeamCutSystem j b h k hl hr B e).toTorusPresentation.pairing.count = 1 := rfl

theorem selfSeamCutSystem_matching (B : PlanarBase.{u} 2)
    (e : (B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
      (fillingProductCarrier E j).model⟯ (fillingProductCarrier E j).Carrier)
    (c : Fin (E.selfSeamCutSystem j b h k hl hr B e).toTorusPresentation.pairing.count) :
    (E.selfSeamCutSystem j b h k hl hr B e).toTorusPresentation.pairing.matching c =
      E.toTorus.pairing.matching k := rfl

include b h k hl hr in
theorem selfSeamPresentation_of_product (B : PlanarBase.{u} 2)
    (e : (B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
      (fillingProductCarrier E j).model⟯ (fillingProductCarrier E j).Carrier) :
    ∃ E' : ElementaryPresentation (NoCuts.carrier Q), E'.complexity = 1 := by
  let S := E.selfSeamCutSystem j b h k hl hr B e
  let T := S.toTorusPresentation
  have hcard (i : Fin T.components.count) : Fintype.card (T.OwnedSide i) = 2 :=
    (Fintype.card_congr (S.port i)).symm.trans (Fintype.card_fin 2)
  obtain ⟨F, hF⟩ := T.exists_elementary_of_forall_piece (fun i =>
    ⟨2, by simp, hcard i, B, ⟨e.trans (S.pieceDiffeomorph i)⟩⟩)
  let F' := F.toPieceSystem.toElementaryPresentation
  have hcount : F'.complexity = F.complexity :=
    F.toPieceSystem.toElementaryPresentation_pairing_count
  exact ⟨F', hcount.trans hF⟩

include b h k hl hr in
theorem exists_complexity_one_of_selfSeam_of_linearSeam (hlin : E.IsLinearSeam j) :
    ∃ E' : ElementaryPresentation (NoCuts.carrier Q), E'.complexity = 1 := by
  obtain ⟨B, ⟨e⟩⟩ := E.exists_fillingProduct_of_hostKind_eq_three_of_linearSeam j b h
    (h.host_sides hl hr).1 hlin
  exact E.selfSeamPresentation_of_product j b h k hl hr B e

include b h k hl hr in
theorem exists_complexity_one_of_selfSeam_core (hT : TorusMappingClassLinear) :
    ∃ E' : ElementaryPresentation (NoCuts.carrier Q), E'.complexity = 1 := by
  obtain ⟨B, ⟨e⟩⟩ := E.exists_fillingProduct_of_hostKind_eq_three_of_torusMappingClassLinear hT
    j b h (h.host_sides hl hr).1
  exact E.selfSeamPresentation_of_product j b h k hl hr B e

include b h k hl hr in
theorem exists_complexity_one_of_selfSeam_redundant_of_linearSeam
    (hH : E.kind (E.hostPiece j b) = 3) (hc : E.toTorus.components.count = 2)
    (hn : E.complexity = 2) (hlin : E.IsLinearSeam j) :
    ∃ E' : ElementaryPresentation (NoCuts.carrier Q), E'.complexity = 1 := by
  obtain ⟨B, ⟨e⟩⟩ := E.exists_fillingProduct_of_hostKind_eq_three_of_linearSeam j b h hH hlin
  obtain ⟨E', hE'⟩ := E.selfSeamPresentation_of_product j b h k hl hr B e
  have hcount : E.complexity = E.toTorus.components.count := hn.trans hc.symm
  refine ⟨E', ?_⟩
  calc
    E'.complexity = E.complexity - 1 := by rw [hE', hcount, hc]
    _ = 1 := by rw [hcount, hc]

include b h k hl hr in
theorem exists_complexity_one_of_selfSeam_redundant
    (hH : E.kind (E.hostPiece j b) = 3) (hc : E.toTorus.components.count = 2)
    (hn : E.complexity = 2) (hT : TorusMappingClassLinear) :
    ∃ E' : ElementaryPresentation (NoCuts.carrier Q), E'.complexity = 1 := by
  obtain ⟨B, ⟨e⟩⟩ :=
    E.exists_fillingProduct_of_hostKind_eq_three_of_torusMappingClassLinear hT j b h hH
  obtain ⟨E', hE'⟩ := E.selfSeamPresentation_of_product j b h k hl hr B e
  have hcount : E.complexity = E.toTorus.components.count := hn.trans hc.symm
  refine ⟨E', ?_⟩
  calc
    E'.complexity = E.complexity - 1 := by rw [hE', hcount, hc]
    _ = 1 := by rw [hcount, hc]

end GC.Seifert.ElementaryPresentation
