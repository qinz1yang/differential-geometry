import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveAbsorb
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.AnnulusLongCollar
import DifferentialGeometry.Topology.Manifold.CollarStretch

/-!
# The merged piece of an absorb contraction is the solid torus

Lane N3b: `mergedSolidTorus` proves `MergedSolidTorus` of `Seifert/MoveAbsorb.lean`, so the absorb
move needs only `ContractionRecollar` (`moveAbsorb_of_contractionRecollar`).

Let `j` be an absorb seam of an elementary presentation on side `b`: `V = seamPiece j b` is a solid
torus, `A = hostPiece j b` is `P₂ × S¹` over an annulus, and the contraction of `{V, A}` has the
region `R = cutMap (V ∪ A)` (with the `restrictCarrier` structure) as its merged piece
(`contractLastDiffeomorph`). `IsAbsorbSeam.exists_diffeomorph_region` gives `V ≅ R` by the collar
stretch `exists_diffeomorph_collarStretch` of `CollarStretch.lean`, with `X = V`, `F = cutMap`
(`regionMap`), the collar `c` of `V` at `j`, `a = 10` and the external collar
`ℓ : T² × [0, 11) → R` built as follows. `exists_annulus_longCollar` gives a half collar `Λ` of `A`
on `T² × [0, 10)` from the far port of `A` to its port on `j`: near `0` it is the presentation
collar of the far port, near `10` the presentation collar of the port on `j` read backwards. Then
`ℓ (t, u)` is `cutMap (Λ (μ t, u))` for `u < 10` and the seam chart `seam j (ν t, ε (u - 10))` for
`u ≥ 10`, with `ν = pairTwist j b`, `ε = seamSign b` and `μ = ι ∘ (pairTwist j !b)⁻¹ ∘ ν` (`ι`
inverts the first circle), so that both formulas agree near `u = 10` and
`cutMap (c (t, s)) = ℓ (t, s + 10)`. Locally `ℓ` is the crossing collar of the far port
(`crossRegion`) near `0`, the cut map at an interior point of `A`
(`isLocalDiffeomorphAt_regionMap`) in the middle and the seam chart of the region (`seamRegion`,
composed with `seamCoordinate`) near `10`. Injectivity and covering come from the gluing relation:
two distinct points of `V ∪ A` with the same image lie on the two sides of `j`
(`IsAbsorbSeam.cutMap_eq_block`), and `Λ` never reaches the torus of `A` on `j`.
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

namespace TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)

theorem cutMap_continuous : Continuous T.cutMap :=
  T.reconstruction.continuous.comp T.pairing.quotientMap.continuous

theorem piece_eq_of_mem {x : T.cutCarrier.Carrier} {i i' : Fin T.components.count}
    (hi : x ∈ T.components.piece i) (hi' : x ∈ T.components.piece i') : i = i' := by
  by_contra h
  exact (T.components.disjoint h).le_bot ⟨hi, hi'⟩

theorem cutMap_eq_cases {x y : T.cutCarrier.Carrier} (h : T.cutMap x = T.cutMap y) :
    x = y ∨ ∃ k, (x ∈ T.pairing.gluing.left k ∧ y ∈ T.pairing.gluing.right k) ∨
      (x ∈ T.pairing.gluing.right k ∧ y ∈ T.pairing.gluing.left k) := by
  have hrel : T.pairing.gluing.rel x y := Quotient.exact (T.reconstruction.injective h)
  rcases hrel with rfl | ⟨k, hx, rfl⟩
  · exact Or.inl rfl
  · right
    refine ⟨k, ?_⟩
    rcases hx with hx | hx
    · left
      rw [T.pairing.gluing.flip_of_mem_left hx]
      exact ⟨hx, (T.pairing.gluing.attaching k ⟨x, hx⟩).2⟩
    · right
      rw [T.pairing.gluing.flip_of_mem_right hx]
      exact ⟨hx, ((T.pairing.gluing.attaching k).symm ⟨x, hx⟩).2⟩

theorem eq_leftCollar_of_mem {k : Fin T.pairing.count} {y : T.cutCarrier.Carrier}
    (hy : y ∈ T.pairing.gluing.left k) :
    y = T.sideCollar (.inl k) ((T.pairing.leftParam k).symm ⟨y, hy⟩, halfZero) := by
  change y = T.pairing.leftCollar k _
  rw [T.pairing.left_zero, Homeomorph.apply_symm_apply]

theorem eq_rightCollar_of_mem {k : Fin T.pairing.count} {y : T.cutCarrier.Carrier}
    (hy : y ∈ T.pairing.gluing.right k) :
    y = T.sideCollar (.inr (.inl k)) ((T.pairing.rightParam k).symm ⟨y, hy⟩, halfZero) := by
  change y = T.pairing.rightCollar k _
  rw [T.pairing.right_zero, Homeomorph.apply_symm_apply]

def pairTwist (j : Fin T.pairing.count) : Bool → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  | true => Diffeomorph.refl torusModel Torus ∞
  | false => (T.pairing.matching j).symm

end TorusPresentation

def seamSign : Bool → ℝ
  | true => -1
  | false => 1

theorem seamSign_not (b : Bool) : seamSign (!b) = -seamSign b := by
  cases b <;> norm_num [seamSign]

theorem seamSign_mul_self (b : Bool) : seamSign b * seamSign b = 1 := by
  cases b <;> norm_num [seamSign]

namespace TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)

theorem cutMap_sideCollar_pairSide_eq (j : Fin T.pairing.count) (b : Bool)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    T.cutMap (T.sideCollar (T.pairSide j b) p) =
      T.seam j (T.pairTwist j b p.1, seamSign b * p.2.val 0) := by
  cases b
  · rw [show seamSign false * p.2.val 0 = p.2.val 0 by simp [seamSign]]
    exact T.cutMap_rightCollar j hp
  · rw [show seamSign true * p.2.val 0 = -(p.2.val 0) by simp [seamSign]]
    exact T.cutMap_leftCollar j hp

variable (S : Finset (Fin T.components.count)) (hext : ∀ i, T.externalPiece i ∉ S)
  (hk : T.cutCarrier.kind = .withBoundary)

theorem cutMap_mem_region {i : Fin T.components.count} (hi : i ∈ S)
    (x : T.components.piece i) : T.cutMap x ∈ Set.range (T.restrictMap S) := by
  rw [range_restrictMap]
  exact ⟨x.val, T.piece_subset_subPiece S hi x.property, rfl⟩

def regionMap {i : Fin T.components.count} (hi : i ∈ S) (x : T.components.piece i) :
    (T.contractRegion S hext hk).Carrier :=
  ⟨T.cutMap x, T.cutMap_mem_region S hi x⟩

theorem regionMap_val {i : Fin T.components.count} (hi : i ∈ S) (x : T.components.piece i) :
    (T.regionMap S hext hk hi x).val = T.cutMap x := rfl

theorem continuous_regionMap {i : Fin T.components.count} (hi : i ∈ S) :
    Continuous (T.regionMap S hext hk hi) :=
  (T.cutMap_continuous.comp continuous_subtype_val).subtype_mk _

theorem isLocalDiffeomorphAt_val_region (r : (T.contractRegion S hext hk).Carrier)
    (hr : r.val ∉ T.crossingSurface S) :
    IsLocalDiffeomorphAt T.cutCarrier.model W.model ∞
      (fun z : (T.contractRegion S hext hk).Carrier => z.val) r := by
  have hrint : r.val ∈ interior (Set.range (T.restrictMap S)) :=
    interior_maximal Set.sdiff_subset (T.isOpen_range_diff_crossingSurface S) ⟨r.property, hr⟩
  exact (recast_isLocalDiffeomorphAt_iff _ _ _ _ r).mpr
    ((T.restrictAtlas S hext).isLocalDiffeomorphAt_subtype_val hrint)

theorem isLocalDiffeomorphAt_regionMap {i : Fin T.components.count} (hi : i ∈ S)
    {x : T.components.piece i}
    (hx : T.cutCarrier.model.IsInteriorPoint (x : T.cutCarrier.Carrier)) :
    IsLocalDiffeomorphAt T.cutCarrier.model T.cutCarrier.model ∞ (T.regionMap S hext hk hi) x := by
  have hne : Nonempty (T.components.piece i) := ⟨x⟩
  have hsub : IsLocalDiffeomorphAt T.cutCarrier.model T.cutCarrier.model ∞
      (Subtype.val : T.components.piece i → T.cutCarrier.Carrier) x :=
    (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph T.cutCarrier.model
      (T.components.piece i) hne).isLocalDiffeomorphAt T.cutCarrier.model T.cutCarrier.model ∞
      (Set.mem_univ _)
  have hcomp := hsub.comp (K := W.model) (P := W.Carrier) (T.isLocalDiffeomorphAt_cutMap hx)
  have hreg := T.isLocalDiffeomorphAt_val_region S hext hk (T.regionMap S hext hk hi x)
    (fun hc => (T.cutMap_pieceInterior_subset_region S hi ⟨x.val, ⟨x.property, hx⟩, rfl⟩).2 hc)
  exact DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_of_comp
    (T.continuous_regionMap S hext hk hi).continuousAt hreg hcomp

def crossRegion (a : T.RestrictSide S) :
    PartialDiffeomorph halfCollarModel (T.contractRegion S hext hk).model
      (Torus × EuclideanHalfSpace 1) (T.contractRegion S hext hk).Carrier ∞ :=
  recastPD (T.restrictCarrier S hext) _ hk.symm (T.crossCollar S hext a)

theorem crossRegion_source (a : T.RestrictSide S) :
    (T.crossRegion S hext hk a).source = halfCollarSource :=
  (recastPD_source _ _ _ _).trans (T.crossCollar_source S hext a)

theorem crossRegion_val (a : T.RestrictSide S) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    (T.crossRegion S hext hk a p).val = T.cutMap (T.sideCollar a.val p) :=
  (congrArg Subtype.val (recastPD_apply _ _ _ _ p)).trans (T.crossCollar_val S hext a hp)

def seamRegion (j : Fin (T.restrictPairing S).count) :
    PartialDiffeomorph signedCollarModel (T.contractRegion S hext hk).model (Torus × ℝ)
      (T.contractRegion S hext hk).Carrier ∞ :=
  recastPD (T.restrictCarrier S hext) _ hk.symm (T.restrictSeam S hext j)

theorem seamRegion_source (j : Fin (T.restrictPairing S).count) :
    (T.seamRegion S hext hk j).source = signedCollarSource :=
  (recastPD_source _ _ _ _).trans (T.restrictSeam_source S hext j)

theorem seamRegion_val (j : Fin (T.restrictPairing S).count) {p : Torus × ℝ}
    (hp : p ∈ signedCollarSource) :
    (T.seamRegion S hext hk j p).val = T.seam (T.keptSeam S j).val p :=
  (congrArg Subtype.val (recastPD_apply _ _ _ _ p)).trans (T.restrictSeam_val S hext j hp)

def contractLastDiffeomorph
    (hconn : IsConnected (Set.range (T.restrictMap S) \ T.crossingSurface S)) :
    (T.contractRegion S hext hk).Carrier ≃ₘ⟮T.cutCarrier.model,
      (T.contract S hext hk hconn).cutCarrier.model⟯
      (T.contract S hext hk hconn).components.piece (T.contractLast S hext hk hconn) where
  toFun r := ⟨Sum.inr r, by
    change Sum.inr r ∈ (T.contractPiece S hext hk (Fin.last _) : Set (T.ContractCut S hext hk))
    rw [contractPiece_last]
    exact ⟨r, rfl⟩⟩
  invFun y := Sum.elim (fun _ => ⟨hconn.nonempty.some, hconn.nonempty.some_mem.1⟩) id y.val
  left_inv _ := rfl
  right_inv y := by
    obtain ⟨y, hy⟩ := y
    have hy' : y ∈ (T.contractPiece S hext hk (Fin.last _) : Set (T.ContractCut S hext hk)) := hy
    rw [contractPiece_last] at hy'
    obtain ⟨r, rfl⟩ := hy'
    rfl
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    exact (ContMDiff.inr : ContMDiff T.cutCarrier.model T.cutCarrier.model ∞
      (@Sum.inr (T.subCarrier Sᶜ).Carrier (T.contractRegion S hext hk).Carrier))
  contMDiff_invFun := by
    have h1 : ContMDiff T.cutCarrier.model T.cutCarrier.model ∞
        (Sum.elim (fun _ => ⟨hconn.nonempty.some, hconn.nonempty.some_mem.1⟩) id :
          T.ContractCut S hext hk → (T.contractRegion S hext hk).Carrier) :=
      ContMDiff.sumElim contMDiff_const contMDiff_id
    have h2 : ContMDiff (T.contract S hext hk hconn).cutCarrier.model
        (T.contract S hext hk hconn).cutCarrier.model ∞
        (Subtype.val : (T.contract S hext hk hconn).components.piece
          (T.contractLast S hext hk hconn) → (T.contract S hext hk hconn).cutCarrier.Carrier) :=
      contMDiff_subtype_val
    exact h1.comp h2

end TorusPresentation

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}} {E : ElementaryPresentation W}
  {j : Fin E.toTorus.pairing.count} {b : Bool}

theorem seamPiece_mem_seamPair (j : Fin E.toTorus.pairing.count) (b : Bool) :
    E.seamPiece j b ∈ E.toTorus.seamPair j :=
  (E.mem_seamPair_iff j b _).mpr (Or.inl rfl)

theorem hostPiece_mem_seamPair (j : Fin E.toTorus.pairing.count) (b : Bool) :
    E.hostPiece j b ∈ E.toTorus.seamPair j :=
  (E.mem_seamPair_iff j b _).mpr (Or.inr rfl)

theorem IsAbsorbSeam.cutMap_eq_block (h : E.IsAbsorbSeam j b)
    {x y : E.toTorus.cutCarrier.Carrier} {i i' : Fin E.toTorus.components.count}
    (hi : i ∈ E.toTorus.seamPair j) (hi' : i' ∈ E.toTorus.seamPair j)
    (hx : x ∈ E.toTorus.components.piece i) (hy : y ∈ E.toTorus.components.piece i')
    (hxy : E.toTorus.cutMap x = E.toTorus.cutMap y) (hne : x ≠ y) :
    (x ∈ E.toTorus.pairing.gluing.left j ∧ y ∈ E.toTorus.pairing.gluing.right j) ∨
      (x ∈ E.toTorus.pairing.gluing.right j ∧ y ∈ E.toTorus.pairing.gluing.left j) := by
  rcases E.toTorus.cutMap_eq_cases hxy with he | ⟨k, hk⟩
  · exact (hne he).elim
  · rcases hk with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · have h1 : E.toTorus.leftPiece k = i :=
        E.toTorus.piece_eq_of_mem (E.toTorus.left_owned k hl) hx
      have h2 : E.toTorus.rightPiece k = i' :=
        E.toTorus.piece_eq_of_mem (E.toTorus.right_owned k hr) hy
      obtain rfl := h.eq_of_internal (by rw [h1]; exact hi) (by rw [h2]; exact hi')
      exact Or.inl ⟨hl, hr⟩
    · have h1 : E.toTorus.rightPiece k = i :=
        E.toTorus.piece_eq_of_mem (E.toTorus.right_owned k hr) hx
      have h2 : E.toTorus.leftPiece k = i' :=
        E.toTorus.piece_eq_of_mem (E.toTorus.left_owned k hl) hy
      obtain rfl := h.eq_of_internal (by rw [h2]; exact hi') (by rw [h1]; exact hi)
      exact Or.inr ⟨hr, hl⟩

theorem IsAbsorbSeam.injOn_cutMap (h : E.IsAbsorbSeam j b) {i : Fin E.toTorus.components.count}
    (hi : i ∈ E.toTorus.seamPair j) :
    InjOn E.toTorus.cutMap (E.toTorus.components.piece i : Set E.toTorus.cutCarrier.Carrier) := by
  intro x hx y hy hxy
  by_contra hne
  rcases h.cutMap_eq_block hi hi hx hy hxy hne with ⟨hl, hr⟩ | ⟨hr, hl⟩
  · exact h.leftPiece_ne_rightPiece
      ((E.toTorus.piece_eq_of_mem (E.toTorus.left_owned j hl) hx).trans
        (E.toTorus.piece_eq_of_mem (E.toTorus.right_owned j hr) hy).symm)
  · exact h.leftPiece_ne_rightPiece
      ((E.toTorus.piece_eq_of_mem (E.toTorus.left_owned j hl) hy).trans
        (E.toTorus.piece_eq_of_mem (E.toTorus.right_owned j hr) hx).symm)

theorem IsAbsorbSeam.eq_sideCollar_of_cutMap_eq (h : E.IsAbsorbSeam j b)
    {x y : E.toTorus.cutCarrier.Carrier} (hx : x ∈ E.toTorus.components.piece (E.seamPiece j b))
    (hy : y ∈ E.toTorus.components.piece (E.hostPiece j b))
    (hxy : E.toTorus.cutMap x = E.toTorus.cutMap y) :
    ∃ t, y = E.toTorus.sideCollar (E.toTorus.pairSide j !b) (t, halfZero) := by
  have hne : x ≠ y := fun he =>
    h.seamPiece_ne_hostPiece (E.toTorus.piece_eq_of_mem hx (he ▸ hy))
  rcases h.cutMap_eq_block (seamPiece_mem_seamPair j b) (hostPiece_mem_seamPair j b) hx hy hxy
    hne with ⟨-, hr⟩ | ⟨-, hl⟩
  · have hA : E.toTorus.rightPiece j = E.hostPiece j b :=
      E.toTorus.piece_eq_of_mem (E.toTorus.right_owned j hr) hy
    cases b
    · exact (h.leftPiece_ne_rightPiece hA.symm).elim
    · exact ⟨_, E.toTorus.eq_rightCollar_of_mem hr⟩
  · have hA : E.toTorus.leftPiece j = E.hostPiece j b :=
      E.toTorus.piece_eq_of_mem (E.toTorus.left_owned j hl) hy
    cases b
    · exact ⟨_, E.toTorus.eq_leftCollar_of_mem hl⟩
    · exact (h.leftPiece_ne_rightPiece hA).elim

theorem IsAbsorbSeam.mem_target_of_isBoundaryPoint (h : E.IsAbsorbSeam j b)
    (hext : ∀ i, E.toTorus.externalPiece i ∉ E.toTorus.seamPair j)
    {x : E.toTorus.cutCarrier.Carrier} (hx : x ∈ E.toTorus.components.piece (E.seamPiece j b))
    (hb : E.toTorus.cutCarrier.model.IsBoundaryPoint x) :
    x ∈ (E.toTorus.sideCollar (E.toTorus.pairSide j b)).target := by
  have hb' : x ∈ E.toTorus.cutCarrier.model.boundary E.toTorus.cutCarrier.Carrier := hb
  rw [E.toTorus.cut_boundary_exhausted] at hb'
  rcases hb' with hb' | hb'
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hb'
    rcases hk with hl | hr
    · have hs : E.toTorus.sidePiece (.inl k) = E.seamPiece j b :=
        E.toTorus.piece_eq_of_mem (E.toTorus.left_owned k hl) hx
      rw [← h.eq_seamSide hs]
      have hxe := E.toTorus.eq_leftCollar_of_mem hl
      rw [hxe]
      exact (E.toTorus.sideCollar _).map_source' (E.toTorus.zero_mem_sideCollar_source _ _)
    · have hs : E.toTorus.sidePiece (.inr (.inl k)) = E.seamPiece j b :=
        E.toTorus.piece_eq_of_mem (E.toTorus.right_owned k hr) hx
      rw [← h.eq_seamSide hs]
      have hxe := E.toTorus.eq_rightCollar_of_mem hr
      rw [hxe]
      exact (E.toTorus.sideCollar _).map_source' (E.toTorus.zero_mem_sideCollar_source _ _)
  · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hb'
    obtain ⟨t, ht⟩ := he
    have hpe := E.toTorus.piece_eq_of_mem (E.toTorus.external_owned e ⟨t, ht⟩) hx
    exact absurd (by rw [hpe]; exact seamPiece_mem_seamPair j b) (hext e)

theorem IsAbsorbSeam.isInteriorPoint_of_not_mem (h : E.IsAbsorbSeam j b)
    (hext : ∀ i, E.toTorus.externalPiece i ∉ E.toTorus.seamPair j)
    {x : E.toTorus.cutCarrier.Carrier} (hx : x ∈ E.toTorus.components.piece (E.seamPiece j b))
    (hxt : x ∉ (E.toTorus.sideCollar (E.toTorus.pairSide j b)).target) :
    E.toTorus.cutCarrier.model.IsInteriorPoint x :=
  (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint _).mpr fun hb =>
    hxt (h.mem_target_of_isBoundaryPoint hext hx hb)

theorem IsAbsorbSeam.not_isKeptSide (h : E.IsAbsorbSeam j b) {s : E.toTorus.Side}
    (hs : E.toTorus.sidePiece s = E.hostPiece j b) (hne : s ≠ E.toTorus.pairSide j !b) :
    ¬ E.toTorus.IsKeptSide (E.toTorus.seamPair j) s := by
  rcases s with k | k | e
  · intro hkept
    obtain rfl := h.eq_of_internal hkept.1 hkept.2
    cases b
    · exact hne rfl
    · exact h.leftPiece_ne_rightPiece hs
  · intro hkept
    obtain rfl := h.eq_of_internal hkept.1 hkept.2
    cases b
    · exact h.leftPiece_ne_rightPiece hs.symm
    · exact hne rfl
  · intro hkept
    exact hkept

end ElementaryPresentation

theorem torusInvFirst_torusInvFirst (p : Torus) : torusInvFirst (torusInvFirst p) = p :=
  Prod.ext (inv_inv p.1) rfl

theorem halfCollarModel_isInteriorPoint {p : Torus × EuclideanHalfSpace 1} (hp : 0 < p.2.val 0) :
    halfCollarModel.IsInteriorPoint p := by
  have h1 : (𝓡∂ 1).IsInteriorPoint p.2 := by
    rw [ModelWithCorners.IsInteriorPoint, interior_range_modelWithCornersEuclideanHalfSpace]
    change 0 < ((𝓡∂ 1) p.2) 0
    exact hp
  have h2 : torusModel.IsInteriorPoint p.1 := BoundarylessManifold.isInteriorPoint
  have h3 : p ∈ halfCollarModel.interior (Torus × EuclideanHalfSpace 1) := by
    rw [ModelWithCorners.interior_prod]
    exact ⟨h2, h1⟩
  exact h3

def affineSeam (b : Bool) : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ where
  toFun t := seamSign b * (t - 10)
  invFun t := seamSign b * t + 10
  left_inv t := by
    change seamSign b * (seamSign b * (t - 10)) + 10 = t
    rw [← mul_assoc, seamSign_mul_self]
    ring
  right_inv t := by
    change seamSign b * (seamSign b * t + 10 - 10) = t
    rw [add_sub_cancel_right, ← mul_assoc, seamSign_mul_self, one_mul]
  contMDiff_toFun := (contDiff_const.mul (contDiff_id.sub contDiff_const)).contMDiff
  contMDiff_invFun := ((contDiff_const.mul contDiff_id).add contDiff_const).contMDiff

def seamCoordinate (ν : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) (b : Bool) :
    PartialDiffeomorph halfCollarModel signedCollarModel (Torus × EuclideanHalfSpace 1)
      (Torus × ℝ) ∞ :=
  DifferentialGeometry.Topology.PartialDiffeomorph.prod ν.toPartialDiffeomorph
    (Manifold.halfSpaceOneInteriorDiffeomorph.symm.trans (affineSeam b).toPartialDiffeomorph)

theorem seamCoordinate_apply (ν : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) (b : Bool)
    (q : Torus × EuclideanHalfSpace 1) :
    seamCoordinate ν b q = (ν q.1, seamSign b * (q.2.val 0 - 10)) := rfl

theorem mem_seamCoordinate_source (ν : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) (b : Bool)
    {q : Torus × EuclideanHalfSpace 1} (hq : 0 < q.2.val 0) :
    q ∈ (seamCoordinate ν b).source :=
  ⟨trivial, hq, trivial⟩

theorem liftVal_of_nonneg {t : ℝ} (ht : 0 ≤ t) : (Manifold.halfSpaceOneLift t).val 0 = t :=
  show max t 0 = t from max_eq_left ht

theorem halfSpace_ext {h h' : EuclideanHalfSpace 1} (e : h.val 0 = h'.val 0) : h = h' := by
  rw [← halfSpaceOneLift_coord h, ← halfSpaceOneLift_coord h', e]

theorem continuous_collarCoord :
    Continuous fun q : Torus × EuclideanHalfSpace 1 => q.2.val 0 :=
  (EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd)

theorem exists_ne_fin_two (n : Fin 2) : ∃ m : Fin 2, m ≠ n := by
  fin_cases n
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩

theorem seamSign_mem_signedCollarSource (b : Bool) (t : Torus) {u : ℝ} (h1 : 9 < u)
    (h2 : u < 11) : (t, seamSign b * (u - 10)) ∈ signedCollarSource := by
  change -1 < seamSign b * (u - 10) ∧ seamSign b * (u - 10) < 1
  cases b <;> simp only [seamSign] <;> constructor <;> linarith

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}} {E : ElementaryPresentation W}
  {j : Fin E.toTorus.pairing.count} {b : Bool}

theorem IsAbsorbSeam.exists_diffeomorph_region (h : E.IsAbsorbSeam j b)
    (hext : ∀ i, E.toTorus.externalPiece i ∉ E.toTorus.seamPair j) :
    Nonempty (E.toTorus.components.piece (E.seamPiece j b) ≃ₘ⟮E.toTorus.cutCarrier.model,
      E.toTorus.cutCarrier.model⟯ (E.toTorus.contractRegion (E.toTorus.seamPair j) hext
        (E.toTorus.cutCarrier_kind_of_pos j.pos)).Carrier) := by
  classical
  have hk := E.toTorus.cutCarrier_kind_of_pos j.pos
  have hV : E.seamPiece j b ∈ E.toTorus.seamPair j := seamPiece_mem_seamPair j b
  have hA : E.hostPiece j b ∈ E.toTorus.seamPair j := hostPiece_mem_seamPair j b
  obtain ⟨P⟩ : Nonempty (ProductFibredPiece E.toTorus (E.hostPiece j b) 2) :=
    ⟨h.2 ▸ E.piece (E.hostPiece j b)⟩
  obtain ⟨nn, hnn⟩ : ∃ nn, (P.port nn).val = E.toTorus.pairSide j !b :=
    ⟨P.port.symm ⟨_, E.sidePiece_pairSide j !b⟩, by rw [P.port.apply_symm_apply]⟩
  obtain ⟨nf, hne⟩ := exists_ne_fin_two nn
  have hs₁ne : (P.port nf).val ≠ E.toTorus.pairSide j !b := fun e =>
    hne (P.port.injective (Subtype.ext (e.trans hnn.symm)))
  obtain ⟨Λ, δ, hδ0, hδ1, hΛs, hΛf, hΛn, hΛc⟩ := exists_annulus_longCollar P hne
  have hΛf' : ∀ p : Torus × EuclideanHalfSpace 1, p.2.val 0 < δ →
      (Λ p : E.toTorus.cutCarrier.Carrier) = E.toTorus.sideCollar (P.port nf).val p := by
    intro p hp
    rw [hΛf p hp]
    exact E.toTorus.pieceCollar_apply _ _ (show p.2.val 0 < 1 from hp.trans_le hδ1)
  have hΛn' : ∀ (t : Torus) (u : ℝ), 10 - δ < u → u < 10 →
      (Λ (t, Manifold.halfSpaceOneLift u) : E.toTorus.cutCarrier.Carrier) =
        E.toTorus.sideCollar (E.toTorus.pairSide j !b)
          (torusInvFirst t, Manifold.halfSpaceOneLift (10 - u)) := by
    intro t u hu1 hu2
    rw [hΛn t u hu1 hu2, E.toTorus.pieceCollar_apply _ _
      (show (Manifold.halfSpaceOneLift (10 - u)).val 0 < 1 by
        rw [liftVal_of_nonneg (by linarith)]
        linarith), hnn]
  have hΛint : ∀ p : Torus × EuclideanHalfSpace 1, 0 < p.2.val 0 → p.2.val 0 < 10 →
      E.toTorus.cutCarrier.model.IsInteriorPoint (Λ p : E.toTorus.cutCarrier.Carrier) := by
    intro p hp0 hp
    have hl := Λ.isLocalDiffeomorphAt halfCollarModel E.toTorus.cutCarrier.model ∞
      ((hΛs p).mpr hp)
    exact ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val.mp
      ((hl.isInteriorPoint_iff (by simp)).mp (halfCollarModel_isInteriorPoint hp0))
  have hΛnot : ∀ p : Torus × EuclideanHalfSpace 1, p.2.val 0 < 10 → ∀ τ : Torus,
      (Λ p : E.toTorus.cutCarrier.Carrier) ≠
        E.toTorus.sideCollar (E.toTorus.pairSide j !b) (τ, halfZero) := by
    intro p hp τ he
    by_cases hpδ : p.2.val 0 < δ
    · have h1 : (Λ p : E.toTorus.cutCarrier.Carrier) ∈
          (E.toTorus.sideCollar (P.port nf).val).target := by
        rw [hΛf' p hpδ]
        apply (E.toTorus.sideCollar _).map_source'
        rw [E.toTorus.sideCollar_source]
        exact hpδ.trans_le hδ1
      have h2 : (Λ p : E.toTorus.cutCarrier.Carrier) ∈
          (E.toTorus.sideCollar (E.toTorus.pairSide j !b)).target := by
        rw [he]
        exact (E.toTorus.sideCollar _).map_source' (E.toTorus.zero_mem_sideCollar_source _ τ)
      exact (E.toTorus.sideCollar_disjoint hs₁ne).le_bot ⟨h1, h2⟩
    · have hint := hΛint p (lt_of_lt_of_le hδ0 (not_lt.mp hpδ)) hp
      rw [he] at hint
      exact (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint _).mp hint
        (E.toTorus.sideCollar_zero_mem _ τ).1
  obtain ⟨j', hj'⟩ : ∃ j' : Fin (E.toTorus.restrictPairing (E.toTorus.seamPair j)).count,
      (E.toTorus.keptSeam (E.toTorus.seamPair j) j').val = j :=
    ⟨Fintype.equivFin (E.toTorus.KeptSeam (E.toTorus.seamPair j))
      ⟨j, E.toTorus.left_mem_seamPair j, E.toTorus.right_mem_seamPair j⟩,
      by rw [TorusPresentation.keptSeam_equivFin]⟩
  have hseamR : ∀ p : Torus × ℝ, p ∈ signedCollarSource →
      (E.toTorus.seamRegion _ hext hk j' p).val = E.toTorus.seam j p := by
    intro p hp
    rw [E.toTorus.seamRegion_val _ hext hk j' hp, hj']
  let a : E.toTorus.RestrictSide (E.toTorus.seamPair j) :=
    ⟨(P.port nf).val, by rw [(P.port nf).property]; exact hA,
      h.not_isKeptSide (P.port nf).property hs₁ne⟩
  let c := E.toTorus.pieceCollar (E.seamPiece j b)
    ⟨E.toTorus.pairSide j b, E.sidePiece_pairSide j b⟩
  have hcs : c.source = {p | p.2.val 0 < 1} := E.toTorus.pieceCollar_source _ _
  have hcv : ∀ p : Torus × EuclideanHalfSpace 1, p.2.val 0 < 1 →
      (c p : E.toTorus.cutCarrier.Carrier) = E.toTorus.sideCollar (E.toTorus.pairSide j b) p :=
    fun p hp => E.toTorus.pieceCollar_apply _ _ hp
  have hct : ∀ x, x ∈ c.target ↔
      (x : E.toTorus.cutCarrier.Carrier) ∈ (E.toTorus.sideCollar (E.toTorus.pairSide j b)).target :=
    fun x => by rw [E.toTorus.pieceCollar_target]; rfl
  let ν := E.toTorus.pairTwist j b
  let ν' := E.toTorus.pairTwist j !b
  let μ := ν.trans (ν'.symm.trans torusInvFirst)
  have hμ : ∀ t, torusInvFirst (μ t) = ν'.symm (ν t) := fun t => torusInvFirst_torusInvFirst _
  let F := E.toTorus.regionMap (E.toTorus.seamPair j) hext hk hV
  let F' := E.toTorus.regionMap (E.toTorus.seamPair j) hext hk hA
  let ℓ : Torus × EuclideanHalfSpace 1 →
      (E.toTorus.contractRegion (E.toTorus.seamPair j) hext hk).Carrier := fun q =>
    if q.2.val 0 < 10 then F' (Λ (μ q.1, q.2))
    else E.toTorus.seamRegion _ hext hk j' (ν q.1, seamSign b * (q.2.val 0 - 10))
  have hℓ1 : ∀ q : Torus × EuclideanHalfSpace 1, q.2.val 0 < 10 → ℓ q = F' (Λ (μ q.1, q.2)) :=
    fun q hq => ite_eq_left hq
  have hℓ2 : ∀ q : Torus × EuclideanHalfSpace 1, ¬ q.2.val 0 < 10 →
      ℓ q = E.toTorus.seamRegion _ hext hk j' (ν q.1, seamSign b * (q.2.val 0 - 10)) :=
    fun q hq => ite_eq_right hq
  have hV1 : ∀ p : Torus × EuclideanHalfSpace 1, p.2.val 0 < 1 →
      (F (c p)).val = E.toTorus.seam j (ν p.1, seamSign b * p.2.val 0) := by
    intro p hp
    change E.toTorus.cutMap (c p : E.toTorus.cutCarrier.Carrier) = _
    rw [hcv p hp]
    exact E.toTorus.cutMap_sideCollar_pairSide_eq j b hp
  have hV2 : ∀ q : Torus × EuclideanHalfSpace 1, 10 ≤ q.2.val 0 → q.2.val 0 < 11 →
      (ℓ q).val = E.toTorus.seam j (ν q.1, seamSign b * (q.2.val 0 - 10)) := by
    intro q h1 h2
    rw [hℓ2 q (not_lt.mpr h1), hseamR _ (seamSign_mem_signedCollarSource b _ (by linarith) h2)]
  have hV3 : ∀ q : Torus × EuclideanHalfSpace 1, 10 - δ < q.2.val 0 → q.2.val 0 < 10 →
      (ℓ q).val = E.toTorus.seam j (ν q.1, seamSign b * (q.2.val 0 - 10)) := by
    rintro ⟨t, w⟩ h1 h2
    rw [hℓ1 _ h2]
    change E.toTorus.cutMap (Λ (μ t, w) : E.toTorus.cutCarrier.Carrier) = _
    have hΛw := hΛn' (μ t) (w.val 0) h1 h2
    rw [halfSpaceOneLift_coord] at hΛw
    have hsrc : (Manifold.halfSpaceOneLift (10 - w.val 0)).val 0 < 1 := by
      rw [liftVal_of_nonneg (by linarith)]
      linarith
    rw [hΛw, E.toTorus.cutMap_sideCollar_pairSide_eq j (!b) hsrc, hμ,
      liftVal_of_nonneg (by linarith), seamSign_not]
    change E.toTorus.seam j (ν' (ν'.symm (ν t)), _) = _
    rw [Diffeomorph.apply_symm_apply,
      show -seamSign b * (10 - w.val 0) = seamSign b * (w.val 0 - 10) by ring]
  have hℓseam : ∀ q : Torus × EuclideanHalfSpace 1, 10 - δ < q.2.val 0 → q.2.val 0 < 11 →
      ℓ q = E.toTorus.seamRegion _ hext hk j' (seamCoordinate ν b q) := by
    intro q h1 h2
    apply Subtype.ext
    rw [seamCoordinate_apply, hseamR _ (seamSign_mem_signedCollarSource b _ (by linarith) h2)]
    by_cases h3 : q.2.val 0 < 10
    · exact hV3 q h1 h3
    · exact hV2 q (not_lt.mp h3) h2
  have hℓcross : ∀ q : Torus × EuclideanHalfSpace 1, q.2.val 0 < δ →
      ℓ q = E.toTorus.crossRegion _ hext hk a (μ q.1, q.2) := by
    intro q hq
    apply Subtype.ext
    rw [hℓ1 q (by linarith), E.toTorus.crossRegion_val _ hext hk a (p := (μ q.1, q.2))
      (show q.2.val 0 < 1 from hq.trans_le hδ1)]
    change E.toTorus.cutMap (Λ (μ q.1, q.2) : E.toTorus.cutCarrier.Carrier) = _
    rw [hΛf' (μ q.1, q.2) hq]
  have hℓV : ∀ q : Torus × EuclideanHalfSpace 1, 10 ≤ q.2.val 0 → q.2.val 0 < 11 →
      ℓ q = F (c (q.1, Manifold.halfSpaceOneLift (q.2.val 0 - 10))) := by
    intro q h1 h2
    have hl : (Manifold.halfSpaceOneLift (q.2.val 0 - 10)).val 0 = q.2.val 0 - 10 :=
      liftVal_of_nonneg (by linarith)
    apply Subtype.ext
    rw [hV2 q h1 h2, hV1 _ (by rw [hl]; linarith), hl]
  have hFc : ∀ p : Torus × EuclideanHalfSpace 1, p.2.val 0 < 1 →
      F (c p) = ℓ (p.1, Manifold.halfSpaceOneLift (p.2.val 0 + 10)) := by
    intro p hp
    have hl : (Manifold.halfSpaceOneLift (p.2.val 0 + 10)).val 0 = p.2.val 0 + 10 :=
      liftVal_of_nonneg (by linarith [p.2.2])
    apply Subtype.ext
    rw [hV1 p hp, hV2 _ (by rw [hl]; linarith [p.2.2]) (by rw [hl]; linarith), hl,
      add_sub_cancel_right]
  have hFinj : Injective F := fun x y hxy =>
    Subtype.ext (h.injOn_cutMap hV x.property y.property (congrArg Subtype.val hxy))
  have hF'inj : Injective F' := fun x y hxy =>
    Subtype.ext (h.injOn_cutMap hA x.property y.property (congrArg Subtype.val hxy))
  have hcsrc : ∀ p : Torus × EuclideanHalfSpace 1, p.2.val 0 < 1 → p ∈ c.source := by
    intro p hp
    rw [hcs]
    exact hp
  have hℓloc : ∀ q : Torus × EuclideanHalfSpace 1, q.2.val 0 < 1 + 10 →
      IsLocalDiffeomorphAt halfCollarModel E.toTorus.cutCarrier.model ∞ ℓ q := by
    intro q hq
    let G : (Torus × EuclideanHalfSpace 1) ≃ₘ⟮halfCollarModel, halfCollarModel⟯
        (Torus × EuclideanHalfSpace 1) := μ.prodCongr (Diffeomorph.refl (𝓡∂ 1) _ ∞)
    have hG : ∀ q', G q' = (μ q'.1, q'.2) := fun q' => rfl
    by_cases h1 : q.2.val 0 < δ
    · have hsrc : G q ∈ (E.toTorus.crossRegion _ hext hk a).source := by
        rw [E.toTorus.crossRegion_source]
        exact (show q.2.val 0 < 1 from h1.trans_le hδ1)
      have hloc := (G.isLocalDiffeomorph q).comp (K := E.toTorus.cutCarrier.model)
        (P := (E.toTorus.contractRegion (E.toTorus.seamPair j) hext hk).Carrier)
        ((E.toTorus.crossRegion _ hext hk a).isLocalDiffeomorphAt _ _ ∞ hsrc)
      refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_ hloc
      filter_upwards [(isOpen_lt continuous_collarCoord continuous_const).mem_nhds h1] with q' hq'
      exact hℓcross q' hq'
    · by_cases h2 : q.2.val 0 < 10
      · have hsrc : G q ∈ Λ.source := (hΛs _).mpr h2
        have hint := hΛint (G q) (lt_of_lt_of_le hδ0 (not_lt.mp h1)) h2
        have hloc := ((G.isLocalDiffeomorph q).comp (K := E.toTorus.cutCarrier.model)
          (P := E.toTorus.components.piece (E.hostPiece j b))
          (Λ.isLocalDiffeomorphAt _ _ ∞ hsrc)).comp (K := E.toTorus.cutCarrier.model)
          (P := (E.toTorus.contractRegion (E.toTorus.seamPair j) hext hk).Carrier)
          (E.toTorus.isLocalDiffeomorphAt_regionMap _ hext hk hA hint)
        refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_ hloc
        filter_upwards [(isOpen_lt continuous_collarCoord continuous_const).mem_nhds h2]
          with q' hq'
        exact hℓ1 q' hq'
      · have h10 : 10 ≤ q.2.val 0 := not_lt.mp h2
        have hsrc : q ∈ ((seamCoordinate ν b).trans
            (E.toTorus.seamRegion _ hext hk j')).source := by
          rw [PartialDiffeomorph.trans_source]
          refine ⟨mem_seamCoordinate_source ν b (by linarith), ?_⟩
          change seamCoordinate ν b q ∈ (E.toTorus.seamRegion _ hext hk j').source
          rw [E.toTorus.seamRegion_source, seamCoordinate_apply]
          exact seamSign_mem_signedCollarSource b _ (by linarith) (by linarith)
        refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_
          (((seamCoordinate ν b).trans (E.toTorus.seamRegion _ hext hk j')).isLocalDiffeomorphAt
            _ _ ∞ hsrc)
        have hO : IsOpen {q' : Torus × EuclideanHalfSpace 1 |
            10 - δ < q'.2.val 0 ∧ q'.2.val 0 < 11} :=
          (isOpen_lt continuous_const continuous_collarCoord).inter
            (isOpen_lt continuous_collarCoord continuous_const)
        filter_upwards [hO.mem_nhds ⟨by linarith, by linarith⟩] with q' hq'
        exact hℓseam q' hq'.1 hq'.2
  have hFloc : ∀ x, x ∉ c.target →
      IsLocalDiffeomorphAt E.toTorus.cutCarrier.model E.toTorus.cutCarrier.model ∞ F x := by
    intro x hx
    exact E.toTorus.isLocalDiffeomorphAt_regionMap _ hext hk hV
      (h.isInteriorPoint_of_not_mem hext x.property fun hm => hx ((hct x).mpr hm))
  have hℓinj : InjOn ℓ {q | q.2.val 0 < 1 + 10} := by
    intro q hq q' hq' he
    have hq11 : q.2.val 0 < 11 := by
      have := hq
      simp only [mem_ofPred_eq] at this
      linarith
    have hq11' : q'.2.val 0 < 11 := by
      have := hq'
      simp only [mem_ofPred_eq] at this
      linarith
    by_cases h1 : q.2.val 0 < 10 <;> by_cases h2 : q'.2.val 0 < 10
    · rw [hℓ1 q h1, hℓ1 q' h2] at he
      have h4 := Λ.toPartialEquiv.injOn ((hΛs (μ q.1, q.2)).mpr h1)
        ((hΛs (μ q'.1, q'.2)).mpr h2) (hF'inj he)
      exact Prod.ext (μ.injective (Prod.mk.inj h4).1) (Prod.mk.inj h4).2
    · rw [hℓ1 q h1, hℓV q' (not_lt.mp h2) hq11'] at he
      obtain ⟨τ, hτ⟩ := h.eq_sideCollar_of_cutMap_eq (c _).property (Λ _).property
        (congrArg Subtype.val he).symm
      exact (hΛnot (μ q.1, q.2) h1 τ hτ).elim
    · rw [hℓV q (not_lt.mp h1) hq11, hℓ1 q' h2] at he
      obtain ⟨τ, hτ⟩ := h.eq_sideCollar_of_cutMap_eq (c _).property (Λ _).property
        (congrArg Subtype.val he)
      exact (hΛnot (μ q'.1, q'.2) h2 τ hτ).elim
    · rw [hℓV q (not_lt.mp h1) hq11, hℓV q' (not_lt.mp h2) hq11'] at he
      have hl : (Manifold.halfSpaceOneLift (q.2.val 0 - 10)).val 0 = q.2.val 0 - 10 :=
        liftVal_of_nonneg (by linarith)
      have hl' : (Manifold.halfSpaceOneLift (q'.2.val 0 - 10)).val 0 = q'.2.val 0 - 10 :=
        liftVal_of_nonneg (by linarith)
      have h3 := c.toPartialEquiv.injOn (hcsrc _ (by rw [hl]; linarith))
        (hcsrc _ (by rw [hl']; linarith)) (hFinj he)
      have h4 := congrArg (fun p : Torus × EuclideanHalfSpace 1 => p.2.val 0) h3
      simp only [hl, hl'] at h4
      exact Prod.ext (Prod.mk.inj h3).1 (halfSpace_ext (by linarith))
  have hdisj : ∀ x, x ∉ c.target → ∀ q : Torus × EuclideanHalfSpace 1,
      q.2.val 0 < 1 + 10 → F x ≠ ℓ q := by
    intro x hx q hq he
    by_cases h1 : q.2.val 0 < 10
    · rw [hℓ1 q h1] at he
      obtain ⟨τ, hτ⟩ := h.eq_sideCollar_of_cutMap_eq x.property (Λ _).property
        (congrArg Subtype.val he)
      exact hΛnot (μ q.1, q.2) h1 τ hτ
    · have hl : (Manifold.halfSpaceOneLift (q.2.val 0 - 10)).val 0 = q.2.val 0 - 10 :=
        liftVal_of_nonneg (by linarith)
      rw [hℓV q (not_lt.mp h1) (by linarith)] at he
      apply hx
      rw [hFinj he]
      exact c.map_source' (hcsrc _ (by rw [hl]; linarith))
  have hcover : ∀ y, (∃ x, x ∉ c.target ∧ F x = y) ∨
      ∃ q : Torus × EuclideanHalfSpace 1, q.2.val 0 < 1 + 10 ∧ ℓ q = y := by
    intro y
    obtain ⟨z, hzS, hz⟩ : ∃ z ∈ (E.toTorus.subPiece (E.toTorus.seamPair j) :
        Set E.toTorus.cutCarrier.Carrier), E.toTorus.cutMap z = y.val := by
      exact (Set.ext_iff.mp (E.toTorus.range_restrictMap _) y.val).mp y.property
    obtain ⟨i, hi, hzi⟩ := (E.toTorus.mem_subPiece _).mp hzS
    rcases (E.mem_seamPair_iff j b i).mp hi with rfl | rfl
    · by_cases hxc : (⟨z, hzi⟩ : E.toTorus.components.piece (E.seamPiece j b)) ∈ c.target
      · right
        have hp : c.symm ⟨z, hzi⟩ ∈ c.source := c.map_target' hxc
        have hp1 : (c.symm ⟨z, hzi⟩).2.val 0 < 1 := by
          rw [hcs] at hp
          exact hp
        refine ⟨((c.symm ⟨z, hzi⟩).1,
          Manifold.halfSpaceOneLift ((c.symm ⟨z, hzi⟩).2.val 0 + 10)), ?_, ?_⟩
        · change (Manifold.halfSpaceOneLift _).val 0 < 1 + 10
          rw [liftVal_of_nonneg (by linarith [(c.symm ⟨z, hzi⟩).2.2])]
          linarith
        · rw [← hFc _ hp1, PartialDiffeomorph.apply_symm_apply c hxc]
          exact Subtype.ext hz
      · exact Or.inl ⟨⟨z, hzi⟩, hxc, Subtype.ext hz⟩
    · rcases hΛc ⟨z, hzi⟩ with hy' | ⟨τ, hτ⟩
      · right
        have hp : Λ.symm ⟨z, hzi⟩ ∈ Λ.source := Λ.map_target' hy'
        have hp10 := (hΛs _).mp hp
        refine ⟨(μ.symm (Λ.symm ⟨z, hzi⟩).1, (Λ.symm ⟨z, hzi⟩).2), by
          change (Λ.symm ⟨z, hzi⟩).2.val 0 < 1 + 10
          linarith, ?_⟩
        rw [hℓ1 (μ.symm (Λ.symm ⟨z, hzi⟩).1, (Λ.symm ⟨z, hzi⟩).2) hp10]
        change F' (Λ (μ (μ.symm (Λ.symm ⟨z, hzi⟩).1), (Λ.symm ⟨z, hzi⟩).2)) = y
        rw [Diffeomorph.apply_symm_apply, Prod.mk.eta, PartialDiffeomorph.apply_symm_apply Λ hy']
        exact Subtype.ext hz
      · right
        refine ⟨(ν.symm (ν' τ), Manifold.halfSpaceOneLift 10), ?_, ?_⟩
        · change (Manifold.halfSpaceOneLift 10).val 0 < 1 + 10
          rw [liftVal_of_nonneg (by norm_num)]
          norm_num
        · have h10 : (Manifold.halfSpaceOneLift 10).val 0 = 10 := liftVal_of_nonneg (by norm_num)
          have hz' : z = E.toTorus.sideCollar (E.toTorus.pairSide j !b) (τ, halfZero) := by
            have h3 := congrArg Subtype.val hτ
            rw [E.toTorus.pieceCollar_apply _ _ (zero_mem_halfCollarSource τ), hnn] at h3
            exact h3
          apply Subtype.ext
          rw [hV2 _ (by rw [h10]) (by rw [h10]; norm_num), ← hz, hz',
            E.toTorus.cutMap_sideCollar_pairSide_eq j (!b) (zero_mem_halfCollarSource τ), h10]
          change E.toTorus.seam j (ν (ν.symm (ν' τ)), _) = E.toTorus.seam j (ν' τ, _)
          rw [Diffeomorph.apply_symm_apply, sub_self, mul_zero,
            show (halfZero : EuclideanHalfSpace 1).val 0 = 0 from rfl, mul_zero]
  obtain ⟨Φ, -, -⟩ := DifferentialGeometry.Topology.Manifold.exists_diffeomorph_collarStretch
    (K := torusModel) (J := E.toTorus.cutCarrier.model) c hcs F ℓ (a := 10) (by norm_num)
    hFc hℓloc hFloc hℓinj hFinj.injOn hdisj hcover
  exact ⟨Φ⟩

end ElementaryPresentation

theorem mergedSolidTorus : MergedSolidTorus.{u} := by
  intro W E j b h hext
  obtain ⟨Φ⟩ := h.exists_diffeomorph_region hext
  exact ⟨(E.toTorus.contractLastDiffeomorph (E.toTorus.seamPair j) hext
    (E.toTorus.cutCarrier_kind_of_pos j.pos) (h.isConnected_region hext)).symm.trans Φ.symm⟩

theorem moveAbsorb_of_contractionRecollar (hR : ContractionRecollar.{u}) : MoveAbsorb.{u} :=
  moveAbsorb_of_mergedSolidTorus_of_contractionRecollar mergedSolidTorus hR

end GC.Seifert
