import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveMergeLedgerLocal
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MergedSolidTorus

/-!
# Actual selected absorption geometry in a mixed stage

The original solid piece and annulus host form a solid product after their selected seam is
joined. The collar-stretch construction uses only these two non-frozen product certificates.
The actual region identification then transports the whole diffeomorphism to the selected
quotient carrier, without assigning product structures to any frozen piece.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Set Function
open scoped Manifold ContDiff Topology
universe u
namespace GC.Seifert.RelativeNormalization
namespace MixedStage
variable {Q : ConnectedClosedOrientedManifold.{u} 3} {σ : MixedStage Q}
  {j : Fin σ.toTorus.pairing.count} {b : Bool}

theorem seamPiece_mem_seamPair (j : Fin σ.toTorus.pairing.count) (b : Bool) :
    σ.seamPiece j b ∈ σ.toTorus.seamPair j :=
  (σ.mem_seamPair_iff j b _).mpr (Or.inl rfl)

theorem hostPiece_mem_seamPair (j : Fin σ.toTorus.pairing.count) (b : Bool) :
    σ.hostPiece j b ∈ σ.toTorus.seamPair j :=
  (σ.mem_seamPair_iff j b _).mpr (Or.inr rfl)

theorem IsAbsorbSeam.seamPiece_ne_hostPiece {j : Fin σ.toTorus.pairing.count} {b : Bool}
    (h : σ.IsAbsorbSeam j b) : σ.seamPiece j b ≠ σ.hostPiece j b := by
  intro he
  have h2 := h.2.2
  rw [← he, h.2.1] at h2
  exact absurd h2 (by decide)

theorem IsAbsorbSeam.leftPiece_ne_rightPiece {j : Fin σ.toTorus.pairing.count} {b : Bool}
    (h : σ.IsAbsorbSeam j b) : σ.toTorus.leftPiece j ≠ σ.toTorus.rightPiece j := by
  have := h.seamPiece_ne_hostPiece
  cases b
  · exact this.symm
  · exact this

theorem IsAbsorbSeam.eq_seamSide {j : Fin σ.toTorus.pairing.count} {b : Bool}
    (h : σ.IsAbsorbSeam j b) {s : σ.toTorus.Side}
    (hs : σ.toTorus.sidePiece s = σ.seamPiece j b) : s = σ.toTorus.pairSide j b := by
  have hc : Fintype.card (σ.toTorus.OwnedSide (σ.seamPiece j b)) ≤ 1 := by
    rw [σ.card_ownedSide_eq_kind _ (σ.seamPiece_not_mem_frozen h.1 b), h.2.1]
  exact congrArg Subtype.val (Fintype.card_le_one_iff.mp hc ⟨s, hs⟩ ⟨_, σ.sidePiece_pairSide j b⟩)

theorem IsAbsorbSeam.eq_of_internal {j : Fin σ.toTorus.pairing.count} {b : Bool}
    (h : σ.IsAbsorbSeam j b) {k : Fin σ.toTorus.pairing.count}
    (hl : σ.toTorus.leftPiece k ∈ σ.toTorus.seamPair j)
    (hr : σ.toTorus.rightPiece k ∈ σ.toTorus.seamPair j) : k = j := by
  by_contra hkj
  have hA : ∀ c : Bool, σ.toTorus.sidePiece (σ.toTorus.pairSide k c) = σ.hostPiece j b := by
    intro c
    have hmem : σ.toTorus.sidePiece (σ.toTorus.pairSide k c) ∈ σ.toTorus.seamPair j := by
      cases c
      · exact hr
      · exact hl
    exact ((σ.mem_seamPair_iff j b _).mp hmem).resolve_left fun hc =>
      σ.toTorus.pairSide_ne_of_ne hkj c b (h.eq_seamSide hc)
  have hc : Fintype.card (σ.toTorus.OwnedSide (σ.hostPiece j b)) = 2 := by
    rw [σ.card_ownedSide_eq_kind _ (σ.hostPiece_not_mem_frozen h.1 b), h.2.2]
  let a : σ.toTorus.OwnedSide (σ.hostPiece j b) := ⟨_, σ.sidePiece_pairSide j !b⟩
  let a1 : σ.toTorus.OwnedSide (σ.hostPiece j b) := ⟨_, hA true⟩
  let a2 : σ.toTorus.OwnedSide (σ.hostPiece j b) := ⟨_, hA false⟩
  have h3 : ({a, a1, a2} : Finset (σ.toTorus.OwnedSide (σ.hostPiece j b))).card = 3 := by
    rw [Finset.card_eq_three]
    refine ⟨a, a1, a2, fun he => ?_, fun he => ?_, fun he => ?_, rfl⟩
    · exact σ.toTorus.pairSide_ne_of_ne (Ne.symm hkj) (!b) true (congrArg Subtype.val he)
    · exact σ.toTorus.pairSide_ne_of_ne (Ne.symm hkj) (!b) false (congrArg Subtype.val he)
    · exact σ.toTorus.pairSide_ne_not k true (congrArg Subtype.val he)
  have := Finset.card_le_univ ({a, a1, a2} : Finset (σ.toTorus.OwnedSide (σ.hostPiece j b)))
  omega

theorem IsAbsorbSeam.cutMap_eq_block (h : σ.IsAbsorbSeam j b)
    {x y : σ.toTorus.cutCarrier.Carrier} {i i' : Fin σ.toTorus.components.count}
    (hi : i ∈ σ.toTorus.seamPair j) (hi' : i' ∈ σ.toTorus.seamPair j)
    (hx : x ∈ σ.toTorus.components.piece i) (hy : y ∈ σ.toTorus.components.piece i')
    (hxy : σ.toTorus.cutMap x = σ.toTorus.cutMap y) (hne : x ≠ y) :
    (x ∈ σ.toTorus.pairing.gluing.left j ∧ y ∈ σ.toTorus.pairing.gluing.right j) ∨
      (x ∈ σ.toTorus.pairing.gluing.right j ∧ y ∈ σ.toTorus.pairing.gluing.left j) := by
  rcases σ.toTorus.cutMap_eq_cases hxy with he | ⟨k, hk⟩
  · exact (hne he).elim
  · rcases hk with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · have h1 : σ.toTorus.leftPiece k = i :=
        σ.toTorus.piece_eq_of_mem (σ.toTorus.left_owned k hl) hx
      have h2 : σ.toTorus.rightPiece k = i' :=
        σ.toTorus.piece_eq_of_mem (σ.toTorus.right_owned k hr) hy
      obtain rfl := h.eq_of_internal (by rw [h1]; exact hi) (by rw [h2]; exact hi')
      exact Or.inl ⟨hl, hr⟩
    · have h1 : σ.toTorus.rightPiece k = i :=
        σ.toTorus.piece_eq_of_mem (σ.toTorus.right_owned k hr) hx
      have h2 : σ.toTorus.leftPiece k = i' :=
        σ.toTorus.piece_eq_of_mem (σ.toTorus.left_owned k hl) hy
      obtain rfl := h.eq_of_internal (by rw [h2]; exact hi') (by rw [h1]; exact hi)
      exact Or.inr ⟨hr, hl⟩

theorem IsAbsorbSeam.injOn_cutMap (h : σ.IsAbsorbSeam j b) {i : Fin σ.toTorus.components.count}
    (hi : i ∈ σ.toTorus.seamPair j) :
    InjOn σ.toTorus.cutMap (σ.toTorus.components.piece i : Set σ.toTorus.cutCarrier.Carrier) := by
  intro x hx y hy hxy
  by_contra hne
  rcases h.cutMap_eq_block hi hi hx hy hxy hne with ⟨hl, hr⟩ | ⟨hr, hl⟩
  · exact h.leftPiece_ne_rightPiece
      ((σ.toTorus.piece_eq_of_mem (σ.toTorus.left_owned j hl) hx).trans
        (σ.toTorus.piece_eq_of_mem (σ.toTorus.right_owned j hr) hy).symm)
  · exact h.leftPiece_ne_rightPiece
      ((σ.toTorus.piece_eq_of_mem (σ.toTorus.left_owned j hl) hy).trans
        (σ.toTorus.piece_eq_of_mem (σ.toTorus.right_owned j hr) hx).symm)

theorem IsAbsorbSeam.eq_sideCollar_of_cutMap_eq (h : σ.IsAbsorbSeam j b)
    {x y : σ.toTorus.cutCarrier.Carrier} (hx : x ∈ σ.toTorus.components.piece (σ.seamPiece j b))
    (hy : y ∈ σ.toTorus.components.piece (σ.hostPiece j b))
    (hxy : σ.toTorus.cutMap x = σ.toTorus.cutMap y) :
    ∃ t, y = σ.toTorus.sideCollar (σ.toTorus.pairSide j !b) (t, halfZero) := by
  have hne : x ≠ y := fun he =>
    h.seamPiece_ne_hostPiece (σ.toTorus.piece_eq_of_mem hx (he ▸ hy))
  rcases h.cutMap_eq_block (seamPiece_mem_seamPair j b) (hostPiece_mem_seamPair j b) hx hy hxy
    hne with ⟨-, hr⟩ | ⟨-, hl⟩
  · have hA : σ.toTorus.rightPiece j = σ.hostPiece j b :=
      σ.toTorus.piece_eq_of_mem (σ.toTorus.right_owned j hr) hy
    cases b
    · exact (h.leftPiece_ne_rightPiece hA.symm).elim
    · exact ⟨_, σ.toTorus.eq_rightCollar_of_mem hr⟩
  · have hA : σ.toTorus.leftPiece j = σ.hostPiece j b :=
      σ.toTorus.piece_eq_of_mem (σ.toTorus.left_owned j hl) hy
    cases b
    · exact ⟨_, σ.toTorus.eq_leftCollar_of_mem hl⟩
    · exact (h.leftPiece_ne_rightPiece hA).elim

theorem IsAbsorbSeam.mem_target_of_isBoundaryPoint (h : σ.IsAbsorbSeam j b)
    (hext : ∀ i, σ.toTorus.externalPiece i ∉ σ.toTorus.seamPair j)
    {x : σ.toTorus.cutCarrier.Carrier} (hx : x ∈ σ.toTorus.components.piece (σ.seamPiece j b))
    (hb : σ.toTorus.cutCarrier.model.IsBoundaryPoint x) :
    x ∈ (σ.toTorus.sideCollar (σ.toTorus.pairSide j b)).target := by
  have hb' : x ∈ σ.toTorus.cutCarrier.model.boundary σ.toTorus.cutCarrier.Carrier := hb
  rw [σ.toTorus.cut_boundary_exhausted] at hb'
  rcases hb' with hb' | hb'
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hb'
    rcases hk with hl | hr
    · have hs : σ.toTorus.sidePiece (.inl k) = σ.seamPiece j b :=
        σ.toTorus.piece_eq_of_mem (σ.toTorus.left_owned k hl) hx
      rw [← h.eq_seamSide hs]
      have hxe := σ.toTorus.eq_leftCollar_of_mem hl
      rw [hxe]
      exact (σ.toTorus.sideCollar _).map_source' (σ.toTorus.zero_mem_sideCollar_source _ _)
    · have hs : σ.toTorus.sidePiece (.inr (.inl k)) = σ.seamPiece j b :=
        σ.toTorus.piece_eq_of_mem (σ.toTorus.right_owned k hr) hx
      rw [← h.eq_seamSide hs]
      have hxe := σ.toTorus.eq_rightCollar_of_mem hr
      rw [hxe]
      exact (σ.toTorus.sideCollar _).map_source' (σ.toTorus.zero_mem_sideCollar_source _ _)
  · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hb'
    obtain ⟨t, ht⟩ := he
    have hpe := σ.toTorus.piece_eq_of_mem (σ.toTorus.external_owned e ⟨t, ht⟩) hx
    exact absurd (by rw [hpe]; exact seamPiece_mem_seamPair j b) (hext e)

theorem IsAbsorbSeam.isInteriorPoint_of_not_mem (h : σ.IsAbsorbSeam j b)
    (hext : ∀ i, σ.toTorus.externalPiece i ∉ σ.toTorus.seamPair j)
    {x : σ.toTorus.cutCarrier.Carrier} (hx : x ∈ σ.toTorus.components.piece (σ.seamPiece j b))
    (hxt : x ∉ (σ.toTorus.sideCollar (σ.toTorus.pairSide j b)).target) :
    σ.toTorus.cutCarrier.model.IsInteriorPoint x :=
  (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint _).mpr fun hb =>
    hxt (h.mem_target_of_isBoundaryPoint hext hx hb)

theorem IsAbsorbSeam.not_isKeptSide (h : σ.IsAbsorbSeam j b) {s : σ.toTorus.Side}
    (hs : σ.toTorus.sidePiece s = σ.hostPiece j b) (hne : s ≠ σ.toTorus.pairSide j !b) :
    ¬ σ.toTorus.IsKeptSide (σ.toTorus.seamPair j) s := by
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

theorem IsAbsorbSeam.exists_diffeomorph_region (h : σ.IsAbsorbSeam j b)
    (hext : ∀ i, σ.toTorus.externalPiece i ∉ σ.toTorus.seamPair j) :
    Nonempty (σ.toTorus.components.piece (σ.seamPiece j b) ≃ₘ⟮σ.toTorus.cutCarrier.model,
      σ.toTorus.cutCarrier.model⟯ (σ.toTorus.contractRegion (σ.toTorus.seamPair j) hext
        (σ.toTorus.cutCarrier_kind_of_pos j.pos)).Carrier) := by
  classical
  have hk := σ.toTorus.cutCarrier_kind_of_pos j.pos
  have hV : σ.seamPiece j b ∈ σ.toTorus.seamPair j := seamPiece_mem_seamPair j b
  have hA : σ.hostPiece j b ∈ σ.toTorus.seamPair j := hostPiece_mem_seamPair j b
  obtain ⟨P⟩ : Nonempty (ProductFibredPiece σ.toTorus (σ.hostPiece j b) 2) :=
    ⟨h.2.2 ▸ σ.piece (σ.hostPiece j b) (σ.hostPiece_not_mem_frozen h.1 b)⟩
  obtain ⟨nn, hnn⟩ : ∃ nn, (P.port nn).val = σ.toTorus.pairSide j !b :=
    ⟨P.port.symm ⟨_, σ.sidePiece_pairSide j !b⟩, by rw [P.port.apply_symm_apply]⟩
  obtain ⟨nf, hne⟩ := exists_ne_fin_two nn
  have hs₁ne : (P.port nf).val ≠ σ.toTorus.pairSide j !b := fun e =>
    hne (P.port.injective (Subtype.ext (e.trans hnn.symm)))
  obtain ⟨Λ, δ, hδ0, hδ1, hΛs, hΛf, hΛn, hΛc⟩ := exists_annulus_longCollar P hne
  have hΛf' : ∀ p : Torus × EuclideanHalfSpace 1, p.2.val 0 < δ →
      (Λ p : σ.toTorus.cutCarrier.Carrier) = σ.toTorus.sideCollar (P.port nf).val p := by
    intro p hp
    rw [hΛf p hp]
    exact σ.toTorus.pieceCollar_apply _ _ (show p.2.val 0 < 1 from hp.trans_le hδ1)
  have hΛn' : ∀ (t : Torus) (u : ℝ), 10 - δ < u → u < 10 →
      (Λ (t, Manifold.halfSpaceOneLift u) : σ.toTorus.cutCarrier.Carrier) =
        σ.toTorus.sideCollar (σ.toTorus.pairSide j !b)
          (torusInvFirst t, Manifold.halfSpaceOneLift (10 - u)) := by
    intro t u hu1 hu2
    rw [hΛn t u hu1 hu2, σ.toTorus.pieceCollar_apply _ _
      (show (Manifold.halfSpaceOneLift (10 - u)).val 0 < 1 by
        rw [liftVal_of_nonneg (by linarith)]
        linarith), hnn]
  have hΛint : ∀ p : Torus × EuclideanHalfSpace 1, 0 < p.2.val 0 → p.2.val 0 < 10 →
      σ.toTorus.cutCarrier.model.IsInteriorPoint (Λ p : σ.toTorus.cutCarrier.Carrier) := by
    intro p hp0 hp
    have hl := Λ.isLocalDiffeomorphAt halfCollarModel σ.toTorus.cutCarrier.model ∞
      ((hΛs p).mpr hp)
    exact ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val.mp
      ((hl.isInteriorPoint_iff (by simp)).mp (halfCollarModel_isInteriorPoint hp0))
  have hΛnot : ∀ p : Torus × EuclideanHalfSpace 1, p.2.val 0 < 10 → ∀ τ : Torus,
      (Λ p : σ.toTorus.cutCarrier.Carrier) ≠
        σ.toTorus.sideCollar (σ.toTorus.pairSide j !b) (τ, halfZero) := by
    intro p hp τ he
    by_cases hpδ : p.2.val 0 < δ
    · have h1 : (Λ p : σ.toTorus.cutCarrier.Carrier) ∈
          (σ.toTorus.sideCollar (P.port nf).val).target := by
        rw [hΛf' p hpδ]
        apply (σ.toTorus.sideCollar _).map_source'
        rw [σ.toTorus.sideCollar_source]
        exact hpδ.trans_le hδ1
      have h2 : (Λ p : σ.toTorus.cutCarrier.Carrier) ∈
          (σ.toTorus.sideCollar (σ.toTorus.pairSide j !b)).target := by
        rw [he]
        exact (σ.toTorus.sideCollar _).map_source' (σ.toTorus.zero_mem_sideCollar_source _ τ)
      exact (σ.toTorus.sideCollar_disjoint hs₁ne).le_bot ⟨h1, h2⟩
    · have hint := hΛint p (lt_of_lt_of_le hδ0 (not_lt.mp hpδ)) hp
      rw [he] at hint
      exact (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint _).mp hint
        (σ.toTorus.sideCollar_zero_mem _ τ).1
  obtain ⟨j', hj'⟩ : ∃ j' : Fin (σ.toTorus.restrictPairing (σ.toTorus.seamPair j)).count,
      (σ.toTorus.keptSeam (σ.toTorus.seamPair j) j').val = j :=
    ⟨Fintype.equivFin (σ.toTorus.KeptSeam (σ.toTorus.seamPair j))
      ⟨j, σ.toTorus.left_mem_seamPair j, σ.toTorus.right_mem_seamPair j⟩,
      by rw [TorusPresentation.keptSeam_equivFin]⟩
  have hseamR : ∀ p : Torus × ℝ, p ∈ signedCollarSource →
      (σ.toTorus.seamRegion _ hext hk j' p).val = σ.toTorus.seam j p := by
    intro p hp
    rw [σ.toTorus.seamRegion_val _ hext hk j' hp, hj']
  let a : σ.toTorus.RestrictSide (σ.toTorus.seamPair j) :=
    ⟨(P.port nf).val, by rw [(P.port nf).property]; exact hA,
      h.not_isKeptSide (P.port nf).property hs₁ne⟩
  let c := σ.toTorus.pieceCollar (σ.seamPiece j b)
    ⟨σ.toTorus.pairSide j b, σ.sidePiece_pairSide j b⟩
  have hcs : c.source = {p | p.2.val 0 < 1} := σ.toTorus.pieceCollar_source _ _
  have hcv : ∀ p : Torus × EuclideanHalfSpace 1, p.2.val 0 < 1 →
      (c p : σ.toTorus.cutCarrier.Carrier) = σ.toTorus.sideCollar (σ.toTorus.pairSide j b) p :=
    fun p hp => σ.toTorus.pieceCollar_apply _ _ hp
  have hct : ∀ x, x ∈ c.target ↔
      (x : σ.toTorus.cutCarrier.Carrier) ∈ (σ.toTorus.sideCollar (σ.toTorus.pairSide j b)).target :=
    fun x => by rw [σ.toTorus.pieceCollar_target]; rfl
  let ν := σ.toTorus.pairTwist j b
  let ν' := σ.toTorus.pairTwist j !b
  let μ := ν.trans (ν'.symm.trans torusInvFirst)
  have hμ : ∀ t, torusInvFirst (μ t) = ν'.symm (ν t) := fun t => torusInvFirst_torusInvFirst _
  let F := σ.toTorus.regionMap (σ.toTorus.seamPair j) hext hk hV
  let F' := σ.toTorus.regionMap (σ.toTorus.seamPair j) hext hk hA
  let ℓ : Torus × EuclideanHalfSpace 1 →
      (σ.toTorus.contractRegion (σ.toTorus.seamPair j) hext hk).Carrier := fun q =>
    if q.2.val 0 < 10 then F' (Λ (μ q.1, q.2))
    else σ.toTorus.seamRegion _ hext hk j' (ν q.1, seamSign b * (q.2.val 0 - 10))
  have hℓ1 : ∀ q : Torus × EuclideanHalfSpace 1, q.2.val 0 < 10 → ℓ q = F' (Λ (μ q.1, q.2)) :=
    fun q hq => ite_eq_left hq
  have hℓ2 : ∀ q : Torus × EuclideanHalfSpace 1, ¬ q.2.val 0 < 10 →
      ℓ q = σ.toTorus.seamRegion _ hext hk j' (ν q.1, seamSign b * (q.2.val 0 - 10)) :=
    fun q hq => ite_eq_right hq
  have hV1 : ∀ p : Torus × EuclideanHalfSpace 1, p.2.val 0 < 1 →
      (F (c p)).val = σ.toTorus.seam j (ν p.1, seamSign b * p.2.val 0) := by
    intro p hp
    change σ.toTorus.cutMap (c p : σ.toTorus.cutCarrier.Carrier) = _
    rw [hcv p hp]
    exact σ.toTorus.cutMap_sideCollar_pairSide_eq j b hp
  have hV2 : ∀ q : Torus × EuclideanHalfSpace 1, 10 ≤ q.2.val 0 → q.2.val 0 < 11 →
      (ℓ q).val = σ.toTorus.seam j (ν q.1, seamSign b * (q.2.val 0 - 10)) := by
    intro q h1 h2
    rw [hℓ2 q (not_lt.mpr h1), hseamR _ (seamSign_mem_signedCollarSource b _ (by linarith) h2)]
  have hV3 : ∀ q : Torus × EuclideanHalfSpace 1, 10 - δ < q.2.val 0 → q.2.val 0 < 10 →
      (ℓ q).val = σ.toTorus.seam j (ν q.1, seamSign b * (q.2.val 0 - 10)) := by
    rintro ⟨t, w⟩ h1 h2
    rw [hℓ1 _ h2]
    change σ.toTorus.cutMap (Λ (μ t, w) : σ.toTorus.cutCarrier.Carrier) = _
    have hΛw := hΛn' (μ t) (w.val 0) h1 h2
    rw [halfSpaceOneLift_coord] at hΛw
    have hsrc : (Manifold.halfSpaceOneLift (10 - w.val 0)).val 0 < 1 := by
      rw [liftVal_of_nonneg (by linarith)]
      linarith
    rw [hΛw, σ.toTorus.cutMap_sideCollar_pairSide_eq j (!b) hsrc, hμ,
      liftVal_of_nonneg (by linarith), seamSign_not]
    change σ.toTorus.seam j (ν' (ν'.symm (ν t)), _) = _
    rw [Diffeomorph.apply_symm_apply,
      show -seamSign b * (10 - w.val 0) = seamSign b * (w.val 0 - 10) by ring]
  have hℓseam : ∀ q : Torus × EuclideanHalfSpace 1, 10 - δ < q.2.val 0 → q.2.val 0 < 11 →
      ℓ q = σ.toTorus.seamRegion _ hext hk j' (seamCoordinate ν b q) := by
    intro q h1 h2
    apply Subtype.ext
    rw [seamCoordinate_apply, hseamR _ (seamSign_mem_signedCollarSource b _ (by linarith) h2)]
    by_cases h3 : q.2.val 0 < 10
    · exact hV3 q h1 h3
    · exact hV2 q (not_lt.mp h3) h2
  have hℓcross : ∀ q : Torus × EuclideanHalfSpace 1, q.2.val 0 < δ →
      ℓ q = σ.toTorus.crossRegion _ hext hk a (μ q.1, q.2) := by
    intro q hq
    apply Subtype.ext
    rw [hℓ1 q (by linarith), σ.toTorus.crossRegion_val _ hext hk a (p := (μ q.1, q.2))
      (show q.2.val 0 < 1 from hq.trans_le hδ1)]
    change σ.toTorus.cutMap (Λ (μ q.1, q.2) : σ.toTorus.cutCarrier.Carrier) = _
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
      IsLocalDiffeomorphAt halfCollarModel σ.toTorus.cutCarrier.model ∞ ℓ q := by
    intro q hq
    let G : (Torus × EuclideanHalfSpace 1) ≃ₘ⟮halfCollarModel, halfCollarModel⟯
        (Torus × EuclideanHalfSpace 1) := μ.prodCongr (Diffeomorph.refl (𝓡∂ 1) _ ∞)
    have hG : ∀ q', G q' = (μ q'.1, q'.2) := fun q' => rfl
    by_cases h1 : q.2.val 0 < δ
    · have hsrc : G q ∈ (σ.toTorus.crossRegion _ hext hk a).source := by
        rw [σ.toTorus.crossRegion_source]
        exact (show q.2.val 0 < 1 from h1.trans_le hδ1)
      have hloc := (G.isLocalDiffeomorph q).comp (K := σ.toTorus.cutCarrier.model)
        (P := (σ.toTorus.contractRegion (σ.toTorus.seamPair j) hext hk).Carrier)
        ((σ.toTorus.crossRegion _ hext hk a).isLocalDiffeomorphAt _ _ ∞ hsrc)
      refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_ hloc
      filter_upwards [(isOpen_lt continuous_collarCoord continuous_const).mem_nhds h1] with q' hq'
      exact hℓcross q' hq'
    · by_cases h2 : q.2.val 0 < 10
      · have hsrc : G q ∈ Λ.source := (hΛs _).mpr h2
        have hint := hΛint (G q) (lt_of_lt_of_le hδ0 (not_lt.mp h1)) h2
        have hloc := ((G.isLocalDiffeomorph q).comp (K := σ.toTorus.cutCarrier.model)
          (P := σ.toTorus.components.piece (σ.hostPiece j b))
          (Λ.isLocalDiffeomorphAt _ _ ∞ hsrc)).comp (K := σ.toTorus.cutCarrier.model)
          (P := (σ.toTorus.contractRegion (σ.toTorus.seamPair j) hext hk).Carrier)
          (σ.toTorus.isLocalDiffeomorphAt_regionMap _ hext hk hA hint)
        refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_ hloc
        filter_upwards [(isOpen_lt continuous_collarCoord continuous_const).mem_nhds h2]
          with q' hq'
        exact hℓ1 q' hq'
      · have h10 : 10 ≤ q.2.val 0 := not_lt.mp h2
        have hsrc : q ∈ ((seamCoordinate ν b).trans
            (σ.toTorus.seamRegion _ hext hk j')).source := by
          rw [PartialDiffeomorph.trans_source]
          refine ⟨mem_seamCoordinate_source ν b (by linarith), ?_⟩
          change seamCoordinate ν b q ∈ (σ.toTorus.seamRegion _ hext hk j').source
          rw [σ.toTorus.seamRegion_source, seamCoordinate_apply]
          exact seamSign_mem_signedCollarSource b _ (by linarith) (by linarith)
        refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_
          (((seamCoordinate ν b).trans (σ.toTorus.seamRegion _ hext hk j')).isLocalDiffeomorphAt
            _ _ ∞ hsrc)
        have hO : IsOpen {q' : Torus × EuclideanHalfSpace 1 |
            10 - δ < q'.2.val 0 ∧ q'.2.val 0 < 11} :=
          (isOpen_lt continuous_const continuous_collarCoord).inter
            (isOpen_lt continuous_collarCoord continuous_const)
        filter_upwards [hO.mem_nhds ⟨by linarith, by linarith⟩] with q' hq'
        exact hℓseam q' hq'.1 hq'.2
  have hFloc : ∀ x, x ∉ c.target →
      IsLocalDiffeomorphAt σ.toTorus.cutCarrier.model σ.toTorus.cutCarrier.model ∞ F x := by
    intro x hx
    exact σ.toTorus.isLocalDiffeomorphAt_regionMap _ hext hk hV
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
    obtain ⟨z, hzS, hz⟩ : ∃ z ∈ (σ.toTorus.subPiece (σ.toTorus.seamPair j) :
        Set σ.toTorus.cutCarrier.Carrier), σ.toTorus.cutMap z = y.val := by
      exact (Set.ext_iff.mp (σ.toTorus.range_restrictMap _) y.val).mp y.property
    obtain ⟨i, hi, hzi⟩ := (σ.toTorus.mem_subPiece _).mp hzS
    rcases (σ.mem_seamPair_iff j b i).mp hi with rfl | rfl
    · by_cases hxc : (⟨z, hzi⟩ : σ.toTorus.components.piece (σ.seamPiece j b)) ∈ c.target
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
          have hz' : z = σ.toTorus.sideCollar (σ.toTorus.pairSide j !b) (τ, halfZero) := by
            have h3 := congrArg Subtype.val hτ
            rw [σ.toTorus.pieceCollar_apply _ _ (zero_mem_halfCollarSource τ), hnn] at h3
            exact h3
          apply Subtype.ext
          rw [hV2 _ (by rw [h10]) (by rw [h10]; norm_num), ← hz, hz',
            σ.toTorus.cutMap_sideCollar_pairSide_eq j (!b) (zero_mem_halfCollarSource τ), h10]
          change σ.toTorus.seam j (ν (ν.symm (ν' τ)), _) = σ.toTorus.seam j (ν' τ, _)
          rw [Diffeomorph.apply_symm_apply, sub_self, mul_zero,
            show (halfZero : EuclideanHalfSpace 1).val 0 = 0 from rfl, mul_zero]
  obtain ⟨Φ, -, -⟩ := DifferentialGeometry.Topology.Manifold.exists_diffeomorph_collarStretch
    (K := torusModel) (J := σ.toTorus.cutCarrier.model) c hcs F ℓ (a := 10) (by norm_num)
    hFc hℓloc hFloc hℓinj hFinj.injOn hdisj hcover
  exact ⟨Φ⟩


theorem exists_selectedAbsorbProduct (σ : MixedStage Q)
    (j : Fin σ.toTorus.pairing.count) (b : Bool) (h : σ.IsAbsorbSeam j b) :
    ∃ B : PlanarBase.{u} 1,
      Nonempty ((B.surface.Carrier × Circle) ≃ₘ⟮
        (SurfaceModel.model B.surface.kind).prod (𝓡 1), (σ.selectedCarrier j).model⟯
          (σ.selectedCarrier j).Carrier) := by
  let hext := TorusPresentation.externalPiece_not_mem_of_closed
    σ.toTorus (σ.toTorus.seamPair j)
  obtain ⟨Φ⟩ := h.exists_diffeomorph_region hext
  obtain ⟨P⟩ : Nonempty (ProductFibredPiece σ.toTorus (σ.seamPiece j b) 1) :=
    ⟨h.2.1 ▸ σ.piece (σ.seamPiece j b) (σ.seamPiece_not_mem_frozen h.1 b)⟩
  exact ⟨P.base, ⟨P.trivialization.trans (Φ.trans
    (σ.selectedRegionDiffeomorph j (fun k hl hr => h.eq_of_internal hl hr)))⟩⟩

end MixedStage
end GC.Seifert.RelativeNormalization
