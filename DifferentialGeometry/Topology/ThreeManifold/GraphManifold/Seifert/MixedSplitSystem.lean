import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedPieces

/-!
# Closed cut systems with arbitrary compact pieces

Lane MS, tier MS4 (design `handoffs/20261004-design-ms-mixed-split.md` §3.3–3.4), the generic part.
`MixedClosedSystem N kind` generalises lane N2c's `ClosedPieceSystem`
(`Seifert/MoveSplitCappedPieces`) from product pieces `Pₖ × S¹` to arbitrary compact connected
pieces modelled on `kind.model` with their own half collars exhausting their boundaries, as in
`EmbeddedCutSystem`; pieces and seams are indexed by finite types. This is the form of the capped
manifold after a mixed split: the passive old pieces (frozen or product) are not products in the
same model, the two capped solid tori are.

On a closed, possibly disconnected `N` every piece and every seam lies in one component
(`mk_map`, `mk_seam`); `restrict` is the system of one component `K`, and `toCutSystem` reindexes
a system of a connected closed manifold through `Fintype.equivFin` into an `EmbeddedCutSystem` of
its carrier. The seam counts of two components exhausting all seams add up
(`card_seam_restrict_add`). The proofs are those of `ClosedPieceSystem` with the product chart
replaced by the piece itself.
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

universe u

structure MixedClosedSystem (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (kind : CarrierModel) where
  Piece : Type
  [fintypePiece : Fintype Piece]
  Seam : Type
  [fintypeSeam : Fintype Seam]
  nonempty : Nonempty Piece
  Part : Piece → Type u
  [topology : ∀ i, TopologicalSpace (Part i)]
  [charts : ∀ i, ChartedSpace kind.Space (Part i)]
  [manifold : ∀ i, IsManifold kind.model ∞ (Part i)]
  [compact : ∀ i, CompactSpace (Part i)]
  [hausdorff : ∀ i, T2Space (Part i)]
  [secondCountable : ∀ i, SecondCountableTopology (Part i)]
  [connected : ∀ i, ConnectedSpace (Part i)]
  map : ∀ i, Part i → M
  smooth : ∀ i, ContMDiff kind.model (𝓡 3) ∞ (map i)
  mfderiv_bijective : ∀ i q, Bijective (mfderiv kind.model (𝓡 3) (map i) q)
  covers : ⋃ i, range (map i) = univ
  torusCount : Piece → ℕ
  collar : ∀ i, Fin (torusCount i) →
    PartialDiffeomorph halfCollarModel kind.model (Torus × EuclideanHalfSpace 1) (Part i) ∞
  collar_source : ∀ i l, (collar i l).source = halfCollarSource
  collar_disjoint : ∀ i, Pairwise fun l l' => Disjoint (collar i l).target (collar i l').target
  boundary_exhausted : ∀ i, kind.model.boundary (Part i) =
    ⋃ l, range fun t => collar i l (t, halfZero)
  side : Seam → Bool → Σ i, Fin (torusCount i)
  side_bijective : Bijective (uncurry side)
  matching : Seam → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  seam : Seam → PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) M ∞
  seam_source : ∀ c, (seam c).source = signedCollarSource
  seam_neg : ∀ c (t : Torus) s (hs : s ≤ 0), -1 < s → seam c (t, s) =
    map (side c true).1 (collar _ (side c true).2 (t, halfPoint (-s) (neg_nonneg.2 hs)))
  seam_pos : ∀ c (t : Torus) s (hs : 0 ≤ s), s < 1 → seam c (t, s) =
    map (side c false).1 (collar _ (side c false).2 (matching c t, halfPoint s hs))
  overlap : ∀ i i' q q', map i q = map i' q' →
    (⟨i, q⟩ : Σ i, Part i) = ⟨i', q'⟩ ∨ ∃ c t, map i q = seam c (t, 0)

attribute [instance] MixedClosedSystem.fintypePiece MixedClosedSystem.fintypeSeam
  MixedClosedSystem.topology MixedClosedSystem.charts MixedClosedSystem.manifold
  MixedClosedSystem.compact MixedClosedSystem.hausdorff MixedClosedSystem.secondCountable
  MixedClosedSystem.connected

namespace MixedClosedSystem

variable {kind : CarrierModel}

section Reindex

variable {A : ConnectedClosedOrientedManifold.{u} 3} (P : MixedClosedSystem.{u} A.Carrier kind)

def pieceEquiv : Fin (Fintype.card P.Piece) ≃ P.Piece :=
  (Fintype.equivFin P.Piece).symm

def seamEquiv : Fin (Fintype.card P.Seam) ≃ P.Seam :=
  (Fintype.equivFin P.Seam).symm

def portEquiv :
    (Σ j : Fin (Fintype.card P.Piece), Fin (P.torusCount (P.pieceEquiv j))) ≃
      Σ i, Fin (P.torusCount i) :=
  Equiv.sigmaCongrLeft (β := fun i => Fin (P.torusCount i)) P.pieceEquiv

def collarPoint (p : Torus × EuclideanHalfSpace 1) (x : Σ i, Fin (P.torusCount i)) : A.Carrier :=
  P.map x.1 (P.collar x.1 x.2 p)

theorem collarPoint_portEquiv_symm (p : Torus × EuclideanHalfSpace 1)
    (x : Σ i, Fin (P.torusCount i)) :
    P.map (P.pieceEquiv (P.portEquiv.symm x).1)
      (P.collar (P.pieceEquiv (P.portEquiv.symm x).1) (P.portEquiv.symm x).2 p) =
      P.collarPoint p x := by
  have h := congrArg (P.collarPoint p) (P.portEquiv.apply_symm_apply x)
  rw [← h]
  rfl

def toCutSystem : EmbeddedCutSystem (NoCuts.carrier A) kind where
  count := Fintype.card P.Piece
  count_pos := Fintype.card_pos_iff.mpr P.nonempty
  Piece j := P.Part (P.pieceEquiv j)
  map j := P.map (P.pieceEquiv j)
  smooth j := P.smooth _
  mfderiv_bijective j := P.mfderiv_bijective _
  covers := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨i, hi⟩ := mem_iUnion.mp (P.covers ▸ mem_univ x : x ∈ ⋃ i, range (P.map i))
    obtain ⟨j, rfl⟩ := P.pieceEquiv.surjective i
    exact mem_iUnion.mpr ⟨j, hi⟩
  torusCount j := P.torusCount (P.pieceEquiv j)
  collar j := P.collar (P.pieceEquiv j)
  collar_source j := P.collar_source _
  collar_disjoint j := P.collar_disjoint _
  boundary_exhausted j := P.boundary_exhausted _
  seamCount := Fintype.card P.Seam
  side c b := P.portEquiv.symm (P.side (P.seamEquiv c) b)
  externalCount := 0
  externalSide i := i.elim0
  sides_bijective := by
    have hb : Bijective (fun cb : Fin (Fintype.card P.Seam) × Bool =>
        P.portEquiv.symm (P.side (P.seamEquiv cb.1) cb.2)) :=
      P.portEquiv.symm.bijective.comp (P.side_bijective.comp
        (Equiv.prodCongr P.seamEquiv (Equiv.refl Bool)).bijective)
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · rcases x with x | x
      · rcases y with y | y
        · exact congrArg Sum.inl (hb.1 hxy)
        · exact y.elim0
      · exact x.elim0
    · obtain ⟨cb, hcb⟩ := hb.2 z
      exact ⟨Sum.inl cb, hcb⟩
  matching c := P.matching (P.seamEquiv c)
  seam c := P.seam (P.seamEquiv c)
  seam_source c := P.seam_source _
  seam_neg c t s hs h1 := (P.seam_neg _ t s hs h1).trans
    (P.collarPoint_portEquiv_symm _ _).symm
  seam_pos c t s hs h1 := (P.seam_pos _ t s hs h1).trans
    (P.collarPoint_portEquiv_symm _ _).symm
  seam_interior c x _ := ClosedPieceSystem.interior_mem x
  external_local i := i.elim0
  overlap j j' q q' hq := by
    rcases P.overlap _ _ q q' hq with he | he
    · left
      have h1 : P.pieceEquiv j = P.pieceEquiv j' := congrArg Sigma.fst he
      have hjj : j = j' := P.pieceEquiv.injective h1
      subst hjj
      have h2 := Sigma.mk.inj_iff.mp he
      rw [eq_of_heq h2.2]
    · right
      obtain ⟨c, t, hc⟩ := he
      exact ⟨P.seamEquiv.symm c, t, by rw [Equiv.apply_symm_apply]; exact hc⟩

theorem toCutSystem_seamCount : P.toCutSystem.seamCount = Fintype.card P.Seam := rfl

end Reindex

section Component

variable {N : ClosedOrientedManifold.{u} 3} (P : MixedClosedSystem.{u} N.Carrier kind)

def pieceComp (i : P.Piece) : ConnectedComponents N.Carrier :=
  ConnectedComponents.mk (P.map i (inferInstance : Nonempty (P.Part i)).some)

theorem mk_map (i : P.Piece) (q : P.Part i) :
    ConnectedComponents.mk (P.map i q) = P.pieceComp i := by
  have hpre : IsPreconnected (range (P.map i)) := isPreconnected_range (P.smooth i).continuous
  exact ConnectedComponents.coe_eq_coe'.mpr
    (hpre.subset_connectedComponent ⟨_, rfl⟩ ⟨q, rfl⟩)

def seamComp (c : P.Seam) : ConnectedComponents N.Carrier :=
  P.pieceComp (P.side c true).1

theorem pieceComp_side (c : P.Seam) : ∀ b, P.pieceComp (P.side c b).1 = P.seamComp c
  | true => rfl
  | false => by
    have h1 := P.seam_neg c 1 0 le_rfl (by norm_num)
    have h2 := P.seam_pos c 1 0 le_rfl one_pos
    rw [← P.mk_map _ (P.collar _ (P.side c false).2 (P.matching c 1, halfPoint 0 le_rfl)), ← h2,
      h1, P.mk_map]
    rfl

theorem mk_seam (c : P.Seam) {p : Torus × ℝ} (hp : p ∈ (P.seam c).source) :
    ConnectedComponents.mk (P.seam c p) = P.seamComp c := by
  have hsrc : (P.seam c).source = (univ : Set Torus) ×ˢ Ioo (-1 : ℝ) 1 := by
    rw [P.seam_source]
    ext q
    simp [signedCollarSource]
  have hpre : IsPreconnected ((P.seam c) '' (P.seam c).source) := by
    refine IsPreconnected.image ?_ _ (P.seam c).contMDiffOn_toFun.continuousOn
    rw [hsrc]
    exact isPreconnected_univ.prod isPreconnected_Ioo
  have h0 : ((1 : Torus), (0 : ℝ)) ∈ (P.seam c).source := by
    rw [P.seam_source]
    constructor <;> norm_num
  have h1 := P.seam_neg c 1 0 le_rfl (by norm_num)
  rw [ConnectedComponents.coe_eq_coe'.mpr (hpre.subset_connectedComponent ⟨_, h0, rfl⟩
    ⟨p, hp, rfl⟩), h1, P.mk_map]
  rfl

theorem mk_seam_target (c : P.Seam) {y : N.Carrier} (hy : y ∈ (P.seam c).target) :
    ConnectedComponents.mk y = P.seamComp c := by
  have h := P.mk_seam c ((P.seam c).map_target' hy)
  rwa [(P.seam c).right_inv' hy] at h

def liftPort (K : ConnectedComponents N.Carrier)
    (x : Σ i : {i : P.Piece // P.pieceComp i = K}, Fin (P.torusCount i.1)) :
    Σ i, Fin (P.torusCount i) :=
  ⟨x.1.1, x.2⟩

theorem liftPort_injective (K : ConnectedComponents N.Carrier) : Injective (P.liftPort K) := by
  rintro ⟨⟨i, hi⟩, l⟩ ⟨⟨i', hi'⟩, l'⟩ h
  have h1 := Sigma.mk.inj_iff.mp h
  obtain rfl : i = i' := h1.1
  have h2 : l = l' := eq_of_heq h1.2
  subst h2
  rfl

theorem seam_target_subset (K : ConnectedComponents N.Carrier)
    (c : {c : P.Seam // P.seamComp c = K}) :
    (P.seam c.1).target ⊆ (N.componentOpen K : Set N.Carrier) := by
  intro y hy
  exact ClosedPieceSystem.mem_componentOpen ((P.mk_seam_target c.1 hy).trans c.2)

theorem seam_mem (K : ConnectedComponents N.Carrier) (c : {c : P.Seam // P.seamComp c = K})
    {p : Torus × ℝ} (hp : p ∈ (P.seam c.1).source) : P.seam c.1 p ∈ N.componentOpen K :=
  P.seam_target_subset K c ((P.seam c.1).map_source' hp)

def restrict (K : ConnectedComponents N.Carrier) (hK : ∃ i, P.pieceComp i = K) :
    MixedClosedSystem.{u} (N.component K).Carrier kind where
  Piece := {i : P.Piece // P.pieceComp i = K}
  fintypePiece := Fintype.ofFinite _
  Seam := {c : P.Seam // P.seamComp c = K}
  fintypeSeam := Fintype.ofFinite _
  nonempty := let ⟨i, hi⟩ := hK; ⟨⟨i, hi⟩⟩
  Part i := P.Part i.1
  map i q := ClosedPieceSystem.compPoint K ((P.mk_map i.1 q).trans i.2)
  smooth i := fun q => codRestr_contMDiffAt (V := N.componentOpen K)
    (fun q => (P.mk_map i.1 q).trans i.2) ((P.smooth i.1) q)
  mfderiv_bijective i q := by
    have hf' : MDifferentiableAt kind.model (𝓡 3)
        (fun q => ClosedPieceSystem.compPoint K ((P.mk_map i.1 q).trans i.2)) q :=
      (codRestr_contMDiffAt (V := N.componentOpen K) (fun q => (P.mk_map i.1 q).trans i.2)
        ((P.smooth i.1) q)).mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hval : MDifferentiableAt (𝓡 3) (𝓡 3) (Subtype.val : N.componentOpen K → N.Carrier)
        (ClosedPieceSystem.compPoint K ((P.mk_map i.1 q).trans i.2)) :=
      ((contMDiff_subtype_val (I := 𝓡 3) (U := N.componentOpen K)).contMDiffAt).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hcomp := mfderiv_comp q hval hf'
    erw [DifferentialGeometry.mfderiv_subtype_val (I := 𝓡 3) (N.componentOpen K),
      ContinuousLinearMap.id_comp] at hcomp
    rw [← hcomp]
    exact P.mfderiv_bijective i.1 q
  covers := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨i, q, hq⟩ := mem_iUnion.mp (P.covers ▸ mem_univ x.val :
      x.val ∈ ⋃ i, range (P.map i))
    have hi : P.pieceComp i = K := by
      rw [← P.mk_map i q, hq]
      exact x.2
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, q, Subtype.ext hq⟩
  torusCount i := P.torusCount i.1
  collar i := P.collar i.1
  collar_source i := P.collar_source i.1
  collar_disjoint i := P.collar_disjoint i.1
  boundary_exhausted i := P.boundary_exhausted i.1
  side c b := ⟨⟨(P.side c.1 b).1, (P.pieceComp_side c.1 b).trans c.2⟩, (P.side c.1 b).2⟩
  side_bijective := by
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · obtain ⟨c, b⟩ := x
      obtain ⟨c', b'⟩ := y
      have h : P.side c.1 b = P.side c'.1 b' := congrArg (P.liftPort K) hxy
      have h' : (c.1, b) = (c'.1, b') := P.side_bijective.1 h
      simp only [Prod.mk.injEq] at h'
      exact Prod.ext (Subtype.ext h'.1) h'.2
    · obtain ⟨⟨c, b⟩, hcb⟩ := P.side_bijective.2 (P.liftPort K z)
      have hc : P.seamComp c = K := by
        rw [← P.pieceComp_side c b]
        change P.pieceComp (uncurry P.side (c, b)).1 = K
        rw [hcb]
        exact z.1.2
      refine ⟨(⟨c, hc⟩, b), P.liftPort_injective K ?_⟩
      exact hcb
  matching c := P.matching c.1
  seam c := codRestrictOpens (P.seam c.1) (N.componentOpen K)
    ⟨ClosedPieceSystem.compPoint K ((P.mk_seam c.1
      (show ((1 : Torus), (0 : ℝ)) ∈ (P.seam c.1).source by
        rw [P.seam_source]; constructor <;> norm_num)).trans c.2)⟩
  seam_source c := (codRestrictOpens_source _ _ _ (P.seam_target_subset K c)).trans
    (P.seam_source c.1)
  seam_neg c t s hs h1 := by
    apply Subtype.ext
    exact (codRestrictOpens_apply _ _ _ (P.seam_mem K c (by rw [P.seam_source]; exact
      ⟨h1, by linarith⟩))).trans (P.seam_neg c.1 t s hs h1)
  seam_pos c t s hs h1 := by
    apply Subtype.ext
    exact (codRestrictOpens_apply _ _ _ (P.seam_mem K c (by rw [P.seam_source]; exact
      ⟨by linarith, h1⟩))).trans (P.seam_pos c.1 t s hs h1)
  overlap i i' q q' hq := by
    have hq' : P.map i.1 q = P.map i'.1 q' := congrArg Subtype.val hq
    rcases P.overlap i.1 i'.1 q q' hq' with he | ⟨c, t, hc⟩
    · left
      have h1 := Sigma.mk.inj_iff.mp he
      obtain ⟨i, hi⟩ := i
      obtain ⟨i', hi'⟩ := i'
      obtain rfl : i = i' := h1.1
      rw [eq_of_heq h1.2]
    · right
      have h0 : ((t, (0 : ℝ)) : Torus × ℝ) ∈ (P.seam c).source := by
        rw [P.seam_source]; constructor <;> norm_num
      have hcK : P.seamComp c = K := by
        rw [← P.mk_seam c h0, ← hc]
        exact (P.mk_map i.1 q).trans i.2
      refine ⟨⟨c, hcK⟩, t, Subtype.ext ?_⟩
      exact hc.trans (codRestrictOpens_apply _ _ _ (P.seam_mem K ⟨c, hcK⟩ h0)).symm

open Classical in
theorem card_seam_restrict (K : ConnectedComponents N.Carrier) (hK : ∃ i, P.pieceComp i = K) :
    Fintype.card (P.restrict K hK).Seam = Fintype.card {c : P.Seam // P.seamComp c = K} :=
  Fintype.card_congr (Equiv.refl _)

open Classical in
theorem card_seam_restrict_add (K₁ K₂ : ConnectedComponents N.Carrier) (hne : K₁ ≠ K₂)
    (h₁ : ∃ i, P.pieceComp i = K₁) (h₂ : ∃ i, P.pieceComp i = K₂)
    (hall : ∀ c, P.seamComp c = K₁ ∨ P.seamComp c = K₂) :
    Fintype.card (P.restrict K₁ h₁).Seam + Fintype.card (P.restrict K₂ h₂).Seam =
      Fintype.card P.Seam := by
  classical
  rw [card_seam_restrict, card_seam_restrict]
  have e : {c : P.Seam // P.seamComp c = K₂} ≃ {c : P.Seam // ¬ P.seamComp c = K₁} :=
    Equiv.subtypeEquivRight fun c => by
      constructor
      · intro h hc
        exact hne (hc.symm.trans h)
      · intro h
        exact (hall c).resolve_left h
  rw [Fintype.card_congr e, Fintype.card_subtype_compl, Nat.add_sub_cancel' (by
    exact Fintype.card_subtype_le _)]

end Component

end MixedClosedSystem

end GC.Seifert
