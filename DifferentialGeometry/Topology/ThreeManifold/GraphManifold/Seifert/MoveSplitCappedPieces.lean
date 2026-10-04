import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.EmbeddedPieces
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.Manifold.Components

/-!
# Piece systems of closed manifolds indexed by finite types

Lane N2c, tier 2 (assembly, generic part). A `ClosedPieceSystem M` is the product form of an
embedded piece system (`EmbeddedPieceSystem` of `Seifert/EmbeddedPieces.lean`) of a closed
`3`-manifold `M`, with the pieces and the seams indexed by arbitrary finite types instead of
`Fin`: product pieces `Pₖ × S¹` over planar bases mapped into `M` with bijective differential and
covering `M`, a bijection from the sides of the seams to the ports of the pieces, seam charts
reading the two sides, and the overlap condition. `toEmbeddedPieceSystem` reindexes it through
`Fintype.equivFin`, so `toElementaryPresentation` is an elementary presentation of a closed
connected `A` with as many seams as the seam type has elements
(`complexity_toElementaryPresentation`).

On a closed but possibly disconnected `N`, every piece and every seam lies in one connected
component (`mk_map`, `mk_seam`), and `restrict` is the piece system of the component `K`
(pieces and seams in `K`, maps and seam charts restricted to the open component), so the seam
counts of two components exhausting all seams add up (`card_seam_restrict_add`).
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

universe u


structure ClosedPieceSystem (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] where
  Piece : Type
  [fintypePiece : Fintype Piece]
  Seam : Type
  [fintypeSeam : Fintype Seam]
  nonempty : Nonempty Piece
  kind : Piece → ℕ
  kind_mem : ∀ i, kind i ∈ ({1, 2, 3} : Finset ℕ)
  base : ∀ i, PlanarBase.{u} (kind i)
  map : ∀ i, (base i).surface.Carrier × Circle → M
  smooth : ∀ i, ContMDiff ((SurfaceModel.model (base i).surface.kind).prod (𝓡 1)) (𝓡 3) ∞
    (map i)
  mfderiv_bijective : ∀ i q, Bijective
    (mfderiv ((SurfaceModel.model (base i).surface.kind).prod (𝓡 1)) (𝓡 3) (map i) q)
  covers : ⋃ i, range (map i) = univ
  side : Seam → Bool → Σ i, Fin (kind i)
  side_bijective : Bijective (uncurry side)
  matching : Seam → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  seam : Seam → PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) M ∞
  seam_source : ∀ c, (seam c).source = signedCollarSource
  seam_neg : ∀ c t s (hs : s ≤ 0), -1 < s → seam c (t, s) =
    map (side c true).1 ((base _).collar (side c true).2
      (t.1, halfPoint (-s) (neg_nonneg.2 hs)), t.2)
  seam_pos : ∀ c t s (hs : 0 ≤ s), s < 1 → seam c (t, s) =
    map (side c false).1 ((base _).collar (side c false).2
      ((matching c t).1, halfPoint s hs), (matching c t).2)
  overlap : ∀ i i' q q', map i q = map i' q' →
    (⟨i, q⟩ : Σ i, (base i).surface.Carrier × Circle) = ⟨i', q'⟩ ∨
      ∃ c t, map i q = seam c (t, 0)

attribute [instance] ClosedPieceSystem.fintypePiece ClosedPieceSystem.fintypeSeam

namespace ClosedPieceSystem

theorem interior_mem {A : ConnectedClosedOrientedManifold.{u} 3} (x : A.Carrier) :
    x ∈ (NoCuts.carrier A).interior :=
  BoundarylessManifold.isInteriorPoint

section Reindex

variable {A : ConnectedClosedOrientedManifold.{u} 3} (P : ClosedPieceSystem.{u} A.Carrier)

def pieceEquiv : Fin (Fintype.card P.Piece) ≃ P.Piece :=
  (Fintype.equivFin P.Piece).symm

def seamEquiv : Fin (Fintype.card P.Seam) ≃ P.Seam :=
  (Fintype.equivFin P.Seam).symm

def portEquiv :
    (Σ j : Fin (Fintype.card P.Piece), Fin (P.kind (P.pieceEquiv j))) ≃ Σ i, Fin (P.kind i) :=
  Equiv.sigmaCongrLeft (β := fun i => Fin (P.kind i)) P.pieceEquiv

theorem portEquiv_mk (j : Fin (Fintype.card P.Piece)) (l : Fin (P.kind (P.pieceEquiv j))) :
    P.portEquiv ⟨j, l⟩ = ⟨P.pieceEquiv j, l⟩ :=
  rfl

def collarPoint (u : Circle) (r : EuclideanHalfSpace 1) (v : Circle) (x : Σ i, Fin (P.kind i)) :
    A.Carrier :=
  P.map x.1 ((P.base x.1).collar x.2 (u, r), v)

theorem collarPoint_portEquiv_symm (u : Circle) (r : EuclideanHalfSpace 1) (v : Circle)
    (x : Σ i, Fin (P.kind i)) :
    P.map (P.pieceEquiv (P.portEquiv.symm x).1)
      ((P.base (P.pieceEquiv (P.portEquiv.symm x).1)).collar (P.portEquiv.symm x).2 (u, r), v) =
      P.collarPoint u r v x := by
  have h := congrArg (P.collarPoint u r v) (P.portEquiv.apply_symm_apply x)
  rw [← h]
  rfl


def toEmbeddedPieceSystem : EmbeddedPieceSystem (NoCuts.carrier A) where
  count := Fintype.card P.Piece
  count_pos := Fintype.card_pos_iff.mpr P.nonempty
  kind j := P.kind (P.pieceEquiv j)
  kind_mem j := P.kind_mem _
  base j := P.base (P.pieceEquiv j)
  map j := P.map (P.pieceEquiv j)
  smooth j := P.smooth _
  mfderiv_bijective j := P.mfderiv_bijective _
  covers := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨i, hi⟩ := mem_iUnion.mp (P.covers ▸ mem_univ x : x ∈ ⋃ i, range (P.map i))
    obtain ⟨j, rfl⟩ := P.pieceEquiv.surjective i
    exact mem_iUnion.mpr ⟨j, hi⟩
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
    (P.collarPoint_portEquiv_symm _ _ _ _).symm
  seam_pos c t s hs h1 := (P.seam_pos _ t s hs h1).trans
    (P.collarPoint_portEquiv_symm _ _ _ _).symm
  seam_interior c x _ := interior_mem x
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

theorem complexity_toElementaryPresentation :
    P.toEmbeddedPieceSystem.toElementaryPresentation.complexity = Fintype.card P.Seam :=
  rfl

end Reindex

section Component

variable {N : ClosedOrientedManifold.{u} 3} (P : ClosedPieceSystem.{u} N.Carrier)

def pieceComp (i : P.Piece) : ConnectedComponents N.Carrier :=
  ConnectedComponents.mk (P.map i (inferInstance : Nonempty _).some)

theorem mk_map (i : P.Piece) (q : (P.base i).surface.Carrier × Circle) :
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
    rw [← P.mk_map _ (((P.base _).collar (P.side c false).2
      ((P.matching c 1).1, halfPoint 0 le_rfl), (P.matching c 1).2)), ← h2, h1, P.mk_map]
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
    (x : Σ i : {i : P.Piece // P.pieceComp i = K}, Fin (P.kind i.1)) : Σ i, Fin (P.kind i) :=
  ⟨x.1.1, x.2⟩

theorem liftPort_injective (K : ConnectedComponents N.Carrier) : Injective (P.liftPort K) := by
  rintro ⟨⟨i, hi⟩, l⟩ ⟨⟨i', hi'⟩, l'⟩ h
  have h1 := Sigma.mk.inj_iff.mp h
  obtain rfl : i = i' := h1.1
  have h2 : l = l' := eq_of_heq h1.2
  subst h2
  rfl

theorem mem_componentOpen {K : ConnectedComponents N.Carrier} {y : N.Carrier}
    (hy : ConnectedComponents.mk y = K) : y ∈ (N.componentOpen K : Set N.Carrier) :=
  hy

def compPoint (K : ConnectedComponents N.Carrier) {y : N.Carrier}
    (hy : ConnectedComponents.mk y = K) : (N.component K).Carrier :=
  ⟨y, hy⟩

theorem seam_target_subset (K : ConnectedComponents N.Carrier)
    (c : {c : P.Seam // P.seamComp c = K}) :
    (P.seam c.1).target ⊆ (N.componentOpen K : Set N.Carrier) := by
  intro y hy
  exact mem_componentOpen ((P.mk_seam_target c.1 hy).trans c.2)

theorem seam_mem (K : ConnectedComponents N.Carrier) (c : {c : P.Seam // P.seamComp c = K})
    {p : Torus × ℝ} (hp : p ∈ (P.seam c.1).source) : P.seam c.1 p ∈ N.componentOpen K :=
  P.seam_target_subset K c ((P.seam c.1).map_source' hp)

def restrict (K : ConnectedComponents N.Carrier) (hK : ∃ i, P.pieceComp i = K) :
    ClosedPieceSystem.{u} (N.component K).Carrier where
  Piece := {i : P.Piece // P.pieceComp i = K}
  fintypePiece := Fintype.ofFinite _
  Seam := {c : P.Seam // P.seamComp c = K}
  fintypeSeam := Fintype.ofFinite _
  nonempty := let ⟨i, hi⟩ := hK; ⟨⟨i, hi⟩⟩
  kind i := P.kind i.1
  kind_mem i := P.kind_mem i.1
  base i := P.base i.1
  map i q := compPoint K ((P.mk_map i.1 q).trans i.2)
  smooth i := fun q => codRestr_contMDiffAt (V := N.componentOpen K)
    (fun q => (P.mk_map i.1 q).trans i.2) ((P.smooth i.1) q)
  mfderiv_bijective i q := by
    have hf' : MDifferentiableAt ((SurfaceModel.model (P.base i.1).surface.kind).prod (𝓡 1))
        (𝓡 3) (fun q => compPoint K ((P.mk_map i.1 q).trans i.2)) q :=
      (codRestr_contMDiffAt (V := N.componentOpen K) (fun q => (P.mk_map i.1 q).trans i.2)
        ((P.smooth i.1) q)).mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hval : MDifferentiableAt (𝓡 3) (𝓡 3) (Subtype.val : N.componentOpen K → N.Carrier)
        (compPoint K ((P.mk_map i.1 q).trans i.2)) :=
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
    ⟨compPoint K ((P.mk_seam c.1 (show ((1 : Torus), (0 : ℝ)) ∈ (P.seam c.1).source by
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
theorem card_seam_restrict_of_forall (K : ConnectedComponents N.Carrier)
    (hK : ∃ i, P.pieceComp i = K) (hall : ∀ c, P.seamComp c = K) :
    Fintype.card (P.restrict K hK).Seam = Fintype.card P.Seam := by
  rw [card_seam_restrict]
  exact Fintype.card_congr (Equiv.subtypeUnivEquiv hall)

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

end ClosedPieceSystem

end GC.Seifert
