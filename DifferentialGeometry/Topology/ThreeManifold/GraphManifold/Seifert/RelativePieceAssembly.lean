import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeProof
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Contract
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledGoodness

/-!
# Relative piece assembly

Packet BA of the X38 survey (`handoffs/20261004-survey-b-with-tori.md` §3, review 20 §6). Given a
torus presentation `T` of `W` and, for every piece `i`, a torus presentation `R i` of the component
carrier whose external tori are the ports of `i` (`port`, with the half collars equal on the whole
collar, `hcollar`), the pieces of all `R i` form a torus presentation of `W`: the sigma pieces
`(i, j)` are mapped by `T.cutMap ∘ ι_i ∘ (R i).cutMap ∘ ι_{i,j}`, the seams are those of `T`
followed by the seams of every `R i` carried into `W`, and the external tori are those of `T`.
This is MD6's `TorusPresentation.Refinement.splice` (`SF/ElementarizeProof.lean`) applied to the
cut systems of the `R i`; no flattening map is assumed.

All pieces of a cut system share one `CarrierModel`. `cutSystemOfKind` is
`TorusPresentation.cutSystem` with its pieces recast (`recastCarrier`) to any kind equal to the
kind of the cut carrier, with the same seams, matchings, sides and external tori.
A `LocalCutSystem k i R` is a cut system of the component `i` of kind `k`, a bijection of its
seams with those of `R` preserving seams and matchings, and the port bijection with its collar
equation; `LocalCutSystem.exists_piecewisePresentation` assembles a family of them into the frozen
conclusion: the external collars of `T`, the old seams `T.seam j` and the inserted seams
`T.pieceToCarrier i ∘ (R i).seam j` on `signedCollarSource`, and both matchings, through one
bijection `Fin T.pairing.count ⊕ Σ i, Fin (R i).pairing.count ≃ Fin S.pairing.count`. Self-seams
of `T` are two distinct ports of one piece, each an external torus of the local presentation.

The kind obligation is derived, not assumed. A cut carrier of kind `.closed` has no boundary
point (`kind_eq_withBoundary_of_isBoundaryPoint`), so a presentation with a seam or an external
torus has kind `.withBoundary` (`cutCarrier_kind_eq_withBoundary_of_pairing_count_pos`,
`…_of_externalCount_pos`), and a presentation of kind `.closed` has neither. Hence:
`exists_piecewisePresentation_of_kind` (all `R i` of one kind), `…_of_ownedSide` (every piece
of `T` owns a side, so every `R i` has an external torus), and `…_of_withBoundary` (the cut
carrier of `T` has kind `.withBoundary`; a closed-kind `R i` has no seams and its component is
represented by itself, `LocalCutSystem.ofPiece`).
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

abbrev recastPiece (k : CarrierModel) (hk : T.cutCarrier.kind = k) (j : Fin T.components.count) :
    CompactCarrier.{u} :=
  recastCarrier (T.Component j) k hk

def cutSystemOfKind (k : CarrierModel) (hk : T.cutCarrier.kind = k) : EmbeddedCutSystem W k where
  count := T.components.count
  count_pos := T.components.count_pos
  Piece j := (T.recastPiece k hk j).Carrier
  topology j := (T.recastPiece k hk j).topology
  charts j := (T.recastPiece k hk j).charts
  manifold j := (T.recastPiece k hk j).smooth
  compact j := (T.recastPiece k hk j).compact
  hausdorff j := (T.recastPiece k hk j).hausdorff
  secondCountable j := (T.recastPiece k hk j).secondCountable
  connected j := T.components.connected j
  map _ x := T.cutMap x.val
  smooth j := (recast_contMDiff_iff_left (T.Component j) k hk (fun x => T.cutMap x.val)).mpr
    (T.quotient_smooth.comp (contMDiff_subtype_val (I := T.cutCarrier.model)
      (U := T.components.piece j)))
  mfderiv_bijective j q := by
    have he := recast_mfderiv_left (T.Component j) k hk
      (J := W.model) (fun q => T.cutMap q.val) q
    exact he ▸ T.bijective_mfderiv_cutMap_val j q
  covers := T.covers_cutMap
  torusCount j := Fintype.card (T.OwnedSide j)
  collar j l := recastPD (T.Component j) k hk ((T.pieceBoundaryTori j).collar l)
  collar_source j l :=
    (recastPD_source (T.Component j) k hk _).trans ((T.pieceBoundaryTori j).source_eq l)
  collar_disjoint j a b hab := by
    have h1 := recastPD_target (T.Component j) k hk ((T.pieceBoundaryTori j).collar a)
    have h2 := recastPD_target (T.Component j) k hk ((T.pieceBoundaryTori j).collar b)
    have h : Disjoint ((T.pieceBoundaryTori j).collar a).target
        ((T.pieceBoundaryTori j).collar b).target := (T.pieceBoundaryTori j).disjoint hab
    rw [← h1, ← h2] at h
    exact h
  boundary_exhausted j := by
    ext q
    change (T.recastPiece k hk j).model.IsBoundaryPoint q ↔ _
    rw [recast_isBoundaryPoint_iff (T.Component j) k hk]
    have hb := congrArg (fun A : Set (T.Component j).Carrier => q ∈ A)
      (T.pieceBoundaryTori_image j)
    dsimp only [BoundaryTori.image, BoundaryTori.torusMap] at hb
    have he : (⋃ l, Set.range fun t =>
        recastPD (T.Component j) k hk ((T.pieceBoundaryTori j).collar l) (t, halfZero)) =
        (T.pieceBoundaryTori j).image := by
      apply Set.iUnion_congr
      intro l
      apply congrArg Set.range
      funext t
      exact recastPD_apply (T.Component j) k hk _ _
    rw [he]
    exact Iff.of_eq hb
  seamCount := T.pairing.count
  side c b := T.sideEquiv (T.sideSum (.inl (c, b)))
  externalCount := T.externalCount
  externalSide i := T.sideEquiv (T.sideSum (.inr i))
  sides_bijective := T.bijective_cutSides
  matching := T.pairing.matching
  seam := T.seam
  seam_source := T.seam_source
  seam_neg c t s hs h1 := (T.seam_negative c t s hs h1).trans (congrArg T.cutMap
    ((congrArg Subtype.val (recastPD_apply (T.Component _) k hk _ _)).trans
      (T.pieceCollar_sideEquiv (.inl c) (p := (t, halfPoint (-s) (neg_nonneg.2 hs)))
        (show -s < 1 by linarith))).symm)
  seam_pos c t s hs h1 := (T.seam_positive c t s hs h1).trans (congrArg T.cutMap
    ((congrArg Subtype.val (recastPD_apply (T.Component _) k hk _ _)).trans
      (T.pieceCollar_sideEquiv (.inr (.inl c)) (p := (T.pairing.matching c t, halfPoint s hs))
        h1)).symm)
  seam_interior := T.seam_interior
  external_local i t := by
    refine (recast_isLocalDiffeomorphAt_iff (T.Component _) k hk _ _).mpr ?_
    have hv := DifferentialGeometry.isLocalDiffeomorph_subtype_val (I := T.cutCarrier.model)
      (T.components.piece (T.externalPiece i))
      ((T.pieceBoundaryTori _).collar (T.sideEquiv (.inr (.inr i))).2 (t, halfZero))
    have hc : IsLocalDiffeomorphAt T.cutCarrier.model W.model ∞ T.cutMap
        (Subtype.val ((T.pieceBoundaryTori (T.sideEquiv (.inr (.inr i))).1).collar
          (T.sideEquiv (.inr (.inr i))).2 (t, halfZero))) := by
      rw [T.pieceCollar_sideEquiv (.inr (.inr i)) (zero_mem_halfCollarSource t)]
      exact T.isLocalDiffeomorphAt_cutMap_external i t
    have h := hv.comp W.model W.Carrier hc
    rwa [← recastPD_apply (T.Component _) k hk] at h
  overlap j j' q q' h := by
    have hq : T.pairing.quotientMap q.val = T.pairing.quotientMap q'.val :=
      T.reconstruction.injective h
    rcases (Quotient.exact hq : T.pairing.gluing.rel q.val q'.val) with he | ⟨c, hc, -⟩
    · left
      have hjj : j = j' := by
        by_contra hne
        exact (T.components.disjoint hne).le_bot ⟨q.property, he ▸ q'.property⟩
      subst hjj
      rw [Subtype.ext he]
    · right
      rcases hc with hl | hr
      · refine ⟨c, (T.pairing.leftParam c).symm ⟨q.val, hl⟩, ?_⟩
        rw [T.seam_zero, Homeomorph.apply_symm_apply]
        rfl
      · refine ⟨c, (T.pairing.matching c).symm ((T.pairing.rightParam c).symm ⟨q.val, hr⟩), ?_⟩
        rw [T.seam_zero]
        change T.reconstruction (T.pairing.quotientMap q.val) = _
        rw [T.quotientMap_leftParam_eq_rightParam_matching, Diffeomorph.apply_symm_apply,
          Homeomorph.apply_symm_apply]

theorem cutSystemOfKind_fold_externalSide (k : CarrierModel) (hk : T.cutCarrier.kind = k)
    (l : Fin T.externalCount) {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    (T.cutSystemOfKind k hk).fold ((T.cutSystemOfKind k hk).sideCollar
      ((T.cutSystemOfKind k hk).externalSide l) p) = T.external.collar l p := by
  rw [EmbeddedCutSystem.fold_sideCollar]
  change T.cutMap (recastPD (T.Component _) k hk
    ((T.pieceBoundaryTori (T.sideEquiv (.inr (.inr l))).1).collar
      (T.sideEquiv (.inr (.inr l))).2) p).val = _
  rw [recastPD_apply (T.Component _) k hk,
    T.pieceCollar_sideEquiv (.inr (.inr l)) hp]
  exact T.marked_collar l p hp

structure LocalCutSystem (k : CarrierModel) (i : Fin T.components.count)
    (R : TorusPresentation (T.Component i)) where
  system : EmbeddedCutSystem (T.Component i) k
  seamEquiv : Fin system.seamCount ≃ Fin R.pairing.count
  seam_eq : ∀ c, system.seam c = R.seam (seamEquiv c)
  matching_eq : ∀ c, system.matching c = R.pairing.matching (seamEquiv c)
  port : Fin system.externalCount ≃ T.OwnedSide i
  port_collar : ∀ l p, p ∈ halfCollarSource →
    Subtype.val (system.fold (system.sideCollar (system.externalSide l) p)) =
      T.sideCollar (port l).val p

namespace LocalCutSystem

variable {T} {k : CarrierModel}

def ofPresentation {i : Fin T.components.count} (R : TorusPresentation (T.Component i))
    (hk : R.cutCarrier.kind = k) (port : Fin R.externalCount ≃ T.OwnedSide i)
    (hcollar : ∀ j p, p ∈ halfCollarSource →
      (R.external.collar j p).val = T.pieceCollar i (port j) p) :
    T.LocalCutSystem k i R where
  system := R.cutSystemOfKind k hk
  seamEquiv := Equiv.refl _
  seam_eq _ := rfl
  matching_eq _ := rfl
  port := port
  port_collar l p hp := by
    rw [R.cutSystemOfKind_fold_externalSide k hk l hp, hcollar l p hp, T.pieceCollar_apply i _ hp]
    rfl

def ofPiece (hT : T.cutCarrier.kind = k) {i : Fin T.components.count}
    (R : TorusPresentation (T.Component i)) (hR : R.pairing.count = 0) :
    T.LocalCutSystem k i R where
  system := (T.ofPiece i).cutSystemOfKind k hT
  seamEquiv := finCongr hR.symm
  seam_eq c := c.elim0
  matching_eq c := c.elim0
  port := (Fintype.equivFin (T.OwnedSide i)).symm
  port_collar l p hp := by
    rw [(T.ofPiece i).cutSystemOfKind_fold_externalSide k hT l hp]
    exact T.pieceCollar_apply i _ hp

def refinement {R : ∀ i, TorusPresentation (T.Component i)}
    (L : ∀ i, T.LocalCutSystem k i (R i)) : T.Refinement k where
  system i := (L i).system
  port i := (L i).port
  port_collar i := (L i).port_collar

theorem exists_piecewisePresentation {R : ∀ i, TorusPresentation (T.Component i)}
    (L : ∀ i, T.LocalCutSystem k i (R i)) :
    ∃ S : TorusPresentation W, ∃ hc : S.externalCount = T.externalCount,
      ∃ e : (Fin T.pairing.count ⊕ Σ i, Fin (R i).pairing.count) ≃ Fin S.pairing.count,
        (∀ j p, p ∈ halfCollarSource →
          S.external.collar (Fin.cast hc.symm j) p = T.external.collar j p) ∧
        (∀ j p, p ∈ signedCollarSource → S.seam (e (.inl j)) p = T.seam j p) ∧
        (∀ i j p, p ∈ signedCollarSource →
          S.seam (e (.inr ⟨i, j⟩)) p = T.pieceToCarrier i ((R i).seam j p)) ∧
        (∀ j, S.pairing.matching (e (.inl j)) = T.pairing.matching j) ∧
        (∀ i j, S.pairing.matching (e (.inr ⟨i, j⟩)) = (R i).pairing.matching j) := by
  let Rf := refinement L
  let σ : (Σ i, Fin (R i).pairing.count) ≃ Σ i, Fin (Rf.system i).seamCount :=
    Equiv.sigmaCongrRight fun i => (L i).seamEquiv.symm
  let e : (Fin T.pairing.count ⊕ Σ i, Fin (R i).pairing.count) ≃
      Fin (Rf.newSeamCount + T.pairing.count) :=
    ((Equiv.sumComm _ _).trans (Equiv.sumCongr (σ.trans finSigmaFinEquiv) (Equiv.refl _))).trans
      finSumFinEquiv
  refine ⟨Rf.splice.toTorusPresentation, rfl, e, fun j p hp => Rf.splice_external_collar j hp,
    fun j p _ => ?_, fun i j p _ => ?_, fun j => ?_, fun i j => ?_⟩
  · change Rf.splice.toTorusPresentation.seam (finSumFinEquiv (.inr j)) p = _
    rw [Rf.splice_seam_old]
  · have h1 := Rf.seam_new i ((L i).seamEquiv.symm j)
    have h2 := Rf.newSeam_apply ⟨i, (L i).seamEquiv.symm j⟩ p
    have h3 := (L i).seam_eq ((L i).seamEquiv.symm j)
    rw [Equiv.apply_symm_apply] at h3
    calc _ = Rf.newSeam ⟨i, (L i).seamEquiv.symm j⟩ p :=
          congrArg (fun Φ : PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞ =>
            Φ p) h1
      _ = T.cutMap ((L i).system.seam ((L i).seamEquiv.symm j) p).val := h2
      _ = T.cutMap ((R i).seam j p).val := by rw [h3]
  · exact Rf.splice_matching_old j
  · have h1 := Rf.matching_new i ((L i).seamEquiv.symm j)
    have h3 := (L i).matching_eq ((L i).seamEquiv.symm j)
    rw [Equiv.apply_symm_apply] at h3
    exact h1.trans h3

end LocalCutSystem

theorem cutCarrier_kind_eq_withBoundary_of_isBoundaryPoint {x : T.cutCarrier.Carrier}
    (hx : T.cutCarrier.model.IsBoundaryPoint x) : T.cutCarrier.kind = .withBoundary :=
  kind_eq_withBoundary_of_isBoundaryPoint hx

theorem cutCarrier_kind_eq_withBoundary_of_externalCount_pos (h : 0 < T.externalCount) :
    T.cutCarrier.kind = .withBoundary :=
  T.cutCarrier_kind_eq_withBoundary_of_isBoundaryPoint (T.cutExternal.boundary_zero ⟨0, h⟩ 1)

theorem cutCarrier_kind_eq_withBoundary_of_pairing_count_pos (h : 0 < T.pairing.count) :
    T.cutCarrier.kind = .withBoundary := by
  refine T.cutCarrier_kind_eq_withBoundary_of_isBoundaryPoint
    (x := (T.pairing.leftParam ⟨0, h⟩ 1).val) ?_
  change _ ∈ T.cutCarrier.model.boundary T.cutCarrier.Carrier
  rw [T.cut_boundary_exhausted]
  exact Or.inl (Set.mem_iUnion.mpr ⟨⟨0, h⟩, Or.inl (T.pairing.leftParam ⟨0, h⟩ 1).property⟩)

theorem pairing_count_eq_zero_of_kind_ne (h : T.cutCarrier.kind ≠ .withBoundary) :
    T.pairing.count = 0 :=
  Nat.eq_zero_of_not_pos fun hp => h (T.cutCarrier_kind_eq_withBoundary_of_pairing_count_pos hp)

theorem externalCount_eq_zero_of_kind_ne (h : T.cutCarrier.kind ≠ .withBoundary) :
    T.externalCount = 0 :=
  Nat.eq_zero_of_not_pos fun hp => h (T.cutCarrier_kind_eq_withBoundary_of_externalCount_pos hp)

section Assembly

variable (R : ∀ i, TorusPresentation (T.Component i))
  (port : ∀ i, Fin (R i).externalCount ≃ T.OwnedSide i)
  (hcollar : ∀ i j p, p ∈ halfCollarSource →
    ((R i).external.collar j p).val = T.pieceCollar i (port i j) p)

include hcollar in
theorem exists_piecewisePresentation_of_kind (k : CarrierModel)
    (hk : ∀ i, (R i).cutCarrier.kind = k) :
    ∃ S : TorusPresentation W, ∃ hc : S.externalCount = T.externalCount,
      ∃ e : (Fin T.pairing.count ⊕ Σ i, Fin (R i).pairing.count) ≃ Fin S.pairing.count,
        (∀ j p, p ∈ halfCollarSource →
          S.external.collar (Fin.cast hc.symm j) p = T.external.collar j p) ∧
        (∀ j p, p ∈ signedCollarSource → S.seam (e (.inl j)) p = T.seam j p) ∧
        (∀ i j p, p ∈ signedCollarSource →
          S.seam (e (.inr ⟨i, j⟩)) p = T.pieceToCarrier i ((R i).seam j p)) ∧
        (∀ j, S.pairing.matching (e (.inl j)) = T.pairing.matching j) ∧
        (∀ i j, S.pairing.matching (e (.inr ⟨i, j⟩)) = (R i).pairing.matching j) :=
  LocalCutSystem.exists_piecewisePresentation fun i =>
    LocalCutSystem.ofPresentation (R i) (hk i) (port i) (hcollar i)

include hcollar in
theorem exists_piecewisePresentation_of_withBoundary (hT : T.cutCarrier.kind = .withBoundary) :
    ∃ S : TorusPresentation W, ∃ hc : S.externalCount = T.externalCount,
      ∃ e : (Fin T.pairing.count ⊕ Σ i, Fin (R i).pairing.count) ≃ Fin S.pairing.count,
        (∀ j p, p ∈ halfCollarSource →
          S.external.collar (Fin.cast hc.symm j) p = T.external.collar j p) ∧
        (∀ j p, p ∈ signedCollarSource → S.seam (e (.inl j)) p = T.seam j p) ∧
        (∀ i j p, p ∈ signedCollarSource →
          S.seam (e (.inr ⟨i, j⟩)) p = T.pieceToCarrier i ((R i).seam j p)) ∧
        (∀ j, S.pairing.matching (e (.inl j)) = T.pairing.matching j) ∧
        (∀ i j, S.pairing.matching (e (.inr ⟨i, j⟩)) = (R i).pairing.matching j) := by
  refine LocalCutSystem.exists_piecewisePresentation (k := .withBoundary) fun i => ?_
  by_cases h : (R i).cutCarrier.kind = .withBoundary
  · exact LocalCutSystem.ofPresentation (R i) h (port i) (hcollar i)
  · exact LocalCutSystem.ofPiece hT (R i) ((R i).pairing_count_eq_zero_of_kind_ne h)

include hcollar in
theorem exists_piecewisePresentation_of_ownedSide (hside : ∀ i, Nonempty (T.OwnedSide i)) :
    ∃ S : TorusPresentation W, ∃ hc : S.externalCount = T.externalCount,
      ∃ e : (Fin T.pairing.count ⊕ Σ i, Fin (R i).pairing.count) ≃ Fin S.pairing.count,
        (∀ j p, p ∈ halfCollarSource →
          S.external.collar (Fin.cast hc.symm j) p = T.external.collar j p) ∧
        (∀ j p, p ∈ signedCollarSource → S.seam (e (.inl j)) p = T.seam j p) ∧
        (∀ i j p, p ∈ signedCollarSource →
          S.seam (e (.inr ⟨i, j⟩)) p = T.pieceToCarrier i ((R i).seam j p)) ∧
        (∀ j, S.pairing.matching (e (.inl j)) = T.pairing.matching j) ∧
        (∀ i j, S.pairing.matching (e (.inr ⟨i, j⟩)) = (R i).pairing.matching j) := by
  refine T.exists_piecewisePresentation_of_kind R port hcollar .withBoundary fun i => ?_
  obtain ⟨s⟩ := hside i
  exact (R i).cutCarrier_kind_eq_withBoundary_of_externalCount_pos
    (Fin.pos ((port i).symm s))

end Assembly

end TorusPresentation

end GC.Seifert
