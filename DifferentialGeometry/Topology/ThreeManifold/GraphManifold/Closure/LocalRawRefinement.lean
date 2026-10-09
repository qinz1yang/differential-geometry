import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawRefinement
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativePieceAssemblyClosed

/-!
Raw piecewise assembly with actual local fibrations, including closed local cut carriers.
-/

set_option autoImplicit false

noncomputable section

open Set Function DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

private def localRawRecastDiffeomorph (C : CompactCarrier.{u}) (k : CarrierModel)
    (h : C.kind = k) :
    (recastCarrier C k h).Carrier ≃ₘ⟮(recastCarrier C k h).model, C.model⟯ C.Carrier := by
  cases C
  subst h
  exact Diffeomorph.refl _ _ _

private theorem localRawCutMap_bijective {C : CompactCarrier.{u}}
    (R : RawGraphPresentation C) (h : R.pairing.count = 0) :
    Bijective R.toTorusPresentation.cutMap := by
  constructor
  · intro x y hxy
    rcases Quotient.exact (R.reconstruction.injective hxy) with he | ⟨j, hj, hrel⟩
    · exact he
    · exact (Fin.cast h j).elim0
  · intro y
    obtain ⟨x, hx⟩ := Quotient.exists_rep (R.reconstruction.symm y)
    refine ⟨x, ?_⟩
    change R.reconstruction (Quotient.mk'' x) = y
    rw [show (Quotient.mk'' x : R.pairing.QuotientSpace) = R.reconstruction.symm y from hx,
      Homeomorph.apply_symm_apply]

private theorem localRawPiece_surjective {C : CompactCarrier.{u}} [ConnectedSpace C.Carrier]
    (R : RawGraphPresentation C) (h : R.pairing.count = 0) (j : Fin R.components.count) :
    Surjective (fun x : R.components.piece j => R.toTorusPresentation.cutMap x.val) := by
  let T := R.toTorusPresentation
  have hb := localRawCutMap_bijective R h
  let K := T.cutMap '' (R.components.piece j : Set R.cutCarrier.Carrier)
  have hk : IsClosed K :=
    ((R.components.piece_compact j).image R.quotient_smooth.continuous).isClosed
  have he : Kᶜ = T.cutMap '' (R.components.piece j : Set R.cutCarrier.Carrier)ᶜ :=
    (Set.image_compl_eq hb).symm
  have ho : IsOpen K := by
    rw [← isClosed_compl_iff, he]
    exact ((R.components.piece j).isOpen.isClosed_compl.isCompact.image
      R.quotient_smooth.continuous).isClosed
  let := R.components.connected j
  obtain ⟨x⟩ := (inferInstance : Nonempty (R.components.piece j))
  have hu : K = univ := IsClopen.eq_univ ⟨hk, ho⟩ ⟨T.cutMap x.val, x.val, x.property, rfl⟩
  intro y
  have hy : y ∈ K := hu ▸ mem_univ y
  obtain ⟨z, hz, hez⟩ := hy
  exact ⟨⟨z, hz⟩, hez⟩

private def localRawClosedPieceDiffeomorph {C : CompactCarrier.{u}} [ConnectedSpace C.Carrier]
    (R : RawGraphPresentation C) (hk : R.cutCarrier.kind ≠ .withBoundary)
    (j : Fin R.components.count) :
    R.components.piece j ≃ₘ⟮R.cutCarrier.model, C.model⟯ C.Carrier := by
  have hint : ∀ x : R.components.piece j, R.cutCarrier.model.IsInteriorPoint x := by
    intro x
    apply R.cutCarrier.model.isInteriorPoint_iff_isInteriorPoint_val.mpr
    apply (R.cutCarrier.model.isInteriorPoint_iff_not_isBoundaryPoint x.val).mpr
    exact fun hx => hk (kind_eq_withBoundary_of_isBoundaryPoint hx)
  have hs : ContMDiff R.cutCarrier.model C.model ∞
      (fun x : R.components.piece j => R.toTorusPresentation.cutMap x.val) :=
    R.quotient_smooth.comp contMDiff_subtype_val
  have hf : IsLocalDiffeomorph R.cutCarrier.model C.model ∞
      (fun x : R.components.piece j => R.toTorusPresentation.cutMap x.val) := fun x =>
    isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective hs (hint x)
      (R.toTorusPresentation.bijective_mfderiv_cutMap_val j x)
  refine hf.diffeomorphOfBijective ⟨?_, ?_⟩
  · intro x y hxy
    exact Subtype.ext ((localRawCutMap_bijective R
      (R.toTorusPresentation.pairing_count_eq_zero_of_kind_ne hk)).1 hxy)
  · exact localRawPiece_surjective R
      (R.toTorusPresentation.pairing_count_eq_zero_of_kind_ne hk) j

private def localRawClosedWholeFibration {C : CompactCarrier.{u}} [ConnectedSpace C.Carrier]
    (R : RawGraphPresentation C) (hk : R.cutCarrier.kind ≠ .withBoundary) :
    CircleFibration C ⊤ :=
  (R.fibration ⟨0, R.components.count_pos⟩).ofDiffeomorph
    ((topOpensDiffeomorph (I := C.model) C.Carrier).trans
      (localRawClosedPieceDiffeomorph R hk ⟨0, R.components.count_pos⟩).symm)

private def localRawPresentationFibration {W : CompactCarrier.{u}}
    (T : TorusPresentation W) {i : Fin T.components.count}
    (R : RawGraphPresentation (T.Component i)) (hk : R.cutCarrier.kind = .withBoundary) :
    (R.toTorusPresentation.cutSystemOfKind .withBoundary hk).toTorusPresentation.Fibration := by
  let S := R.toTorusPresentation.cutSystemOfKind .withBoundary hk
  intro j
  letI : TopologicalSpace (S.Piece j) := S.topology j
  letI : ChartedSpace CarrierModel.withBoundary.Space (S.Piece j) := S.charts j
  let e : (recastCarrier (R.toTorusPresentation.Component j) .withBoundary hk).Carrier
      ≃ₘ⟮(recastCarrier (R.toTorusPresentation.Component j) .withBoundary hk).model,
        R.cutCarrier.model⟯ R.components.piece j :=
    localRawRecastDiffeomorph (R.toTorusPresentation.Component j) .withBoundary hk
  let f : S.Piece j ≃ₘ⟮CarrierModel.withBoundary.model, R.cutCarrier.model⟯
      R.components.piece j := e
  letI : ChartedSpace S.cutCarrier.kind.Space S.cutCarrier.Carrier := S.cutCarrier.charts
  let g : S.Piece j ≃ₘ⟮CarrierModel.withBoundary.model, S.cutCarrier.model⟯
      S.components.piece j := S.pieceDiffeomorph j
  exact (R.fibration j).ofDiffeomorph (g.symm.trans f)

private def localRawOfPieceFibration {W : CompactCarrier.{u}} (T : TorusPresentation W)
    (hk : T.cutCarrier.kind = .withBoundary) (i : Fin T.components.count)
    (F : CircleFibration (T.Component i) ⊤) :
    ((T.ofPiece i).cutSystemOfKind .withBoundary hk).toTorusPresentation.Fibration := by
  let S := (T.ofPiece i).cutSystemOfKind .withBoundary hk
  intro j
  letI : TopologicalSpace (S.Piece j) := S.topology j
  letI : ChartedSpace CarrierModel.withBoundary.Space (S.Piece j) := S.charts j
  let e : S.Piece j ≃ₘ⟮CarrierModel.withBoundary.model, (T.Component i).model⟯
      (T.Component i).Carrier :=
    (localRawRecastDiffeomorph ((T.ofPiece i).Component j) .withBoundary hk).trans
      (topOpensDiffeomorph (I := (T.Component i).model) (T.Component i).Carrier)
  letI : ChartedSpace S.cutCarrier.kind.Space S.cutCarrier.Carrier := S.cutCarrier.charts
  let g : S.Piece j ≃ₘ⟮CarrierModel.withBoundary.model, S.cutCarrier.model⟯
      S.components.piece j := S.pieceDiffeomorph j
  exact F.ofDiffeomorph ((g.symm.trans e).trans
    (topOpensDiffeomorph (I := (T.Component i).model) (T.Component i).Carrier).symm)

private def localRawClosedSystemFibration (C : CompactCarrier.{u}) (hk : C.kind = .closed)
    [ConnectedSpace C.Carrier] (F : CircleFibration C ⊤) :
    (closedCutSystem C hk).toTorusPresentation.Fibration := by
  let S := closedCutSystem C hk
  intro j
  letI : TopologicalSpace (S.Piece j) := S.topology j
  letI : ChartedSpace CarrierModel.withBoundary.Space (S.Piece j) := S.charts j
  letI : IsManifold CarrierModel.withBoundary.model ∞ (S.Piece j) := S.manifold j
  have hint : ∀ x : S.Piece j, CarrierModel.withBoundary.model.IsInteriorPoint x := by
    intro x
    apply (CarrierModel.withBoundary.model.isInteriorPoint_iff_not_isBoundaryPoint x).mpr
    intro hx
    have hb : x ∈ CarrierModel.withBoundary.model.boundary (S.Piece j) := hx
    rw [S.boundary_exhausted j] at hb
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hb
    exact l.elim0
  have hf : IsLocalDiffeomorph CarrierModel.withBoundary.model C.model ∞ (S.map j) :=
    fun x => isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective
      (S.smooth j) (hint x) (S.mfderiv_bijective j x)
  let e : S.Piece j ≃ₘ⟮CarrierModel.withBoundary.model, C.model⟯ C.Carrier :=
    hf.diffeomorphOfBijective ⟨fun x y h => Subtype.ext h,
      fun x => ⟨⟨x, trivial⟩, rfl⟩⟩
  letI : ChartedSpace S.cutCarrier.kind.Space S.cutCarrier.Carrier := S.cutCarrier.charts
  let g : S.Piece j ≃ₘ⟮CarrierModel.withBoundary.model, S.cutCarrier.model⟯
      S.components.piece j := S.pieceDiffeomorph j
  exact F.ofDiffeomorph ((g.symm.trans e).trans
    (topOpensDiffeomorph (I := C.model) C.Carrier).symm)

private def localRawFibredCutSystem {W : CompactCarrier.{u}} (T : TorusPresentation W)
    (R : ∀ i, RawGraphPresentation (T.Component i))
    (port : ∀ i, Fin (R i).externalCount ≃ T.OwnedSide i)
    (hcollar : ∀ i j p, p ∈ halfCollarSource →
      ((R i).external.collar j p).val = T.pieceCollar i (port i j) p)
    (i : Fin T.components.count) :
    Σ L : T.LocalCutSystem .withBoundary i (R i).toTorusPresentation,
      L.system.toTorusPresentation.Fibration := by
  letI : ConnectedSpace (T.Component i).Carrier := T.components.connected i
  by_cases hk : (R i).cutCarrier.kind = .withBoundary
  · exact ⟨TorusPresentation.LocalCutSystem.ofPresentation (R i).toTorusPresentation
      hk (port i) (hcollar i), localRawPresentationFibration T (R i) hk⟩
  · let F := localRawClosedWholeFibration (R i) hk
    by_cases hT : T.cutCarrier.kind = .withBoundary
    · exact ⟨TorusPresentation.LocalCutSystem.ofPiece hT (R i).toTorusPresentation
        ((R i).toTorusPresentation.pairing_count_eq_zero_of_kind_ne hk),
        localRawOfPieceFibration T hT i F⟩
    · exact ⟨TorusPresentation.LocalCutSystem.ofClosed hT (R i).toTorusPresentation
        ((R i).toTorusPresentation.pairing_count_eq_zero_of_kind_ne hk),
        localRawClosedSystemFibration (T.Component i)
          (TorusPresentation.component_kind_eq_closed hT i) F⟩

theorem exists_rawPiecewisePresentation {W : CompactCarrier.{u}} (T : TorusPresentation W)
    (R : ∀ i, RawGraphPresentation (T.Component i))
    (port : ∀ i, Fin (R i).externalCount ≃ T.OwnedSide i)
    (hcollar : ∀ i j p, p ∈ halfCollarSource →
      ((R i).external.collar j p).val = T.pieceCollar i (port i j) p) :
    ∃ G : RawGraphPresentation W, ∃ hc : G.externalCount = T.externalCount,
      ∃ e : (Fin T.pairing.count ⊕ Σ i, Fin (R i).pairing.count) ≃ Fin G.pairing.count,
        (∀ j p, p ∈ halfCollarSource →
          G.external.collar (Fin.cast hc.symm j) p = T.external.collar j p) ∧
        (∀ j p, p ∈ signedCollarSource → G.seam (e (.inl j)) p = T.seam j p) ∧
        (∀ i j p, p ∈ signedCollarSource →
          G.seam (e (.inr ⟨i, j⟩)) p = T.pieceToCarrier i ((R i).seam j p)) ∧
        (∀ j, G.pairing.matching (e (.inl j)) = T.pairing.matching j) ∧
        (∀ i j, G.pairing.matching (e (.inr ⟨i, j⟩)) = (R i).pairing.matching j) := by
  let L := fun i => (localRawFibredCutSystem T R port hcollar i).1
  let Rf := TorusPresentation.LocalCutSystem.refinement L
  let F : ∀ i, (Rf.system i).toTorusPresentation.Fibration :=
    fun i => (localRawFibredCutSystem T R port hcollar i).2
  let G := rawGraphPresentation_of_fibredRefinement T Rf F
  let σ : (Σ i, Fin (R i).pairing.count) ≃ Σ i, Fin (Rf.system i).seamCount :=
    Equiv.sigmaCongrRight fun i => (L i).seamEquiv.symm
  let e : (Fin T.pairing.count ⊕ Σ i, Fin (R i).pairing.count) ≃
      Fin (Rf.newSeamCount + T.pairing.count) :=
    ((Equiv.sumComm _ _).trans (Equiv.sumCongr (σ.trans finSigmaFinEquiv) (Equiv.refl _))).trans
      finSumFinEquiv
  refine ⟨G, rfl, e, fun j p hp => Rf.splice_external_collar j hp,
    fun j p hp => ?_, fun i j p hp => ?_, fun j => ?_, fun i j => ?_⟩
  · change Rf.splice.toTorusPresentation.seam (finSumFinEquiv (.inr j)) p = _
    rw [Rf.splice_seam_old]
  · have h1 := Rf.seam_new i ((L i).seamEquiv.symm j)
    have h2 := Rf.newSeam_apply ⟨i, (L i).seamEquiv.symm j⟩ p
    have h3 := (L i).seam_eq ((L i).seamEquiv.symm j)
    have h3 := h3.trans (congrArg (R i).toTorusPresentation.seam
      ((L i).seamEquiv.apply_symm_apply j))
    calc _ = Rf.newSeam ⟨i, (L i).seamEquiv.symm j⟩ p :=
          congrArg (fun Φ : PartialDiffeomorph signedCollarModel W.model
            (Torus × ℝ) W.Carrier ∞ => Φ p) h1
      _ = T.cutMap ((L i).system.seam ((L i).seamEquiv.symm j) p).val := h2
      _ = T.cutMap ((R i).seam j p).val := by
        rw [h3]
        rfl
  · exact Rf.splice_matching_old j
  · have h1 := Rf.matching_new i ((L i).seamEquiv.symm j)
    have h3 := (L i).matching_eq ((L i).seamEquiv.symm j)
    have h3 := h3.trans (congrArg (R i).toTorusPresentation.pairing.matching
      ((L i).seamEquiv.apply_symm_apply j))
    exact h1.trans h3

end GC.GraphManifold
