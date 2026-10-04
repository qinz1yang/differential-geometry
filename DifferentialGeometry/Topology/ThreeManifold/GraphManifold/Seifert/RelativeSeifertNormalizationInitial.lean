import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationMixedRefinement
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationPorts
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringMobiusFinal

/-!
# The initial mixed stage

Lane BR, tier R6 (review 26 §2.2). Let `T` be a torus presentation of a closed connected oriented
`Q` whose pieces are interior hyperbolic or carry a raw graph presentation of their component
carrier. For every raw piece, P1 (`Wiring.elementarizeOnSubCollar`) gives an elementary
presentation of the component carrier, and it is moved by an orientation-preserving
diffeomorphism so that its external collars are the port collars of `T`, up to a bijection of
ports, torus diffeomorphisms `ψ` and a sub-collar of width `δᵢ`
(`exists_elementary_subCollar_of_boundaryTori`). The coarse presentation is reparametrised on
the matching sides by these `ψ` (`TorusPresentation.reparam`, matchings conjugated on both sides)
and then `T` and every local presentation are shrunk by one width `δ ≤ min δᵢ`
(`TorusPresentation.shrink`, `ElementaryPresentation.shrink`); the local external collars are then
the port collars of `T₁ = (T.reparam α).shrink δ` on the whole collar. With the components
themselves for the hyperbolic pieces this is a mixed refinement of `T₁`, whose splice is the
initial mixed stage. Every old seam `j` of `T` is a protected seam of the stage with the exact
ledger `seam'(t, s) = T.seam j (α t, δ s)` (`exists_initialMixedStage_of_kind`).

When some piece is hyperbolic and `T` has no seam with boundary model, `T` has no seam at all, so
it has one piece, which is frozen, and `T` itself is the stage
(`components_count_eq_one_of_pairing_count_eq_zero`, `initialMixedStage_of_single`).
`initialMixedStage` is the statement consumed by lane BE as `hInit`, proved unconditionally.
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization

def recastDiffeomorph (D : CompactCarrier.{u}) (k : CarrierModel) (h : D.kind = k) :
    (recastCarrier D k h).Carrier ≃ₘ⟮(recastCarrier D k h).model, D.model⟯ D.Carrier := by
  cases D
  subst h
  exact Diffeomorph.refl _ _ _

def ofPieceDiffeomorph {W : CompactCarrier.{u}} (T : TorusPresentation W) {k : CarrierModel}
    (hk : T.cutCarrier.kind = k) (i : Fin T.components.count)
    (j : Fin ((T.ofPiece i).cutSystemOfKind k hk).count) :
    (T.Component i).Carrier ≃ₘ⟮(T.Component i).model, k.model⟯
      ((T.ofPiece i).cutSystemOfKind k hk).Piece j :=
  (topOpensDiffeomorph (I := (T.Component i).model) (T.Component i).Carrier).symm.trans
    (recastDiffeomorph ((T.ofPiece i).Component j) k hk).symm

theorem exists_initialMixedStage_of_kind {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T : TorusPresentation.{u} (NoCuts.carrier Q)) (raw : Finset (Fin T.components.count))
    (hraw : ∀ i ∈ raw, Nonempty (RawGraphPresentation (T.Component i)))
    (hhyp : ∀ i, i ∉ raw → ∃ g : (T.Component i).InteriorGeometry ⊤,
      letI := Manifold.interiorChartedSpace (T.Component i).model ∞
        (M := (T.Component i).pieceInterior ⊤)
      letI := Manifold.interiorIsManifold (T.Component i).model ∞
        (M := (T.Component i).pieceInterior ⊤)
      g.model = .hyperbolic)
    (hk : (∃ i, i ∉ raw) → T.cutCarrier.kind = .withBoundary) :
    ∃ (σ : MixedStage Q) (e : Fin T.pairing.count ≃ σ.ProtSeam),
      ∀ j, Nonempty (CollarLedger Eq (T.seam j) (σ.toTorus.seam (e j).1)) := by
  classical
  have hdata : ∀ i, i ∈ raw → ∃ (E : ElementaryPresentation (T.Component i))
      (σ : Fin E.toTorus.externalCount ≃ Fin (Fintype.card (T.OwnedSide i)))
      (ψ : Fin E.toTorus.externalCount → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)) (δ : ℝ),
      0 < δ ∧ ∀ l p, p ∈ halfCollarSource → p.2.val 0 < δ →
        E.toTorus.external.collar l p = (T.pieceBoundaryTori i).collar (σ l) (ψ l p.1, p.2) := by
    intro i hi
    obtain ⟨G⟩ := hraw i hi
    obtain ⟨E₀, -⟩ := Wiring.elementarizeOnSubCollar _ G
    exact exists_elementary_subCollar_of_boundaryTori (T.pieceBoundaryTori i)
      (T.pieceBoundaryTori_image i) E₀
  choose E σ ψ δi hδi hagree using hdata
  let δ' : Fin T.components.count → ℝ := fun i => if hi : i ∈ raw then δi i hi else 1
  have hδ' : ∀ i, 0 < δ' i := fun i => by
    by_cases hi : i ∈ raw
    · simp only [δ', hi, dite_true]
      exact hδi i hi
    · simp only [δ', hi, dite_false]
      exact one_pos
  obtain ⟨m, hm, hmle⟩ := Wiring.exists_pos_le_of_finite δ' hδ'
  let δ : ℝ := min m 1
  have hδ : 0 < δ := lt_min hm one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδle : ∀ i (hi : i ∈ raw), δ ≤ δi i hi := fun i hi => by
    have h := hmle i
    simp only [δ', hi, dite_true] at h
    exact (min_le_left _ _).trans h
  let α : T.Side → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) := fun s =>
    if hi : T.sidePiece s ∈ raw then
      ψ _ hi ((σ _ hi).symm (Fintype.equivFin (T.OwnedSide (T.sidePiece s)) ⟨s, rfl⟩))
    else Diffeomorph.refl _ _ _
  let T₁ : TorusPresentation (NoCuts.carrier Q) := (T.reparam α).shrink hδ hδ1
  have hside : ∀ i (hi : i ∈ raw) (o : T.OwnedSide i) (p : Torus × EuclideanHalfSpace 1),
      T₁.sideCollar o.val p = T.sideCollar o.val
        (ψ i hi ((σ i hi).symm (Fintype.equivFin _ o)) p.1, halfSpaceScale hδ p.2) := by
    have hgen : ∀ (s : T.Side) (p : Torus × EuclideanHalfSpace 1),
        T₁.sideCollar s p = T.sideCollar s (α s p.1, halfSpaceScale hδ p.2) := by
      intro s p
      rcases s with c | c | c <;> rfl
    rintro i hi ⟨s, rfl⟩ p
    rw [hgen]
    simp only [α, hi, dite_true]
    rfl
  have hsp : ∀ s : T.Side, T₁.sidePiece s = T.sidePiece s := fun s => by
    rcases s with c | c | c <;> rfl
  let own : ∀ i, T.OwnedSide i ≃ T₁.OwnedSide i := fun i =>
    Equiv.subtypeEquivRight fun s => by rw [hsp s]; exact Iff.rfl
  let E' : ∀ i, i ∈ raw → ElementaryPresentation (T₁.Component i) := fun i hi =>
    (E i hi).shrink hδ hδ1
  let port : ∀ i (hi : i ∈ raw), Fin (E' i hi).toTorus.externalCount ≃ T₁.OwnedSide i :=
    fun i hi => (σ i hi).trans ((Fintype.equivFin _).symm.trans (own i))
  have hcol : ∀ i (hi : i ∈ raw) l p, p ∈ halfCollarSource →
      ((E' i hi).toTorus.external.collar l p).val = T₁.sideCollar (port i hi l).val p := by
    intro i hi l p hp
    have hmem : (p.1, halfSpaceScale hδ p.2) ∈ halfCollarSource := halfSpaceScale_mem hδ hδ1 hp
    have hlt : (halfSpaceScale hδ p.2).val 0 < δi i hi :=
      (halfSpaceScale_lt hδ hp).trans_le (hδle i hi)
    have h1 : (E' i hi).toTorus.external.collar l p =
        (E i hi).toTorus.external.collar l (p.1, halfSpaceScale hδ p.2) := rfl
    have hmem' : (ψ i hi l p.1, halfSpaceScale hδ p.2) ∈ halfCollarSource := hmem
    rw [h1, hagree i hi l _ hmem hlt]
    change (T.pieceCollar i ((Fintype.equivFin _).symm (σ i hi l))
      (ψ i hi l p.1, halfSpaceScale hδ p.2) : T.cutCarrier.Carrier) =
        T₁.sideCollar ((Fintype.equivFin _).symm (σ i hi l)).val p
    rw [T.pieceCollar_apply i _ hmem', hside i hi]
    simp only [Equiv.apply_symm_apply]
    have hl : (σ i hi).symm ((σ i hi) l) = l := Equiv.symm_apply_apply _ _
    exact (congrArg (fun z => T.sideCollar ((Fintype.equivFin (T.OwnedSide i)).symm
      ((σ i hi) l)).val (ψ i hi z p.1, halfSpaceScale hδ p.2)) hl).symm
  have hk₁ : (∃ i, i ∉ raw) → T₁.cutCarrier.kind = .withBoundary := hk
  let datum : ∀ i, LocalDatum T₁ .withBoundary i := fun i =>
    if hi : i ∈ raw then LocalDatum.ofElementary (E' i hi) (port i hi) (hcol i hi)
    else LocalDatum.ofPiece (hk₁ ⟨i, hi⟩) i
  have hdr : ∀ i (hi : i ∈ raw),
      datum i = LocalDatum.ofElementary (E' i hi) (port i hi) (hcol i hi) := fun i hi =>
    dite_eq_left hi
  have hdf : ∀ i (hi : i ∉ raw), datum i = LocalDatum.ofPiece (hk₁ ⟨i, hi⟩) i := fun i hi =>
    dite_eq_right hi
  let R : MixedRefinement T₁ .withBoundary :=
    { datum := datum
      frozen := rawᶜ
      frozen_seam := fun i hi => by
        rw [hdf i (Finset.mem_compl.mp hi)]
        rfl
      frozen_geom := fun i hi => by
        have hi' := Finset.mem_compl.mp hi
        rw [hdf i hi']
        intro j
        obtain ⟨g, hg⟩ := hhyp i hi'
        exact ⟨T.Component i, ofPieceDiffeomorph T₁ (hk₁ ⟨i, hi'⟩) i j, g, hg⟩
      cert := fun i hi => by
        have hi' : i ∈ raw := by
          by_contra h
          exact hi (Finset.mem_compl.mpr h)
        rw [hdr i hi']
        exact (E' i hi').toPieceSystem.certificate }
  refine ⟨R.toMixedStage, R.toMixedStage_protEquiv, fun j => ⟨
    { reparam := α (.inl j)
      scale := δ
      scale_pos := hδ
      scale_le_one := hδ1
      tracked := fun p _ => ?_ }⟩⟩
  have hs : R.toMixedStage.toTorus.seam (R.toMixedStage_protEquiv j).1 = T₁.seam j :=
    R.toMixedStage_seam j
  have h2 : T₁.seam j p = T.seam j (α (Sum.inl j) p.1, δ * p.2) := rfl
  have h3 : (R.toMixedStage.toTorus.seam (R.toMixedStage_protEquiv j).1) p = T₁.seam j p :=
    congrArg (fun F => F p) hs
  exact (h3.trans h2).symm

theorem eq_of_pairing_count_eq_zero {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T : TorusPresentation.{u} (NoCuts.carrier Q)) (h : T.pairing.count = 0)
    (i i' : Fin T.components.count) : i = i' := by
  have hinj : Injective T.cutMap := by
    intro x y hxy
    rcases Quotient.exact (T.reconstruction.injective hxy) with he | ⟨j, -, -⟩
    · exact he
    · exact (Fin.cast h j).elim0
  have hsurj : Surjective T.cutMap := fun y => by
    obtain ⟨x, hx⟩ := Quotient.exists_rep (T.reconstruction.symm y)
    refine ⟨x, ?_⟩
    change T.reconstruction (Quotient.mk'' x) = y
    rw [show (Quotient.mk'' x : T.pairing.QuotientSpace) = T.reconstruction.symm y from hx,
      Homeomorph.apply_symm_apply]
  have hc : Continuous T.cutMap := T.quotient_smooth.continuous
  let K := T.cutMap '' (T.components.piece i : Set T.cutCarrier.Carrier)
  have hk : IsClosed K := ((T.components.piece_compact i).image hc).isClosed
  have he : Kᶜ = T.cutMap '' (T.components.piece i : Set T.cutCarrier.Carrier)ᶜ :=
    (Set.image_compl_eq ⟨hinj, hsurj⟩).symm
  have ho : IsOpen K := by
    rw [← isClosed_compl_iff, he]
    exact ((T.components.piece i).isOpen.isClosed_compl.isCompact.image hc).isClosed
  have hn : K.Nonempty := by
    let := T.components.connected i
    obtain ⟨x⟩ := (inferInstance : Nonempty (T.components.piece i))
    exact ⟨T.cutMap x, x, x.property, rfl⟩
  have hu : K = univ := IsClopen.eq_univ ⟨hk, ho⟩ hn
  let := T.components.connected i'
  obtain ⟨y⟩ := (inferInstance : Nonempty (T.components.piece i'))
  have hy : T.cutMap y ∈ K := by
    rw [hu]
    exact mem_univ _
  obtain ⟨z, hz, hzy⟩ := hy
  have hzy' : z = y := hinj hzy
  by_contra hne
  exact (T.components.disjoint hne).le_bot ⟨hzy' ▸ hz, y.property⟩

def singleFrozenStage {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T : TorusPresentation.{u} (NoCuts.carrier Q)) (h : T.pairing.count = 0)
    (hhyp : ∀ i, ∃ g : (T.Component i).InteriorGeometry ⊤,
      letI := Manifold.interiorChartedSpace (T.Component i).model ∞
        (M := (T.Component i).pieceInterior ⊤)
      letI := Manifold.interiorIsManifold (T.Component i).model ∞
        (M := (T.Component i).pieceInterior ⊤)
      g.model = .hyperbolic) : MixedStage Q where
  toTorus := T
  prot := ∅
  frozen := Finset.univ
  hyperbolic i _ := by
    obtain ⟨g, hg⟩ := hhyp i
    exact ⟨transportInteriorGeometry (pieceInteriorCongr
      (topOpensDiffeomorph (I := (T.Component i).model) (T.Component i).Carrier).symm) g, hg⟩
  kind _ := 1
  kind_mem i hi := absurd (Finset.mem_univ i) hi
  piece i hi := absurd (Finset.mem_univ i) hi
  left_prot j _ := (Fin.cast h j).elim0
  right_prot j _ := (Fin.cast h j).elim0

theorem initialMixedStage : ∀ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (T₀ : TorusPresentation.{u} (NoCuts.carrier Q)),
      (∀ i, (∃ g : (GC.Topology.componentCarrier T₀.cutCarrier T₀.components i).InteriorGeometry ⊤,
          letI := Manifold.interiorChartedSpace
            (GC.Topology.componentCarrier T₀.cutCarrier T₀.components i).model ∞
            (M := (GC.Topology.componentCarrier T₀.cutCarrier T₀.components i).pieceInterior ⊤)
          letI := Manifold.interiorIsManifold
            (GC.Topology.componentCarrier T₀.cutCarrier T₀.components i).model ∞
            (M := (GC.Topology.componentCarrier T₀.cutCarrier T₀.components i).pieceInterior ⊤)
          g.model = .hyperbolic) ∨
        Nonempty (RawGraphPresentation
          (GC.Topology.componentCarrier T₀.cutCarrier T₀.components i))) →
      ∃ (σ : MixedStage Q) (e : Fin T₀.pairing.count ≃ σ.ProtSeam),
        ∀ j, Nonempty (CollarLedger Eq (T₀.seam j) (σ.toTorus.seam (e j).1)) := by
  intro Q T hprof
  classical
  let raw : Finset (Fin T.components.count) :=
    Finset.univ.filter fun i => Nonempty (RawGraphPresentation (T.Component i))
  have hraw : ∀ i ∈ raw, Nonempty (RawGraphPresentation (T.Component i)) := fun i hi =>
    (Finset.mem_filter.mp hi).2
  have hhyp : ∀ i, i ∉ raw → _ := fun i hi =>
    (hprof i).resolve_right fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  by_cases hk : T.cutCarrier.kind = .withBoundary
  · exact exists_initialMixedStage_of_kind T raw hraw hhyp fun _ => hk
  by_cases hall : ∀ i, i ∈ raw
  · exact exists_initialMixedStage_of_kind T raw hraw hhyp fun ⟨i, hi⟩ => absurd (hall i) hi
  obtain ⟨i₀, hi₀⟩ := not_forall.mp hall
  have h0 : T.pairing.count = 0 := T.pairing_count_eq_zero_of_kind_ne hk
  have hall' : ∀ i, i ∉ raw := fun i => (eq_of_pairing_count_eq_zero T h0 i i₀) ▸ hi₀
  refine ⟨singleFrozenStage T h0 fun i => hhyp i (hall' i),
    ⟨fun j => (Fin.cast h0 j).elim0, fun c => absurd c.2 (Finset.notMem_empty _),
      fun j => (Fin.cast h0 j).elim0, fun c => absurd c.2 (Finset.notMem_empty _)⟩,
    fun j => (Fin.cast h0 j).elim0⟩

end GC.Seifert.RelativeNormalization
