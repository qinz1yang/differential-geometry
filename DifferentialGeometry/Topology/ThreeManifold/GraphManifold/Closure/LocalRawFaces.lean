import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.LocalRawRefinement
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CollarGermAdapter
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringComponent

/-!
Actual face matching and finite collar straightening for raw piecewise assembly.
-/

set_option autoImplicit false

noncomputable section

open Set Function DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

private theorem rawFaces_disjoint {C : CompactCarrier.{u}} {n : ℕ} (A : BoundaryTori C n) :
    Pairwise fun j k => Disjoint (range (A.torusMap j)) (range (A.torusMap k)) := by
  intro j k hjk
  rw [Set.disjoint_left]
  rintro x ⟨t, rfl⟩ ⟨s, hs⟩
  have ha : A.torusMap j t ∈ (A.collar j).target :=
    (A.collar j).map_source' ((A.source_eq j).symm ▸ zero_mem_halfCollarSource t)
  have hb : A.torusMap k s ∈ (A.collar k).target :=
    (A.collar k).map_source' ((A.source_eq k).symm ▸ zero_mem_halfCollarSource s)
  exact (A.disjoint hjk).le_bot ⟨ha, hs ▸ hb⟩

theorem exists_boundaryTori_faces {C : CompactCarrier.{u}} {n m : ℕ}
    (A : BoundaryTori C n) (B : BoundaryTori C m)
    (hA : C.model.boundary C.Carrier = A.image)
    (hB : C.model.boundary C.Carrier = B.image) :
    ∃ e : Fin n ≃ Fin m, ∃ ψ : Fin n → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus),
      ∀ j t, B.collar (e j) (ψ j t, halfZero) = A.collar j (t, halfZero) := by
  classical
  let E : Fin n → Set C.Carrier := fun j => range (A.torusMap j)
  let F : Fin m → Set C.Carrier := fun r => range (B.torusMap r)
  have hEc : ∀ j, IsClosed (E j) :=
    fun j => (isCompact_range (A.torusMap_smooth j).continuous).isClosed
  have hFc : ∀ r, IsClosed (F r) :=
    fun r => (isCompact_range (B.torusMap_smooth r).continuous).isClosed
  have hEd : Pairwise fun j k => Disjoint (E j) (E k) := rawFaces_disjoint A
  have hFd : Pairwise fun r s => Disjoint (F r) (F s) := rawFaces_disjoint B
  have hEF : ∀ j, E j ⊆ ⋃ r, F r := by
    intro j x hx
    have hb : x ∈ C.model.boundary C.Carrier := by
      rw [hA]
      exact mem_iUnion.mpr ⟨j, hx⟩
    rw [hB] at hb
    exact hb
  have hFE : ∀ r, F r ⊆ ⋃ j, E j := by
    intro r x hx
    have hb : x ∈ C.model.boundary C.Carrier := by
      rw [hB]
      exact mem_iUnion.mpr ⟨r, hx⟩
    rw [hA] at hb
    exact hb
  choose rj hrj using fun j => Set.mem_iUnion.mp (hEF j ⟨(1, 1), rfl⟩)
  have hsub1 : ∀ j, E j ⊆ F (rj j) := fun j =>
    subset_of_isPreconnected_of_subset_iUnion hFc hFd
      (isPreconnected_range (A.torusMap_smooth j).continuous) (hEF j)
      ⟨_, ⟨(1, 1), rfl⟩, hrj j⟩
  have hsub2 : ∀ j, F (rj j) ⊆ E j := fun j =>
    subset_of_isPreconnected_of_subset_iUnion hEc hEd
      (isPreconnected_range (B.torusMap_smooth (rj j)).continuous) (hFE _)
      ⟨_, hrj j, ⟨(1, 1), rfl⟩⟩
  have hinj : Injective rj := by
    intro j k h
    by_contra hjk
    have he : E j ⊆ E k := (hsub1 j).trans (h ▸ hsub2 k)
    exact (hEd hjk).le_bot ⟨⟨(1, 1), rfl⟩, he ⟨(1, 1), rfl⟩⟩
  have hsurj : Surjective rj := by
    intro r
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hFE r ⟨(1, 1), rfl⟩)
    have hj' := hsub1 j hj
    by_contra hn
    have hne : rj j ≠ r := fun h => hn ⟨j, h⟩
    exact (hFd hne).le_bot ⟨hj', ⟨(1, 1), rfl⟩⟩
  let e := Equiv.ofBijective rj ⟨hinj, hsurj⟩
  have hsrcA (j : Fin n) (t : Torus) : (t, halfZero) ∈ (A.collar j).source :=
    (A.source_eq j).symm ▸ zero_mem_halfCollarSource t
  have hsrcB (r : Fin m) (t : Torus) : (t, halfZero) ∈ (B.collar r).source :=
    (B.source_eq r).symm ▸ zero_mem_halfCollarSource t
  have K1 (j : Fin n) (t : Torus) :
      ∃ s, A.collar j (t, halfZero) = B.collar (rj j) (s, halfZero) := by
    obtain ⟨s, hs⟩ := hsub1 j ⟨t, rfl⟩
    exact ⟨s, hs.symm⟩
  have K2 (j : Fin n) (s : Torus) :
      ∃ t, B.collar (rj j) (s, halfZero) = A.collar j (t, halfZero) := by
    obtain ⟨t, ht⟩ := hsub2 j ⟨s, rfl⟩
    exact ⟨t, ht.symm⟩
  have hψ : ∀ j, ∃ ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus,
      ∀ t, B.collar (rj j) (ψ t, halfZero) = A.collar j (t, halfZero) := by
    intro j
    let a := A.collar j
    let b := B.collar (rj j)
    let f : Torus → Torus := fun t => (b.symm (a (t, halfZero))).1
    let g : Torus → Torus := fun s => (a.symm (b (s, halfZero))).1
    have hf (t : Torus) : b (f t, halfZero) = a (t, halfZero) := by
      obtain ⟨s, hs⟩ := K1 j t
      change b ((b.symm (a (t, halfZero))).1, halfZero) = a (t, halfZero)
      rw [hs, b.symm_apply_apply (hsrcB _ s)]
    have hg (s : Torus) : a (g s, halfZero) = b (s, halfZero) := by
      obtain ⟨t, ht⟩ := K2 j s
      change a ((a.symm (b (s, halfZero))).1, halfZero) = b (s, halfZero)
      rw [ht, a.symm_apply_apply (hsrcA _ t)]
    have hleft (t : Torus) : g (f t) = t := by
      change (a.symm (b (f t, halfZero))).1 = t
      rw [hf, a.symm_apply_apply (hsrcA _ t)]
    have hright (s : Torus) : f (g s) = s := by
      change (b.symm (a (g s, halfZero))).1 = s
      rw [hg, b.symm_apply_apply (hsrcB _ s)]
    have hfs : ContMDiff torusModel torusModel ∞ f :=
      contMDiff_fst.comp (b.symm.contMDiffOn.comp_contMDiff
        (A.torusMap_smooth j) fun t => hf t ▸ b.map_source' (hsrcB _ (f t)))
    have hgs : ContMDiff torusModel torusModel ∞ g :=
      contMDiff_fst.comp (a.symm.contMDiffOn.comp_contMDiff
        (B.torusMap_smooth (rj j)) fun s => hg s ▸ a.map_source' (hsrcA _ (g s)))
    exact ⟨⟨⟨f, g, hleft, hright⟩, hfs, hgs⟩, hf⟩
  choose ψ hψ using hψ
  exact ⟨e, ψ, hψ⟩

private def rawFacesReindex {C : CompactCarrier.{u}} {n m : ℕ}
    (B : BoundaryTori C m) (e : Fin n ≃ Fin m) : BoundaryTori C n where
  collar j := B.collar (e j)
  source_eq j := B.source_eq (e j)
  boundary_zero j := B.boundary_zero (e j)
  disjoint := by
    intro j k hjk
    exact B.disjoint (e.injective.ne hjk)

def rawFacesExternalReparam {C : CompactCarrier.{u}} (R : RawGraphPresentation C)
    (ψ : Fin R.externalCount → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)) :
    RawGraphPresentation C :=
  (R.toTorusPresentation.reparam (fun s => match s with
    | .inl _j => Diffeomorph.refl _ _ _
    | .inr (.inl _j) => Diffeomorph.refl _ _ _
    | .inr (.inr j) => (ψ j).symm)).withFibration R.fibration

def rawFacesShrink {C : CompactCarrier.{u}} (R : RawGraphPresentation C)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : RawGraphPresentation C :=
  (R.toTorusPresentation.shrink hδ hδ1).withFibration R.fibration

def rawFacesLocal {C : CompactCarrier.{u}} (R : RawGraphPresentation C)
    (ψ : Fin R.externalCount → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (Φ : C.Carrier ≃ₘ⟮C.model, C.model⟯ C.Carrier)
    (hΦ : Φ.preservesOrientation C.orientation C.orientation)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : RawGraphPresentation C :=
  rawFacesShrink ((rawFacesExternalReparam R ψ).transport Φ hΦ) hδ hδ1

def rawFacesShrinkOwnedSide {W : CompactCarrier.{u}} (T : TorusPresentation W)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (i : Fin T.components.count) :
    T.OwnedSide i ≃ (T.shrink hδ hδ1).OwnedSide i :=
  Equiv.subtypeEquivRight fun s => by
    rw [T.shrink_sidePiece hδ hδ1]
    exact Iff.rfl

private theorem rawFacesLocal_collar {C : CompactCarrier.{u}} (R : RawGraphPresentation C)
    (ψ : Fin R.externalCount → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (Φ : C.Carrier ≃ₘ⟮C.model, C.model⟯ C.Carrier)
    (hΦ : Φ.preservesOrientation C.orientation C.orientation)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (j : Fin R.externalCount) (p : Torus × EuclideanHalfSpace 1) :
    (rawFacesLocal R ψ Φ hΦ hδ hδ1).external.collar j p =
      Φ (R.external.collar j ((ψ j).symm p.1, halfSpaceScale hδ p.2)) := rfl

private theorem rawFacesLocal_seam {C : CompactCarrier.{u}} (R : RawGraphPresentation C)
    (ψ : Fin R.externalCount → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (Φ : C.Carrier ≃ₘ⟮C.model, C.model⟯ C.Carrier)
    (hΦ : Φ.preservesOrientation C.orientation C.orientation)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (j : Fin R.pairing.count) (p : Torus × ℝ) :
    (rawFacesLocal R ψ Φ hΦ hδ hδ1).seam j p = Φ (R.seam j (p.1, δ * p.2)) := rfl

private theorem rawFacesLocal_matching {C : CompactCarrier.{u}} (R : RawGraphPresentation C)
    (ψ : Fin R.externalCount → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (Φ : C.Carrier ≃ₘ⟮C.model, C.model⟯ C.Carrier)
    (hΦ : Φ.preservesOrientation C.orientation C.orientation)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (j : Fin R.pairing.count) :
    (rawFacesLocal R ψ Φ hΦ hδ hδ1).pairing.matching j = R.pairing.matching j := by
  apply Diffeomorph.ext
  intro t
  rfl

private theorem exists_rawFacesLocalData {W : CompactCarrier.{u}}
    (T : TorusPresentation W) (i : Fin T.components.count)
    (R : RawGraphPresentation (T.Component i)) :
    ∃ port : Fin R.externalCount ≃ T.OwnedSide i,
      ∃ ψ : Fin R.externalCount → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus),
        ∃ ε > (0 : ℝ), ∃ Φ : (T.Component i).Carrier
            ≃ₘ⟮(T.Component i).model, (T.Component i).model⟯ (T.Component i).Carrier,
          Φ.preservesOrientation (T.Component i).orientation (T.Component i).orientation ∧
          (∀ j t, T.pieceCollar i (port j) (ψ j t, halfZero) =
            R.external.collar j (t, halfZero)) ∧
          (∀ j p, p ∈ halfCollarSource → p.2.val 0 < ε →
            Φ (R.external.collar j p) = T.pieceCollar i (port j) (ψ j p.1, p.2)) := by
  let B := T.pieceBoundaryTori i
  have hB : (T.Component i).model.boundary (T.Component i).Carrier = B.image :=
    T.pieceBoundaryTori_image i
  obtain ⟨e, ψ, hzero⟩ := exists_boundaryTori_faces R.external B R.external_exhausted hB
  let port := e.trans (Fintype.equivFin (T.OwnedSide i)).symm
  have hcollar (j : Fin R.externalCount) (p : Torus × EuclideanHalfSpace 1) :
      B.collar (e j) p = T.pieceCollar i (port j) p := by
    rfl
  obtain ⟨ε, hε, Φ, hΦ, hagree, hfix⟩ := exists_boundaryTori_straightening
    R.external (rawFacesReindex B e) ψ (fun j t => (hzero j t).symm)
  refine ⟨port, ψ, ε, hε, Φ, hΦ, ?_, ?_⟩
  · intro j t
    exact (hcollar j _).symm.trans (hzero j t)
  · intro j p hp hlt
    exact (hagree j p hp hlt).trans (hcollar j _)

private theorem rawFacesShrink_pieceCollar {W : CompactCarrier.{u}} (T : TorusPresentation W)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (i : Fin T.components.count) (s : T.OwnedSide i)
    (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
    (T.shrink hδ hδ1).pieceCollar i (rawFacesShrinkOwnedSide T hδ hδ1 i s) p =
      T.pieceCollar i s (p.1, halfSpaceScale hδ p.2) := by
  apply Subtype.ext
  have h1 := (T.shrink hδ hδ1).pieceCollar_apply i
    (rawFacesShrinkOwnedSide T hδ hδ1 i s) hp
  have h2 := T.pieceCollar_apply i s (p := (p.1, halfSpaceScale hδ p.2))
    (halfSpaceScale_mem hδ hδ1 hp)
  have h3 : (T.shrink hδ hδ1).sideCollar s.val p =
      T.sideCollar s.val (p.1, halfSpaceScale hδ p.2) := by
    rw [T.shrink_sideCollar hδ hδ1]
    rfl
  exact h1.trans (h3.trans h2.symm)

private theorem rawFacesAssemblyLedger {W : CompactCarrier.{u}} (T : TorusPresentation W)
    (R : ∀ i, RawGraphPresentation (T.Component i))
    (port : ∀ i, Fin (R i).externalCount ≃ T.OwnedSide i)
    (ψ : ∀ i, Fin (R i).externalCount → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (Φ : ∀ i, (T.Component i).Carrier
      ≃ₘ⟮(T.Component i).model, (T.Component i).model⟯ (T.Component i).Carrier)
    (hΦ : ∀ i, (Φ i).preservesOrientation (T.Component i).orientation (T.Component i).orientation)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hfull : ∀ i j p, p ∈ halfCollarSource →
      (rawFacesLocal (R i) (ψ i) (Φ i) (hΦ i) hδ hδ1).external.collar j p =
        (T.shrink hδ hδ1).pieceCollar i
          (rawFacesShrinkOwnedSide T hδ hδ1 i (port i j)) p) :
    ∃ G : RawGraphPresentation W, ∃ hc : G.externalCount = T.externalCount,
      ∃ e : (Fin T.pairing.count ⊕ Σ i, Fin (R i).pairing.count) ≃ Fin G.pairing.count,
        (∀ j p, p ∈ halfCollarSource →
          G.external.collar (Fin.cast hc.symm j) p =
            T.external.collar j (p.1, halfSpaceScale hδ p.2)) ∧
        (∀ j p, p ∈ signedCollarSource →
          G.seam (e (.inl j)) p = T.seam j (p.1, δ * p.2)) ∧
        (∀ i j p, p ∈ signedCollarSource → G.seam (e (.inr ⟨i, j⟩)) p =
          T.pieceToCarrier i (Φ i ((R i).seam j (p.1, δ * p.2)))) ∧
        (∀ j, G.pairing.matching (e (.inl j)) = T.pairing.matching j) ∧
        (∀ i j, G.pairing.matching (e (.inr ⟨i, j⟩)) = (R i).pairing.matching j) := by
  let T₁ := T.shrink hδ hδ1
  let R₁ : ∀ i, RawGraphPresentation (T₁.Component i) :=
    fun i => rawFacesLocal (R i) (ψ i) (Φ i) (hΦ i) hδ hδ1
  let port₁ : ∀ i, Fin (R₁ i).externalCount ≃ T₁.OwnedSide i :=
    fun i => (port i).trans (rawFacesShrinkOwnedSide T hδ hδ1 i)
  have hcompat : ∀ i j p, p ∈ halfCollarSource →
      ((R₁ i).external.collar j p).val = T₁.pieceCollar i (port₁ i j) p := by
    intro i j p hp
    exact congrArg Subtype.val (hfull i j p hp)
  obtain ⟨G, hc, e, hexternal, hold, hnew, hmatch, hmatchnew⟩ :=
    exists_rawPiecewisePresentation T₁ R₁ port₁ hcompat
  refine ⟨G, hc, e, hexternal, hold, ?_, hmatch, ?_⟩
  · intro i j p hp
    exact (hnew i j p hp).trans (congrArg (T.pieceToCarrier i)
      (rawFacesLocal_seam (R i) (ψ i) (Φ i) (hΦ i) hδ hδ1 j p))
  · intro i j
    exact (hmatchnew i j).trans (rawFacesLocal_matching (R i) (ψ i) (Φ i) (hΦ i) hδ hδ1 j)

theorem exists_rawFacesAssembly {W : CompactCarrier.{u}} (T : TorusPresentation W)
    (R : ∀ i, RawGraphPresentation (T.Component i)) :
    ∃ port : ∀ i, Fin (R i).externalCount ≃ T.OwnedSide i,
      ∃ ψ : ∀ i, Fin (R i).externalCount → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus),
        ∃ Φ : ∀ i, (T.Component i).Carrier
            ≃ₘ⟮(T.Component i).model, (T.Component i).model⟯ (T.Component i).Carrier,
          ∃ hΦ : ∀ i, (Φ i).preservesOrientation
              (T.Component i).orientation (T.Component i).orientation,
            ∃ δ : ℝ, ∃ hδ : 0 < δ, ∃ hδ1 : δ ≤ 1,
              (∀ i j t, T.pieceCollar i (port i j) (ψ i j t, halfZero) =
                (R i).external.collar j (t, halfZero)) ∧
              (∀ i j p, p ∈ halfCollarSource → p.2.val 0 < δ →
                Φ i ((R i).external.collar j p) =
                  T.pieceCollar i (port i j) (ψ i j p.1, p.2)) ∧
              (∀ i j p, p ∈ halfCollarSource →
                (rawFacesLocal (R i) (ψ i) (Φ i) (hΦ i) hδ hδ1).external.collar j p =
                  (T.shrink hδ hδ1).pieceCollar i
                    (rawFacesShrinkOwnedSide T hδ hδ1 i (port i j)) p) ∧
              ∃ G : RawGraphPresentation W, ∃ hc : G.externalCount = T.externalCount,
                ∃ e : (Fin T.pairing.count ⊕ Σ i, Fin (R i).pairing.count) ≃ Fin G.pairing.count,
                  (∀ j p, p ∈ halfCollarSource →
                    G.external.collar (Fin.cast hc.symm j) p =
                      T.external.collar j (p.1, halfSpaceScale hδ p.2)) ∧
                  (∀ j p, p ∈ signedCollarSource →
                    G.seam (e (.inl j)) p = T.seam j (p.1, δ * p.2)) ∧
                  (∀ i j p, p ∈ signedCollarSource →
                    G.seam (e (.inr ⟨i, j⟩)) p =
                      T.pieceToCarrier i (Φ i ((R i).seam j (p.1, δ * p.2)))) ∧
                  (∀ j, G.pairing.matching (e (.inl j)) = T.pairing.matching j) ∧
                  (∀ i j, G.pairing.matching (e (.inr ⟨i, j⟩)) = (R i).pairing.matching j) := by
  choose port ψ ε hε Φ hΦ hzero hagree using fun i => exists_rawFacesLocalData T i (R i)
  obtain ⟨m, hm, hmle⟩ := Wiring.exists_pos_le_of_finite ε hε
  let δ := min m 1
  have hδ : 0 < δ := lt_min hm one_pos
  have hδ1 : δ ≤ 1 := min_le_right m 1
  have hδle : ∀ i, δ ≤ ε i := fun i => (min_le_left m 1).trans (hmle i)
  let T₁ := T.shrink hδ hδ1
  let R₁ : ∀ i, RawGraphPresentation (T₁.Component i) :=
    fun i => rawFacesLocal (R i) (ψ i) (Φ i) (hΦ i) hδ hδ1
  let port₁ : ∀ i, Fin (R₁ i).externalCount ≃ T₁.OwnedSide i :=
    fun i => (port i).trans (rawFacesShrinkOwnedSide T hδ hδ1 i)
  have hfull : ∀ i j p, p ∈ halfCollarSource →
      (R₁ i).external.collar j p = T₁.pieceCollar i (port₁ i j) p := by
    intro i j p hp
    have hq : ((ψ i j).symm p.1, halfSpaceScale hδ p.2) ∈ halfCollarSource :=
      halfSpaceScale_mem hδ hδ1 hp
    have h := hagree i j ((ψ i j).symm p.1, halfSpaceScale hδ p.2) hq
      ((halfSpaceScale_lt hδ hp).trans_le (hδle i))
    have he : (ψ i j ((ψ i j).symm p.1), halfSpaceScale hδ p.2) =
        (p.1, halfSpaceScale hδ p.2) :=
      Prod.ext ((ψ i j).apply_symm_apply p.1) rfl
    have h := h.trans (congrArg (T.pieceCollar i (port i j)) he)
    exact (rawFacesLocal_collar (R i) (ψ i) (Φ i) (hΦ i) hδ hδ1 j p).trans
      (h.trans (rawFacesShrink_pieceCollar T hδ hδ1 i (port i j) p hp).symm)
  refine ⟨port, ψ, Φ, hΦ, δ, hδ, hδ1, hzero, ?_, hfull,
    rawFacesAssemblyLedger T R port ψ Φ hΦ hδ hδ1 hfull⟩
  intro i j p hp hlt
  exact hagree i j p hp (hlt.trans_le (hδle i))

theorem exists_rawGraphPresentation_of_rawPieces {W : CompactCarrier.{u}}
    (T : TorusPresentation W) (R : ∀ i, RawGraphPresentation (T.Component i)) :
    Nonempty (RawGraphPresentation W) := by
  obtain ⟨port, ψ, Φ, hΦ, δ, hδ, hδ1, hzero, hgerm, hfull, G, hc, e, hledger⟩ :=
    exists_rawFacesAssembly T R
  exact ⟨G⟩

end GC.GraphManifold
