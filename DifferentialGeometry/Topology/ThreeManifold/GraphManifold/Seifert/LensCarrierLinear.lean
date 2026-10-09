import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensCarrierModels
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensCarrierCut
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingEquivalenceGluing

/-!
# Actual linear genus-one carriers and lens spaces

The two genuine solid-piece maps are straightened near their boundary tori. The resulting full
cut-carrier comparison descends through the actual quotient to a lens-space diffeomorphism.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

section Lens

variable (p : ℕ) [NeZero p] (q : ℤ) (hpq : IsCoprime (p : ℤ) q)

abbrev lensCarrierTorusPresentation := (lensSpaceRawGraphPresentation p q hpq).toTorusPresentation

def lensCarrierLeftIndex : Fin (lensCarrierTorusPresentation p q hpq).components.count :=
  ⟨0, by change 0 < 2; decide⟩

def lensCarrierRightIndex : Fin (lensCarrierTorusPresentation p q hpq).components.count :=
  ⟨1, by change 1 < 2; decide⟩

def lensCarrierPieceTrivialization
    (i : Fin (lensCarrierTorusPresentation p q hpq).components.count) :
    (lensCarrierTorusPresentation p q hpq).components.piece i ≃ₘ⟮
      (lensCarrierTorusPresentation p q hpq).cutCarrier.model, (𝓡∂ 2).prod (𝓡 1)⟯
      UnitDisc.{0} × Circle := lensPieceTrivialization p q hpq i

def lensCarrierLeftPort : Fin 1 ≃
    (lensCarrierTorusPresentation p q hpq).OwnedSide (lensCarrierLeftIndex p q hpq) where
  toFun c := ⟨.inl ⟨c.val, c.isLt⟩, rfl⟩
  invFun := Function.const _ 0
  left_inv c := Subsingleton.elim 0 c
  right_inv s := by
    obtain ⟨k | k | k, hs⟩ := s
    · exact Subtype.ext (congrArg Sum.inl
        (Fin.ext (Nat.lt_one_iff.mp (k.isLt : k.val < 1)).symm))
    · exact absurd (congrArg Fin.val hs : (1 : ℕ) = 0) one_ne_zero
    · exact k.elim0

def lensCarrierRightPort : Fin 1 ≃
    (lensCarrierTorusPresentation p q hpq).OwnedSide (lensCarrierRightIndex p q hpq) where
  toFun c := ⟨.inr (.inl ⟨c.val, c.isLt⟩), rfl⟩
  invFun := Function.const _ 0
  left_inv c := Subsingleton.elim 0 c
  right_inv s := by
    obtain ⟨k | k | k, hs⟩ := s
    · exact absurd (congrArg Fin.val hs : (0 : ℕ) = 1) zero_ne_one
    · exact Subtype.ext (congrArg (Sum.inr ∘ Sum.inl)
        (Fin.ext (Nat.lt_one_iff.mp (k.isLt : k.val < 1)).symm))
    · exact k.elim0

theorem lensCarrierPieceTrivialization_symm_left_val (x : UnitDisc.{0} × Circle) :
    ((lensCarrierPieceTrivialization p q hpq (lensCarrierLeftIndex p q hpq)).symm x).val =
      Sum.inl ((lensLeftCover p q hpq).pieceDiffeo.symm x) := rfl

theorem lensCarrierPieceTrivialization_symm_right_val (x : UnitDisc.{0} × Circle) :
    ((lensCarrierPieceTrivialization p q hpq (lensCarrierRightIndex p q hpq)).symm x).val =
      Sum.inr ((lensRightCover p q hpq).pieceDiffeo.symm x) := rfl

theorem lensCarrierLeft_boundary (t : Torus) :
    (lensCarrierTorusPresentation p q hpq).pieceCollar (lensCarrierLeftIndex p q hpq)
      (lensCarrierLeftPort p q hpq 0) (t, halfZero) =
      (lensCarrierPieceTrivialization p q hpq (lensCarrierLeftIndex p q hpq)).symm
        (cliffordDiscCollarMap (t.1, halfZero), t.2) := by
  apply Subtype.ext
  rw [TorusPresentation.pieceCollar_apply _ _ _ (zero_mem_halfCollarSource t),
    lensCarrierPieceTrivialization_symm_left_val]
  change Sum.inl ((lensLeftCover p q hpq).torusPoint t) =
    Sum.inl ((lensLeftCover p q hpq).pieceDiffeo.symm _)
  apply congrArg Sum.inl
  apply (lensLeftCover p q hpq).pieceDiffeo.injective
  refine Eq.trans ?_ ((lensLeftCover p q hpq).pieceDiffeo.apply_symm_apply
    (cliffordDiscCollarMap (t.1, halfZero), t.2)).symm
  obtain ⟨h1, h2⟩ := (lensLeftCover p q hpq).pieceDiffeo_torusPoint t
  apply Prod.ext
  · apply ULift.ext
    apply Subtype.ext
    exact h1.trans (cliffordDiscCollarMap_zero_val t.1).symm
  · exact h2

theorem lensCarrierRight_boundary (t : Torus) :
    (lensCarrierTorusPresentation p q hpq).pieceCollar (lensCarrierRightIndex p q hpq)
      (lensCarrierRightPort p q hpq 0) (t, halfZero) =
      (lensCarrierPieceTrivialization p q hpq (lensCarrierRightIndex p q hpq)).symm
        (cliffordDiscCollarMap (t.1, halfZero), t.2) := by
  apply Subtype.ext
  rw [TorusPresentation.pieceCollar_apply _ _ _ (zero_mem_halfCollarSource t),
    lensCarrierPieceTrivialization_symm_right_val]
  change Sum.inr ((lensRightCover p q hpq).torusPoint t) =
    Sum.inr ((lensRightCover p q hpq).pieceDiffeo.symm _)
  apply congrArg Sum.inr
  apply (lensRightCover p q hpq).pieceDiffeo.injective
  refine Eq.trans ?_ ((lensRightCover p q hpq).pieceDiffeo.apply_symm_apply
    (cliffordDiscCollarMap (t.1, halfZero), t.2)).symm
  obtain ⟨h1, h2⟩ := (lensRightCover p q hpq).pieceDiffeo_torusPoint t
  apply Prod.ext
  · apply ULift.ext
    apply Subtype.ext
    exact h1.trans (cliffordDiscCollarMap_zero_val t.1).symm
  · exact h2

theorem exists_lensCarrierLeft_germ :
    ∃ δ > (0 : ℝ), ∃ Θ : (UnitDisc.{0} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      (lensCarrierTorusPresentation p q hpq).cutCarrier.model⟯
        (lensCarrierTorusPresentation p q hpq).components.piece (lensCarrierLeftIndex p q hpq),
      ∀ r, r ∈ halfCollarSource → r.2.val 0 < δ →
        (lensCarrierTorusPresentation p q hpq).pieceCollar (lensCarrierLeftIndex p q hpq)
          (lensCarrierLeftPort p q hpq 0) r = Θ (cliffordDiscCollarMap (r.1.1, r.2), r.1.2) := by
  let T := lensCarrierTorusPresentation p q hpq
  have h0 : ∀ c (t : Torus),
      T.pieceCollar (lensCarrierLeftIndex p q hpq) (lensCarrierLeftPort p q hpq c) (t, halfZero) =
      (lensCarrierPieceTrivialization p q hpq (lensCarrierLeftIndex p q hpq)).symm
        (unitDiscPlanarBase.collar c (t.1, halfZero), t.2) := by
    intro c t
    obtain rfl : c = 0 := Subsingleton.elim _ _
    exact lensCarrierLeft_boundary p q hpq t
  obtain ⟨δ, hδ, Θ, hΘ⟩ := T.exists_germ_trivialization (lensCarrierLeftIndex p q hpq)
    unitDiscPlanarBase (lensCarrierLeftPort p q hpq)
    (Function.const (Fin 1) (Diffeomorph.refl torusModel Torus ∞))
    (lensCarrierPieceTrivialization p q hpq (lensCarrierLeftIndex p q hpq)).symm h0
  exact ⟨δ, hδ, Θ, fun r hr hlt => hΘ 0 r hr hlt⟩

theorem exists_lensCarrierRight_germ :
    ∃ δ > (0 : ℝ), ∃ Θ : (UnitDisc.{0} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      (lensCarrierTorusPresentation p q hpq).cutCarrier.model⟯
        (lensCarrierTorusPresentation p q hpq).components.piece (lensCarrierRightIndex p q hpq),
      ∀ r, r ∈ halfCollarSource → r.2.val 0 < δ →
        (lensCarrierTorusPresentation p q hpq).pieceCollar (lensCarrierRightIndex p q hpq)
          (lensCarrierRightPort p q hpq 0) r = Θ (cliffordDiscCollarMap (r.1.1, r.2), r.1.2) := by
  let T := lensCarrierTorusPresentation p q hpq
  have h0 : ∀ c (t : Torus),
      T.pieceCollar (lensCarrierRightIndex p q hpq) (lensCarrierRightPort p q hpq c) (t, halfZero) =
      (lensCarrierPieceTrivialization p q hpq (lensCarrierRightIndex p q hpq)).symm
        (unitDiscPlanarBase.collar c (t.1, halfZero), t.2) := by
    intro c t
    obtain rfl : c = 0 := Subsingleton.elim _ _
    exact lensCarrierRight_boundary p q hpq t
  obtain ⟨δ, hδ, Θ, hΘ⟩ := T.exists_germ_trivialization (lensCarrierRightIndex p q hpq)
    unitDiscPlanarBase (lensCarrierRightPort p q hpq)
    (Function.const (Fin 1) (Diffeomorph.refl torusModel Torus ∞))
    (lensCarrierPieceTrivialization p q hpq (lensCarrierRightIndex p q hpq)).symm h0
  exact ⟨δ, hδ, Θ, fun r hr hlt => hΘ 0 r hr hlt⟩

def lensCarrierSeamIndex : Fin (lensCarrierTorusPresentation p q hpq).pairing.count :=
  ⟨0, by change 0 < 1; decide⟩

theorem exists_diffeomorph_lens_of_linearTwoSolidTori
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T : TorusPresentation (NoCuts.carrier Q)) (hc : T.components.count = 2)
    (P : ∀ i, SolidTorusPiece T i) (j : Fin T.pairing.count)
    (hm : T.pairing.matching j = linearTorusDiffeomorph (lensMatrixUnit p q hpq)) :
    Nonempty (Q.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (lensSpaceFormGroup p q hpq).manifold.Carrier) := by
  classical
  let D := lensCarrierTorusPresentation p q hpq
  let l := lensCarrierLeftIndex p q hpq
  let r := lensCarrierRightIndex p q hpq
  have hne : l ≠ r := by
    intro h
    exact zero_ne_one (congrArg Fin.val h)
  obtain ⟨δL, hδL, ΘL, hΘL⟩ := (P (T.leftPiece j)).exists_lensUnitDisc_germ.{u, 0}
  obtain ⟨δR, hδR, ΘR, hΘR⟩ := (P (T.rightPiece j)).exists_lensUnitDisc_germ.{u, 0}
  obtain ⟨δL', hδL', ΘL', hΘL'⟩ := exists_lensCarrierLeft_germ p q hpq
  obtain ⟨δR', hδR', ΘR', hΘR'⟩ := exists_lensCarrierRight_germ p q hpq
  let L := ΘL.symm.trans ΘL'
  let R := ΘR.symm.trans ΘR'
  let H := twoComponentComparisonDiffeomorph T.cutCarrier T.components D.cutCarrier D.components
    hc rfl (T.leftPiece j) (T.rightPiece j) l r (T.leftPiece_ne_rightPiece j (P _)) hne L R
  have hHL (x : T.components.piece (T.leftPiece j)) : H x.val = (L x).val :=
    twoComponentComparisonDiffeomorph_left T.cutCarrier T.components D.cutCarrier D.components
      hc rfl (T.leftPiece j) (T.rightPiece j) l r (T.leftPiece_ne_rightPiece j (P _)) hne L R x
  have hHR (x : T.components.piece (T.rightPiece j)) : H x.val = (R x).val :=
    twoComponentComparisonDiffeomorph_right T.cutCarrier T.components D.cutCarrier D.components
      hc rfl (T.leftPiece j) (T.rightPiece j) l r (T.leftPiece_ne_rightPiece j (P _)) hne L R x
  let δ := min δL (min δR (min δL' (min δR' 1)))
  have hδ : 0 < δ := by
    exact lt_min hδL (lt_min hδR (lt_min hδL' (lt_min hδR' zero_lt_one)))
  have hδ1 : δ ≤ 1 := by
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _)))
  let : Subsingleton (Fin D.pairing.count) := by
    change Subsingleton (Fin 1)
    infer_instance
  let e : Fin T.pairing.count ≃ Fin D.pairing.count :=
    Equiv.ofBijective (Function.const _ (lensCarrierSeamIndex p q hpq)) (by
      constructor
      · intro k k' h
        exact (T.all_seams_eq_of_solidSides j (P _) (P _) k).trans
          (T.all_seams_eq_of_solidSides j (P _) (P _) k').symm
      · intro k
        exact ⟨j, Subsingleton.elim _ _⟩)
  let A := Function.const (Fin T.pairing.count) (Diffeomorph.refl torusModel Torus ∞)
  have hl : ∀ k t s (hs0 : 0 ≤ s), s < δ →
      H (T.pairing.leftCollar k (t, halfPoint s hs0)) =
        D.pairing.leftCollar (e k) (A k t, halfPoint s hs0) := by
    intro k t s hs0 hlt
    have hk := T.all_seams_eq_of_solidSides j (P _) (P _) k
    subst k
    have hlt' : s < δL ∧ s < δR ∧ s < δL' ∧ s < δR' ∧ s < 1 := by
      simpa only [δ, lt_min_iff] using hlt
    have hp : (t, halfPoint s hs0) ∈ halfCollarSource := hlt'.2.2.2.2
    have hport : (P (T.leftPiece j)).port 0 = ⟨.inl j, rfl⟩ :=
      (P (T.leftPiece j)).subsingleton_ownedSide.elim _ _
    have hval : (T.pieceCollar (T.leftPiece j) ((P (T.leftPiece j)).port 0)
        (t, halfPoint s hs0)).val = T.pairing.leftCollar j (t, halfPoint s hs0) := by
      rw [T.pieceCollar_apply _ _ hp, hport]
      rfl
    rw [← hval, hHL, hΘL _ hp hlt'.1]
    change (ΘL' (ΘL.symm (ΘL _))).val = _
    rw [Diffeomorph.symm_apply_apply, ← hΘL' _ hp hlt'.2.2.1]
    exact D.pieceCollar_apply l (lensCarrierLeftPort p q hpq 0) hp
  have hr : ∀ k t s (hs0 : 0 ≤ s), s < δ →
      H (T.pairing.rightCollar k (T.pairing.matching k t, halfPoint s hs0)) =
        D.pairing.rightCollar (e k) (D.pairing.matching (e k) (A k t), halfPoint s hs0) := by
    intro k t s hs0 hlt
    have hk := T.all_seams_eq_of_solidSides j (P _) (P _) k
    subst k
    have hlt' : s < δL ∧ s < δR ∧ s < δL' ∧ s < δR' ∧ s < 1 := by
      simpa only [δ, lt_min_iff] using hlt
    have hp : (T.pairing.matching j t, halfPoint s hs0) ∈ halfCollarSource := hlt'.2.2.2.2
    have hport : (P (T.rightPiece j)).port 0 = ⟨.inr (.inl j), rfl⟩ :=
      (P (T.rightPiece j)).subsingleton_ownedSide.elim _ _
    have hval : (T.pieceCollar (T.rightPiece j) ((P (T.rightPiece j)).port 0)
        (T.pairing.matching j t, halfPoint s hs0)).val =
        T.pairing.rightCollar j (T.pairing.matching j t, halfPoint s hs0) := by
      rw [T.pieceCollar_apply _ _ hp, hport]
      rfl
    rw [← hval, hHR, hΘR _ hp hlt'.2.1]
    change (ΘR' (ΘR.symm (ΘR _))).val = _
    rw [Diffeomorph.symm_apply_apply, ← hΘR' _ hp hlt'.2.2.2.1]
    have hd := D.pieceCollar_apply r (lensCarrierRightPort p q hpq 0) hp
    rw [hd]
    change D.pairing.rightCollar (e j) (T.pairing.matching j t, halfPoint s hs0) = _
    rw [hm]
    rfl
  exact ⟨T.fillingComparisonDiffeomorph_of_collarGerms D H e A δ hδ hδ1 hl hr⟩

end Lens

theorem exists_orientedDiffeomorph_lens_of_linearTwoSolidTori
    {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T : TorusPresentation (NoCuts.carrier Q)) (hc : T.components.count = 2)
    (P : ∀ i, SolidTorusPiece T i) (j : Fin T.pairing.count)
    (p : ℕ) [NeZero p] (q : ℤ) (hpq : IsCoprime (p : ℤ) q)
    (hm : T.pairing.matching j = linearTorusDiffeomorph (lensMatrixUnit p q hpq)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph Q.toClosedOrientedManifold
      (lensSpaceFormGroup p q hpq).manifold.toClosedOrientedManifold) ∨
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph Q.toClosedOrientedManifold
      (lensSpaceFormGroup p q hpq).manifold.opposite.toClosedOrientedManifold) := by
  obtain ⟨f⟩ := exists_diffeomorph_lens_of_linearTwoSolidTori p q hpq T hc P j hm
  rcases f.preservesOrientation_or_preservesOrientation_opposite Q.orientation
    (lensSpaceFormGroup p q hpq).manifold.orientation with h | h
  · exact Or.inl ⟨⟨f, h⟩⟩
  · exact Or.inr ⟨⟨f, h⟩⟩

end GC.Seifert
