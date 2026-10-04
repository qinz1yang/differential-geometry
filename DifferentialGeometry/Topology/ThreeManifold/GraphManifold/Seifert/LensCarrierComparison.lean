import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensCarrierModels
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensCarrierCut
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingEquivalenceGluing
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingEquivalencePieces

/-!
# Comparison of full two-solid quotient carriers

Standard target piece germs and an extendable linear meridian correction determine a genuine
full cut-carrier diffeomorphism. It descends through the actual one-seam quotient.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u v

namespace GC.Seifert

def comparisonLeftSide {V : CompactCarrier.{v}} (D : TorusPresentation V)
    (k : Fin D.pairing.count) : D.OwnedSide (D.leftPiece k) := ⟨.inl k, rfl⟩

def comparisonRightSide {V : CompactCarrier.{v}} (D : TorusPresentation V)
    (k : Fin D.pairing.count) : D.OwnedSide (D.rightPiece k) := ⟨.inr (.inl k), rfl⟩

theorem exists_twoSolidComparison_of_linearCorrection
    {Q : ConnectedClosedOrientedManifold.{u} 3} {V : CompactCarrier.{v}}
    (T : TorusPresentation (NoCuts.carrier Q)) (D : TorusPresentation V)
    (hc : T.components.count = 2) (hcD : D.components.count = 2)
    (hcS : D.pairing.count = 1) (P : ∀ i, SolidTorusPiece T i)
    (j : Fin T.pairing.count) (k : Fin D.pairing.count)
    (hne : D.leftPiece k ≠ D.rightPiece k)
    (hL : ∃ δ > (0 : ℝ), ∃ Θ : (UnitDisc.{0} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      D.cutCarrier.model⟯ D.components.piece (D.leftPiece k),
      ∀ p ∈ halfCollarSource, p.2.val 0 < δ →
        D.pieceCollar (D.leftPiece k) (comparisonLeftSide D k) p =
          Θ (cliffordDiscCollarMap (p.1.1, p.2), p.1.2))
    (hR : ∃ δ > (0 : ℝ), ∃ Θ : (UnitDisc.{0} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      D.cutCarrier.model⟯ D.components.piece (D.rightPiece k),
      ∀ p ∈ halfCollarSource, p.2.val 0 < δ →
        D.pieceCollar (D.rightPiece k) (comparisonRightSide D k) p =
          Θ (cliffordDiscCollarMap (p.1.1, p.2), p.1.2))
    (M U : GL (Fin 2) ℤ) (hm : T.pairing.matching j = linearTorusDiffeomorph M)
    (hU : U • meridianSlope = meridianSlope)
    (hMUD : D.pairing.matching k = linearTorusDiffeomorph (M * U)) :
    Nonempty (Q.Carrier ≃ₘ⟮𝓡 3, V.model⟯ V.Carrier) := by
  classical
  let l := D.leftPiece k
  let r := D.rightPiece k
  obtain ⟨δL, hδL, ΘL, hΘL⟩ := (P (T.leftPiece j)).exists_lensUnitDisc_germ.{u, 0}
  obtain ⟨δR, hδR, ΘR, hΘR⟩ := (P (T.rightPiece j)).exists_lensUnitDisc_germ.{u, 0}
  obtain ⟨δL', hδL', ΘL', hΘL'⟩ := hL
  obtain ⟨δR', hδR', ΘR', hΘR'⟩ := hR
  have hV : U⁻¹ • meridianSlope = meridianSlope := by
    calc
      U⁻¹ • meridianSlope = U⁻¹ • (U • meridianSlope) := congrArg (U⁻¹ • ·) hU.symm
      _ = meridianSlope := inv_smul_smul U meridianSlope
  obtain ⟨δF, hδF, F, hF⟩ := (P (T.leftPiece j)).exists_linear_comparison_germ
    (P (T.leftPiece j)) U⁻¹ hV
  let α := linearTorusDiffeomorph U⁻¹
  have hmatch (t : Torus) : T.pairing.matching j t =
      D.pairing.matching k (α t) := by
    rw [hm, hMUD]
    change linearTorusMap M t = linearTorusMap (M * U : GL (Fin 2) ℤ)
      (linearTorusMap (U⁻¹ : GL (Fin 2) ℤ) t)
    rw [← linearTorusMap_mul]
    have he : (M * U) * U⁻¹ = M := by rw [mul_assoc, mul_inv_cancel, mul_one]
    exact congrArg (fun N : GL (Fin 2) ℤ => linearTorusMap N t) he.symm
  let L := F.trans (ΘL.symm.trans ΘL')
  let R := ΘR.symm.trans ΘR'
  let H := twoComponentComparisonDiffeomorph T.cutCarrier T.components D.cutCarrier D.components
    hc hcD (T.leftPiece j) (T.rightPiece j) l r (T.leftPiece_ne_rightPiece j (P _)) hne L R
  have hHL (x : T.components.piece (T.leftPiece j)) : H x.val = (L x).val :=
    twoComponentComparisonDiffeomorph_left T.cutCarrier T.components D.cutCarrier D.components
      hc hcD (T.leftPiece j) (T.rightPiece j) l r (T.leftPiece_ne_rightPiece j (P _)) hne L R x
  have hHR (x : T.components.piece (T.rightPiece j)) : H x.val = (R x).val :=
    twoComponentComparisonDiffeomorph_right T.cutCarrier T.components D.cutCarrier D.components
      hc hcD (T.leftPiece j) (T.rightPiece j) l r (T.leftPiece_ne_rightPiece j (P _)) hne L R x
  let δ := min δL (min δR (min δL' (min δR' (min δF 1))))
  have hδ : 0 < δ := by
    exact lt_min hδL (lt_min hδR (lt_min hδL' (lt_min hδR' (lt_min hδF zero_lt_one))))
  have hδ1 : δ ≤ 1 := by
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  let : Subsingleton (Fin D.pairing.count) := by
    rw [hcS]
    infer_instance
  let e : Fin T.pairing.count ≃ Fin D.pairing.count :=
    Equiv.ofBijective (Function.const _ k) (by
      constructor
      · intro k k' h
        exact (T.all_seams_eq_of_solidSides j (P _) (P _) k).trans
          (T.all_seams_eq_of_solidSides j (P _) (P _) k').symm
      · intro k
        exact ⟨j, Subsingleton.elim _ _⟩)
  let A := Function.const (Fin T.pairing.count) α
  have hl : ∀ k t s (hs0 : 0 ≤ s), s < δ →
      H (T.pairing.leftCollar k (t, halfPoint s hs0)) =
        D.pairing.leftCollar (e k) (A k t, halfPoint s hs0) := by
    intro k t s hs0 hlt
    have hk := T.all_seams_eq_of_solidSides j (P _) (P _) k
    subst k
    have hlt' : s < δL ∧ s < δR ∧ s < δL' ∧ s < δR' ∧ s < δF ∧ s < 1 := by
      simpa only [δ, lt_min_iff] using hlt
    have hp : (t, halfPoint s hs0) ∈ halfCollarSource := hlt'.2.2.2.2.2
    have hport : (P (T.leftPiece j)).port 0 = ⟨.inl j, rfl⟩ :=
      (P (T.leftPiece j)).subsingleton_ownedSide.elim _ _
    have hval : (T.pieceCollar (T.leftPiece j) ((P (T.leftPiece j)).port 0)
        (t, halfPoint s hs0)).val = T.pairing.leftCollar j (t, halfPoint s hs0) := by
      rw [T.pieceCollar_apply _ _ hp, hport]
      rfl
    have hpα : (α t, halfPoint s hs0) ∈ halfCollarSource := hlt'.2.2.2.2.2
    rw [← hval, hHL]
    change (ΘL' (ΘL.symm (F (T.pieceCollar (T.leftPiece j)
      ((P (T.leftPiece j)).port 0) (t, halfPoint s hs0))))).val = _
    rw [hF _ hp hlt'.2.2.2.2.1, hΘL _ hpα hlt'.1, Diffeomorph.symm_apply_apply,
      ← hΘL' _ hpα hlt'.2.2.1]
    exact D.pieceCollar_apply l (comparisonLeftSide D k) hpα
  have hr : ∀ k t s (hs0 : 0 ≤ s), s < δ →
      H (T.pairing.rightCollar k (T.pairing.matching k t, halfPoint s hs0)) =
        D.pairing.rightCollar (e k) (D.pairing.matching (e k) (A k t), halfPoint s hs0) := by
    intro k t s hs0 hlt
    have hk := T.all_seams_eq_of_solidSides j (P _) (P _) k
    subst k
    have hlt' : s < δL ∧ s < δR ∧ s < δL' ∧ s < δR' ∧ s < δF ∧ s < 1 := by
      simpa only [δ, lt_min_iff] using hlt
    have hp : (T.pairing.matching j t, halfPoint s hs0) ∈ halfCollarSource := hlt'.2.2.2.2.2
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
    have hd := D.pieceCollar_apply r (comparisonRightSide D k) hp
    rw [hd]
    change D.pairing.rightCollar (e j) (T.pairing.matching j t, halfPoint s hs0) = _
    rw [hmatch]
    rfl
  exact ⟨T.fillingComparisonDiffeomorph_of_collarGerms D H e A δ hδ hδ1 hl hr⟩


end GC.Seifert
