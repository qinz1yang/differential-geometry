import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveTerminal

/-!
# Exhaustion and slope arithmetic for an actual genus-one presentation

Two incident solid pieces exhaust a connected closed presentation. The lens parameter compares
with the meridian, while the filling distance compares with the fibre.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

namespace TorusPresentation

variable {Q : ConnectedClosedOrientedManifold.{u} 3}
  (T : TorusPresentation (NoCuts.carrier Q)) (j : Fin T.pairing.count)
  (PL : SolidTorusPiece T (T.leftPiece j)) (PR : SolidTorusPiece T (T.rightPiece j))

include PL PR

theorem mem_seamPair_of_solidSides (i : Fin T.components.count) : i ∈ T.seamPair j := by
  classical
  have hsideL := PL.subsingleton_ownedSide
  have hsideR := PR.subsingleton_ownedSide
  have hL : T.leftPiece j ∈ T.seamPair j := by simp [seamPair]
  have hR : T.rightPiece j ∈ T.seamPair j := by simp [seamPair]
  refine T.mem_of_not_isCrossing (T.seamPair j) ⟨T.leftPiece j, hL⟩ (fun k hk => ?_) i
  rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [seamPair, Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with he | he
    · have hs := congrArg Subtype.val (hsideL.elim
        (⟨.inl k, he⟩ : T.OwnedSide (T.leftPiece j)) ⟨.inl j, rfl⟩)
      obtain rfl : k = j := Sum.inl_injective hs
      exact h2 hR
    · have hs := congrArg Subtype.val (hsideR.elim
        (⟨.inl k, he⟩ : T.OwnedSide (T.rightPiece j)) ⟨.inr (.inl j), rfl⟩)
      exact Sum.inl_ne_inr hs
  · simp only [seamPair, Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with he | he
    · have hs := congrArg Subtype.val (hsideL.elim
        (⟨.inr (.inl k), he⟩ : T.OwnedSide (T.leftPiece j)) ⟨.inl j, rfl⟩)
      exact Sum.inr_ne_inl hs
    · have hs := congrArg Subtype.val (hsideR.elim
        (⟨.inr (.inl k), he⟩ : T.OwnedSide (T.rightPiece j)) ⟨.inr (.inl j), rfl⟩)
      obtain rfl : k = j := Sum.inl_injective (Sum.inr_injective hs)
      exact h2 hL

theorem components_count_of_solidSides : T.components.count = 2 := by
  classical
  have hAll : T.seamPair j = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr (T.mem_seamPair_of_solidSides j PL PR)
  have hc := congrArg Finset.card hAll
  simpa only [seamPair, Finset.card_pair (T.leftPiece_ne_rightPiece j PL),
    Finset.card_univ, Fintype.card_fin] using hc.symm

theorem all_seams_eq_of_solidSides (k : Fin T.pairing.count) : k = j := by
  have hsideL := PL.subsingleton_ownedSide
  have hsideR := PR.subsingleton_ownedSide
  have hk := T.mem_seamPair_of_solidSides j PL PR (T.leftPiece k)
  simp only [seamPair, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with he | he
  · exact Sum.inl_injective (congrArg Subtype.val (hsideL.elim
      (⟨.inl k, he⟩ : T.OwnedSide (T.leftPiece j)) ⟨.inl j, rfl⟩))
  · exact (Sum.inl_ne_inr (congrArg Subtype.val (hsideR.elim
      (⟨.inl k, he⟩ : T.OwnedSide (T.rightPiece j)) ⟨.inr (.inl j), rfl⟩))).elim

theorem pairing_count_of_solidSides : T.pairing.count = 1 := by
  let : Subsingleton (Fin T.pairing.count) := ⟨fun k k' =>
    (T.all_seams_eq_of_solidSides j PL PR k).trans
      (T.all_seams_eq_of_solidSides j PL PR k').symm⟩
  have hc := (Fintype.card_le_one_iff_subsingleton (α := Fin T.pairing.count)).mpr
    inferInstance
  rw [Fintype.card_fin] at hc
  have hp := j.pos
  omega

end TorusPresentation

namespace ElementaryPresentation

variable {Q : ConnectedClosedOrientedManifold.{u} 3}
  (E : ElementaryPresentation (NoCuts.carrier Q)) {j : Fin E.toTorus.pairing.count}
  (hL : E.kind (E.toTorus.leftPiece j) = 1) (hR : E.kind (E.toTorus.rightPiece j) = 1)

include hL hR in
theorem kind_eq_one_of_solidSides (i : Fin E.toTorus.components.count) : E.kind i = 1 := by
  have hi := E.toTorus.mem_seamPair_of_solidSides j (E.pieceOfKind hL) (E.pieceOfKind hR) i
  simp only [TorusPresentation.seamPair, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact hL
  · exact hR

def solidPieces_of_solidSides (i : Fin E.toTorus.components.count) : SolidTorusPiece E.toTorus i :=
  E.pieceOfKind (E.kind_eq_one_of_solidSides hL hR i)

include hL hR in
theorem genusOne_counts_of_solidSides : E.toTorus.components.count = 2 ∧ E.complexity = 1 :=
  ⟨E.toTorus.components_count_of_solidSides j (E.pieceOfKind hL) (E.pieceOfKind hR),
    E.toTorus.pairing_count_of_solidSides j (E.pieceOfKind hL) (E.pieceOfKind hR)⟩

end ElementaryPresentation

theorem delta_smul_meridian_fiber (A : GL (Fin 2) ℤ) :
    PrimitiveSlope.delta (A • meridianSlope) fiberSlope =
      ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 0).natAbs := by
  simp [meridianSlope, fiberSlope, PrimitiveSlope.smul_mk, PrimitiveSlope.delta_mk,
    smulVec, slopeDet]

theorem delta_smul_fiber_meridian (A : GL (Fin 2) ℤ) :
    PrimitiveSlope.delta (A • fiberSlope) meridianSlope =
      ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 1).natAbs := by
  simp [meridianSlope, fiberSlope, PrimitiveSlope.smul_mk, PrimitiveSlope.delta_mk,
    smulVec, slopeDet]

theorem delta_smul_meridian_meridian (A : GL (Fin 2) ℤ) :
    PrimitiveSlope.delta (A • meridianSlope) meridianSlope =
      ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0).natAbs := by
  simp [meridianSlope, PrimitiveSlope.smul_mk, PrimitiveSlope.delta_mk, smulVec, slopeDet]

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
  (j : Fin E.toTorus.pairing.count)

theorem fillingDistance_true_eq_matrix : E.fillingDistance j true =
    (torusMatrix (E.toTorus.pairing.matching j) 0 0).natAbs :=
  delta_smul_meridian_fiber _

theorem fillingDistance_false_eq_matrix : E.fillingDistance j false =
    (torusMatrix (E.toTorus.pairing.matching j) 1 1).natAbs :=
  delta_smul_fiber_meridian _

theorem lensDistance_eq_matrix :
    PrimitiveSlope.delta (torusUnit (E.toTorus.pairing.matching j) • meridianSlope)
      meridianSlope = (torusMatrix (E.toTorus.pairing.matching j) 1 0).natAbs :=
  delta_smul_meridian_meridian _

theorem lensDistance_eq_one_of_zero_fillingDistance (h0 : E.fillingDistance j true = 0) :
    PrimitiveSlope.delta (torusUnit (E.toTorus.pairing.matching j) • meridianSlope)
      meridianSlope = 1 := by
  change PrimitiveSlope.delta (torusUnit (E.toTorus.pairing.matching j) • meridianSlope)
    fiberSlope = 0 at h0
  have he := (PrimitiveSlope.delta_eq_zero_iff _ _).mp h0
  rw [he]
  decide

end ElementaryPresentation

end GC.Seifert
