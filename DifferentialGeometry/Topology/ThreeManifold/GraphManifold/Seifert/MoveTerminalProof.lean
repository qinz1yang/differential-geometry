import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveTerminalSelfSeam
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensCarrierSphereGeneral

/-!
# The terminal move with the self-seam case proved

`moveTerminal'` repeats the case split of `moveTerminal` (`Seifert/MoveTerminal.lean`) with the
self-seam branch closed by `seifertFactor_of_centre_selfSeam_proved` (Codex X20) instead of the
ledger lemma R2, and the two-solid-tori branch closed by
`seifertFactor_of_solidSeam_zero_of_lensCarrier` (Codex X22, R1's statement) instead of R1, so it
uses no ledger lemma.
-/

set_option autoImplicit false

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold

universe u

namespace GC.Seifert

theorem moveTerminal' : MoveTerminal.{u} := by
  intro Q E hE
  by_cases hNS : ∃ j, E.kind (E.toTorus.leftPiece j) = 1 ∧ E.kind (E.toTorus.rightPiece j) = 1
  · obtain ⟨j, hL, hR⟩ := hNS
    rcases Nat.eq_zero_or_pos (E.fillingDistance j true) with h0 | h1
    · rcases Nat.eq_zero_or_pos (E.fillingDistance j false) with h0' | h1'
      · exact E.seifertFactor_of_solidSeam_zero_of_lensCarrier hL hR h0 h0'
      · exact E.seifertFactor_of_solidSeam_flip hL hR h1'
    · exact E.seifertFactor_of_solidSeam hL hR h1
  · have hNS' : ∀ j, ¬(E.kind (E.toTorus.leftPiece j) = 1 ∧
        E.kind (E.toTorus.rightPiece j) = 1) := fun j h => hNS ⟨j, h⟩
    have hE' := E.isMoveFree_flip E.solidFlip hE
    have hR := E.kind_rightPiece_flip_ne hNS'
    by_cases hS : ∀ c, 0 < (E.flip E.solidFlip).armCount c →
        ∀ k, (E.flip E.solidFlip).toTorus.leftPiece k = c →
          (E.flip E.solidFlip).toTorus.rightPiece k ≠ c
    · exact seifertFactor_of_isMoveFree_of_normal _ hE' hR hS
    · simp only [not_forall, not_not] at hS
      obtain ⟨c, hc, k, hl, hr⟩ := hS
      exact (E.flip E.solidFlip).seifertFactor_of_centre_selfSeam_proved hE' hR hc hl hr

end GC.Seifert
