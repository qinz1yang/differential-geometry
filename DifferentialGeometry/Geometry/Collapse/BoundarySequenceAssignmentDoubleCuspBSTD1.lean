import DifferentialGeometry.Geometry.Collapse.BoundarySequenceAssignmentBSTD1
import DifferentialGeometry.Geometry.Collapse.Inhabitants.DoubleCuspStandingSequenceInstApplications

/-!
# The boundary sequence assignment on the double-cusp standing sequence (lane BSTG-D1, consumer)

Task 61, D61-11 / draft §7.5: the double-cusp instance is a non-emptiness regression of the
sequence entry. With the derivative-control function `A` of the double-cusp standing sequence
(`exists_doubleCusp_standing_sequence_ratio_INST`, lane BDRY-INST; members `T² × [0, 240]`, two
boundary components), the early choices over the exported boundary thresholds are inhabited (a
staged prefix at the trivial requests), and for EVERY early choice the double-cusp sequence at
`δ₀ = δStar` carries the per-sequence assignment: a zero scale `V`, a register over `(early, V)`
and a tail of members with nonempty output. No counterfactual hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter

namespace DifferentialGeometry.Geometry.Collapse

/-- **Consumer: the boundary sequence assignment is nonempty on the double cusps** (D61-11,
draft §7.5): one derivative-control function `A`; the early choices over the exported boundary
thresholds are inhabited; and for every early choice the double-cusp standing sequence at
`δ₀ = δStar` (two boundary components per member) has a zero scale `V`, a boundary register over
`(early, V)` and `n₀` with nonempty member output for every `n ≥ n₀`. -/
theorem boundarySequenceAssignment_doubleCusp_BSTD1 (K : ℕ) (hK : 10 ≤ K) :
    ∃ A : ℝ → ℝ, ∃ hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w,
      Nonempty (BoundaryEarlyChoices_BSTD1 K hK A hA) ∧
      ∀ E : BoundaryEarlyChoices_BSTD1 K hK A hA,
      ∃ S : BoundaryStandingSequence_BSTD1 K A (bdryThresholds_BSTD1 K hK A hA).δStar,
        (∀ n, (S.B n).count = 2) ∧
        ∃ V : ℝ, ∃ R : BoundaryRegisterOver_BSTD1 E V, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
          Nonempty (BoundaryMemberOutput_BSTD1 S n R) := by
  obtain ⟨A, hApos, hseq⟩ := exists_doubleCusp_standing_sequence_ratio_INST K
  have hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w := fun w _ _ => hApos w
  refine ⟨A, hA, ?_, fun E => ?_⟩
  · let t : C14Tol :=
      { γT := 1
        θs := 1 / 2
        θe := 1 / 2
        θ2 := 1 / 2
        Cρ := 1
        e₁ := 1
        C₁ := 1
        γT_pos := one_pos
        γT_le := le_rfl
        θs_pos := by norm_num
        θs_lt := by norm_num
        θe_pos := by norm_num
        θe_lt := by norm_num
        θ2_pos := by norm_num
        θ2_lt := by norm_num
        Cρ_pos := one_pos
        e₁_pos := one_pos
        C₁_pos := one_pos }
    obtain ⟨E, -⟩ := exists_boundaryEarlyChoices_staged_BSTD1 K hK A hA t (fun _ => 1)
      (fun _ => one_pos) 0 le_rfl 1 le_rfl (tcp01SupportBound + 1) le_rfl
      C14StagedRequestsSTG.trivial
    exact ⟨E⟩
  · have hδ := (bdryThresholds_BSTD1 K hK A hA).δStar_pos
    obtain ⟨W, hW, g, B, hc, hvol, hder⟩ := hseq _ hδ
    exact ⟨⟨_, hδ, le_rfl, W, hW, g, B, hvol, hder⟩, hc,
      exists_boundarySequenceAssignment_BSTD1 E ⟨_, hδ, le_rfl, W, hW, g, B, hvol, hder⟩⟩

end DifferentialGeometry.Geometry.Collapse
