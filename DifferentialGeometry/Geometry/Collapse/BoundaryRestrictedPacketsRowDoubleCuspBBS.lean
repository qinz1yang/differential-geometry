import DifferentialGeometry.Geometry.Collapse.BoundaryRestrictedPacketsRowBBS
import DifferentialGeometry.Geometry.Collapse.BoundarySequenceAssignmentDoubleCuspBSTD1

/-!
# BCP04 / BCP05 on the double-cusp standing sequence (lane B-BBR-BSA, consumer)

Draft 61 §7.5: the double-cusp instance is the non-emptiness regression of the sequence entry.
With the derivative-control function `A` of the double-cusp standing sequence
(`exists_doubleCusp_standing_sequence_ratio_INST`; members `T² × [0, 240]`, two boundary
components), the early choices are inhabited, and `bcp04_bcp05_row_BBS` applies to the double-cusp
sequence at `δ₀ = δStar`: for EVERY early choice one zero scale, one register and one tail on which
every member has its labelled packet (two components) and BCP04.a at its index `n + 1`. No
counterfactual hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Collapse

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-- **Consumer: BCP04 / BCP05 on the double cusps.** One `A`; the early choices are inhabited; the
double-cusp standing sequence at `δ₀ = δStar` carries, for EVERY early choice, one zero scale `V`,
one register over `(E, V)` and one tail on which every member has a labelled packet with two
boundary components and BCP04.a at the index `n + 1` at every point off the boundary. -/
theorem bcp04_bcp05_row_doubleCusp_BBS (K : ℕ) (hK : 10 ≤ K) :
    ∃ A : ℝ → ℝ, ∃ hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w,
      Nonempty (BoundaryEarlyChoices_BSTD1 K hK A hA) ∧
      ∃ S : BoundaryStandingSequence_BSTD1 K A (bdryThresholds_BSTD1 K hK A hA).δStar,
        (∀ n, (S.B n).count = 2) ∧
        ∀ E : BoundaryEarlyChoices_BSTD1 K hK A hA,
        ∃ V : ℝ, ∃ R : BoundaryRegisterOver_BSTD1 E V, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        ∃ P : BoundaryExportPacket (S.W n) (S.g n) K A (boundaryCounterexampleRatio S.δ₀ (n + 1))
          (cuspTolerance_BCUSP1 (E.β 1) R.βd R.εN),
        P.cusp.count = 2 ∧ ∃ ρ : (S.W n).Carrier → ℝ, (∀ p, 0 < ρ p) ∧
          ∀ p, 0 < distanceToBoundary (S.W n) (S.g n) p →
            ((n + 1 : ℕ) : ℝ) * (distanceToBoundary (S.W n) (S.g n) p).toReal /
                ((distanceToBoundary (S.W n) (S.g n) p).toReal + 3) <
              (distanceToBoundary (S.W n) (S.g n) p).toReal / ρ p := by
  obtain ⟨A, hApos, hseq⟩ := exists_doubleCusp_standing_sequence_ratio_INST K
  have hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w := fun w _ _ => hApos w
  have hδ := (bdryThresholds_BSTD1 K hK A hA).δStar_pos
  obtain ⟨W, hW, g, B, hc, hvol, hder⟩ := hseq _ hδ
  let S : BoundaryStandingSequence_BSTD1 K A (bdryThresholds_BSTD1 K hK A hA).δStar :=
    ⟨_, hδ, le_rfl, W, hW, g, B, hvol, hder⟩
  have hE : Nonempty (BoundaryEarlyChoices_BSTD1 K hK A hA) := by
    let t : C14Tol :=
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
  refine ⟨A, hA, hE, S, hc, fun E => ?_⟩
  obtain ⟨V, R, n₀, hn⟩ := bcp04_bcp05_row_BBS E S
  refine ⟨V, R, n₀, fun n h => ?_⟩
  obtain ⟨P, hPB, ρ, hρpos, ha, -⟩ := hn n h
  exact ⟨P, hPB ▸ hc n, ρ, hρpos, ha⟩

end DifferentialGeometry.Geometry.Collapse
