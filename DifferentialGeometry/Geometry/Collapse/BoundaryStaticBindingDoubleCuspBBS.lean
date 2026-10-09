import DifferentialGeometry.Geometry.Collapse.BoundaryStaticBindingBBS
import DifferentialGeometry.Geometry.Collapse.BoundarySequenceAssignmentDoubleCuspBSTD1

/-!
# BBR02's binding on the double-cusp standing sequence (lane B-BBR-BSA, consumer)

Draft 61 §7.5: the double-cusp instance is a non-emptiness regression of the sequence entry. With
the derivative-control function `A` of the double-cusp standing sequence
(`exists_doubleCusp_standing_sequence_ratio_INST`; members `T² × [0, 240]`, two boundary
components), the early choices are inhabited (a staged prefix at the trivial requests), and BBR02's
binding `bbr02_standing_tail_BBS` applies to the double-cusp sequence at `δ₀ = δ₁`: for EVERY early
choice one zero scale, one register and one tail of members carrying the member output and BSA04's
standing data. No counterfactual hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-- **Consumer: BBR02's binding on the double cusps.** One `A`; the early choices are inhabited;
the double-cusp standing sequence below `δ₁` (two boundary components per member) carries, for every
early choice, one zero scale `V`, one register over `(E, V)` and one tail of members with nonempty
member output and BSA04.a `R_p > 2n r_p(1/n)` at every point. -/
theorem bbr02_standing_tail_doubleCusp_BBS (K : ℕ) (hK : 10 ≤ K) :
    ∃ A : ℝ → ℝ, ∃ hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w,
      Nonempty (BoundaryEarlyChoices_BSTD1 K hK A hA) ∧
      ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∃ hδ₁ : δ₁ ≤ (bdryThresholds_BSTD1 K hK A hA).δStar,
      ∃ S : BoundaryStandingSequence_BSTD1 K A δ₁, (∀ n, (S.B n).count = 2) ∧
      ∀ E : BoundaryEarlyChoices_BSTD1 K hK A hA,
        ∃ V : ℝ, ∃ R : BoundaryRegisterOver_BSTD1 E V, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
          Nonempty (BoundaryMemberOutput_BSTD1 (S.mono_BBS hδ₁) n R) ∧
          ∀ p : (S.W n).Carrier,
            ENNReal.ofReal (2 * n * firstVolumeScale (S.g n) p (n : ℝ)⁻¹) <
              curvatureRadius (S.g n) p := by
  obtain ⟨A, hApos, hseq⟩ := exists_doubleCusp_standing_sequence_ratio_INST K
  have hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w := fun w _ _ => hApos w
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
  obtain ⟨E₀, -⟩ := exists_boundaryEarlyChoices_staged_BSTD1 K hK A hA t (fun _ => 1)
    (fun _ => one_pos) 0 le_rfl 1 le_rfl (tcp01SupportBound + 1) le_rfl
    C14StagedRequestsSTG.trivial
  obtain ⟨δ₁, hδ₁, hδ₁Θ, hbind⟩ := bbr02_standing_tail_BBS K hK A hA
  obtain ⟨W, hW, g, B, hc, hvol, hder⟩ := hseq δ₁ hδ₁
  let S : BoundaryStandingSequence_BSTD1 K A δ₁ := ⟨δ₁, hδ₁, le_rfl, W, hW, g, B, hvol, hder⟩
  refine ⟨A, hA, ⟨E₀⟩, δ₁, hδ₁, hδ₁Θ, S, hc, fun E => ?_⟩
  obtain ⟨V, R, n₀, hn⟩ := hbind E S
  exact ⟨V, R, n₀, fun n h => ⟨(hn n h).1, fun p => ((hn n h).2 p).1⟩⟩

end DifferentialGeometry.Geometry.Collapse
