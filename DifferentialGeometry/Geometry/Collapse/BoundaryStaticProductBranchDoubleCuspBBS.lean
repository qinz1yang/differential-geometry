import DifferentialGeometry.Geometry.Collapse.BoundaryStaticProductBranchBBS
import DifferentialGeometry.Geometry.Collapse.BoundarySequenceAssignmentDoubleCuspBSTD1

/-!
# BBR02's graph clause on the double-cusp standing sequence (lane B-BBR-BSA, consumer)

The double-cusp standing sequence of lane BDRY-INST (`exists_doubleCusp_standing_sequence_INST`:
members `annulusCircleCarrier = T² × [0, 240]` with the double-cusp metrics, two boundary
components) is a standing sequence at `δ₀ = δStar`. Through `bbr02_graph_or_separated_BBS`, for
EVERY early choice one zero scale, one register and one tail on which every member has a raw graph
presentation labelled by its two boundary components: in the separated branch as well, since every
member is diffeomorphic to `T² × [0, 1]`
(`exists_labelledRawGraphPresentation_of_torusProduct_BBS`). No counterfactual hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry GC.Seifert GC.Endpoint GC.GraphManifold GC.GraphManifold.Assembly

namespace DifferentialGeometry.Geometry.Collapse

attribute [local instance] BoundaryStandingSequence_BSTD1.conn

/-- **Consumer: BBR02's graph clause on the double cusps.** One `A`; the early choices are
inhabited; the double-cusp standing sequence at `δ₀ = δStar` (members `T² × [0, 240]`, two boundary
components) carries, for EVERY early choice, one zero scale `V`, one register over `(E, V)` and one
tail on which every member has a raw graph presentation labelled by its boundary components. -/
theorem bbr02_graph_doubleCusp_BBS (K : ℕ) (hK : 10 ≤ K) :
    ∃ A : ℝ → ℝ, ∃ hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w,
      Nonempty (BoundaryEarlyChoices_BSTD1 K hK A hA) ∧
      ∃ S : BoundaryStandingSequence_BSTD1 K A (bdryThresholds_BSTD1 K hK A hA).δStar,
        (∀ n, (S.B n).count = 2) ∧
        ∀ E : BoundaryEarlyChoices_BSTD1 K hK A hA,
        ∃ V : ℝ, ∃ _ : BoundaryRegisterOver_BSTD1 E V, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
          ∃ G : RawGraphPresentation (S.W n), ∃ e : Fin (S.B n).count ≃ Fin G.externalCount,
            ∀ i, Set.range (G.external.torusMap (e i)) = (S.B n).component i := by
  obtain ⟨A, hApos, hseq⟩ := exists_doubleCusp_standing_sequence_INST.{0} K
  have hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w := fun w _ _ => hApos w
  have hδ := (bdryThresholds_BSTD1 K hK A hA).δStar_pos
  obtain ⟨a, ha, B, hc, hvol, hder⟩ := hseq
    (fun n => boundaryCounterexampleRatio (bdryThresholds_BSTD1 K hK A hA).δStar (n + 1))
    (fun n => boundaryCounterexampleRatio_pos hδ (Nat.le_add_left 1 n))
  let S : BoundaryStandingSequence_BSTD1 K A (bdryThresholds_BSTD1 K hK A hA).δStar :=
    ⟨_, hδ, le_rfl, fun _ => annulusCircleCarrier.{0},
      fun _ => connectedSpace_productSet (Or.inl rfl), fun n => doubleCuspMetric.{0} (a n) (ha n),
      B, hvol, hder⟩
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
  obtain ⟨V, R, n₀, hR⟩ := bbr02_graph_or_separated_BBS E S
  refine ⟨V, R, n₀, fun n hn => ?_⟩
  rcases hR n hn with hG | -
  · exact hG
  · exact exists_labelledRawGraphPresentation_of_torusProduct_BBS (S.B n)
      annulusCircleCarrierDiffeomorphTorusInterval.{0}.symm

end DifferentialGeometry.Geometry.Collapse
