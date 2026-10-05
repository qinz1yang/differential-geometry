import DifferentialGeometry.Geometry.Collapse.BoundarySequenceSupplyV3
import DifferentialGeometry.Geometry.Collapse.Inhabitants.DoubleCuspStandingSequenceInstApplications

/-!
# Instance evidence for the per-sequence boundary supply (lane FC39-BQ3)

External review 54, §4 and §7 (dispositions rows 4, 7): the boundary supply is re-accepted when
the wiring AND an unconditional instance are committed. Here FC39-BQ3 G3's proved supply
(`boundarySupplyV3_holds_BQ3`) is applied to BDRY-INST's double-cusp standing sequence
(`exists_doubleCusp_standing_sequence_ratio_INST`, two boundary components per member, ONE `A`
before `δ⋆`) at the supply's own `δ⋆`: the analytic supply package exists on that ACTUAL
sequence, and at a register of its strategy T3B-R's export packets exist on the universe-`0`
models of all members of a tail, with `packet.cusp = B₀`. No counterfactual hypothesis.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

/-- **The boundary supply on an actual sequence** (review 54 §4, §7): for `K ≥ 10`, one `A > 0`,
the supply's early data `D`, BDRY-INST's double-cusp standing sequence at `D.δStar`, the analytic
supply package on it, a register of its strategy and a tail on which T3B-R's export packets exist
on the models of the members, with `packet.cusp = B₀`. -/
theorem exists_boundarySupply_doubleCusp_BQ3 (K : ℕ) (hK : 10 ≤ K) :
    ∃ A : ℝ → ℝ, (∀ w, 0 < A w) ∧ ∃ D : BoundaryEarlyData,
      ∃ (W : ℕ → CompactCarrier.{0}) (_ : ∀ n, ConnectedSpace (W n).Carrier)
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K
          (boundaryCounterexampleRatio D.δStar (n + 1))),
        (∀ n, (B n).count = 2) ∧ ∃ S : BoundaryAnalyticSupplyV3_BQ3 K A D W g B,
          ∃ R : BoundaryRegisterV2 D S.thresholds, ∃ N : ℕ, R.tail ≤ N ∧ ∀ n : ℕ, N ≤ n →
            letI := (S.models n).connected₀
            ∃ Pk : BoundaryExportPacket (S.models n).W₀ (S.models n).g₀ K A
                (boundaryCounterexampleRatio D.δStar (n + 1))
                (cuspTolerance_BCUSP1 (closedβV3 R.later.split.β₁ R.later.excl 1) R.cuspQuality
                  R.cuspQuality),
              Pk.cusp = (S.models n).B₀ := by
  obtain ⟨A, hA, hseq⟩ := exists_doubleCusp_standing_sequence_ratio_INST K
  obtain ⟨D, hD⟩ := boundarySupplyV3_holds_BQ3.{0} K hK A (fun w _ _ => hA w)
  obtain ⟨W, hW, g, B, hc, hvol, hder⟩ := hseq D.δStar D.δStar_pos
  obtain ⟨S⟩ := hD W g B (fun n => ⟨hvol n, hder n⟩)
  obtain ⟨R⟩ := exists_boundaryRegisterV2 D S.thresholds
  obtain ⟨N, hN, hn⟩ := S.exists_packet_rest_BQ3 R
  refine ⟨A, hA, D, W, hW, g, B, hc, S, R, N, hN, fun n hNn => ?_⟩
  obtain ⟨Pk, hPk, -⟩ := hn n hNn
  exact ⟨Pk, hPk⟩

end DifferentialGeometry.Geometry.Collapse
