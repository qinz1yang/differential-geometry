import DifferentialGeometry.Geometry.Collapse.BoundarySequenceStageOrder
import DifferentialGeometry.Geometry.Collapse.BoundaryPacketsOutBFRSeqIdx

/-!
# The per-sequence boundary realization (lane FC39-BQ3; review 54 §5–§6, work item 2)

The boundary analogue of the accepted closed realization `exists_closed_realization_VAL3`
(`StaticRegisterV2Realization.lean`), on lane FC39-BQ2's records and proved from lane BDRY-IDX4's
`lc88_boundary_packets_BFR_out_BQ_IDX4` (T3B-R on BBR03's sequences at `δ_{n+1}`, BCP04.a index
`n + 1`, cusp requests after `V, δ, L_max`).

* `exists_boundary_sequence_realization_core_BQ3` (the CORE realization, frozen target (a) of
  `state-FC39-BQ2.md`): `δ⋆` first (the producer's); for every early data `D` with `D.δStar ≤ δ⋆`
  and every boundary standing sequence at `D.δStar` (member `n` at `δ_{n+1}`), the producer's Skolem
  outputs `P : BoundaryProducerOutputs_BQ2 D` (`εr, δ', Λz` at the values chosen before `T₀`; `V, δ`
  at those and `T₀`) are fixed BEFORE any request strategy; then for every request strategy `U` a
  strategy `T` refining `U.withV_BQ2 P.VF` (so `V` is the producer's output, review 54 §6.3) on
  whose EVERY register the per-sequence family `PartialBoundaryFamilyAtSeqV3_BQ2` holds: T3B-R's
  per-member conclusion on every member of the register's tail, at the register's values, with
  cusp requests `βd = εN = R.cuspQuality` (BR24). The thresholds of `T` are the producer's Skolem
  thresholds added slot by slot to `U`'s (as on the closed side, without LC09's `w₀`), LC18's
  obstruction in `lc18`, and the producer's eventual tail (which reads `L_max` and the cusp quality)
  in the boundary tail slot `tailLow` (BR25).
* `exists_boundary_sequence_supply_BQ3` (frozen target (b), review 54 §6.2): with the validity
  bridge `of_withV_refines_BQ2`, the realizing strategy carries the partial validity
  `PartialBoundaryThresholdValidityV3_BQ2` for the SAME `D` whenever `U` does.
* Consumers: `exists_sourced_boundary_sequence_supply_BQ3` (sourced early data
  `boundaryEarlyDataSrc_BQ2` below both thresholds, request strategy `boundaryThresholdsSrc_BQ2`: a
  valid realizing strategy exists on every boundary standing sequence), and
  `exists_realized_boundaryRegister_BQ3` (one register at a valid realizing strategy, and on a tail
  of the sequence an export packet with `packet.cusp = B n` at the register's cusp tolerance).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

/-- **The core per-sequence boundary realization** (frozen target (a); review 54 §6): `δ⋆` first;
on every boundary standing sequence at `D.δStar ≤ δ⋆` the producer's outputs `P` are fixed before
any request strategy `U`, and a strategy `T` refining `U` with `V` the producer's output realizes
the per-sequence family on every staged register at `T`. -/
theorem exists_boundary_sequence_realization_core_BQ3 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ δStar : ℝ, 0 < δStar ∧ ∀ D : BoundaryEarlyData, D.δStar ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K
          (boundaryCounterexampleRatio D.δStar (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio D.δStar (n + 1)) ∧
          curvatureDerivativesControlled (g n) K A
            (boundaryCounterexampleRatio D.δStar (n + 1))) →
        ∃ P : BoundaryProducerOutputs_BQ2 D, ∀ U : BoundaryThresholdsV2 D,
          ∃ T : BoundaryThresholdsV2 D,
            BoundaryStrategyRefinesV3_BQ2 T (U.withV_BQ2 P.VF P.T₀_le_VF) ∧
            PartialBoundaryFamilyAtSeqV3_BQ2 K A W g B T P := by
  classical
  obtain ⟨δS, hδS, a₂, ha₂, hP⟩ := lc88_boundary_packets_BFR_out_BQ_IDX4 K hK A hA
  refine ⟨δS, hδS, fun D hD W _ g B hs => ?_⟩
  let C1 : ℝ → Prop := fun γ =>
    0 < γ ∧ γ < 1 / 10
  have hP1 : ∀ (γ : ℝ) (hc : C1 γ), _ := fun γ hc =>
    hP γ hc.1 hc.2
  choose β₀ hβ₀ hβ₀a hP using hP1
  let B0 : ℝ → ℝ := fun γ =>
    if hc : C1 γ then β₀ γ hc else 1
  have B0_pos : ∀ (γ : ℝ), 0 < B0 γ := fun γ => by
    by_cases hc : C1 γ
    · rw [show B0 γ = β₀ γ hc from dite_eq_left hc]
      exact hβ₀ γ hc
    · rw [show B0 γ = 1 from dite_eq_right hc]
      exact one_pos
  let C2 : ℝ → ℝ → ℝ → Prop := fun γ βc γc =>
    C1 γ ∧ (0 < βc ∧ βc < γc / 1000 ∧ 0 < γc ∧ γc < 1 / 100)
  have hP2 : ∀ (γ βc γc : ℝ) (hc : C2 γ βc γc), _ := fun γ βc γc hc =>
    hP γ hc.1 βc γc hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  choose σ₀ hσ₀ Δ₀ hΔ₀ hP using hP2
  let S0 : ℝ → ℝ → ℝ → ℝ := fun γ βc γc =>
    if hc : C2 γ βc γc then σ₀ γ βc γc hc else 1
  have S0_pos : ∀ (γ βc γc : ℝ), 0 < S0 γ βc γc := fun γ βc γc => by
    by_cases hc : C2 γ βc γc
    · rw [show S0 γ βc γc = σ₀ γ βc γc hc from dite_eq_left hc]
      exact hσ₀ γ βc γc hc
    · rw [show S0 γ βc γc = 1 from dite_eq_right hc]
      exact one_pos
  let D0 : ℝ → ℝ → ℝ → ℝ := fun γ βc γc =>
    if hc : C2 γ βc γc then Δ₀ γ βc γc hc else 1
  have D0_pos : ∀ (γ βc γc : ℝ), 0 < D0 γ βc γc := fun γ βc γc => by
    by_cases hc : C2 γ βc γc
    · rw [show D0 γ βc γc = Δ₀ γ βc γc hc from dite_eq_left hc]
      exact hΔ₀ γ βc γc hc
    · rw [show D0 γ βc γc = 1 from dite_eq_right hc]
      exact one_pos
  let C3 : ℝ → ℝ → ℝ → ℝ → ℝ → Prop := fun γ βc γc β₂ Δ =>
    C2 γ βc γc ∧ (0 < β₂ ∧ β₂ ≤ B0 γ ∧ β₂ < 1 / 100 ∧ 100 / β₂ < Δ ∧ D0 γ βc γc ≤ Δ)
  have hP3 : ∀ (γ βc γc β₂ Δ : ℝ) (hc : C3 γ βc γc β₂ Δ), _ := fun γ βc γc β₂ Δ hc =>
    hP γ βc γc hc.1 β₂ Δ hc.2.1 ((hc.2.2.1).trans_eq (dite_eq_left hc.1.1)) hc.2.2.2.1 hc.2.2.2.2.1
        ((dite_eq_left hc.1).symm.trans_le (hc.2.2.2.2.2))
  choose τ₀ hτ₀ bc₀ hbc₀ hP using hP3
  let T0 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun γ βc γc β₂ Δ =>
    if hc : C3 γ βc γc β₂ Δ then τ₀ γ βc γc β₂ Δ hc else 1
  have T0_pos : ∀ (γ βc γc β₂ Δ : ℝ), 0 < T0 γ βc γc β₂ Δ := fun γ βc γc β₂ Δ => by
    by_cases hc : C3 γ βc γc β₂ Δ
    · rw [show T0 γ βc γc β₂ Δ = τ₀ γ βc γc β₂ Δ hc from dite_eq_left hc]
      exact hτ₀ γ βc γc β₂ Δ hc
    · rw [show T0 γ βc γc β₂ Δ = 1 from dite_eq_right hc]
      exact one_pos
  let BC : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun γ βc γc β₂ Δ =>
    if hc : C3 γ βc γc β₂ Δ then bc₀ γ βc γc β₂ Δ hc else 1
  have BC_pos : ∀ (γ βc γc β₂ Δ : ℝ), 0 < BC γ βc γc β₂ Δ := fun γ βc γc β₂ Δ => by
    by_cases hc : C3 γ βc γc β₂ Δ
    · rw [show BC γ βc γc β₂ Δ = bc₀ γ βc γc β₂ Δ hc from dite_eq_left hc]
      exact hbc₀ γ βc γc β₂ Δ hc
    · rw [show BC γ βc γc β₂ Δ = 1 from dite_eq_right hc]
      exact one_pos
  let C4 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop := fun γ βc γc β₂ Δ σc ε μ τ s b' s'
      =>
    C3 γ βc γc β₂ Δ ∧ (0 < σc ∧ σc ≤ S0 γ βc γc ∧ σc < 1 ∧ 0 < ε ∧ ε < 1 / 100 ∧ 0 < μ ∧ μ ≤ 1 /
        1000000 ∧ 0 < τ ∧ τ ≤ T0 γ βc γc β₂ Δ ∧ 140 * Real.sqrt τ < ε ^ 2 / 20 ∧ ε ≤ 1 / 10 ^ 8 ∧ μ
        ≤ 1 / 10 ^ 8) ∧ (0 < s ∧ s < 1 / 100 ∧ s < b' / 100000 ∧ s < s' / 100000 ∧ b' < 1 / (1000000
        * Δ) ∧ s' < 1 / (1000000 * Δ) ∧ b' < τ * Δ / 1000000000 ∧ s' < τ * Δ / 1000000000)
  have hP4 : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' : ℝ) (hc : C4 γ βc γc β₂ Δ σc ε μ τ s b' s'), _ := fun
      γ βc γc β₂ Δ σc ε μ τ s b' s' hc =>
    hP γ βc γc β₂ Δ hc.1 σc ε μ τ hc.2.1.1 ((hc.2.1.2.1).trans_eq (dite_eq_left hc.1.1))
        hc.2.1.2.2.1 hc.2.1.2.2.2.1 hc.2.1.2.2.2.2.1 hc.2.1.2.2.2.2.2.1 hc.2.1.2.2.2.2.2.2.1
        hc.2.1.2.2.2.2.2.2.2.1 ((hc.2.1.2.2.2.2.2.2.2.2.1).trans_eq (dite_eq_left hc.1))
        hc.2.1.2.2.2.2.2.2.2.2.2.1 hc.2.1.2.2.2.2.2.2.2.2.2.2.1 hc.2.1.2.2.2.2.2.2.2.2.2.2.2 s b' s'
        hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.1
        hc.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2
  choose a₀ b₁ ha₀ hb₁ hP using hP4
  let A0 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' =>
    if hc : C4 γ βc γc β₂ Δ σc ε μ τ s b' s' then a₀ γ βc γc β₂ Δ σc ε μ τ s b' s' hc else 1
  have A0_pos : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' : ℝ), 0 < A0 γ βc γc β₂ Δ σc ε μ τ s b' s' := fun γ
      βc γc β₂ Δ σc ε μ τ s b' s' => by
    by_cases hc : C4 γ βc γc β₂ Δ σc ε μ τ s b' s'
    · rw [show A0 γ βc γc β₂ Δ σc ε μ τ s b' s' = a₀ γ βc γc β₂ Δ σc ε μ τ s b' s' hc from
        dite_eq_left hc]
      exact ha₀ γ βc γc β₂ Δ σc ε μ τ s b' s' hc
    · rw [show A0 γ βc γc β₂ Δ σc ε μ τ s b' s' = 1 from dite_eq_right hc]
      exact one_pos
  let B1 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' =>
    if hc : C4 γ βc γc β₂ Δ σc ε μ τ s b' s' then b₁ γ βc γc β₂ Δ σc ε μ τ s b' s' hc else 1
  have B1_pos : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' : ℝ), 0 < B1 γ βc γc β₂ Δ σc ε μ τ s b' s' := fun γ
      βc γc β₂ Δ σc ε μ τ s b' s' => by
    by_cases hc : C4 γ βc γc β₂ Δ σc ε μ τ s b' s'
    · rw [show B1 γ βc γc β₂ Δ σc ε μ τ s b' s' = b₁ γ βc γc β₂ Δ σc ε μ τ s b' s' hc from
        dite_eq_left hc]
      exact hb₁ γ βc γc β₂ Δ σc ε μ τ s b' s' hc
    · rw [show B1 γ βc γc β₂ Δ σc ε μ τ s b' s' = 1 from dite_eq_right hc]
      exact one_pos
  let C5 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop := fun γ βc γc β₂ Δ σc ε μ τ
      s b' s' σ Λ =>
    C4 γ βc γc β₂ Δ σc ε μ τ s b' s' ∧ (0 < σ ∧ σ ≤ a₂ ∧ σ ≤ threeSplittingExclusionThreshold.{0, 0}
        ∧ σ ≤ A0 γ βc γc β₂ Δ σc ε μ τ s b' s') ∧ (0 < Λ ∧ Δ * Λ * 2000000 ≤ 1 / 100 ∧ Λ < 1 /
        (1000000 * Δ) ∧ 100 * Δ * Λ ≤ 1 / 1000000 ∧ 2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ +
        3780 * τ) < γc / 1000 ∧ Λ < s' / (100000000 * Δ ^ 2) ∧ 100 * Δ * Λ ≤ 1 / 10 ^ 8)
  have hP5 : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ : ℝ) (hc : C5 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ),
      _ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ hc =>
    hP γ βc γc β₂ Δ σc ε μ τ s b' s' hc.1 σ hc.2.1.1 hc.2.1.2.1 hc.2.1.2.2.1
        ((hc.2.1.2.2.2).trans_eq (dite_eq_left hc.1)) Λ hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1
        hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2
  choose w₀ hw₀ hP using hP5
  let W0 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun γ βc γc β₂ Δ σc ε μ τ s
      b' s' σ Λ =>
    if hc : C5 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ then w₀ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ hc else 1
  have W0_pos : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ : ℝ), 0 < W0 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ
      := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ => by
    by_cases hc : C5 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ
    · rw [show W0 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ = w₀ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ hc from
        dite_eq_left hc]
      exact hw₀ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ hc
    · rw [show W0 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ = 1 from dite_eq_right hc]
      exact one_pos
  let C6 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop := fun γ βc γc β₂ Δ σc ε
      μ τ s b' s' σ Λ w =>
    C5 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ ∧ (0 < w ∧ w < W0 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ ∧ w < 4
        * Real.pi / 3)
  have hP6 : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w : ℝ) (hc : C6 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ
      w), _ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w hc =>
    hP γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ hc.1 w hc.2.1 ((hc.2.2.1).trans_eq (dite_eq_left hc.1))
        hc.2.2.2
  choose bd₀ hbd₀ hP using hP6
  let BD : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun γ βc γc β₂ Δ σc ε μ
      τ s b' s' σ Λ w =>
    if hc : C6 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w then bd₀ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w hc
        else 1
  have BD_pos : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w : ℝ), 0 < BD γ βc γc β₂ Δ σc ε μ τ s b' s' σ
      Λ w := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w => by
    by_cases hc : C6 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w
    · rw [show BD γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w = bd₀ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w hc
        from dite_eq_left hc]
      exact hbd₀ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w hc
    · rw [show BD γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w = 1 from dite_eq_right hc]
      exact one_pos
  let C7 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop := fun γ βc
      γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs =>
    C6 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w ∧ (0 < b ∧ b < s / 100000 ∧ b < BC γ βc γc β₂ Δ ∧ b < B1
        γ βc γc β₂ Δ σc ε μ τ s b' s' ∧ 100 * Δ < b⁻¹ ∧ b < BD γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w)
        ∧ (0 < σs ∧ σs ≤ 1 / 100 ∧ 0 < vs)
  have hP7 : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs : ℝ) (hc : C7 γ βc γc β₂ Δ σc ε μ τ s b'
      s' σ Λ w b σs vs), _ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs hc =>
    hP γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w hc.1 b hc.2.1.1 hc.2.1.2.1 ((hc.2.1.2.2.1).trans_eq
        (dite_eq_left hc.1.1.1.1)) ((hc.2.1.2.2.2.1).trans_eq (dite_eq_left hc.1.1.1))
        hc.2.1.2.2.2.2.1 ((hc.2.1.2.2.2.2.2).trans_eq (dite_eq_left hc.1)) σs vs hc.2.2.1 hc.2.2.2.1
        hc.2.2.2.2
  choose b₀ hb₀ hP using hP7
  let BZ : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun γ βc γc
      β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs =>
    if hc : C7 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs then b₀ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ
        w b σs vs hc else 1
  have BZ_pos : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs : ℝ), 0 < BZ γ βc γc β₂ Δ σc ε μ τ s
      b' s' σ Λ w b σs vs := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs => by
    by_cases hc : C7 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs
    · rw [show BZ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs = b₀ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ
        w b σs vs hc from dite_eq_left hc]
      exact hb₀ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs hc
    · rw [show BZ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs = 1 from dite_eq_right hc]
      exact one_pos
  let C8 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℕ → ℝ) → ℝ → ℝ →
      Prop := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap =>
    C7 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs ∧ (β 2 = β₂ ∧ 0 < β 1 ∧ β 1 < BZ γ βc γc β₂ Δ σc
        ε μ τ s b' s' σ Λ w b σs vs ∧ β 1 < 1 ∧ β 3 ≤ threeSplittingExclusionThreshold.{0, 0}) ∧ (β
        1 < ζ ∧ ζ < 1 ∧ 0 < cap)
  have hP8 : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs : ℝ) (β : ℕ → ℝ) (ζ cap : ℝ) (hc : C8 γ
      βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap), _ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ
      w b σs vs β ζ cap hc =>
    hP γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs hc.1 β hc.2.1.1 hc.2.1.2.1
        ((hc.2.1.2.2.1).trans_eq (dite_eq_left hc.1)) hc.2.1.2.2.2.1 hc.2.1.2.2.2.2 ζ cap hc.2.2.1
        hc.2.2.2.1 hc.2.2.2.2
  choose εr δ' Λ' hεr hεr4 hεrcap hδ' hΛ' hP using hP8
  let ER : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℕ → ℝ) → ℝ → ℝ →
      ℝ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap =>
    if hc : C8 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap then εr γ βc γc β₂ Δ σc ε μ τ s
        b' s' σ Λ w b σs vs β ζ cap hc else 1
  have ER_pos : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs : ℝ) (β : ℕ → ℝ) (ζ cap : ℝ), 0 < ER
      γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w
      b σs vs β ζ cap => by
    by_cases hc : C8 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap
    · rw [show ER γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap = εr γ βc γc β₂ Δ σc ε μ τ s
        b' s' σ Λ w b σs vs β ζ cap hc from dite_eq_left hc]
      exact hεr γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap hc
    · rw [show ER γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap = 1 from dite_eq_right hc]
      exact one_pos
  let DP : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℕ → ℝ) → ℝ → ℝ →
      ℝ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap =>
    if hc : C8 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap then δ' γ βc γc β₂ Δ σc ε μ τ s
        b' s' σ Λ w b σs vs β ζ cap hc else 1
  have DP_pos : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs : ℝ) (β : ℕ → ℝ) (ζ cap : ℝ), 0 < DP
      γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w
      b σs vs β ζ cap => by
    by_cases hc : C8 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap
    · rw [show DP γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap = δ' γ βc γc β₂ Δ σc ε μ τ s
        b' s' σ Λ w b σs vs β ζ cap hc from dite_eq_left hc]
      exact hδ' γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap hc
    · rw [show DP γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap = 1 from dite_eq_right hc]
      exact one_pos
  let LZ : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℕ → ℝ) → ℝ → ℝ →
      ℝ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap =>
    if hc : C8 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap then Λ' γ βc γc β₂ Δ σc ε μ τ s
        b' s' σ Λ w b σs vs β ζ cap hc else 1
  have LZ_pos : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs : ℝ) (β : ℕ → ℝ) (ζ cap : ℝ), 0 < LZ
      γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w
      b σs vs β ζ cap => by
    by_cases hc : C8 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap
    · rw [show LZ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap = Λ' γ βc γc β₂ Δ σc ε μ τ s
        b' s' σ Λ w b σs vs β ζ cap hc from dite_eq_left hc]
      exact hΛ' γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap hc
    · rw [show LZ γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap = 1 from dite_eq_right hc]
      exact one_pos
  let C9 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℕ → ℝ) → ℝ → ℝ →
      ℝ → ℝ → Prop := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e =>
    C8 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap ∧ (0 < T ∧ 20 * LZ γ βc γc β₂ Δ σc ε μ τ
        s b' s' σ Λ w b σs vs β ζ cap ≤ T) ∧ (0 < e ∧ e < 1 / 40)
  have hP9 : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs : ℝ) (β : ℕ → ℝ) (ζ cap T e : ℝ) (hc :
      C9 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e), _ := fun γ βc γc β₂ Δ σc ε μ τ s
      b' s' σ Λ w b σs vs β ζ cap T e hc =>
    hP γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap hc.1 T hc.2.1.1 ((congrArg (fun x => 20 *
        x) (dite_eq_left hc.1)).symm.trans_le (hc.2.1.2)) e hc.2.2.1 hc.2.2.2 D.δStar D.δStar_pos hD
        W g B (fun n => (hs n).1) (fun n => (hs n).2)
  choose V hV δ hδ hδδ' hev using hP9
  let VV : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℕ → ℝ) → ℝ → ℝ →
      ℝ → ℝ → ℝ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e =>
    if hc : C9 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e then V γ βc γc β₂ Δ σc ε μ τ
        s b' s' σ Λ w b σs vs β ζ cap T e hc else T
  have VV_ge : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs : ℝ) (β : ℕ → ℝ) (ζ cap T e : ℝ), T ≤
      VV γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e := fun γ βc γc β₂ Δ σc ε μ τ s b'
      s' σ Λ w b σs vs β ζ cap T e => by
    by_cases hc : C9 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e
    · rw [show VV γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e = V γ βc γc β₂ Δ σc ε μ τ
        s b' s' σ Λ w b σs vs β ζ cap T e hc from dite_eq_left hc]
      exact hV γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e hc
    · rw [show VV γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e = T from dite_eq_right hc]
  let DD : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℕ → ℝ) → ℝ → ℝ →
      ℝ → ℝ → ℝ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e =>
    if hc : C9 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e then δ γ βc γc β₂ Δ σc ε μ τ
        s b' s' σ Λ w b σs vs β ζ cap T e hc else 1
  let CT : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℕ → ℝ) → ℝ → ℝ →
      ℝ → ℝ → ℝ → ℝ → Prop := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e Lmax q =>
    C9 γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e ∧ 0 < Lmax ∧ 0 < q
  have hTL : ∀ (γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs : ℝ) (β : ℕ → ℝ) (ζ cap T e : ℝ) (Lmax q
      : ℝ) (hc : CT γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e Lmax q), _ := fun γ βc
      γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e Lmax q hc =>
    Filter.eventually_atTop.mp (hev γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e hc.1
        Lmax hc.2.1 q q hc.2.2 hc.2.2)
  choose TLd hTLd using hTL
  let TL : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℕ → ℝ) → ℝ → ℝ →
      ℝ → ℝ → ℝ → ℝ → ℕ := fun γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e Lmax q =>
    if hc : CT γ βc γc β₂ Δ σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e Lmax q then TLd γ βc γc β₂ Δ
        σc ε μ τ s b' s' σ Λ w b σs vs β ζ cap T e Lmax q hc else 0
  have hthr : (0 : ℝ) < threeSplittingExclusionThreshold.{0, 0} :=
      threeSplittingExclusionThreshold_pos
  refine ⟨⟨fun _ ci ex er sc b β₁ => ER ci.γ ci.βc ci.γc ex.β₂ ex.Δ er.co.qe er.co.ε er.bd.μ er.bd.τ
      er.s er.wk.b' er.wk.s' er.σcol sc.Λ sc.w b er.co.qs er.co.ve (closedβV3 β₁ ex) er.co.ζ
      er.co.ε₀, fun _ ci ex er sc b β₁ => DP ci.γ ci.βc ci.γc ex.β₂ ex.Δ er.co.qe er.co.ε er.bd.μ
      er.bd.τ er.s er.wk.b' er.wk.s' er.σcol sc.Λ sc.w b er.co.qs er.co.ve (closedβV3 β₁ ex) er.co.ζ
      er.co.ε₀,
    fun _ ci ex er sc b β₁ => LZ ci.γ ci.βc ci.γc ex.β₂ ex.Δ er.co.qe er.co.ε er.bd.μ er.bd.τ er.s
        er.wk.b' er.wk.s' er.σcol sc.Λ sc.w b er.co.qs er.co.ve (closedβV3 β₁ ex) er.co.ζ er.co.ε₀,
        fun _ ci ex er sc b β₁ T₀ => VV ci.γ ci.βc ci.γc ex.β₂ ex.Δ er.co.qe er.co.ε er.bd.μ er.bd.τ
        er.s er.wk.b' er.wk.s' er.σcol sc.Λ sc.w b er.co.qs er.co.ve (closedβV3 β₁ ex) er.co.ζ
        er.co.ε₀ T₀ er.co.e₀,
    fun _ ci ex er sc b β₁ T₀ => DD ci.γ ci.βc ci.γc ex.β₂ ex.Δ er.co.qe er.co.ε er.bd.μ er.bd.τ
        er.s er.wk.b' er.wk.s' er.σcol sc.Λ sc.w b er.co.qs er.co.ve (closedβV3 β₁ ex) er.co.ζ
        er.co.ε₀ T₀ er.co.e₀, fun _ ci ex er sc b β₁ T₀ => VV_ge ci.γ ci.βc ci.γc ex.β₂ ex.Δ
        er.co.qe er.co.ε er.bd.μ er.bd.τ er.s er.wk.b' er.wk.s' er.σcol sc.Λ sc.w b er.co.qs
        er.co.ve (closedβV3 β₁ ex) er.co.ζ er.co.ε₀ T₀ er.co.e₀⟩,
    fun U => ?_⟩
  refine ⟨{
    ϑUp := U.ϑUp, ϑUp_pos := U.ϑUp_pos, shortUp := U.shortUp, shortUp_pos := U.shortUp_pos
    bcgUp := U.bcgUp, bcgUp_pos := U.bcgUp_pos
    interior := fun ϑ sh bc => {
      Nb := (U.interior ϑ sh bc).Nb, Nb_nonneg := (U.interior ϑ sh bc).Nb_nonneg, cw := (U.interior
          ϑ sh bc).cw, cw_nonneg := (U.interior ϑ sh bc).cw_nonneg
      circleUp := fun st θs θe θ₂ => min ((U.interior ϑ sh bc).circleUp st θs θe θ₂) (1 / 100)
      circleUp_pos := fun st θs θe θ₂ => lt_min ((U.interior ϑ sh bc).circleUp_pos st θs θe θ₂) (by
          norm_num)
      lc18 := min (U.interior ϑ sh bc).lc18 threeSplittingExclusionThreshold.{0, 0}
      lc18_pos := lt_min (U.interior ϑ sh bc).lc18_pos hthr
      β₂Up := fun st ci β₃ => min ((U.interior ϑ sh bc).β₂Up st ci β₃) (B0 ci.γ)
      β₂Up_pos := fun st ci β₃ => lt_min ((U.interior ϑ sh bc).β₂Up_pos st ci β₃) (B0_pos ci.γ)
      ΔLow := fun st ci β₃ β₂ => max ((U.interior ϑ sh bc).ΔLow st ci β₃ β₂) (max (D0 ci.γ ci.βc
          ci.γc) (504000 * (4000 / ci.γc) ^ 2))
      errorsUp := fun st ci ex => min ((U.interior ϑ sh bc).errorsUp st ci ex) (min (S0 ci.γ ci.βc
          ci.γc) (min (1 / 10 ^ 10) (posOr_VAL3 (ci.γc / 8000))))
      errorsUp_pos := fun st ci ex => lt_min ((U.interior ϑ sh bc).errorsUp_pos st ci ex) (lt_min
          (S0_pos _ _ _) (lt_min (by norm_num) (posOr_pos_VAL3 _)))
      sectionUp := fun st ci ex co => min ((U.interior ϑ sh bc).sectionUp st ci ex co) (min (T0 ci.γ
          ci.βc ci.γc ex.β₂ ex.Δ) (min (posOr_VAL3 ((co.ε ^ 2 / 2800) ^ 2)) (posOr_VAL3 ((ci.γc /
          4000) ^ 2 / 3780))))
      sectionUp_pos := fun st ci ex co => lt_min ((U.interior ϑ sh bc).sectionUp_pos st ci ex co)
          (lt_min (T0_pos _ _ _ _ _) (lt_min (posOr_pos_VAL3 _) (posOr_pos_VAL3 _)))
      lfr29W := fun st ci ex co bd => min ((U.interior ϑ sh bc).lfr29W st ci ex co bd) (min
          (posOr_VAL3 (1 / (1000000 * ex.Δ))) (posOr_VAL3 (bd.τ * ex.Δ / 1000000000)))
      lfr29W_pos := fun st ci ex co bd => lt_min ((U.interior ϑ sh bc).lfr29W_pos st ci ex co bd)
          (lt_min (posOr_pos_VAL3 _) (posOr_pos_VAL3 _))
      endpointUp := (U.interior ϑ sh bc).endpointUp, endpointUp_pos := (U.interior ϑ sh
          bc).endpointUp_pos
      σcolUp := fun st ci ex co bd wk s => min ((U.interior ϑ sh bc).σcolUp st ci ex co bd wk s)
          (min a₂ (min threeSplittingExclusionThreshold.{0, 0} (A0 ci.γ ci.βc ci.γc ex.β₂ ex.Δ co.qe
          co.ε bd.μ bd.τ s wk.b' wk.s')))
      σcolUp_pos := fun st ci ex co bd wk s => lt_min ((U.interior ϑ sh bc).σcolUp_pos st ci ex co
          bd wk s) (lt_min ha₂ (lt_min hthr (A0_pos _ _ _ _ _ _ _ _ _ _ _ _)))
      I₁ := (U.interior ϑ sh bc).I₁, I₁_pos := (U.interior ϑ sh bc).I₁_pos
      scaleUp := fun st ci ex er => min ((U.interior ϑ sh bc).scaleUp st ci ex er) (posOr_VAL3
          (ci.γc / (1200000 * ex.Δ)))
      scaleUp_pos := fun st ci ex er => lt_min ((U.interior ϑ sh bc).scaleUp_pos st ci ex er)
          (posOr_pos_VAL3 _)
      wUp := fun st ci ex er Λ => min ((U.interior ϑ sh bc).wUp st ci ex er Λ) (W0 ci.γ ci.βc ci.γc
          ex.β₂ ex.Δ er.co.qe er.co.ε er.bd.μ er.bd.τ er.s er.wk.b' er.wk.s' er.σcol Λ)
      wUp_pos := fun st ci ex er Λ => lt_min ((U.interior ϑ sh bc).wUp_pos st ci ex er Λ) (W0_pos _
          _ _ _ _ _ _ _ _ _ _ _ _ _)
      splitUp := fun st ci ex er sc => min ((U.interior ϑ sh bc).splitUp st ci ex er sc) (min
          (posOr_VAL3 (er.s / 100000)) (min (BC ci.γ ci.βc ci.γc ex.β₂ ex.Δ) (min (B1 ci.γ ci.βc
          ci.γc ex.β₂ ex.Δ er.co.qe er.co.ε er.bd.μ er.bd.τ er.s er.wk.b' er.wk.s') (min (posOr_VAL3
          (1 / (100 * ex.Δ))) (BD ci.γ ci.βc ci.γc ex.β₂ ex.Δ er.co.qe er.co.ε er.bd.μ er.bd.τ er.s
          er.wk.b' er.wk.s' er.σcol sc.Λ sc.w)))))
      splitUp_pos := fun st ci ex er sc => lt_min ((U.interior ϑ sh bc).splitUp_pos st ci ex er sc)
          (lt_min (posOr_pos_VAL3 _) (lt_min (BC_pos _ _ _ _ _) (lt_min (B1_pos _ _ _ _ _ _ _ _ _ _
          _ _) (lt_min (posOr_pos_VAL3 _) (BD_pos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)))))
      β₁Up := fun st ci ex er sc b => min ((U.interior ϑ sh bc).β₁Up st ci ex er sc b) (BZ ci.γ
          ci.βc ci.γc ex.β₂ ex.Δ er.co.qe er.co.ε er.bd.μ er.bd.τ er.s er.wk.b' er.wk.s' er.σcol
          sc.Λ sc.w b er.co.qs er.co.ve)
      β₁Up_pos := fun st ci ex er sc b => lt_min ((U.interior ϑ sh bc).β₁Up_pos st ci ex er sc b)
          (BZ_pos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      T₀Low := fun st ci ex er sc b β₁ => max ((U.interior ϑ sh bc).T₀Low st ci ex er sc b β₁) (20 *
          LZ ci.γ ci.βc ci.γc ex.β₂ ex.Δ er.co.qe er.co.ε er.bd.μ er.bd.τ er.s er.wk.b' er.wk.s'
          er.σcol sc.Λ sc.w b er.co.qs er.co.ve (closedβV3 β₁ ex) er.co.ζ er.co.ε₀)
      lpa02V := fun _ ci ex er sc b β₁ T₀ => VV ci.γ ci.βc ci.γc ex.β₂ ex.Δ er.co.qe er.co.ε er.bd.μ
          er.bd.τ er.s er.wk.b' er.wk.s' er.σcol sc.Λ sc.w b er.co.qs er.co.ve (closedβV3 β₁ ex)
          er.co.ζ er.co.ε₀ T₀ er.co.e₀
      T₀_le_lpa02V := fun _ ci ex er sc b β₁ T₀ => VV_ge ci.γ ci.βc ci.γc ex.β₂ ex.Δ er.co.qe
          er.co.ε er.bd.μ er.bd.τ er.s er.wk.b' er.wk.s' er.σcol sc.Λ sc.w b er.co.qs er.co.ve
          (closedβV3 β₁ ex) er.co.ζ er.co.ε₀ T₀ er.co.e₀
      LmaxLow := (U.interior ϑ sh bc).LmaxLow, tailLow := (U.interior ϑ sh bc).tailLow, H :=
          (U.interior ϑ sh bc).H, H_tendsto := (U.interior ϑ sh bc).H_tendsto }
    cuspUp := U.cuspUp, cuspUp_pos := U.cuspUp_pos, cuspRadii := U.cuspRadii
    productUp := U.productUp, productUp_pos := U.productUp_pos
    tailLow := fun st ϑ sh bc v q H r => max (U.tailLow st ϑ sh bc v q H r) (TL v.circle.γ
        v.circle.βc v.circle.γc v.excl.β₂ v.excl.Δ v.err.co.qe v.err.co.ε v.err.bd.μ v.err.bd.τ
        v.err.s v.err.wk.b' v.err.wk.s' v.err.σcol v.scale.Λ v.scale.w v.split.b v.err.co.qs
        v.err.co.ve (closedβV3 v.split.β₁ v.excl) v.err.co.ζ v.err.co.ε₀ v.split.T₀ v.err.co.e₀
        v.Lmax q)
    fixedConstants := U.fixedConstants }, ?_, ?_⟩
  · exact {
      ϑUp_le := fun _ => le_rfl, shortUp_le := fun _ _ => le_rfl, bcgUp_le := fun _ _ => le_rfl,
      interior_refines := fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ => min_le_left _ _,
        min_le_left _ _, fun _ _ _ => min_le_left _ _, fun _ _ _ _ => le_max_left _ _,
        fun _ _ _ => min_le_left _ _, fun _ _ _ _ => min_le_left _ _,
        fun _ _ _ _ _ => min_le_left _ _,
        fun _ _ _ _ _ _ _ => min_le_left _ _, fun _ _ _ _ => min_le_left _ _,
        fun _ _ _ _ _ => min_le_left _ _, fun _ _ _ _ _ => min_le_left _ _,
        fun _ _ _ _ _ _ => min_le_left _ _, fun _ _ _ _ _ _ _ => le_max_left _ _,
        fun _ _ _ _ _ _ _ => le_rfl⟩,
      cuspUp_le := fun _ _ _ _ _ => le_rfl, cuspRadii_ge := fun _ _ _ _ _ _ => le_rfl,
      productUp_le := fun _ _ _ _ _ _ _ => le_rfl,
      tailLow_ge := fun _ _ _ _ _ _ _ _ => le_max_left _ _,
      fixed_subset := Finset.Subset.refl _,
      lpa02V_eq := fun _ _ _ => rfl }
  intro R
  have hΔ0 : 0 < R.later.excl.Δ := R.later.Δ_pos_VAL2
  have hγc0 : 0 < R.later.circle.γc := R.later.γc_pos
  have hε0 : 0 < R.later.err.co.ε := R.later.ε_pos
  have hτ0 : 0 < R.later.err.bd.τ := R.later.τ_pos
  have hε10 : R.later.err.co.ε < 1 / 10 ^ 10 :=
    R.later.ε_lt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hζ10 : R.later.err.co.ζ < 1 / 10 ^ 10 :=
    R.later.ζ_lt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hε8000 : R.later.err.co.ε < R.later.circle.γc / 8000 :=
    (R.later.ε_lt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))).trans_eq (posOr_eq_VAL3 (by positivity))
  have hroot : 504000 * (4000 / R.later.circle.γc) ^ 2 < R.later.excl.Δ :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans ((le_max_right _ _).trans
      (le_max_right _ _))).trans_lt R.later.Δ_gt
  have hτε : R.later.err.bd.τ < (R.later.err.co.ε ^ 2 / 2800) ^ 2 :=
    (R.later.τ_lt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _
        _).trans
      (min_le_left _ _))))).trans_eq (posOr_eq_VAL3 (by positivity))
  have hτγc : R.later.err.bd.τ < (R.later.circle.γc / 4000) ^ 2 / 3780 :=
    (R.later.τ_lt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _
        _).trans
      (min_le_right _ _))))).trans_eq (posOr_eq_VAL3 (by positivity))
  have hΛγc : R.later.scale.Λ < R.later.circle.γc / (1200000 * R.later.excl.Δ) :=
    (R.later.Λ_lt.trans_le (min_le_right _ _)).trans_eq (posOr_eq_VAL3 (by positivity))
  have hβ1 : closedβV3 R.later.split.β₁ R.later.excl 1 = R.later.split.β₁ := by simp [closedβV3]
  have hβ2 : closedβV3 R.later.split.β₁ R.later.excl 2 = R.later.excl.β₂ := by simp [closedβV3]
  have hβ3 : closedβV3 R.later.split.β₁ R.later.excl 3 = R.later.excl.β₃ := by simp [closedβV3]
  have hb100 : R.later.split.b < 1 / (100 * R.later.excl.Δ) :=
    (R.later.b_lt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans ((min_le_right _
        _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))).trans_eq
      (posOr_eq_VAL3 (by positivity))
  have h1 : C1 R.later.circle.γ := ⟨R.later.γ_pos, R.later.γ_lt.trans_le
    (((min_le_right _ _).trans (min_le_right _ _)).trans (by norm_num))⟩
  have h2 : C2 R.later.circle.γ R.later.circle.βc R.later.circle.γc := ⟨h1, R.later.βc_pos,
      R.later.βc_lt_γc_VAL2, hγc0,
    R.later.γc_lt.trans_le (min_le_right _ _)⟩
  have h3 : C3 R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      := ⟨h2, R.later.β₂_pos,
    (R.later.β₂_lt.trans_le ((min_le_left _ _).trans (min_le_right _ _))).le,
    R.later.β₂_lt_audit_VAL2.trans (by norm_num), R.later.hundred_div_β₂_lt_Δ_VAL2,
    (((le_max_left _ _).trans (le_max_right _ _)).trans ((le_max_right _ _).trans
      (le_max_right _ _))).trans R.later.Δ_gt.le⟩
  have h4 : C4 R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' := ⟨h3, ⟨R.later.qe_pos,
    (R.later.qe_lt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _
        _)))).le,
    R.later.qe_lt_one_VAL2, hε0, hε10.trans (by norm_num), R.later.μ_pos,
    (R.later.μ_lt_VAL2.trans (by norm_num)).le, hτ0,
    (R.later.τ_lt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _
        _)))).le,
    c14_tau_sqrt_FAM2b hε0 hτ0.le hτε, (hε10.trans (by norm_num)).le, R.later.μ_lt_VAL2.le⟩,
    R.later.s_pos, R.later.s_lt_audit_VAL2.trans (by norm_num), R.later.s_lt_b'_VAL2,
    R.later.s_lt_s'_VAL2,
    (R.later.b'_lt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _
        _)))).trans_eq
      (posOr_eq_VAL3 (by positivity)),
    (R.later.s'_lt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _
        _)))).trans_eq
      (posOr_eq_VAL3 (by positivity)),
    (R.later.b'_lt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _
        _)))).trans_eq
      (posOr_eq_VAL3 (by positivity)),
    (R.later.s'_lt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _
        _)))).trans_eq
      (posOr_eq_VAL3 (by positivity))⟩
  have hσlt := R.later.σcol_lt
  have h5 : C5 R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ := ⟨h4,
      ⟨R.later.σcol_pos,
    (hσlt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))).le,
    (hσlt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _))))).le,
    (hσlt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _))))).le⟩,
    R.later.Λ_pos, by linarith [R.later.regScale_two],
    by
      have h := R.later.regScale_L
      unfold closedLongLength at h
      rw [lt_div_iff₀ (by positivity)]
      nlinarith,
    (R.later.regScale_100.trans (by norm_num)).le,
    c14_staged_budget_FAM2b hγc0 hε8000 hroot hΛγc hτ0.le hτγc,
    R.later.lfr29_Λ.trans_eq (by norm_num), R.later.regScale_100.le⟩
  have h6 : C6 R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w := ⟨h5,
      R.later.w_pos,
    R.later.w_lt.trans_le ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))),
    R.later.w_lt.trans_le (min_le_right _ _)⟩
  have hblt := R.later.b_lt
  have h7 : C7 R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w
      R.later.split.b R.later.err.co.qs R.later.err.co.ve := ⟨h6, ⟨R.later.b_pos,
    (hblt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))).trans_eq
      (posOr_eq_VAL3 (by have := R.later.s_pos; positivity)),
    hblt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))),
    hblt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))),
    by
      have hb0 := R.later.b_pos
      have hb' : R.later.split.b < (100 * R.later.excl.Δ)⁻¹ := hb100.trans_eq (one_div _)
      exact (lt_inv_comm₀ (by positivity) hb0).mpr hb',
    hblt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))))⟩,
    R.later.qs_pos, R.later.qs_le_hundredth_VAL2, R.later.ve_pos⟩
  have h8 : C8 R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w
      R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3 R.later.split.β₁ R.later.excl)
      R.later.err.co.ζ R.later.err.co.ε₀ := ⟨h7, ⟨hβ2, hβ1 ▸ R.later.β₁_pos,
    hβ1 ▸ R.later.β₁_lt.trans_le ((min_le_left _ _).trans (min_le_right _ _)),
    hβ1 ▸ R.later.β₁_lt_β₂_VAL2.trans (R.later.β₂_lt_audit_VAL2.trans (by norm_num)),
    hβ3 ▸ (R.later.β₃_lt.trans_le (min_le_right _ _)).le⟩,
    hβ1 ▸ R.later.β₁_lt_ζ_VAL2, hζ10.trans (by norm_num), R.later.ε₀_pos⟩
  have h9 : C9 R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w
      R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3 R.later.split.β₁ R.later.excl)
      R.later.err.co.ζ R.later.err.co.ε₀ R.later.split.T₀ R.later.err.co.e₀ := ⟨h8,
      ⟨R.later.T₀_pos_VAL2,
    (le_max_right _ _).trans ((le_max_right _ _).trans R.later.T₀_ge)⟩,
    R.later.e₀_pos, R.later.e₀_lt_VAL2⟩
  have hCT : CT R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w
      R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3 R.later.split.β₁ R.later.excl)
      R.later.err.co.ζ R.later.err.co.ε₀ R.later.split.T₀ R.later.err.co.e₀ R.later.Lmax
      R.cuspQuality := ⟨h9, R.later.Lmax_pos_VAL2, R.cuspQuality_pos⟩
  have eER : ER R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w
      R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3 R.later.split.β₁ R.later.excl)
      R.later.err.co.ζ R.later.err.co.ε₀ = εr R.later.circle.γ R.later.circle.βc R.later.circle.γc
      R.later.excl.β₂ R.later.excl.Δ R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ
      R.later.err.bd.τ R.later.err.s R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol
      R.later.scale.Λ R.later.scale.w R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3
      R.later.split.β₁ R.later.excl) R.later.err.co.ζ R.later.err.co.ε₀ h8 := dite_eq_left h8
  have eDP : DP R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w
      R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3 R.later.split.β₁ R.later.excl)
      R.later.err.co.ζ R.later.err.co.ε₀ = δ' R.later.circle.γ R.later.circle.βc R.later.circle.γc
      R.later.excl.β₂ R.later.excl.Δ R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ
      R.later.err.bd.τ R.later.err.s R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol
      R.later.scale.Λ R.later.scale.w R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3
      R.later.split.β₁ R.later.excl) R.later.err.co.ζ R.later.err.co.ε₀ h8 := dite_eq_left h8
  have eLZ : LZ R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w
      R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3 R.later.split.β₁ R.later.excl)
      R.later.err.co.ζ R.later.err.co.ε₀ = Λ' R.later.circle.γ R.later.circle.βc R.later.circle.γc
      R.later.excl.β₂ R.later.excl.Δ R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ
      R.later.err.bd.τ R.later.err.s R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol
      R.later.scale.Λ R.later.scale.w R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3
      R.later.split.β₁ R.later.excl) R.later.err.co.ζ R.later.err.co.ε₀ h8 := dite_eq_left h8
  have eDD : DD R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w
      R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3 R.later.split.β₁ R.later.excl)
      R.later.err.co.ζ R.later.err.co.ε₀ R.later.split.T₀ R.later.err.co.e₀ = δ R.later.circle.γ
      R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ R.later.err.co.qe
      R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s R.later.err.wk.b'
      R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w R.later.split.b
      R.later.err.co.qs R.later.err.co.ve (closedβV3 R.later.split.β₁ R.later.excl) R.later.err.co.ζ
      R.later.err.co.ε₀ R.later.split.T₀ R.later.err.co.e₀ h9 := dite_eq_left h9
  have eV : R.later.split.V = V R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂
      R.later.excl.Δ R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ
      R.later.err.s R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ
      R.later.scale.w R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3
      R.later.split.β₁ R.later.excl) R.later.err.co.ζ R.later.err.co.ε₀ R.later.split.T₀
      R.later.err.co.e₀ h9 := R.later.V_eq.trans (dite_eq_left h9)
  have eTL : TL R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w
      R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3 R.later.split.β₁ R.later.excl)
      R.later.err.co.ζ R.later.err.co.ε₀ R.later.split.T₀ R.later.err.co.e₀ R.later.Lmax
      R.cuspQuality = TLd R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂
      R.later.excl.Δ R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ
      R.later.err.s R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ
      R.later.scale.w R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3
      R.later.split.β₁ R.later.excl) R.later.err.co.ζ R.later.err.co.ε₀ R.later.split.T₀
      R.later.err.co.e₀ R.later.Lmax R.cuspQuality hCT :=
    dite_eq_left hCT
  simp only [PartialBoundaryFamilyOnSeqV3_BQ2]
  refine ⟨eER ▸ hεr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h8, eER ▸ hεr4 _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ h8, eER ▸ hεrcap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h8,
    eDP ▸ hδ' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h8, eLZ ▸ hΛ' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ h8, le_max_right _ _,
    eDD ▸ hδ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h9, eDD ▸ eDP ▸ hδδ' _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _ _ h9, fun n hn => ?_⟩
  have hmT : TLd R.later.circle.γ R.later.circle.βc R.later.circle.γc R.later.excl.β₂ R.later.excl.Δ
      R.later.err.co.qe R.later.err.co.ε R.later.err.bd.μ R.later.err.bd.τ R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.σcol R.later.scale.Λ R.later.scale.w
      R.later.split.b R.later.err.co.qs R.later.err.co.ve (closedβV3 R.later.split.β₁ R.later.excl)
      R.later.err.co.ζ R.later.err.co.ε₀ R.later.split.T₀ R.later.err.co.e₀ R.later.Lmax
      R.cuspQuality hCT ≤ n :=
    (le_of_eq eTL.symm).trans ((le_max_right _ _).trans (R.tail_ge.trans hn))
  have hOut := hTLd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hCT n hmT
  rw [eER, eLZ, eDD, eV]
  exact hOut

/-- **The frozen per-sequence boundary supply** (frozen target (b); review 54 §6.2, the validity
bridge): as `exists_boundary_sequence_realization_core_BQ3`, and the realizing strategy carries the
partial validity for the SAME early data `D` whenever the request strategy `U` does. -/
theorem exists_boundary_sequence_supply_BQ3 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ δStar : ℝ, 0 < δStar ∧ ∀ D : BoundaryEarlyData, D.δStar ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K
          (boundaryCounterexampleRatio D.δStar (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio D.δStar (n + 1)) ∧
          curvatureDerivativesControlled (g n) K A
            (boundaryCounterexampleRatio D.δStar (n + 1))) →
        ∃ P : BoundaryProducerOutputs_BQ2 D, ∀ U : BoundaryThresholdsV2 D,
          PartialBoundaryThresholdValidityV3_BQ2 K D U →
          ∃ T : BoundaryThresholdsV2 D,
            BoundaryStrategyRefinesV3_BQ2 T (U.withV_BQ2 P.VF P.T₀_le_VF) ∧
            PartialBoundaryThresholdValidityV3_BQ2 K D T ∧
            PartialBoundaryFamilyAtSeqV3_BQ2 K A W g B T P := by
  obtain ⟨δS, hδS, h⟩ := exists_boundary_sequence_realization_core_BQ3 K hK A hA
  refine ⟨δS, hδS, fun D hD W _ g B hs => ?_⟩
  obtain ⟨P, hP⟩ := h D hD W g B hs
  refine ⟨P, fun U hv => ?_⟩
  obtain ⟨T, hT, hF⟩ := hP U
  exact ⟨T, hT, hv.of_withV_refines_BQ2 hT, hF⟩

/-- **Consumer (sourced early data)**: below both thresholds (the producer's and BSA01's), the
early data with sources `boundaryEarlyDataSrc_BQ2 K δ` carries, on every boundary standing
sequence at `δ`, a VALID strategy realizing the per-sequence family (request strategy
`boundaryThresholdsSrc_BQ2`). -/
theorem exists_sourced_boundary_sequence_supply_BQ3 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ,
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ (n + 1)) ∧
          curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ (n + 1))) →
        ∃ P : BoundaryProducerOutputs_BQ2 (boundaryEarlyDataSrc_BQ2 K δ hδ),
        ∃ T : BoundaryThresholdsV2 (boundaryEarlyDataSrc_BQ2 K δ hδ),
          PartialBoundaryThresholdValidityV3_BQ2 K (boundaryEarlyDataSrc_BQ2 K δ hδ) T ∧
          PartialBoundaryFamilyAtSeqV3_BQ2 K A W g B T P := by
  obtain ⟨δS, hδS, h⟩ := exists_boundary_sequence_supply_BQ3 K hK A hA
  obtain ⟨δB, hδB, hsrc⟩ := exists_sourced_boundaryEarlyData_BQ2 K
  refine ⟨min δS δB, lt_min hδS hδB, fun W _ g B hs => ?_⟩
  obtain ⟨P, hP⟩ := h (boundaryEarlyDataSrc_BQ2 K _ (lt_min hδS hδB)) (min_le_left _ _) W g B hs
  obtain ⟨T, -, hv, hF⟩ := hP _ (hsrc _ (lt_min hδS hδB) (min_le_right _ _))
  exact ⟨P, T, hv, hF⟩

/-- **Consumer (one realized register)**: on every boundary standing sequence at the sourced
threshold, a valid realizing strategy, one staged register at it and a tail on which every member
carries T3B-R's export packet with `packet.cusp = B n` at the register's cusp tolerance. -/
theorem exists_realized_boundaryRegister_BQ3 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ,
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ (n + 1)) ∧
          curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ (n + 1))) →
        ∃ T : BoundaryThresholdsV2 (boundaryEarlyDataSrc_BQ2 K δ hδ),
          PartialBoundaryThresholdValidityV3_BQ2 K (boundaryEarlyDataSrc_BQ2 K δ hδ) T ∧
          ∃ R : BoundaryRegisterV2 (boundaryEarlyDataSrc_BQ2 K δ hδ) T, ∃ N : ℕ, R.tail ≤ N ∧
            ∀ n : ℕ, N ≤ n →
              ∃ Pk : BoundaryExportPacket (W n) (g n) K A (boundaryCounterexampleRatio δ (n + 1))
                (cuspTolerance_BCUSP1 (closedβV3 R.later.split.β₁ R.later.excl 1) R.cuspQuality
                  R.cuspQuality), Pk.cusp = B n := by
  obtain ⟨δ, hδ, h⟩ := exists_sourced_boundary_sequence_supply_BQ3 K hK A hA
  refine ⟨δ, hδ, fun W _ g B hs => ?_⟩
  obtain ⟨P, T, hv, hF⟩ := h W g B hs
  obtain ⟨R⟩ := exists_boundaryRegisterV2 _ T
  obtain ⟨N, hN, -, hn⟩ := hF.exists_tail_BQ2 R
  exact ⟨T, hv, R, N, hN, hn⟩

end DifferentialGeometry.Geometry.Collapse
