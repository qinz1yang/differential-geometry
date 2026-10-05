import DifferentialGeometry.Geometry.Collapse.BoundarySequenceRealization
import DifferentialGeometry.Geometry.Collapse.BoundaryPacketRestBFR
import DifferentialGeometry.Geometry.Collapse.BoundaryMemberModelV2

/-!
# The per-sequence boundary analytic supply on universe-`u` sequences, PROVED (lane FC39-BQ3)

External review 54, §5 (d) and §7 (dispositions rows 5–7, work item 2): items (c) and (h) of the V2
boundary targets file (`build-logs/scratch/FC39-BQ3/TargetsBoundaryV2.lean`) in production.

* `BoundaryAnalyticSupplyV3_BQ3 K A D W g B` — (c): for a universe-`u` boundary standing sequence
  at `D.δStar` (member `n` at `δ_{n+1}`), universe-`0` boundary models of EVERY member with both
  transport groups (`BoundaryModelV2_BQ3`, chosen first, review 54 §7), a strategy valid for `D`
  (FC39-BQ2's V3 validity), the producer's outputs fixed before the strategy, and the per-sequence
  family on the MODEL sequence. (Strengthening of the scratch (c): the models are V2.)
* `BoundarySupplyV3_BQ3 K A` — ONE early data and such a package for every boundary standing
  sequence at its `δ⋆`.
* `boundarySupplyV3_holds_BQ3` — (h), PROVED: from FC39-BQ3 G1's sourced supply
  (`exists_sourced_boundary_sequence_supply_BQ3`, frozen targets (a), (b)) and G2's models for the
  whole sequence (`exists_boundaryModelsV2_standing_BQ3`, target (h1)); the producer is called ONCE
  on the model sequence.
* Consumers: `BoundaryAnalyticSupplyV3_BQ3.exists_packet_rest_BQ3` (at every register, on a tail:
  THE export packet on the model of member `n` with `packet.cusp = B₀` and T3B-R's rest for it at
  the register's values and the producer's witnesses — the packet fields of FC39-BQ2's
  `BoundaryRowsAtBFR_BQ2`), `BoundaryAnalyticSupplyV3_BQ3.standing_models_BQ3` (the standing
  hypotheses hold on the model sequence).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- **(c) The per-sequence boundary analytic supply** on a universe-`u` boundary standing sequence:
universe-`0` models of EVERY member with both transport groups (chosen first, review 54 §7), a
strategy valid for `D`, the producer's outputs and the per-sequence family on the model sequence. -/
structure BoundaryAnalyticSupplyV3_BQ3 (K : ℕ) (A : ℝ → ℝ) (D : BoundaryEarlyData)
    (W : ℕ → CompactCarrier.{u}) (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
    (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio D.δStar (n + 1)))
    where
  /-- The universe-`0` models of the members, for the whole sequence. -/
  models : ∀ n, BoundaryModelV2_BQ3 (W n) (g n) (B n)
  /-- The strategy. -/
  thresholds : BoundaryThresholdsV2 D
  /-- It is valid for the early data `D` (V3 validity, review 54 §6.2). -/
  valid : PartialBoundaryThresholdValidityV3_BQ2 K D thresholds
  /-- The producer's outputs, fixed before the strategy (review 54 §6.3). -/
  outputs : BoundaryProducerOutputs_BQ2 D
  /-- The per-sequence family on the model sequence. -/
  family : @PartialBoundaryFamilyAtSeqV3_BQ2 K A D (fun n => (models n).W₀)
    (fun n => (models n).connected₀) (fun n => (models n).g₀) (fun n => (models n).B₀) thresholds
    outputs

/-- **(c) The boundary supply**: ONE early data, and for every universe-`u` boundary standing
sequence at its `δ⋆` an analytic supply package. -/
def BoundarySupplyV3_BQ3 (K : ℕ) (A : ℝ → ℝ) : Prop :=
  ∃ D : BoundaryEarlyData,
    ∀ (W : ℕ → CompactCarrier.{u}) [∀ n, ConnectedSpace (W n).Carrier]
      (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
      (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K
        (boundaryCounterexampleRatio D.δStar (n + 1))),
      (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio D.δStar (n + 1)) ∧
        curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio D.δStar (n + 1))) →
      Nonempty (BoundaryAnalyticSupplyV3_BQ3 K A D W g B)

/-- **(h) THE BOUNDARY SUPPLY HOLDS** (every universe): the sourced early data below both
thresholds, the request strategy refined by the realization, the models of the whole sequence
chosen first and the producer called once on the model sequence. -/
theorem boundarySupplyV3_holds_BQ3 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    BoundarySupplyV3_BQ3.{u} K A := by
  obtain ⟨δ, hδ, h⟩ := exists_sourced_boundary_sequence_supply_BQ3 K hK A hA
  refine ⟨boundaryEarlyDataSrc_BQ2 K δ hδ, fun W _ g B hs => ?_⟩
  obtain ⟨M, hM⟩ := exists_boundaryModelsV2_standing_BQ3 K A _ W g B hs
  have : ∀ n, ConnectedSpace (M n).W₀.Carrier := fun n => (M n).connected₀
  obtain ⟨P, T, hv, hF⟩ := h (fun n => (M n).W₀) (fun n => (M n).g₀) (fun n => (M n).B₀) hM
  exact ⟨{ models := M, thresholds := T, valid := hv, outputs := P, family := hF }⟩

namespace BoundaryAnalyticSupplyV3_BQ3

variable {K : ℕ} {A : ℝ → ℝ} {D : BoundaryEarlyData} {W : ℕ → CompactCarrier.{u}}
  {g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier}
  {B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio D.δStar (n + 1))}

/-- **Consumer**: the standing hypotheses of the members hold on the model sequence of a package
(G2's analytic transport). -/
theorem standing_models_BQ3 (S : BoundaryAnalyticSupplyV3_BQ3 K A D W g B)
    (hs : ∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio D.δStar (n + 1)) ∧
      curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio D.δStar (n + 1)))
    (n : ℕ) :
    boundaryVolumeCollapsed (S.models n).W₀ (S.models n).g₀
        (boundaryCounterexampleRatio D.δStar (n + 1)) ∧
      curvatureDerivativesControlled (S.models n).g₀ K A
        (boundaryCounterexampleRatio D.δStar (n + 1)) :=
  ⟨BoundaryModel.boundaryVolumeCollapsed_iff_BQ3.mpr (hs n).1,
    BoundaryModel.curvatureDerivativesControlled_iff_BQ3.mpr (hs n).2⟩

/-- **Consumer (the packet fields of the rows record)**: at every register of the package's
strategy, on a tail of the sequence, THE export packet on the model of member `n` with
`packet.cusp = B₀` and T3B-R's rest for it, at the register's values and the producer's witnesses
`εr, Λz, δ` — exactly the `packet`, `packet_cusp`, `rest` fields of `BoundaryRowsAtBFR_BQ2` with
`model := (S.models n).toBoundaryModel`. -/
theorem exists_packet_rest_BQ3 (S : BoundaryAnalyticSupplyV3_BQ3 K A D W g B)
    (R : BoundaryRegisterV2 D S.thresholds) :
    ∃ N : ℕ, R.tail ≤ N ∧ ∀ n : ℕ, N ≤ n →
      letI := (S.models n).connected₀
      ∃ Pk : BoundaryExportPacket (S.models n).W₀ (S.models n).g₀ K A
          (boundaryCounterexampleRatio D.δStar (n + 1))
          (cuspTolerance_BCUSP1 (closedβV3 R.later.split.β₁ R.later.excl 1) R.cuspQuality
            R.cuspQuality),
        Pk.cusp = (S.models n).B₀ ∧
        BoundaryPacketRestBFR_BQ2 (S.models n).W₀ (S.models n).g₀ K A
          (boundaryCounterexampleRatio D.δStar (n + 1)) ((n + 1 : ℕ) : ℝ) R.later.scale.Λ
          R.later.scale.w (closedβV3 R.later.split.β₁ R.later.excl) R.later.excl.Δ
          R.later.err.co.qs R.later.err.co.qe R.later.err.bd.μ R.later.split.b R.later.err.s
          R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc
          R.later.circle.βc R.later.Lmax R.later.err.bd.τ R.later.circle.γ
          (S.outputs.δF R.stage R.later.circle R.later.excl R.later.err R.later.scale
            R.later.split.b R.later.split.β₁ R.later.split.T₀)
          (S.outputs.εrF R.stage R.later.circle R.later.excl R.later.err R.later.scale
            R.later.split.b R.later.split.β₁)
          R.later.err.co.e₀ R.later.split.T₀ R.later.split.V R.later.err.co.ve R.later.err.co.ζ
          (S.outputs.ΛzF R.stage R.later.circle R.later.excl R.later.err R.later.scale
            R.later.split.b R.later.split.β₁)
          R.cuspQuality R.cuspQuality Pk := by
  obtain ⟨-, -, -, -, -, -, -, -, hn⟩ := S.family R
  refine ⟨R.tail, le_rfl, fun n hN => ?_⟩
  have : ConnectedSpace (S.models n).W₀.Carrier := (S.models n).connected₀
  exact boundaryPacketsOutBFR_iff_rest_BQ2.mp (hn n hN)

end BoundaryAnalyticSupplyV3_BQ3

end DifferentialGeometry.Geometry.Collapse
