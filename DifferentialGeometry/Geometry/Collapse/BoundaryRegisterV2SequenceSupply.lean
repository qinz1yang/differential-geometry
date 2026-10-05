import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterV2SequenceValidity
import DifferentialGeometry.Geometry.Collapse.BoundaryPacketsOutBFRSeq

/-!
# The per-sequence boundary family at a staged register (lane FC39-BQ; review 52 R-c, route 2)

The member part of the boundary supply, on ONE boundary standing sequence (BBR03, B:10624–10625:
member `n` at the ratio `δ_{n+1}`, as `exists_boundary_counterexample_sequence_of_no_threshold`), at
the staged boundary register `BoundaryRegisterV2` (BBR01), on the final boundary family
`LocalPacketsOnBFR` (T3B-R's per-member conclusion `BoundaryPacketsOutBFR_BQ`):

* `PartialBoundaryFamilyOnSeqV2_BQ K A W g B R βd εN εr δ' Λz` — the prefix witnesses
  `εr < 1/4`, `εr < cap`, `δ' > 0`, `Λz > 0` with `20 Λz ≤ T₀Low` of the register's prefix, one cone
  error `δ < δ'`, and on EVERY member `n ≥ R.tail` of the sequence T3B-R's per-member conclusion at
  the register's values (BR20–BR23, B:10452–10455: `V` is the register's, `T = T₀`; BR25: the
  register's tail) with BCP04.a at the member's counterexample index `n + 1`;
* `PartialBoundaryFamilyAtSeqV2_BQ K A W g B T` — prefix witness FUNCTIONS (as on the closed side,
  `PartialClosedFamilyAtV2`) and the chain on every register at `T`, with the cusp request
  `βd := R.cuspQuality` (BR24, B:10458–10465: the cusp splitting quality, chosen after `V`) and
  every positive norm error `εN`.

PARTIAL (the name says so): the universe-`u` lift of the sequence (`BoundaryModel`) and the joint
LPA02 witness are not part of it; boundary-slot `Out`s are open. The supply statement that produces
it for every standing sequence is frozen in `build-logs/resume/sheet-FC39-BQ.md` §2 and elaborates
in `build-logs/scratch/FC39-BQ/TargetsBQ.lean`.

Consumers: `PartialBoundaryFamilyOnSeqV2_BQ.exists_tail_BQ` (one tail `N ≥ R.tail` with the Out on
every member, wrapper (6) shape per sequence), `PartialBoundaryFamilyOnSeqV2_BQ.ratio_le_BQ`
(`δ_{n+1} ≤ βd²/1000` on the tail, T3B's cusp-tolerance clause).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

/-- **The per-sequence boundary family at one staged register** (PARTIAL): prefix witnesses, one
cone error `δ < δ'`, and T3B-R's per-member conclusion on every member of the register's tail. -/
def PartialBoundaryFamilyOnSeqV2_BQ (K : ℕ) (A : ℝ → ℝ) {δStar : ℝ}
    (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
    (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
    (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δStar (n + 1)))
    {D : BoundaryEarlyData} {T : BoundaryThresholdsV2 D} (R : BoundaryRegisterV2 D T)
    (βd εN εr δ' Λz : ℝ) : Prop :=
  0 < εr ∧ εr < 1 / 4 ∧ εr < R.later.err.co.ε₀ ∧ 0 < δ' ∧ 0 < Λz ∧
    20 * Λz ≤ (T.toClosed R.ϑ R.shortErr R.bcgErr).T₀Low R.stage R.later.circle R.later.excl
      R.later.err R.later.scale R.later.split.b R.later.split.β₁ ∧
    ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ n : ℕ, R.tail ≤ n →
      BoundaryPacketsOutBFR_BQ (W n) (g n) K A (boundaryCounterexampleRatio δStar (n + 1)) (B n)
        ((n + 1 : ℕ) : ℝ) R.later.scale.Λ R.later.scale.w
        (closedβV3 R.later.split.β₁ R.later.excl) R.later.excl.Δ R.later.err.co.qs
        R.later.err.co.qe R.later.err.bd.μ R.later.split.b R.later.err.s R.later.err.wk.b'
        R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc R.later.circle.βc R.later.Lmax
        R.later.err.bd.τ R.later.circle.γ δ εr R.later.err.co.e₀ R.later.split.T₀
        R.later.split.V R.later.err.co.ve R.later.err.co.ζ Λz βd εN

/-- **The per-sequence boundary family on every staged register at `T`** (PARTIAL): prefix witness
functions `εr, δ', Λz` of `(stage, circle, exclusions, errors, scales, b, β₁)`, and for every
register and every positive norm error the chain at the cusp request `βd = R.cuspQuality`. -/
def PartialBoundaryFamilyAtSeqV2_BQ (K : ℕ) (A : ℝ → ℝ) {δStar : ℝ}
    (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
    (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
    (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δStar (n + 1)))
    {D : BoundaryEarlyData} (T : BoundaryThresholdsV2 D) : Prop :=
  ∃ εrF δ'F ΛzF : ClosedStage D.toClosedEarlyData → ClosedCircleRequestsV2 → ClosedExclusions →
      ClosedErrorsV2 → ClosedScales → ℝ → ℝ → ℝ,
    ∀ (R : BoundaryRegisterV2 D T) (εN : ℝ), 0 < εN →
      PartialBoundaryFamilyOnSeqV2_BQ K A W g B R R.cuspQuality εN
        (εrF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
          R.later.split.β₁)
        (δ'F R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
          R.later.split.β₁)
        (ΛzF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
          R.later.split.β₁)

namespace PartialBoundaryFamilyOnSeqV2_BQ

variable {K : ℕ} {A : ℝ → ℝ} {δStar : ℝ} {W : ℕ → CompactCarrier.{0}}
  [∀ n, ConnectedSpace (W n).Carrier] {g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier}
  {B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δStar (n + 1))}
  {D : BoundaryEarlyData} {T : BoundaryThresholdsV2 D} {R : BoundaryRegisterV2 D T}
  {βd εN εr δ' Λz : ℝ}

/-- **Consumer (wrapper (6) shape, per sequence)**: one tail `N ≥ R.tail` with the export packet
`P.cusp = B n` of T3B-R on every member `n ≥ N`. -/
theorem exists_tail_BQ (h : PartialBoundaryFamilyOnSeqV2_BQ K A W g B R βd εN εr δ' Λz) :
    ∃ N : ℕ, R.tail ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∃ P : BoundaryExportPacket (W n) (g n) K A (boundaryCounterexampleRatio δStar (n + 1))
        (cuspTolerance_BCUSP1 (closedβV3 R.later.split.β₁ R.later.excl 1) βd εN), P.cusp = B n := by
  obtain ⟨-, -, -, -, -, -, δ, -, -, hn⟩ := h
  exact ⟨R.tail, le_rfl, fun n hN => by
    obtain ⟨P, hP, -⟩ := hn n hN
    exact ⟨P, hP⟩⟩

/-- **Consumer**: on the register's tail the member's ratio is below T3B's cusp tolerance
`βd²/1000`. -/
theorem ratio_le_BQ (h : PartialBoundaryFamilyOnSeqV2_BQ K A W g B R βd εN εr δ' Λz) (n : ℕ)
    (hn : R.tail ≤ n) : boundaryCounterexampleRatio δStar (n + 1) ≤ βd ^ 2 / 1000 := by
  obtain ⟨-, -, -, -, -, -, δ, -, -, hseq⟩ := h
  obtain ⟨P, -, hle, -⟩ := hseq n hn
  exact hle

end PartialBoundaryFamilyOnSeqV2_BQ

end DifferentialGeometry.Geometry.Collapse
