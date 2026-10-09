import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterV2SequenceSupply

/-!
# The per-sequence boundary family with the cusp norm error tied to the register (lane FC39-BQ)

`PartialBoundaryFamilyAtSeqV2_BQ` (`BoundaryRegisterV2SequenceSupply.lean`, kept as history) asks
for EVERY positive norm error `εN` against the register's tail; T3B's tail depends on `εN` (its cusp
certificates), so that form is stronger than the producer. BBR01's BR24 (B:10458–10465) chooses the
cusp splitting quality and its adapted/norm error together, after `V`, below the requested margins,
and BR25 takes the tail after them. The register `BoundaryRegisterV2` records one cusp quality, so
both cusp requests are read from it:

* `PartialBoundaryFamilyAtSeqTied_BQ K A W g B T` — prefix witness functions `εr, δ', Λz` of the
  register prefix and, on every register at `T`, `PartialBoundaryFamilyOnSeqV2_BQ` at
  `βd = εN = R.cuspQuality` (PARTIAL, as its predecessor).
* Consumer `PartialBoundaryFamilyAtSeqV2_BQ.toTied_BQ` (the old form implies the new one) and
  `PartialBoundaryFamilyAtSeqTied_BQ.exists_tail_BQ` (one tail per register with the export packet
  on every later member).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

/-- **The per-sequence boundary family on every staged register at `T`, cusp requests tied to the
register** (PARTIAL). -/
def PartialBoundaryFamilyAtSeqTied_BQ (K : ℕ) (A : ℝ → ℝ) {δStar : ℝ}
    (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
    (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
    (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δStar (n + 1)))
    {D : BoundaryEarlyData} (T : BoundaryThresholdsV2 D) : Prop :=
  ∃ εrF δ'F ΛzF : ClosedStage D.toClosedEarlyData → ClosedCircleRequestsV2 → ClosedExclusions →
      ClosedErrorsV2 → ClosedScales → ℝ → ℝ → ℝ,
    ∀ R : BoundaryRegisterV2 D T,
      PartialBoundaryFamilyOnSeqV2_BQ K A W g B R R.cuspQuality R.cuspQuality
        (εrF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
          R.later.split.β₁)
        (δ'F R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
          R.later.split.β₁)
        (ΛzF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
          R.later.split.β₁)

variable {K : ℕ} {A : ℝ → ℝ} {δStar : ℝ} {W : ℕ → CompactCarrier.{0}}
  [∀ n, ConnectedSpace (W n).Carrier] {g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier}
  {B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δStar (n + 1))}
  {D : BoundaryEarlyData} {T : BoundaryThresholdsV2 D}

/-- **Consumer**: the untied form (every norm error) gives the tied form. -/
theorem PartialBoundaryFamilyAtSeqV2_BQ.toTied_BQ
    (h : PartialBoundaryFamilyAtSeqV2_BQ K A W g B T) :
    PartialBoundaryFamilyAtSeqTied_BQ K A W g B T := by
  obtain ⟨εrF, δ'F, ΛzF, h⟩ := h
  exact ⟨εrF, δ'F, ΛzF, fun R => h R R.cuspQuality R.cuspQuality_pos⟩

/-- **Consumer (wrapper (6) shape, per sequence)**: at every register, one tail `N ≥ R.tail` with
T3B-R's export packet `P.cusp = B n` on every later member. -/
theorem PartialBoundaryFamilyAtSeqTied_BQ.exists_tail_BQ
    (h : PartialBoundaryFamilyAtSeqTied_BQ K A W g B T) (R : BoundaryRegisterV2 D T) :
    ∃ N : ℕ, R.tail ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∃ P : BoundaryExportPacket (W n) (g n) K A (boundaryCounterexampleRatio δStar (n + 1))
        (cuspTolerance_BCUSP1 (closedβV3 R.later.split.β₁ R.later.excl 1) R.cuspQuality
          R.cuspQuality), P.cusp = B n := by
  obtain ⟨εrF, δ'F, ΛzF, h⟩ := h
  exact (h R).exists_tail_BQ

end DifferentialGeometry.Geometry.Collapse
