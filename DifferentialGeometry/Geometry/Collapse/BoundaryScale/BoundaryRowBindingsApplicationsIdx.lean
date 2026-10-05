import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryRowBindingsIdx

/-!
# Consumers of the index-shifted BSA04 / BSA06 sequence forms (lane BDRY-IDX4)

The accepted consumers `bsa04_standing_eventually` and `bsa06_scaled_ball_interior_eventually`
(`BoundaryRowBindingsApplications.lean`) take a counterexample sequence at `δ_n` for ALL `n`, an
EMPTY hypothesis (`δ_0 = 0`; lane FC39-BQ, `isEmpty_boundarySequence_ratio_IDX`). Restated on
sequences at `δ_{n+1}` (BBR03's sequence), proofs re-run on lane BDRY-IDX3's
`bsa04_row_counterexample_IDX` / `bsa06_row_eventually_IDX` (index changes only; `α = n` kept):

* `bsa04_standing_eventually_IDX4`: the standing inequality at every point on a tail (BSA04.a);
* `bsa06_scaled_ball_interior_eventually_IDX4`: for a fixed buffer `b`, on one tail every scaled
  ball `B(p, b ρ_n(p))` at a center with `d > 10` lies in the interior (BSA06 exhaustion).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- BSA04.a consumer, index-shifted (lane BDRY-IDX4): along the counterexample ratios `δ_{n+1}`
(BBR03's sequence; the accepted statement at `δ_n` is vacuous at `n = 0`), the standing inequality
with `α = n` holds at every point on a tail. -/
theorem bsa04_standing_eventually_IDX4 :
    ∃ δStar > 0, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar → ∀ (K : ℕ), 2 ≤ K → ∀ (A : ℝ → ℝ)
      (W : ℕ → CompactCarrier.{u}) (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier),
      (∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))) →
      (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
      (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) →
      ∀ᶠ n : ℕ in atTop, ∀ p : (W n).Carrier,
        ENNReal.ofReal (2 * n * firstVolumeScale (g n) p (n : ℝ)⁻¹) <
          curvatureRadius (g n) p := by
  obtain ⟨δS, hδS, h4⟩ := bsa04_row_counterexample_IDX.{u}
  refine ⟨δS, hδS, ?_⟩
  intro δ₀ hδ₀ hδ₀S K hK A W g B hcoll hder
  filter_upwards [eventually_ge_atTop 3] with n hn p
  exact (h4 hδ₀ hδ₀S K hK A W g B hcoll hder n hn p).1

/-- BSA06 consumer, index-shifted (lane BDRY-IDX4): for a fixed buffer `b`, on one tail of a
counterexample sequence at `δ_{n+1}` (BBR03's sequence) every scaled ball `B(p, b ρ_n(p))` at a
center with `d(p, ∂W) > 10` lies in the interior. -/
theorem bsa06_scaled_ball_interior_eventually_IDX4 :
    ∃ δStar > 0, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar → ∀ (K : ℕ), 2 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ (W : ℕ → CompactCarrier.{u}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier),
        (∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) →
        ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < euclideanThreeUnitBallVolume / 4 → ∀ b : ℝ,
          ∃ ρ : ∀ n, (W n).Carrier → ℝ, ∀ᶠ n : ℕ in atTop, (∀ p, 0 < ρ n p) ∧
            ∀ p : (W n).Carrier, ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) p →
              riemannianBallOf (g n) p (b * ρ n p) ⊆ (W n).model.interior (W n).Carrier := by
  obtain ⟨δS, hδS, h6⟩ := bsa06_row_eventually_IDX.{u}
  refine ⟨δS, hδS, ?_⟩
  intro δ₀ hδ₀ hδ₀S K hK A hA W _ g B hcoll hder Λ w hΛ hw hwc b
  obtain ⟨ρ, hev, -⟩ := h6 hδ₀ hδ₀S K hK A hA W g B hcoll hder hΛ hw hwc
  refine ⟨ρ, ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * b)
  filter_upwards [hev, eventually_ge_atTop N] with n hn hnN
  obtain ⟨hpos, -, -, -, hcl⟩ := hn
  refine ⟨hpos, fun p hp => ((hcl p).2.2.2.2 hp).2 b ?_⟩
  have : (N : ℝ) ≤ n := by exact_mod_cast hnN
  linarith

end DifferentialGeometry.Geometry.Collapse
