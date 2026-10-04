import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryRowBindings

/-!
# Consumers of the chapter 14 boundary row bindings

* `bsa01_curvatureRadius_le_thirteen_of_near`: on a connected carrier, every point within `10` of
  the boundary has curvature scale in `[1, 13]` (BSA01 localisation, (b) and (c)).
* `bsa04_standing_eventually`: the standing inequality at every point on a tail of the
  counterexample sequence (BSA04.a, filter form).
* `bsa06_scaled_ball_interior_eventually`: for a fixed buffer `b`, on one tail every scaled ball
  `B(p, b ρ_n(p))` at a center with `d > 10` lies in the interior (BSA06 exhaustion).
* `bcp05a_zeroBall_radius_lt_hundredth`: with `n > 300 V`, a zero ball meeting a collar at height
  `≤ 98` has radius `< 1/100` (the choice of `n` in the proof of BCP05).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- BSA01 consumer: on a connected carrier with nearly cuspidal boundary (`K ≥ 2`, small `δ`),
every point within `10` of the boundary has `1 ≤ R_p ≤ 13`. -/
theorem bsa01_curvatureRadius_le_thirteen_of_near :
    ∃ δStar > 0, ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (δ : ℝ), 2 ≤ K → 0 ≤ δ →
      δ ≤ δStar → NearlyCuspidalBoundary W g K δ → ∀ p,
        distanceToBoundary W g p ≤ ENNReal.ofReal 10 →
          1 ≤ curvatureRadius g p ∧ curvatureRadius g p ≤ ENNReal.ofReal 13 := by
  obtain ⟨δS, hδS, h1⟩ := bsa01_clauses_except_II.{u}
  refine ⟨δS, hδS, ?_⟩
  intro W _ g K δ hK hδ0 hδ B p hp
  obtain ⟨-, -, hball, hloc, hc, -, -⟩ := h1 W g K δ hK hδ0 hδ B
  obtain ⟨i, x, z₁, hz0, hz11, hpx⟩ := hloc p hp
  have hz : (x, halfSpaceOneLift z₁).2.val 0 ≤ 96 := by
    change max z₁ 0 ≤ 96
    exact max_le (by linarith) (by norm_num)
  have hR1 := (hball i _ hz).2.2.1
  rw [hpx] at hR1
  refine ⟨hR1, ((hc ‹_› p).2).trans ?_⟩
  calc distanceToBoundary W g p + ENNReal.ofReal 3
      ≤ ENNReal.ofReal 10 + ENNReal.ofReal 3 := by gcongr
    _ = ENNReal.ofReal 13 := by
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num

/-- BSA04.a consumer: along the counterexample ratios, the standing inequality holds at every
point on a tail. -/
theorem bsa04_standing_eventually :
    ∃ δStar > 0, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar → ∀ (K : ℕ), 2 ≤ K → ∀ (A : ℝ → ℝ)
      (W : ℕ → CompactCarrier.{u}) (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier),
      (∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ n)) →
      (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ n)) →
      (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ n)) →
      ∀ᶠ n : ℕ in atTop, ∀ p : (W n).Carrier,
        ENNReal.ofReal (2 * n * firstVolumeScale (g n) p (n : ℝ)⁻¹) <
          curvatureRadius (g n) p := by
  obtain ⟨δS, hδS, h4⟩ := bsa04_row_counterexample.{u}
  refine ⟨δS, hδS, ?_⟩
  intro δ₀ hδ₀ hδ₀S K hK A W g B hcoll hder
  filter_upwards [eventually_ge_atTop 3] with n hn p
  exact (h4 hδ₀ hδ₀S K hK A W g B hcoll hder n hn p).1

/-- BSA06 consumer: for a fixed buffer `b`, on one tail of the counterexample sequence every
scaled ball `B(p, b ρ_n(p))` at a center with `d(p, ∂W) > 10` lies in the interior. -/
theorem bsa06_scaled_ball_interior_eventually :
    ∃ δStar > 0, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar → ∀ (K : ℕ), 2 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ (W : ℕ → CompactCarrier.{u}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier),
        (∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ n)) →
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ n)) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ n)) →
        ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < euclideanThreeUnitBallVolume / 4 → ∀ b : ℝ,
          ∃ ρ : ∀ n, (W n).Carrier → ℝ, ∀ᶠ n : ℕ in atTop, (∀ p, 0 < ρ n p) ∧
            ∀ p : (W n).Carrier, ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) p →
              riemannianBallOf (g n) p (b * ρ n p) ⊆ (W n).model.interior (W n).Carrier := by
  obtain ⟨δS, hδS, h6⟩ := bsa06_row_eventually.{u}
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

/-- BCP05.a consumer: with `n > 300 V`, a ball `B(z, R⁰)`, `R⁰ ≤ V ρ(z)`, meeting a collar at
height `≤ 98` has radius `< 1/100`. -/
theorem bcp05a_zeroBall_radius_lt_hundredth :
    ∃ δStar > 0, ∀ (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)
      (K : ℕ) (δ : ℝ), 2 ≤ K → 0 ≤ δ → δ ≤ δStar → ∀ B : NearlyCuspidalBoundary W g K δ,
      boundaryVolumeCollapsed W g δ →
      ∀ {n w' : ℝ}, 3 ≤ n → δ * (16 * n ^ 4) ≤ 1 → n⁻¹ ≤ w' →
      ∀ ρ : W.Carrier → ℝ, (∀ p, 0 < ρ p) → (∀ p, ρ p ≤ 2 * firstVolumeScale g p w') →
      ∀ (i : Fin B.count) (q : CuspHalfSpace), q.2.val 0 ≤ 98 →
      ∀ (z : W.Carrier) {R₀ V : ℝ}, 0 ≤ V → 300 * V < n →
        (B.collar i).toFun q ∈ riemannianBallOf g z R₀ → R₀ ≤ V * ρ z → R₀ < 1 / 100 := by
  obtain ⟨δS, hδS, h5⟩ := bcp05a_zeroBall_small_of_scale.{u}
  refine ⟨δS, hδS, ?_⟩
  intro W g K δ hK hδ0 hδ B hcoll n w' hn hδn hwn ρ hρ hρu i q hq z R₀ V hV hVn hx hR₀
  have hnpos : 0 < n := by linarith
  have hVn' : V < n := by linarith
  have h := (h5 W g K δ hK hδ0 hδ B hcoll hn hδn hwn ρ hρ hρu i q hq z hx hR₀ hVn').2.2
  have h3 : 3 * V / n ≤ 1 / 100 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]
    linarith
  linarith

end DifferentialGeometry.Geometry.Collapse
