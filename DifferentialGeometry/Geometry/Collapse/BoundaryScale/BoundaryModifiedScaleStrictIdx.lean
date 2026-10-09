import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryModifiedScaleStrict

/-!
# Strict BSA05 / BSA06 along the index-shifted counterexample sequence (lane BDRY-IDX)

The accepted sequence theorems `H_bsa05_eventually_strict_BDRY4` and
`bsa06_row_eventually_strict_BDRY4` take `B : ∀ n, NearlyCuspidalBoundary … (δ_n)` for ALL `n`;
since `δ_0 = boundaryCounterexampleRatio δ₀ 0 = 0` and nearly cuspidal data at ratio `0` do not
exist (lane FC39-BQ), they apply to no sequence. BBR03's counterexample sequence
(`exists_boundary_counterexample_sequence_of_no_threshold`) is at `δ_{n+1}`. This module restates
both theorems on sequences at `δ_{n+1}` (proofs re-run; the per-member kernels are unchanged and
are applied at the REAL parameter `n` with the ratio `δ_{n+1}`, which satisfies
`δ_{n+1}·16n⁴ ≤ 1`):

* `boundaryCounterexampleRatio_succ_mul_le_IDX`, `boundaryCounterexampleRatio_succ_le_IDX`;
* `eventually_boundaryCounterexampleRatio_tail_succ_IDX`,
  `eventually_thousand_mul_boundaryCounterexampleRatio_succ_sq_lt_IDX` (the tails at `δ_{n+1}`);
* `H_bsa05_eventually_strict_BDRY4_IDX`, `bsa06_row_eventually_strict_BDRY4_IDX`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- The shifted ratio meets the BSA04 budget at the unshifted parameter:
`δ_{n+1} · 16 n⁴ ≤ 1` for every `n` (no positivity of `δ₀` needed). -/
theorem boundaryCounterexampleRatio_succ_mul_le_IDX (δ₀ : ℝ) (n : ℕ) :
    boundaryCounterexampleRatio δ₀ (n + 1) * (16 * (n : ℝ) ^ 4) ≤ 1 := by
  have h := boundaryCounterexampleRatio_mul_le δ₀ (Nat.le_add_left 1 n)
  have hn4 : (n : ℝ) ^ 4 ≤ ((n + 1 : ℕ) : ℝ) ^ 4 :=
    pow_le_pow_left₀ (Nat.cast_nonneg n) (by exact_mod_cast Nat.le_succ n) 4
  have h0 : (0 : ℝ) ≤ 16 * (n : ℝ) ^ 4 := by positivity
  rcases le_or_gt 0 (boundaryCounterexampleRatio δ₀ (n + 1)) with hr | hr
  · nlinarith
  · nlinarith

/-- The counterexample ratio is antitone from `n = 1` on: `δ_{n+1} ≤ δ_n` for `n ≥ 1`. -/
theorem boundaryCounterexampleRatio_succ_le_IDX (δ₀ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    boundaryCounterexampleRatio δ₀ (n + 1) ≤ boundaryCounterexampleRatio δ₀ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h4 : 16 * (n : ℝ) ^ 4 ≤ 16 * ((n + 1 : ℕ) : ℝ) ^ 4 := by
    have := pow_le_pow_left₀ (Nat.cast_nonneg n)
      (by exact_mod_cast Nat.le_succ n : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ)) 4
    linarith
  have hdiv : 1 / (16 * ((n + 1 : ℕ) : ℝ) ^ 4) ≤ 1 / (16 * (n : ℝ) ^ 4) :=
    one_div_le_one_div_of_le (by positivity) h4
  unfold boundaryCounterexampleRatio
  exact min_le_min_left _ (min_le_min_left _ hdiv)

/-- The uniform tail conditions of `H_envelope` at the SHIFTED ratio: for all large `n`,
`3 ≤ n`, `2S < n`, `1/n ≤ w'`, `0 ≤ δ_{n+1}`, `δ_{n+1}·16n⁴ ≤ 1` and `1000δ_{n+1}² < w'a²`. -/
theorem eventually_boundaryCounterexampleRatio_tail_succ_IDX {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {Λ w : ℝ}
    (hΛ : 0 < Λ) (hw : 0 < w) :
    ∀ᶠ n : ℕ in atTop, 3 ≤ (n : ℝ) ∧ 2 * (1 + 2 / Λ) < n ∧
      (n : ℝ)⁻¹ ≤ w / (2 * (1 + 2 / Λ) ^ 3) ∧ 0 ≤ boundaryCounterexampleRatio δ₀ (n + 1) ∧
      boundaryCounterexampleRatio δ₀ (n + 1) * (16 * (n : ℝ) ^ 4) ≤ 1 ∧
      1000 * boundaryCounterexampleRatio δ₀ (n + 1) ^ 2 <
        w / (2 * (1 + 2 / Λ) ^ 3) * ((1 / 100) / (2 * (1 + 2 / Λ))) ^ 2 := by
  filter_upwards [eventually_boundaryCounterexampleRatio_tail hδ₀ hΛ hw,
    (tendsto_add_atTop_nat 1).eventually (eventually_boundaryCounterexampleRatio_tail hδ₀ hΛ hw)]
    with n hn hn1
  exact ⟨hn.1, hn.2.1, hn.2.2.1, hn1.2.2.2.1, boundaryCounterexampleRatio_succ_mul_le_IDX δ₀ n,
    hn1.2.2.2.2.2⟩

/-- The shifted ratio is eventually small in the quadratic sense: `1000 δ_{n+1}² < c`. -/
theorem eventually_thousand_mul_boundaryCounterexampleRatio_succ_sq_lt_IDX {δ₀ : ℝ}
    (hδ₀ : 0 < δ₀) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 1000 * boundaryCounterexampleRatio δ₀ (n + 1) ^ 2 < c :=
  (tendsto_add_atTop_nat 1).eventually
    (eventually_thousand_mul_boundaryCounterexampleRatio_sq_lt hδ₀ hc)

/-- **BSA05 along the boundary counterexample sequence, strict bounds (index-shifted).** The
sequence is at `δ_{n+1}` (BBR03's form; the accepted statement at `δ_n` is vacuous at `n = 0`).
One smooth scale `ρ_n`
per member: smooth, positive, `Λ`-Lipschitz, `r_p(w)/2 < ρ_n(p) < 2 r_p(w')` on one tail, and for
every `ε > 0`, `ρ_n < ε` on all collar regions `0 ≤ z ≤ 96` of all components on a further tail. -/
theorem H_bsa05_eventually_strict_BDRY4_IDX :
    ∃ δStar > 0, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar → ∀ (K : ℕ), 2 ≤ K →
      ∀ (W : ℕ → CompactCarrier.{u}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
        ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < euclideanThreeUnitBallVolume / 4 →
          ∃ ρ : ∀ n, (W n).Carrier → ℝ,
            (∀ᶠ n in atTop, ContMDiff (W n).model 𝓘(ℝ, ℝ) ∞ (ρ n) ∧ (∀ p, 0 < ρ n p) ∧
              (∀ p, firstVolumeScale (g n) p w / 2 < ρ n p ∧
                ρ n p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
              ∀ x y, ENNReal.ofReal |ρ n x - ρ n y| ≤
                ENNReal.ofReal Λ * riemannianEDistOf (g n) x y) ∧
            ∀ ε > 0, ∀ᶠ n in atTop, ∀ (i : Fin (B n).count) (p : CuspHalfSpace),
              p.2.val 0 ≤ 96 → ρ n (((B n).collar i).toFun p) < ε := by
  obtain ⟨δStar, hδStar, hS⟩ := H_smooth_scale_strict_BDRY4.{u}
  refine ⟨min δStar (1 / 100), lt_min hδStar (by norm_num), ?_⟩
  intro δ₀ hδ₀ hδ₀S K hK W _ g B hcoll Λ w hΛ hw hwc
  have hw' : 0 < w / (2 * (1 + 2 / Λ) ^ 3) := by positivity
  have hδle (n : ℕ) : boundaryCounterexampleRatio δ₀ (n + 1) ≤ min δStar (1 / 100) :=
    (boundaryCounterexampleRatio_le δ₀ (n + 1)).trans hδ₀S
  have hex : ∀ n : ℕ, ∃ ρ : (W n).Carrier → ℝ,
      (3 ≤ (n : ℝ) ∧ 2 * (1 + 2 / Λ) < n ∧ (n : ℝ)⁻¹ ≤ w / (2 * (1 + 2 / Λ) ^ 3) ∧
        0 ≤ boundaryCounterexampleRatio δ₀ (n + 1) ∧
        boundaryCounterexampleRatio δ₀ (n + 1) * (16 * (n : ℝ) ^ 4) ≤ 1 ∧
        1000 * boundaryCounterexampleRatio δ₀ (n + 1) ^ 2 <
          w / (2 * (1 + 2 / Λ) ^ 3) * ((1 / 100) / (2 * (1 + 2 / Λ))) ^ 2) →
      ContMDiff (W n).model 𝓘(ℝ, ℝ) ∞ ρ ∧ (∀ p, 0 < ρ p) ∧
        (∀ p, firstVolumeScale (g n) p w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
        ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf (g n) x y := by
    intro n
    by_cases htail : 3 ≤ (n : ℝ) ∧ 2 * (1 + 2 / Λ) < n ∧
        (n : ℝ)⁻¹ ≤ w / (2 * (1 + 2 / Λ) ^ 3) ∧ 0 ≤ boundaryCounterexampleRatio δ₀ (n + 1) ∧
        boundaryCounterexampleRatio δ₀ (n + 1) * (16 * (n : ℝ) ^ 4) ≤ 1 ∧
        1000 * boundaryCounterexampleRatio δ₀ (n + 1) ^ 2 <
          w / (2 * (1 + 2 / Λ) ^ 3) * ((1 / 100) / (2 * (1 + 2 / Λ))) ^ 2
    · obtain ⟨h3, h2S, hnw, hδ0, hδn, hδa⟩ := htail
      obtain ⟨ρ, hρ⟩ := hS (W n) (g n) K _ hK hδ0 ((hδle n).trans (min_le_left _ _)) (B n)
        (hcoll n) hΛ hw hwc h3 h2S hnw hδn hδa
      exact ⟨ρ, fun _ => hρ⟩
    · exact ⟨fun _ => 0, fun h => absurd h htail⟩
  choose ρ hρ using hex
  refine ⟨ρ, ?_, fun ε hε => ?_⟩
  · filter_upwards [eventually_boundaryCounterexampleRatio_tail_succ_IDX hδ₀ hΛ hw] with n hn
    exact hρ n hn
  · have hc : 0 < w / (2 * (1 + 2 / Λ) ^ 3) * min (1 / 2) (ε / 4) ^ 2 :=
      mul_pos hw' (pow_pos (lt_min (by norm_num) (by positivity)) 2)
    filter_upwards [eventually_boundaryCounterexampleRatio_tail_succ_IDX hδ₀ hΛ hw,
      eventually_thousand_mul_boundaryCounterexampleRatio_succ_sq_lt_IDX hδ₀ hc] with n hn hsmall
    intro i p hp
    exact (B n).lt_of_le_two_mul_firstVolumeScale ((hδle n).trans (min_le_right _ _)) hw' hε
      hsmall (fun p => ((hρ n hn).2.2.1 p).2.le) i hp

/-- **BSA06 along the counterexample ratios, strict LC02 bounds (index-shifted).** Sequence at
`δ_{n+1}`; the BSA04 parameter stays `α = n`. `bsa06_row_eventually` with
`r_p(w)/2 < ρ_n(p) < 2 r_p(w')`. -/
theorem bsa06_row_eventually_strict_BDRY4_IDX :
    ∃ δStar > 0, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar → ∀ (K : ℕ), 2 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ (W : ℕ → CompactCarrier.{u}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) →
        ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < euclideanThreeUnitBallVolume / 4 →
          ∃ ρ : ∀ n, (W n).Carrier → ℝ,
            (∀ᶠ n : ℕ in atTop, ∃ hρ : ∀ p, 0 < ρ n p,
              ContMDiff (W n).model 𝓘(ℝ, ℝ) ∞ (ρ n) ∧
              (∀ p, firstVolumeScale (g n) p w / 2 < ρ n p ∧
                ρ n p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
              (∀ x y, ENNReal.ofReal |ρ n x - ρ n y| ≤
                ENNReal.ofReal Λ * riemannianEDistOf (g n) x y) ∧
              ∀ p : (W n).Carrier,
                w / (2 * (1 + 2 / Λ) ^ 3) / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ≤
                    (ballVolume (g n) p (ρ n p)).toReal / ρ n p ^ 3 ∧
                (∀ y ∈ riemannianBallOf (normalizedCenterMetric (g n) (ρ n p) (hρ p)) p
                    ((n : ℝ) / 4),
                  SectionalBoundedBelowAt (normalizedCenterMetric (g n) (ρ n p) (hρ p)) y
                    (-(((n : ℝ) / 4) ^ 2)⁻¹)) ∧
                (∀ R : ℝ, 0 < R → 2 * R + 2 < n → ∀ k ≤ K,
                  ∀ y ∈ riemannianBallOf (normalizedCenterMetric (g n) (ρ n p) (hρ p)) p R,
                    curvatureDerivativeNorm (normalizedCenterMetric (g n) (ρ n p) (hρ p)) k y ≤
                      (2 : ℝ) ^ (K + 2) * boundaryDerivativeConstant A K (2 * R + 2)
                        (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
                (0 < distanceToBoundary (W n) (g n) p →
                  n * (distanceToBoundary (W n) (g n) p).toReal /
                      ((distanceToBoundary (W n) (g n) p).toReal + 3) <
                    (distanceToBoundary (W n) (g n) p).toReal / ρ n p) ∧
                (ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) p →
                  (n : ℝ) / 2 < (distanceToBoundary (W n) (g n) p).toReal / ρ n p ∧
                  ∀ b : ℝ, b ≤ (n : ℝ) / 2 →
                    riemannianBallOf (g n) p (b * ρ n p) ⊆
                      (W n).model.interior (W n).Carrier)) ∧
            ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ (i : Fin (B n).count) (p : CuspHalfSpace),
              p.2.val 0 ≤ 96 → ρ n (((B n).collar i).toFun p) < ε := by
  obtain ⟨δH, hδH, hH⟩ := H_bsa05_eventually_strict_BDRY4_IDX.{u}
  obtain ⟨δC, hδC, hC⟩ := bsa06_clauses_of_scale.{u}
  refine ⟨min δH δC, lt_min hδH hδC, ?_⟩
  intro δ₀ hδ₀ hδ₀S K hK A hA W _ g B hcoll hder Λ w hΛ hw hwc
  obtain ⟨ρ, hev, hcol⟩ := hH hδ₀ (hδ₀S.trans (min_le_left _ _)) K hK W g B hcoll hΛ hw hwc
  refine ⟨ρ, ?_, hcol⟩
  have hS : 1 < 2 * (1 + 2 / Λ) ^ 3 := by
    have h1 : 1 ≤ 1 + 2 / Λ := le_add_of_nonneg_right (by positivity)
    nlinarith [one_le_pow₀ (n := 3) h1]
  have hw'c : w / (2 * (1 + 2 / Λ) ^ 3) < euclideanThreeUnitBallVolume := by
    have hlt : w / (2 * (1 + 2 / Λ) ^ 3) < w := div_lt_self hw hS
    linarith [euclideanThreeUnitBallVolume_pos]
  filter_upwards [hev, eventually_boundaryCounterexampleRatio_tail_succ_IDX hδ₀ hΛ hw]
    with n hn htail
  obtain ⟨hsm, hpos, hbd, hlip⟩ := hn
  obtain ⟨h3, -, hnw, hδ0, hδn, -⟩ := htail
  exact ⟨hpos, hsm, hbd, hlip, hC (W n) (g n) K _ hK hδ0
    ((boundaryCounterexampleRatio_le δ₀ (n + 1)).trans (hδ₀S.trans (min_le_right _ _))) (B n)
    (hcoll n) (hder n) hA h3 hδn hnw hw'c (ρ n) hpos fun p => (hbd p).2.le⟩

end DifferentialGeometry.Geometry.Collapse
