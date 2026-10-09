import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryModifiedScaleStrictIdx

/-!
# BSA04 / BSA05 / BSA06 / H along the index-shifted counterexample sequence (lane BDRY-IDX3)

The accepted sequence forms `H_envelope_eventually`, `H_bsa05_eventually`,
`bsa04_row_counterexample`, `bsa06_row_eventually` and `eventually_strict_scale_boundary_BDRY4`
(the recorded statements of the BSA04 / BSA05 / BSA06 rows and of T2's clause (i)) take
`∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ n)`, which is EMPTY:
`δ_0 = 0` and nearly cuspidal data at ratio `0` do not exist (lane FC39-BQ;
`isEmpty_boundarySequence_ratio_IDX`). This module restates them on sequences at `δ_{n+1}` —
BBR03's sequence (`exists_boundary_counterexample_sequence_of_no_threshold`) — with proofs re-run
from the accepted sources (index changes only). The per-member kernels (`H_envelope`,
`H_smooth_scale`, `bsa04_row`, `bsa06_clauses_of_scale`) are unchanged and are applied at the REAL
parameter `n` with the ratio `δ_{n+1}` (`δ_{n+1}·16n⁴ ≤ 1`,
`boundaryCounterexampleRatio_succ_mul_le_IDX`); every clause using the index as the BSA04
parameter keeps `α = n` (lane BDRY-IDX's index decision).

* `H_envelope_eventually_IDX`, `H_bsa05_eventually_IDX`;
* `bsa04_row_counterexample_IDX`, `bsa06_row_eventually_IDX`;
* `eventually_strict_scale_boundary_BDRY4_IDX` (on `H_bsa05_eventually_strict_BDRY4_IDX`).
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

/-- **H along the boundary counterexample sequence (index-shifted).** With `δStar` of
`H_envelope`, for `0 < δ₀ ≤ δStar` and `K ≥ 2`, every sequence of connected carriers with nearly
cuspidal boundaries and static collapse at the ratios `δ_{n+1}` (BBR03's sequence; the accepted
statement at `δ_n` is vacuous at `n = 0`) satisfies, on one tail of `n`, the envelope
`r_p(w) - (Λ/2) d(p, q) ≤ r_q(w')` at ALL pairs, `w' = w/(2(1 + 2/Λ)³)`. -/
theorem H_envelope_eventually_IDX :
    ∃ δStar > 0, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar → ∀ (K : ℕ), 2 ≤ K →
      ∀ (W : ℕ → CompactCarrier.{u}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier),
        (∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
        ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < euclideanThreeUnitBallVolume / 4 →
          ∀ᶠ n : ℕ in atTop, ∀ p q : (W n).Carrier,
            firstVolumeScale (g n) p w - Λ / 2 * (riemannianEDistOf (g n) p q).toReal ≤
              firstVolumeScale (g n) q (w / (2 * (1 + 2 / Λ) ^ 3)) := by
  obtain ⟨δStar, hδStar, hH⟩ := H_envelope.{u}
  refine ⟨δStar, hδStar, ?_⟩
  intro δ₀ hδ₀ hδ₀S K hK W _ g B hcoll Λ w hΛ hw hwc
  filter_upwards [eventually_boundaryCounterexampleRatio_tail_succ_IDX hδ₀ hΛ hw] with n hn
  obtain ⟨h3, h2S, hnw, hδ0, hδn, hδa⟩ := hn
  exact hH (W n) (g n) K _ hK hδ0 ((boundaryCounterexampleRatio_le δ₀ (n + 1)).trans hδ₀S) (B n)
    (hcoll n) hΛ hw hwc h3 h2S hnw hδn hδa

/-- **BSA05 along the boundary counterexample sequence (index-shifted).** Sequence at `δ_{n+1}`
(BBR03's form). One smooth scale `ρ_n` per member: smooth, positive, `Λ`-Lipschitz,
`r_p(w)/2 ≤ ρ_n(p) ≤ 2 r_p(w')` on one tail, and for every `ε > 0`, `ρ_n < ε` on all collar regions
`0 ≤ z ≤ 96` of all components on a further tail. -/
theorem H_bsa05_eventually_IDX :
    ∃ δStar > 0, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar → ∀ (K : ℕ), 2 ≤ K →
      ∀ (W : ℕ → CompactCarrier.{u}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
        ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < euclideanThreeUnitBallVolume / 4 →
          ∃ ρ : ∀ n, (W n).Carrier → ℝ,
            (∀ᶠ n in atTop, ContMDiff (W n).model 𝓘(ℝ, ℝ) ∞ (ρ n) ∧ (∀ p, 0 < ρ n p) ∧
              (∀ p, firstVolumeScale (g n) p w / 2 ≤ ρ n p ∧
                ρ n p ≤ 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
              ∀ x y, ENNReal.ofReal |ρ n x - ρ n y| ≤
                ENNReal.ofReal Λ * riemannianEDistOf (g n) x y) ∧
            ∀ ε > 0, ∀ᶠ n in atTop, ∀ (i : Fin (B n).count) (p : CuspHalfSpace),
              p.2.val 0 ≤ 96 → ρ n (((B n).collar i).toFun p) < ε := by
  obtain ⟨δStar, hδStar, hS⟩ := H_smooth_scale.{u}
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
        (∀ p, firstVolumeScale (g n) p w / 2 ≤ ρ p ∧
          ρ p ≤ 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
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
      hsmall (fun p => ((hρ n hn).2.2.1 p).2) i hp

/-- **BSA04 along the counterexample ratios (index-shifted).** With `δStar` of `bsa04_row`,
`0 < δ₀ ≤ δStar` and `K ≥ 2`, every sequence of carriers with nearly cuspidal boundaries, static
collapse and derivative control at `δ_{n+1} = boundaryCounterexampleRatio δ₀ (n + 1)` (BBR03's
sequence) satisfies (BSA04.a) and (BSA04.c) at every point, for EVERY `n ≥ 3`, with the BSA04
parameter `α = n` (`δ_{n+1}·16n⁴ ≤ 1`). -/
theorem bsa04_row_counterexample_IDX :
    ∃ δStar > 0, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar → ∀ (K : ℕ), 2 ≤ K → ∀ (A : ℝ → ℝ)
      (W : ℕ → CompactCarrier.{u}) (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier),
      (∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))) →
      (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
      (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) →
      ∀ n : ℕ, 3 ≤ n → ∀ p : (W n).Carrier,
        ENNReal.ofReal (2 * n * firstVolumeScale (g n) p (n : ℝ)⁻¹) < curvatureRadius (g n) p ∧
        ∀ {C w : ℝ}, C < n → (n : ℝ)⁻¹ ≤ w → w < euclideanThreeUnitBallVolume →
          ∀ k ≤ K, ∀ q ∈ riemannianBallOf (g n) p (C * firstVolumeScale (g n) p w),
            curvatureDerivativeNorm (g n) k q ≤
              boundaryDerivativeConstant A K C w * (firstVolumeScale (g n) p w ^ (k + 2))⁻¹ := by
  obtain ⟨δS, hδS, h4⟩ := bsa04_row.{u}
  refine ⟨δS, hδS, ?_⟩
  intro δ₀ hδ₀ hδ₀S K hK A W g B hcoll hder n hn p
  exact h4 (W n) (g n) K _ hK (boundaryCounterexampleRatio_pos hδ₀ (Nat.le_add_left 1 n)).le
    ((boundaryCounterexampleRatio_le δ₀ (n + 1)).trans hδ₀S) (B n) (hcoll n) (hder n)
    (by exact_mod_cast hn) (boundaryCounterexampleRatio_succ_mul_le_IDX δ₀ n) p

/-- **BSA06 along the counterexample ratios (index-shifted).** For `0 < δ₀ ≤ δStar`, `K ≥ 2`,
`A > 0`, `Λ > 0`, `0 < w < ω₃/4`, every sequence of connected carriers with nearly cuspidal
boundaries, static collapse and derivative control at `δ_{n+1}` (BBR03's sequence) has scales `ρ_n`
with, on one tail, BSA05.a and all BSA06 / BCP04.a clauses at every point (with `α = n`), and, for
every `ε > 0`, `ρ_n < ε` on every collar region `z ≤ 96` on a further tail. -/
theorem bsa06_row_eventually_IDX :
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
              (∀ p, firstVolumeScale (g n) p w / 2 ≤ ρ n p ∧
                ρ n p ≤ 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
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
  obtain ⟨δH, hδH, hH⟩ := H_bsa05_eventually_IDX.{u}
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
    (hcoll n) (hder n) hA h3 hδn hnw hw'c (ρ n) hpos fun p => (hbd p).2⟩

/-- **T2 clause (i) verbatim, index-shifted.** Along the counterexample ratios `δ_{n+1}` (BBR03's
sequence), one scale `ρ_n` with, on one tail, smoothness, positivity, the `Λ`-Lipschitz bound for
`g_n`, the STRICT LC02 bounds written as in T2 (`2 * Λ⁻¹`), and for every `ε > 0` the collar
smallness `ρ_n ≤ ε` on `z ≤ 96` on a further tail. -/
theorem eventually_strict_scale_boundary_BDRY4_IDX :
    ∃ δStar > 0, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar → ∀ (K : ℕ), 2 ≤ K →
      ∀ (W : ℕ → CompactCarrier.{u}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
        ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < euclideanThreeUnitBallVolume / 4 →
          ∃ ρ : ∀ n, (W n).Carrier → ℝ,
            (∀ᶠ n in atTop, (∀ p, 0 < ρ n p) ∧
              ContMDiff (W n).model 𝓘(ℝ, ℝ) ∞ (ρ n) ∧
              (∀ x y, ENNReal.ofReal |ρ n x - ρ n y| ≤
                ENNReal.ofReal Λ * riemannianEDistOf (g n) x y) ∧
              ∀ p, firstVolumeScale (g n) p w / 2 < ρ n p ∧
                ρ n p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
            ∀ ε > 0, ∀ᶠ n in atTop, ∀ (i : Fin (B n).count) (q : CuspHalfSpace),
              q.2.val 0 ≤ 96 → ρ n (((B n).collar i).toFun q) ≤ ε := by
  obtain ⟨δStar, hδStar, hH⟩ := H_bsa05_eventually_strict_BDRY4_IDX.{u}
  refine ⟨δStar, hδStar, ?_⟩
  intro δ₀ hδ₀ hδ₀S K hK W _ g B hcoll Λ w hΛ hw hwc
  obtain ⟨ρ, hev, hcol⟩ := hH hδ₀ hδ₀S K hK W g B hcoll hΛ hw hwc
  refine ⟨ρ, ?_, fun ε hε => ?_⟩
  · filter_upwards [hev] with n hn
    obtain ⟨hsm, hpos, hbd, hlip⟩ := hn
    refine ⟨hpos, hsm, hlip, fun p => ?_⟩
    rw [← div_eq_mul_inv]
    exact hbd p
  · filter_upwards [hcol ε hε] with n hn
    exact fun i q hq => (hn i q hq).le

end DifferentialGeometry.Geometry.Collapse
