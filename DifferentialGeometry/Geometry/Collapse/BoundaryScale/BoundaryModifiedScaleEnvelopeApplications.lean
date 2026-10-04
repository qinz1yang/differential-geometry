import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryModifiedScaleEnvelope
import DifferentialGeometry.Geometry.Collapse.StaticCounterexamples

/-!
# Consumer of statement H: the envelope along the boundary counterexample sequence

The uniform tail of `H_envelope` is a tail of the BBR03 counterexample ratio
`δ_n = boundaryCounterexampleRatio δ₀ n = min{δ₀, ω₃/8, 1/(16n⁴)}` (design §(c), step 4):
* `eventually_boundaryCounterexampleRatio_tail`: for `δ₀ > 0`, `Λ > 0`, `w > 0`, all large `n`
  satisfy `3 ≤ n`, `2S < n`, `1/n ≤ w'`, `0 ≤ δ_n`, `δ_n·16n⁴ ≤ 1` and `1000δ_n² < w'a²`;
* `H_envelope_eventually`: along any sequence of connected nearly cuspidal carriers at the ratios
  `δ_n` (`δ₀ ≤ δStar`, `K ≥ 2`) with the static collapse, the envelope
  `r_p(w) - (Λ/2) d(p, q) ≤ r_q(w')` holds at all pairs on one tail of `n`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry GC.Endpoint
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- The counterexample ratio is eventually small in the quadratic sense needed by the collar
clauses: `1000 δ_n² < c` for all large `n`, for every `c > 0` (`δ₀ > 0`). -/
theorem eventually_thousand_mul_boundaryCounterexampleRatio_sq_lt {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 1000 * boundaryCounterexampleRatio δ₀ n ^ 2 < c := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (1000 / c))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hbig := hN.trans_le hnN
  rw [max_lt_iff] at hbig
  obtain ⟨h1, hcn⟩ := hbig
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : 1 ≤ n := by exact_mod_cast h1.le
  have hδpos := boundaryCounterexampleRatio_pos hδ₀ hn1
  have hmul := boundaryCounterexampleRatio_mul_le δ₀ hn1
  have hn4 : (n : ℝ) ≤ n ^ 4 := le_self_pow₀ h1.le (by norm_num)
  have hδn : boundaryCounterexampleRatio δ₀ n * n ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hn4 hδpos.le]
  have hδ1 : boundaryCounterexampleRatio δ₀ n ≤ 1 := by nlinarith
  have hcn' : 1000 < c * n := by
    rw [div_lt_iff₀ hc] at hcn
    linarith
  have hsq : boundaryCounterexampleRatio δ₀ n ^ 2 * n ≤ 1 := by nlinarith
  nlinarith

/-- The uniform tail conditions of `H_envelope` hold for all large `n` at the ratio
`δ_n = boundaryCounterexampleRatio δ₀ n`, `δ₀ > 0`. -/
theorem eventually_boundaryCounterexampleRatio_tail {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {Λ w : ℝ}
    (hΛ : 0 < Λ) (hw : 0 < w) :
    ∀ᶠ n : ℕ in atTop, 3 ≤ (n : ℝ) ∧ 2 * (1 + 2 / Λ) < n ∧
      (n : ℝ)⁻¹ ≤ w / (2 * (1 + 2 / Λ) ^ 3) ∧ 0 ≤ boundaryCounterexampleRatio δ₀ n ∧
      boundaryCounterexampleRatio δ₀ n * (16 * (n : ℝ) ^ 4) ≤ 1 ∧
      1000 * boundaryCounterexampleRatio δ₀ n ^ 2 <
        w / (2 * (1 + 2 / Λ) ^ 3) * ((1 / 100) / (2 * (1 + 2 / Λ))) ^ 2 := by
  have hw' : 0 < w / (2 * (1 + 2 / Λ) ^ 3) := div_pos hw (by positivity)
  have hwa : 0 < w / (2 * (1 + 2 / Λ) ^ 3) * ((1 / 100) / (2 * (1 + 2 / Λ))) ^ 2 := by
    positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (max (max 3 (2 * (1 + 2 / Λ)))
    (w / (2 * (1 + 2 / Λ) ^ 3))⁻¹)
  filter_upwards [eventually_ge_atTop N,
    eventually_thousand_mul_boundaryCounterexampleRatio_sq_lt hδ₀ hwa] with n hn hsmall
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hbig := hN.trans_le hnN
  simp only [max_lt_iff] at hbig
  obtain ⟨⟨h3, h2S⟩, hw'n⟩ := hbig
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : 1 ≤ n := by exact_mod_cast (by linarith : (1 : ℝ) ≤ n)
  refine ⟨h3.le, h2S, ?_, (boundaryCounterexampleRatio_pos hδ₀ hn1).le,
    boundaryCounterexampleRatio_mul_le δ₀ hn1, hsmall⟩
  rw [inv_le_comm₀ hn0 hw']
  exact hw'n.le

/-- **H along the boundary counterexample sequence.** With `δStar` of `H_envelope`, for
`0 < δ₀ ≤ δStar` and `K ≥ 2`, every sequence of connected carriers with nearly cuspidal boundaries
and static collapse at the ratios `δ_n = boundaryCounterexampleRatio δ₀ n` satisfies, on one tail of
`n`, the envelope `r_p(w) - (Λ/2) d(p, q) ≤ r_q(w')` at ALL pairs, `w' = w/(2(1 + 2/Λ)³)`. -/
theorem H_envelope_eventually :
    ∃ δStar > 0, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar → ∀ (K : ℕ), 2 ≤ K →
      ∀ (W : ℕ → CompactCarrier.{u}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier),
        (∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ n)) →
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ n)) →
        ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < euclideanThreeUnitBallVolume / 4 →
          ∀ᶠ n : ℕ in atTop, ∀ p q : (W n).Carrier,
            firstVolumeScale (g n) p w - Λ / 2 * (riemannianEDistOf (g n) p q).toReal ≤
              firstVolumeScale (g n) q (w / (2 * (1 + 2 / Λ) ^ 3)) := by
  obtain ⟨δStar, hδStar, hH⟩ := H_envelope.{u}
  refine ⟨δStar, hδStar, ?_⟩
  intro δ₀ hδ₀ hδ₀S K hK W _ g B hcoll Λ w hΛ hw hwc
  filter_upwards [eventually_boundaryCounterexampleRatio_tail hδ₀ hΛ hw] with n hn
  obtain ⟨h3, h2S, hnw, hδ0, hδn, hδa⟩ := hn
  exact hH (W n) (g n) K _ hK hδ0 ((boundaryCounterexampleRatio_le δ₀ n).trans hδ₀S) (B n)
    (hcoll n) hΛ hw hwc h3 h2S hnw hδn hδa

end DifferentialGeometry.Geometry.Collapse
