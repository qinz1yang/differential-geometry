import DifferentialGeometry.Geometry.Collapse.EdgeSourceHeights
import DifferentialGeometry.Geometry.Metric.Approximation.CoarseBorderDistance
import DifferentialGeometry.Analysis.Calculus.Cutoff.EdgeSublevelProfile

/-!
# LFR28 I5: values on the same whole model cylinder

The metric producer preserves the selected source and model smoothings, scale function and
fixed sublevel profile. Its bounds hold at every point of the specified open cylinder domain,
which supplies the global value input of the interpolation and disk-bundle consumers. The
image also lies in LFR27's buffered smooth domain. No differential comparison is asserted.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped NNReal

namespace DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open GC.MetricGeometry

theorem abs_edgeValueQuotient_sub_model_le {Δ μ τ h l d b r F G ρ : ℝ}
    (hΔ : 0 < Δ) (hl : 0 ≤ l)
    (hlhalf : l < 1 / 2) (hsmall : μ + 2 * τ + h ≤ 1)
    (hr : 0 ≤ r) (hr9 : r ≤ 9 * Δ) (hF : |F - d| ≤ μ * Δ)
    (hdb : |d - b| ≤ 2 * (τ * Δ)) (hbr : |b - r| ≤ h * Δ)
    (hG : |G - r| ≤ μ * Δ) (hρ : |ρ - 1| ≤ l) :
    |F / ρ - G| ≤ (2 * μ + 2 * τ + h + 20 * l) * Δ
 := by
  have hρlo := (abs_le.mp hρ).1
  have hρ0 : 0 < ρ := by linarith
  have hFr : |F - r| ≤ (μ + 2 * τ + h) * Δ := by
    calc
      |F - r| = |(F - d) + (d - b) + (b - r)| := by congr 1; ring
      _ ≤ |F - d| + |d - b| + |b - r| := abs_add_three _ _ _
      _ ≤ (μ + 2 * τ + h) * Δ := by linarith
  have hFabs : |F| ≤ 10 * Δ := by
    have ht := abs_add_le (F - r) r
    rw [sub_add_cancel, abs_of_nonneg hr] at ht
    nlinarith
  have hquot : |F / ρ - F| ≤ 20 * l * Δ := by
    rw [show F / ρ - F = F * (1 - ρ) / ρ by field_simp,
      abs_div, abs_mul, abs_of_pos hρ0]
    have hρabs : |1 - ρ| ≤ l := by simpa [abs_sub_comm] using hρ
    have hm := mul_le_mul hFabs hρabs (abs_nonneg _) (by positivity)
    rw [div_le_iff₀ hρ0]
    nlinarith [mul_nonneg hl hΔ.le]
  calc
    |F / ρ - G| = |(F / ρ - F) + (F - r) - (G - r)| := by congr 1; ring
    _ ≤ |F / ρ - F| + |F - r| + |G - r| := by
      calc
        |(F / ρ - F) + (F - r) - (G - r)| ≤
            |(F / ρ - F) + (F - r)| + |G - r| := abs_sub _ _
        _ ≤ |F / ρ - F| + |F - r| + |G - r| := by
          gcongr
          exact abs_add_le _ _
    _ ≤ (2 * μ + 2 * τ + h + 20 * l) * Δ := by linarith

theorem abs_edgeValueProfile_sub_le {Δ η G : ℝ} (hΔ : 0 < Δ) :
    |Δ * edgeSublevelProfile (η / Δ) - Δ * edgeSublevelProfile (G / Δ)| ≤ 4 * |η - G|
 := by
  have hp := lipschitzWith_edgeSublevelProfile.dist_le_mul (η / Δ) (G / Δ)
  simp only [Real.dist_eq, NNReal.coe_ofNat] at hp
  rw [← mul_sub, abs_mul, abs_of_pos hΔ]
  have hd : |η / Δ - G / Δ| = |η - G| / Δ := by
    rw [← sub_div, abs_div, abs_of_pos hΔ]
  rw [hd] at hp
  have hm := mul_le_mul_of_nonneg_left hp hΔ.le
  have he : Δ * (4 * (|η - G| / Δ)) = 4 * |η - G| := by field_simp
  exact hm.trans_eq he

theorem eventually_edgeValueComparison
    {N : Type*} [metricN : MetricSpace N] {M : ℕ → Type*}
    [metricSequence : ∀ i, MetricSpace (M i)]
    {W : Type*} [metricFactor : MetricSpace W] (j : ∀ i, N → M i) (q : N)
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {z₀ : W}
    (hΦq : Φ q = WithLp.toLp 2 ((0 : ℝ), z₀))
    {Δ μ τ h l : ℝ} {Λ : ℝ≥0} (hΔ : 0 < Δ) (hμ : 0 ≤ μ)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hl : 0 ≤ l) (hlhalf : l < 1 / 2)
    (hh : 20 * Real.sqrt τ < h)
    (hbudget : 2 * μ + 2 * τ + h + 20 * l < 1 / 1000)
    (hΛ : 100 * Δ * (Λ : ℝ) ≤ l)
    (Q : ∀ i, M i → WithLp 2 (ℝ × ℝ)) (A : ∀ i, Set (M i))
    (F f ρ : ∀ i, M i → ℝ) (G : N → ℝ)
    (hQp : ∀ i, Q i (j i q) = 0)
    (hQdist : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ),
      ∀ y ∈ ball (j i q) (200 * Δ), |dist (Q i x) (Q i y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), 0 ≤ (Q i x).snd)
    (hcoord : TendstoUniformlyOn (fun i x => (Q i (j i x)).fst)
      (fun x => (Φ x).fst) atTop (closedBall q (100 * Δ)))
    (hpA : ∀ i, j i q ∈ A i)
    (hborder : ∀ i, ∀ a ∈ A i ∩ ball (j i q) (190 * Δ), (Q i a).snd ≤ τ * Δ)
    (hbordercover : ∀ i, ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ a ∈ A i ∩ ball (j i q) (190 * Δ),
        dist (Q i a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    (hF : ∀ i x, |F i x - infDist x (A i)| < μ * Δ)
    (hf : ∀ i, ∀ x ∈ ball (j i q) (100 * Δ), |f i x - (Q i x).fst| < μ * Δ)
    (hG : ∀ x, |G x - dist (Φ x).snd z₀| < μ * Δ)
    (hρ : ∀ i, LipschitzWith Λ (ρ i)) (hρp : ∀ i, ρ i (j i q) = 1)
    (Ω : TopologicalSpace.Opens N)
    (hΩ : ∀ x ∈ Ω, |(Φ x).fst| ≤ 6 * Δ ∧ dist (Φ x).snd z₀ ≤ 9 * Δ) :
    ∀ᶠ i in atTop, ∀ x : Ω,
      j i x ∈ ball (j i q) (20 * Δ) ∧ infDist (j i x) (A i) < 41 * Δ / 4 ∧
      |F i (j i x) / ρ i (j i x) - G x| < Δ / 1000 ∧
      |Δ * edgeSublevelProfile ((F i (j i x) / ρ i (j i x)) / Δ) -
        Δ * edgeSublevelProfile (G x / Δ)| < Δ / 100 ∧
      |(f i (j i x), Δ * edgeSublevelProfile ((F i (j i x) / ρ i (j i x)) / Δ)).1 -
        ((Φ x).fst, Δ * edgeSublevelProfile (G x / Δ)).1| ≤ Δ / 100 ∧
      |(f i (j i x), Δ * edgeSublevelProfile ((F i (j i x) / ρ i (j i x)) / Δ)).2 -
        ((Φ x).fst, Δ * edgeSublevelProfile (G x / Δ)).2| ≤ Δ / 100
 := by
  have hh0 : 0 ≤ h := (by positivity : 0 ≤ 20 * Real.sqrt τ).trans hh.le
  have hsmall : μ + 2 * τ + h ≤ 1 := by linarith
  have hmuSmall : μ < 1 / 1000 := by linarith
  have hheightTail := eventually_abs_height_sub_axisDist_le j q hdist Φ hΦq hΔ hτ hτ1
    Q hQp hQdist hheight hcoord h hh
  have hp20 : q ∈ ball q (20 * Δ) := mem_ball_self (by positivity)
  filter_upwards [hheightTail, hdist (20 * Δ) Δ hΔ,
    Metric.tendstoUniformlyOn_iff.mp hcoord (Δ / 1000) (by positivity)] with i hhi hdi hci
  intro x
  have hxΩ := hΩ x x.property
  have hr0 : 0 ≤ dist (Φ x).snd z₀ := dist_nonneg
  have hsq : dist (x : N) q ^ 2 = (Φ x).fst ^ 2 + dist (Φ x).snd z₀ ^ 2 := by
    rw [← Φ.dist_eq, hΦq, dist_withLp_two_prod, Real.sq_sqrt (by positivity)]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.dist_eq, sub_zero, sq_abs]
  have hxp : dist (x : N) q ≤ 15 * Δ := by
    have hfst := abs_le.mp hxΩ.1
    have hs1 : (Φ x).fst ^ 2 ≤ (6 * Δ) ^ 2 := by nlinarith
    have hs2 : dist (Φ x).snd z₀ ^ 2 ≤ (9 * Δ) ^ 2 := by nlinarith [hxΩ.2]
    nlinarith [show 0 ≤ dist (x : N) q from dist_nonneg]
  have hx20 : (x : N) ∈ ball q (20 * Δ) := by change dist (x : N) q < 20 * Δ; linarith
  have hx100 : (x : N) ∈ ball q (100 * Δ) := by
    change dist (x : N) q < 100 * Δ
    linarith
  have hj20 : j i x ∈ ball (j i q) (20 * Δ) := by
    have hd := (abs_lt.mp (hdi x hx20 q hp20)).2
    change dist (j i x) (j i q) < 20 * Δ
    linarith
  have hj70 : j i x ∈ ball (j i q) (70 * Δ) := by
    change dist (j i x) (j i q) < 70 * Δ
    have hj := hj20
    change dist (j i x) (j i q) < 20 * Δ at hj
    linarith
  have hj100 : j i x ∈ ball (j i q) (100 * Δ) := by
    change dist (j i x) (j i q) < 100 * Δ
    have hj := hj20
    change dist (j i x) (j i q) < 20 * Δ at hj
    linarith
  have hdb := coarseBorder_abs_infDist_sub_height_le hΔ hτ1 (hQp i) (hQdist i)
    (hheight i) (hpA i) (hborder i) (hbordercover i) hj70
  have hbr := hhi x hx100
  have hρx : |ρ i (j i x) - 1| ≤ l := by
    have hrho := (hρ i).dist_le_mul (j i x) (j i q)
    rw [Real.dist_eq, hρp i] at hrho
    have hmul := mul_le_mul_of_nonneg_left (le_of_lt hj20) (NNReal.coe_nonneg Λ)
    have htwenty : (Λ : ℝ) * (20 * Δ) ≤ l := by
      nlinarith [NNReal.coe_nonneg Λ]
    exact hrho.trans (hmul.trans htwenty)
  have hη := abs_edgeValueQuotient_sub_model_le hΔ hl hlhalf hsmall hr0 hxΩ.2
    (hF i (j i x)).le hdb hbr (hG x).le hρx
  have hηstrict : |F i (j i x) / ρ i (j i x) - G x| < Δ / 1000 := by
    have hb := mul_lt_mul_of_pos_right hbudget hΔ
    linarith
  have hprofile := abs_edgeValueProfile_sub_le (η := F i (j i x) / ρ i (j i x))
    (G := G x) hΔ
  have hHstrict : |Δ * edgeSublevelProfile ((F i (j i x) / ρ i (j i x)) / Δ) -
      Δ * edgeSublevelProfile (G x / Δ)| < Δ / 100 := by linarith
  have haxis : |(Q i (j i x)).fst - (Φ x).fst| < Δ / 1000 := by
    have hc := hci x (ball_subset_closedBall hx100)
    rwa [Real.dist_eq, abs_sub_comm] at hc
  have hfvalue : |f i (j i x) - (Φ x).fst| ≤ Δ / 100 := by
    have ht := abs_add_le (f i (j i x) - (Q i (j i x)).fst)
      ((Q i (j i x)).fst - (Φ x).fst)
    have hs := hf i (j i x) hj100
    have hm := mul_lt_mul_of_pos_right hmuSmall hΔ
    rw [sub_add_sub_cancel] at ht
    linarith
  have hdistA : infDist (j i x) (A i) < 41 * Δ / 4 := by
    have hdb' := (abs_le.mp hdb).2
    have hbr' := (abs_le.mp hbr).2
    have hb := mul_lt_mul_of_pos_right hbudget hΔ
    nlinarith [hxΩ.2, mul_nonneg hμ hΔ.le, mul_nonneg hl hΔ.le]
  exact ⟨hj20, hdistA, hηstrict, hHstrict, hfvalue, hHstrict.le⟩

end DifferentialGeometry.Geometry.Collapse
