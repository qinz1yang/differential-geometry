import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter Topology

namespace Real

theorem exists_pos_lt_mul_rpow_lt_mul_rpow {A p q ε R : ℝ} (hqp : q < p)
    (hε : 0 < ε) (hR : 0 < R) :
    ∃ θ : ℝ, 0 < θ ∧ θ < R ∧ A * θ ^ p < ε * θ ^ q := by
  have hcont : ContinuousAt (fun θ : ℝ => A * θ ^ (p - q)) 0 :=
    (Real.continuousAt_rpow_const 0 (p - q) (.inr (sub_pos.mpr hqp).le)).const_mul A
  have hlim : Tendsto (fun θ : ℝ => A * θ ^ (p - q)) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa [Real.zero_rpow (sub_pos.mpr hqp).ne'] using hcont.tendsto
  have hsmall : ∀ᶠ θ : ℝ in 𝓝[>] (0 : ℝ), A * θ ^ (p - q) < ε := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    exact hlim.eventually (Iio_mem_nhds hε)
  have hpos : ∀ᶠ θ : ℝ in 𝓝[>] (0 : ℝ), 0 < θ := self_mem_nhdsWithin
  have hbound : ∀ᶠ θ : ℝ in 𝓝[>] (0 : ℝ), θ < R :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hR)
  obtain ⟨θ, hθ, hθR, hθsmall⟩ := (hpos.and (hbound.and hsmall)).exists
  refine ⟨θ, hθ, hθR, ?_⟩
  calc
    A * θ ^ p = (A * θ ^ (p - q)) * θ ^ q := by
      rw [mul_assoc, ← Real.rpow_add hθ, sub_add_cancel]
    _ < ε * θ ^ q := mul_lt_mul_of_pos_right hθsmall (Real.rpow_pos_of_pos hθ q)

end Real

namespace DifferentialGeometry.Analysis.Asymptotics

theorem le_geometric_of_recurrence
    {u : ℕ → ℝ} {r s B : ℝ} (hr : 0 ≤ r) (hrs : r ≠ s)
    (k : ℕ) (hstep : ∀ n < k, u (n + 1) ≤ r * u n + B * s ^ n) :
    u k ≤ r ^ k * (u 0 - B / (s - r)) + B / (s - r) * s ^ k := by
  have hne : s - r ≠ 0 := sub_ne_zero.mpr hrs.symm
  have hmul : B / (s - r) * (s - r) = B := div_mul_cancel₀ B hne
  have hrec : ∀ n < k,
      u (n + 1) - B / (s - r) * s ^ (n + 1) ≤
        r * (u n - B / (s - r) * s ^ n) := by
    intro n hn
    have h := hstep n hn
    have heq : B * s ^ n = B / (s - r) * (s - r) * s ^ n := by rw [hmul]
    rw [heq] at h
    rw [pow_succ]
    nlinarith
  have h := le_geom (u := fun n => u n - B / (s - r) * s ^ n) hr k
    hrec
  simp only [pow_zero, mul_one] at h
  nlinarith

theorem le_geometric_of_recurrence_of_lt
    {u : ℕ → ℝ} {r s B : ℝ} (hr : 0 ≤ r) (hrs : r < s)
    (hu0 : 0 ≤ u 0) (hB : 0 ≤ B)
    (k : ℕ) (hstep : ∀ n < k, u (n + 1) ≤ r * u n + B * s ^ n) :
    u k ≤ s ^ k * (u 0 + B / (s - r)) := by
  have hmain := le_geometric_of_recurrence hr hrs.ne k hstep
  have hp : r ^ k ≤ s ^ k := pow_le_pow_left₀ hr hrs.le k
  have hden : 0 ≤ B / (s - r) := div_nonneg hB (sub_nonneg.mpr hrs.le)
  have hprod := mul_nonneg (pow_nonneg hr k) hden
  have hup := mul_le_mul_of_nonneg_right hp hu0
  nlinarith

theorem geometric_scale_bound_of_recurrence
    {Φ : ℝ → ℝ} {R θ A B p q : ℝ}
    (hR : 0 < R) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hΦ : 0 ≤ Φ R)
    (hcontract : A * θ ^ p < θ ^ q)
    (hstep : ∀ r ∈ Set.Ioc (0 : ℝ) R,
      Φ (θ * r) ≤ A * θ ^ p * Φ r + B * r ^ q) (k : ℕ) :
    Φ (θ ^ k * R) ≤ (θ ^ q) ^ k *
      (Φ R + B * R ^ q / (θ ^ q - A * θ ^ p)) := by
  have hrec : ∀ n < k,
      Φ (θ ^ (n + 1) * R) ≤
        (A * θ ^ p) * Φ (θ ^ n * R) + (B * R ^ q) * (θ ^ q) ^ n := by
    intro n _
    have hnpos : 0 < θ ^ n * R := mul_pos (pow_pos hθ n) hR
    have hnle : θ ^ n * R ≤ R := by
      have hp : θ ^ n ≤ 1 := pow_le_one₀ hθ.le hθ1
      nlinarith
    have h := hstep (θ ^ n * R) ⟨hnpos, hnle⟩
    have hp : (θ ^ n * R) ^ q = (θ ^ q) ^ n * R ^ q := by
      rw [Real.mul_rpow (pow_nonneg hθ.le n) hR.le, ← Real.rpow_pow_comm hθ.le]
    rw [hp] at h
    have harg : θ ^ (n + 1) * R = θ * (θ ^ n * R) := by
      rw [pow_succ]
      ring
    rw [harg]
    calc
      _ ≤ A * θ ^ p * Φ (θ ^ n * R) + B * ((θ ^ q) ^ n * R ^ q) := h
      _ = _ := by ring
  simpa only [pow_zero, one_mul] using
    le_geometric_of_recurrence_of_lt
      (u := fun n => Φ (θ ^ n * R))
      (mul_nonneg hA (Real.rpow_nonneg hθ.le _)) hcontract
      (by simpa only [pow_zero, one_mul] using hΦ)
      (mul_nonneg hB (Real.rpow_nonneg hR.le _)) k hrec

theorem geometric_scale_bound_of_half_contraction
    {Φ : ℝ → ℝ} {R θ A B p q : ℝ}
    (hR : 0 < R) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hΦ : 0 ≤ Φ R)
    (hcontract : A * θ ^ p ≤ θ ^ q / 2)
    (hstep : ∀ r ∈ Set.Ioc (0 : ℝ) R,
      Φ (θ * r) ≤ A * θ ^ p * Φ r + B * r ^ q) (k : ℕ) :
    Φ (θ ^ k * R) ≤ θ ^ ((k : ℝ) * q) *
      (Φ R + 2 * B * R ^ q / θ ^ q) := by
  have hθq : 0 < θ ^ q := Real.rpow_pos_of_pos hθ q
  have hgap : 0 < θ ^ q - A * θ ^ p := by linarith
  have hmain := geometric_scale_bound_of_recurrence hR hθ hθ1 hA hB hΦ
    (by linarith : A * θ ^ p < θ ^ q) hstep k
  have hnum : 0 ≤ B * R ^ q := mul_nonneg hB (Real.rpow_nonneg hR.le _)
  have hquot : B * R ^ q / (θ ^ q - A * θ ^ p) ≤ 2 * B * R ^ q / θ ^ q := by
    apply (div_le_div_iff₀ hgap hθq).mpr
    nlinarith
  have hp : (θ ^ q) ^ k = θ ^ ((k : ℝ) * q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hθ.le, mul_comm q]
  rw [← hp]
  exact hmain.trans (mul_le_mul_of_nonneg_left
    (by simpa [add_comm] using add_le_add_left hquot (Φ R)) (pow_nonneg hθq.le k))

theorem exists_geometric_scale_bound
    {A p q : ℝ} (hA : 0 ≤ A) (hqp : q < p) :
    ∃ θ C : ℝ, 0 < θ ∧ θ < 1 ∧ 0 < C ∧
      ∀ (Φ : ℝ → ℝ) (R B : ℝ), 0 < R → 0 ≤ B → 0 ≤ Φ R →
        (∀ r ∈ Set.Ioc (0 : ℝ) R,
          Φ (θ * r) ≤ A * θ ^ p * Φ r + B * r ^ q) →
        ∀ k : ℕ, Φ (θ ^ k * R) ≤
          C * θ ^ ((k : ℝ) * q) * (Φ R + B * R ^ q) := by
  obtain ⟨θ, hθ, hθ1, hsmall⟩ :=
    Real.exists_pos_lt_mul_rpow_lt_mul_rpow (A := A) hqp
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1)
  have hθq : 0 < θ ^ q := Real.rpow_pos_of_pos hθ q
  have hcontract : A * θ ^ p ≤ θ ^ q / 2 := by linarith
  refine ⟨θ, max 1 (2 / θ ^ q), hθ, hθ1, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro Φ R B hR hB hΦ hstep k
  have hmain := geometric_scale_bound_of_half_contraction hR hθ hθ1.le hA hB hΦ
    hcontract hstep k
  have hnum : 0 ≤ B * R ^ q := mul_nonneg hB (Real.rpow_nonneg hR.le _)
  have hc0 := mul_le_mul_of_nonneg_right
    (le_max_left (1 : ℝ) (2 / θ ^ q)) hΦ
  have hcB := mul_le_mul_of_nonneg_right
    (le_max_right (1 : ℝ) (2 / θ ^ q)) hnum
  have hsum : Φ R + 2 * B * R ^ q / θ ^ q ≤
      max 1 (2 / θ ^ q) * (Φ R + B * R ^ q) := by
    have hid : 2 * B * R ^ q / θ ^ q = (2 / θ ^ q) * (B * R ^ q) := by ring
    rw [hid]
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsum
    (Real.rpow_nonneg hθ.le ((k : ℝ) * q))
  calc
    _ ≤ θ ^ ((k : ℝ) * q) * (Φ R + 2 * B * R ^ q / θ ^ q) := hmain
    _ ≤ θ ^ ((k : ℝ) * q) * (max 1 (2 / θ ^ q) * (Φ R + B * R ^ q)) := hmul
    _ = _ := by ring

end DifferentialGeometry.Analysis.Asymptotics
