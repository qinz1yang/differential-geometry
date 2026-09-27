import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.Order


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open scoped Topology


def collapsedVolumeChi : ℝ := 1 / (576 * (3 + 1) ^ 2)

theorem collapsedVolumeChi_pos : 0 < collapsedVolumeChi := by
  norm_num [collapsedVolumeChi]

private theorem summable_cubic_gaussian {b : ℝ} (hb : 0 < b) :
    Summable (fun j : ℕ => ((j : ℝ) + 2) ^ 3 * Real.exp (-b * ((j : ℝ) + 1) ^ 2)) := by
  have hlinear : Summable (fun j : ℕ =>
      ((j : ℝ) + 1) ^ 3 * Real.exp (-b * ((j : ℝ) + 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_pow_mul_exp_neg_nat_mul 3 hb)
  apply (hlinear.mul_left 8).of_nonneg_of_le (fun j => by positivity)
  intro j
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hpoly : ((j : ℝ) + 2) ^ 3 ≤ 8 * ((j : ℝ) + 1) ^ 3 := by
    calc
      ((j : ℝ) + 2) ^ 3 ≤ (2 * ((j : ℝ) + 1)) ^ 3 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 3
      _ = 8 * ((j : ℝ) + 1) ^ 3 := by ring
  have hsquare : (j : ℝ) + 1 ≤ ((j : ℝ) + 1) ^ 2 := by nlinarith
  have hexp : Real.exp (-b * ((j : ℝ) + 1) ^ 2) ≤
      Real.exp (-b * ((j : ℝ) + 1)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hsquare (by linarith))
  calc
    ((j : ℝ) + 2) ^ 3 * Real.exp (-b * ((j : ℝ) + 1) ^ 2) ≤
        (8 * ((j : ℝ) + 1) ^ 3) * Real.exp (-b * ((j : ℝ) + 1)) :=
      mul_le_mul hpoly hexp (Real.exp_pos _).le (by positivity)
    _ = 8 * (((j : ℝ) + 1) ^ 3 * Real.exp (-b * ((j : ℝ) + 1))) := by ring

private theorem gaussian_tail_factor {b theta : ℝ}
    (hb : 0 < b) (htheta : 0 < theta) (htheta1 : theta ≤ 1) (j : ℕ) :
    Real.exp (-b * ((j : ℝ) + 1) ^ 2 / theta) ≤
      Real.exp (-(b / 2) / theta) * Real.exp (-(b / 2) * ((j : ℝ) + 1) ^ 2) := by
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hsquare : 1 ≤ ((j : ℝ) + 1) ^ 2 := by nlinarith
  have hproduct : theta * ((j : ℝ) + 1) ^ 2 ≤ ((j : ℝ) + 1) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right htheta1 (sq_nonneg ((j : ℝ) + 1))]
  have hmain : b / 2 + (b / 2) * ((j : ℝ) + 1) ^ 2 * theta ≤
      b * ((j : ℝ) + 1) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsquare hb.le,
      mul_le_mul_of_nonneg_left hproduct hb.le]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ htheta).mpr
  rw [add_mul, div_mul_cancel₀ _ htheta.ne']
  nlinarith


theorem collapsedVolumeTail_summable {theta : ℝ} (htheta : 0 < theta) :
    Summable (fun j : ℕ => ((j : ℝ) + 2) ^ 3 *
      Real.exp (-collapsedVolumeChi * ((j : ℝ) + 1) ^ 2 / theta)) := by
  have h := summable_cubic_gaussian (div_pos collapsedVolumeChi_pos htheta)
  convert h using 1
  ext j
  congr 2
  ring


def collapsedReducedVolumeTail (a theta : ℝ) : ℝ :=
  Real.exp (1 + a * theta / 3) * (4 * Real.pi * theta) ^ (-(3 / 2 : ℝ)) *
    (4 * Real.pi / 3) *
    ∑' j : ℕ, ((j : ℝ) + 2) ^ 3 *
      Real.exp (-collapsedVolumeChi * ((j : ℝ) + 1) ^ 2 / theta)

theorem collapsedReducedVolumeTail_nonneg (a : ℝ) {theta : ℝ} (htheta : 0 < theta) :
    0 ≤ collapsedReducedVolumeTail a theta := by
  unfold collapsedReducedVolumeTail
  apply mul_nonneg
  · positivity
  · exact tsum_nonneg (fun j => by positivity)

private theorem collapsedVolumeTail_series_le {theta : ℝ}
    (htheta : 0 < theta) (htheta1 : theta ≤ 1) :
    (∑' j : ℕ, ((j : ℝ) + 2) ^ 3 *
      Real.exp (-collapsedVolumeChi * ((j : ℝ) + 1) ^ 2 / theta)) ≤
    Real.exp (-(collapsedVolumeChi / 2) / theta) *
      ∑' j : ℕ, ((j : ℝ) + 2) ^ 3 *
        Real.exp (-(collapsedVolumeChi / 2) * ((j : ℝ) + 1) ^ 2) := by
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (collapsedVolumeTail_summable htheta)
    ((summable_cubic_gaussian (half_pos collapsedVolumeChi_pos)).mul_left _)
  intro j
  calc
    ((j : ℝ) + 2) ^ 3 * Real.exp (-collapsedVolumeChi * ((j : ℝ) + 1) ^ 2 / theta) ≤
        ((j : ℝ) + 2) ^ 3 * (Real.exp (-(collapsedVolumeChi / 2) / theta) *
          Real.exp (-(collapsedVolumeChi / 2) * ((j : ℝ) + 1) ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (gaussian_tail_factor collapsedVolumeChi_pos htheta htheta1 j) (by positivity)
    _ = Real.exp (-(collapsedVolumeChi / 2) / theta) *
        (((j : ℝ) + 2) ^ 3 * Real.exp (-(collapsedVolumeChi / 2) * ((j : ℝ) + 1) ^ 2)) := by
      ring


theorem collapsedReducedVolumeTail_tendsto_zero (a : ℝ) :
    Tendsto (collapsedReducedVolumeTail a) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let K : ℝ := (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * (4 * Real.pi / 3) *
    ∑' j : ℕ, ((j : ℝ) + 2) ^ 3 *
      Real.exp (-(collapsedVolumeChi / 2) * ((j : ℝ) + 1) ^ 2)
  have hdecay : Tendsto
      (fun theta : ℝ => theta ^ (-(3 / 2 : ℝ)) *
        Real.exp (-(collapsedVolumeChi / 2) / theta)) (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 / 2)
      (collapsedVolumeChi / 2) (half_pos collapsedVolumeChi_pos)).comp
        tendsto_inv_nhdsGT_zero
    apply h.congr
    intro theta
    dsimp only [Function.comp_def]
    rw [← Real.rpow_neg_eq_inv_rpow]
    simp only [div_eq_mul_inv]
  have hprefactor : Tendsto (fun theta : ℝ => Real.exp (1 + a * theta / 3))
      (𝓝[>] 0) (𝓝 (Real.exp 1)) := by
    have hcont : Continuous (fun theta : ℝ => Real.exp (1 + a * theta / 3)) := by fun_prop
    simpa only [mul_zero, zero_div, add_zero] using
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hupper : Tendsto
      (fun theta : ℝ => Real.exp (1 + a * theta / 3) *
        (theta ^ (-(3 / 2 : ℝ)) * Real.exp (-(collapsedVolumeChi / 2) / theta)) * K)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (hprefactor.mul hdecay).mul_const K
  apply squeeze_zero' _ _ hupper
  · filter_upwards [self_mem_nhdsWithin] with theta (htheta : 0 < theta)
    exact collapsedReducedVolumeTail_nonneg a htheta
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with theta (htheta : 0 < theta) (htheta1 : theta < 1)
    have hbound := mul_le_mul_of_nonneg_left (collapsedVolumeTail_series_le htheta htheta1.le)
      (by positivity : 0 ≤ Real.exp (1 + a * theta / 3) *
        (4 * Real.pi * theta) ^ (-(3 / 2 : ℝ)) * (4 * Real.pi / 3))
    change collapsedReducedVolumeTail a theta ≤ _
    unfold collapsedReducedVolumeTail
    refine hbound.trans_eq ?_
    rw [Real.mul_rpow (by positivity : 0 ≤ 4 * Real.pi) htheta.le]
    dsimp only [K]
    ring


theorem exists_collapsedVolumeTail_small (a : ℝ) :
    ∃ theta : ℝ, 0 < theta ∧ theta ≤ 1 ∧
      collapsedReducedVolumeTail a theta < Real.exp (-1) / 4 := by
  have heps : 0 < Real.exp (-1 : ℝ) / 4 := by positivity
  have hsmall := (collapsedReducedVolumeTail_tendsto_zero a).eventually
    (Iio_mem_nhds heps)
  have hpos : ∀ᶠ theta : ℝ in 𝓝[>] 0, 0 < theta := self_mem_nhdsWithin
  have hlt : ∀ᶠ theta : ℝ in 𝓝[>] 0, theta < 1 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨theta, htheta, htheta1, htail⟩ := (hpos.and (hlt.and hsmall)).exists
  exact ⟨theta, htheta, htheta1.le, htail⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
