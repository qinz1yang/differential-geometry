import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.ConvergenceRadius
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# F3-c (c5)：Taylor criterion（O-MY-F3C G5a，后缀 `_F3C`）

`‖D^n f‖ ≤ C K^n n!` 在 `ball x r` 上一致成立 ⇒ `f` 在 `x` 实解析（Mathlib `AnalyticAt`）。
证明：Mathlib 的多元 Taylor 积分余项 `map_add_eq_sum_add_integral_iteratedFDeriv`，余项
`≤ C (n+1) (K‖y‖)^{n+1} → 0`；形式幂级数 `p n = (n!)⁻¹ • D^n f x`，`‖p n‖ ≤ C K^n`，
收敛半径 `≥ min r K⁻¹`。写法 following Armstrong–Vicol CIVAxisymmetric D12（Apache-2.0）的
`analyticAt_of_norm_iteratedFDeriv_le`，独立重写，不搬。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ENNReal NNReal Nat ContDiff

namespace DifferentialGeometry.Analysis.Elliptic.HarmonicMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Taylor 级数 `p n = (n!)⁻¹ • D^n f x`。 -/
def taylorSeries_F3C (f : E → F) (x : E) : FormalMultilinearSeries ℝ E F :=
  fun n => ((n ! : ℝ)⁻¹) • iteratedFDeriv ℝ n f x

theorem norm_taylorSeries_le_F3C {f : E → F} {x : E} {C K : ℝ}
    (hb : ∀ n : ℕ, ‖iteratedFDeriv ℝ n f x‖ ≤ C * K ^ n * n !) (n : ℕ) :
    ‖taylorSeries_F3C f x n‖ ≤ C * K ^ n := by
  have hpos : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  rw [taylorSeries_F3C, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos,
    inv_mul_le_iff₀ hpos]
  linarith [hb n]

/-- 多重线性映射在对角上的范数界。 -/
theorem norm_apply_diag_le_F3C {n : ℕ} (L : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F)
    (y : E) : ‖L (fun _ => y)‖ ≤ ‖L‖ * ‖y‖ ^ n := by
  have h := L.le_opNorm (fun _ => y)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

variable [CompleteSpace F]

/-- **Taylor criterion（c5）**：`ball x r` 上 `‖D^n f‖ ≤ C K^n n!`（所有 `n`）⇒ `AnalyticAt ℝ f x`。 -/
theorem analyticAt_of_norm_iteratedFDeriv_le_F3C {f : E → F} {x : E} {r C K : ℝ}
    (hr : 0 < r) (hK : 0 < K) (hf : ContDiffOn ℝ ∞ f (ball x r))
    (hb : ∀ n : ℕ, ∀ y ∈ ball x r, ‖iteratedFDeriv ℝ n f y‖ ≤ C * K ^ n * n !) :
    AnalyticAt ℝ f x := by
  have hx : x ∈ ball x r := mem_ball_self hr
  have hC : 0 ≤ C := by
    have h := hb 0 x hx
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one] at h
    exact (norm_nonneg _).trans h
  set ρ : ℝ := min r K⁻¹ with hρdef
  have hρ : 0 < ρ := lt_min hr (inv_pos.mpr hK)
  have hKρ : K * ρ ≤ 1 := by
    calc K * ρ ≤ K * K⁻¹ := mul_le_mul_of_nonneg_left (min_le_right _ _) hK.le
      _ = 1 := mul_inv_cancel₀ hK.ne'
  have hpb := norm_taylorSeries_le_F3C (fun n => hb n x hx)
  refine ⟨taylorSeries_F3C f x, ENNReal.ofReal ρ, ?_⟩
  refine ⟨?_, ENNReal.ofReal_pos.mpr hρ, ?_⟩
  · -- 收敛半径
    have hbd : ∀ n : ℕ, ‖taylorSeries_F3C f x n‖ * ((ρ.toNNReal : ℝ≥0) : ℝ) ^ n ≤ C := by
      intro n
      rw [Real.coe_toNNReal _ hρ.le]
      calc ‖taylorSeries_F3C f x n‖ * ρ ^ n ≤ C * K ^ n * ρ ^ n :=
            mul_le_mul_of_nonneg_right (hpb n) (pow_nonneg hρ.le n)
        _ = C * (K * ρ) ^ n := by rw [mul_pow, mul_assoc]
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left
            (pow_le_one₀ (mul_nonneg hK.le hρ.le) hKρ) hC
        _ = C := mul_one C
    have h := (taylorSeries_F3C f x).le_radius_of_bound C hbd
    exact h
  · intro y hy
    have hyρ : ‖y‖ < ρ := by
      rw [Metric.mem_eball, edist_dist, dist_zero_right] at hy
      exact (ENNReal.ofReal_lt_ofReal_iff hρ).mp hy
    have hyr : ‖y‖ < r := hyρ.trans_le (min_le_left _ _)
    set q : ℝ := K * ‖y‖ with hqdef
    have hq0 : 0 ≤ q := mul_nonneg hK.le (norm_nonneg y)
    have hq1 : q < 1 := by
      calc q < K * ρ := mul_lt_mul_of_pos_left hyρ hK
        _ ≤ 1 := hKρ
    -- 线段在球内
    have hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • y ∈ ball x r := by
      intro t ht
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht.1]
      calc t * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg y)
        _ < r := by rw [one_mul]; exact hyr
    -- 项的范数界（可和）
    have hterm : ∀ n, ‖taylorSeries_F3C f x n (fun _ => y)‖ ≤ C * q ^ n := by
      intro n
      calc ‖taylorSeries_F3C f x n (fun _ => y)‖ ≤ ‖taylorSeries_F3C f x n‖ * ‖y‖ ^ n :=
            norm_apply_diag_le_F3C _ y
        _ ≤ C * K ^ n * ‖y‖ ^ n := mul_le_mul_of_nonneg_right (hpb n) (pow_nonneg (norm_nonneg y) n)
        _ = C * q ^ n := by rw [hqdef, mul_pow, mul_assoc]
    have hsum : Summable fun n => ‖taylorSeries_F3C f x n (fun _ => y)‖ :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm
        ((summable_geometric_of_lt_one hq0 hq1).mul_left C)
    rw [hasSum_iff_tendsto_nat_of_summable_norm hsum]
    -- 余项 → 0
    have hrem : ∀ n : ℕ, ‖f (x + y) - ∑ i ∈ Finset.range (n + 1),
        taylorSeries_F3C f x i (fun _ => y)‖ ≤ C * ((n + 1 : ℕ) * q ^ (n + 1)) := by
      intro n
      have hT := map_add_eq_sum_add_integral_iteratedFDeriv (n := n) (f := f) (x := x) (y := y)
        (fun t ht => (hf.contDiffAt (isOpen_ball.mem_nhds (hseg t ht))).of_le
          (by exact_mod_cast le_top))
      have hsumeq : ∑ i ∈ Finset.range (n + 1), taylorSeries_F3C f x i (fun _ => y) =
          ∑ k ∈ Finset.range (n + 1), (k ! : ℝ)⁻¹ • (iteratedFDeriv ℝ k f x (fun _ => y)) := by
        rfl
      rw [hsumeq, hT, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos (by exact_mod_cast Nat.factorial_pos n : (0 : ℝ) < n !)]
      have hint : ‖∫ t in (0 : ℝ)..1, (1 - t) ^ n •
          iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖ ≤
            C * K ^ (n + 1) * (n + 1) ! * ‖y‖ ^ (n + 1) * |1 - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t ht
        rw [uIoc_of_le zero_le_one] at ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
        have h1 : |1 - t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
        rw [norm_smul, Real.norm_eq_abs, abs_pow]
        calc |1 - t| ^ n * ‖iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖
            ≤ 1 * (‖iteratedFDeriv ℝ (n + 1) f (x + t • y)‖ * ‖y‖ ^ (n + 1)) :=
              mul_le_mul (pow_le_one₀ (abs_nonneg _) h1) (norm_apply_diag_le_F3C _ y)
                (norm_nonneg _) zero_le_one
          _ ≤ 1 * (C * K ^ (n + 1) * (n + 1) ! * ‖y‖ ^ (n + 1)) := by
              gcongr
              exact hb (n + 1) _ (hseg t ht')
          _ = C * K ^ (n + 1) * (n + 1) ! * ‖y‖ ^ (n + 1) := one_mul _
      have hfac : ((n + 1) ! : ℝ) = (n + 1 : ℕ) * n ! := by
        rw [Nat.factorial_succ, Nat.cast_mul]
      have hnpos : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
      calc (n ! : ℝ)⁻¹ * ‖∫ t in (0 : ℝ)..1, (1 - t) ^ n •
            iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖
          ≤ (n ! : ℝ)⁻¹ * (C * K ^ (n + 1) * (n + 1) ! * ‖y‖ ^ (n + 1) * |1 - 0|) :=
            mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hnpos.le)
        _ = C * ((n + 1 : ℕ) * q ^ (n + 1)) := by
            rw [hfac, hqdef, mul_pow]
            field_simp
            simp
    have hlim : Tendsto (fun n : ℕ => C * ((n + 1 : ℕ) * q ^ (n + 1))) atTop (𝓝 0) := by
      have h := (tendsto_self_mul_const_pow_of_lt_one hq0 hq1).comp (tendsto_add_atTop_nat 1)
      have h' := h.const_mul C
      rw [mul_zero] at h'
      refine h'.congr fun n => ?_
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    have hlim' : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
        taylorSeries_F3C f x i (fun _ => y)) atTop (𝓝 (f (x + y))) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
      rw [norm_sub_rev]
      exact hrem n
    exact (tendsto_add_atTop_iff_nat 1).mp hlim'

end DifferentialGeometry.Analysis.Elliptic.HarmonicMap
