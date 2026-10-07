import DifferentialGeometry.Analysis.Elliptic.Planar.AnalyticNodalRootR3AW
import DifferentialGeometry.Analysis.Elliptic.Planar.PolarZeroLocalization
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Algebra.Order.ToIntervalMod

/-!
# R3a-ω（`_R3AW`）F4a：极坐标 `2k` 条根弧（纯实变量）

`W(r, θ)` 在 `|r| < ε` 光滑、`θ` 方向 `2π` 周期，`W(0, θ) = c sin (k (θ - θ₀))`（`c ≠ 0`）：
对每个 `m < 2k` 有光滑根弧 `ϑ_m(r)`（`ϑ_m(0) = θ₀ + mπ/k`），其零点非退化，彼此在 `2π` 同余意义下分离，
且 `0 ≤ r < ρ₁` 内 `W(r, ·)` 的零点（模 `2π`）恰是这 `2k` 条弧。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

/-- 极坐标 blow-up `W(r, θ)` 的 `0` 层是 `c sin (k (θ - θ₀))`（`c ≠ 0`）时的 `2k` 条根弧数据（纯实变量）。 -/
theorem polar_root_arcs_R3AW {W : ℝ × ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hW : ContDiffOn ℝ ∞ W {q : ℝ × ℝ | |q.1| < ε})
    (hper : ∀ r : ℝ, |r| < ε → Function.Periodic (fun θ => W (r, θ)) (2 * Real.pi))
    {k : ℕ} (hk : 1 ≤ k) {c θ₀ : ℝ} (hc : c ≠ 0)
    (hW0 : ∀ θ : ℝ, W (0, θ) = c * Real.sin (k * (θ - θ₀))) :
    ∃ ρ₁ : ℝ, 0 < ρ₁ ∧ ρ₁ ≤ ε ∧ ∃ ϑ : Fin (2 * k) → ℝ → ℝ,
      (∀ m, ϑ m 0 = θ₀ + ((m : ℕ) : ℝ) * Real.pi / k) ∧
      (∀ m, ContDiffOn ℝ ∞ (ϑ m) (Ioo (-ρ₁) ρ₁)) ∧
      (∀ m, ∀ r : ℝ, |r| < ρ₁ → W (r, ϑ m r) = 0 ∧ fderiv ℝ W (r, ϑ m r) (0, 1) ≠ 0) ∧
      (∀ m m', m ≠ m' → ∀ r : ℝ, |r| < ρ₁ → ∀ n : ℤ, ϑ m r ≠ ϑ m' r + 2 * Real.pi * n) ∧
      (∀ r : ℝ, 0 ≤ r → r < ρ₁ → ∀ θ : ℝ, W (r, θ) = 0 →
        ∃ m, ∃ n : ℤ, θ = ϑ m r + 2 * Real.pi * n) := by
  classical
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set θm : Fin (2 * k) → ℝ := fun m => θ₀ + ((m : ℕ) : ℝ) * Real.pi / k with hθm
  have hzero_m : ∀ m, W (0, θm m) = 0 := by
    intro m
    rw [hW0]
    have : (k : ℝ) * (θm m - θ₀) = ((m : ℕ) : ℝ) * Real.pi := by
      simp only [hθm]
      field_simp
      ring
    rw [this, Real.sin_nat_mul_pi, mul_zero]
  have hderiv_m : ∀ m, fderiv ℝ W (0, θm m) (0, 1) ≠ 0 := by
    intro m
    have hopen : IsOpen {q : ℝ × ℝ | |q.1| < ε} :=
      isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
    have hWd : DifferentiableAt ℝ W (0, θm m) :=
      ((hW.contDiffAt (hopen.mem_nhds (by simp [hε]))).differentiableAt (by simp))
    have h1 : HasDerivAt (fun θ : ℝ => W (0, θ)) (fderiv ℝ W (0, θm m) (0, 1)) (θm m) := by
      have hl : HasDerivAt (fun θ : ℝ => ((0 : ℝ), θ)) ((0 : ℝ), (1 : ℝ)) (θm m) :=
        HasDerivAt.prodMk (hasDerivAt_const (θm m) (0 : ℝ)) (hasDerivAt_id (θm m))
      exact hWd.hasFDerivAt.comp_hasDerivAt (θm m) hl
    have h2 : HasDerivAt (fun θ : ℝ => W (0, θ))
        (c * (Real.cos (k * (θm m - θ₀)) * k)) (θm m) := by
      have : (fun θ : ℝ => W (0, θ)) = fun θ => c * Real.sin (k * (θ - θ₀)) := funext hW0
      rw [this]
      have h3 := ((hasDerivAt_id (θm m)).sub_const θ₀).const_mul (k : ℝ) |>.sin.const_mul c
      simpa using h3
    rw [h1.unique h2]
    have : (k : ℝ) * (θm m - θ₀) = ((m : ℕ) : ℝ) * Real.pi := by
      simp only [hθm]
      field_simp
      ring
    rw [this, Real.cos_nat_mul_pi]
    have : ((-1 : ℝ) ^ (m : ℕ)) ≠ 0 := pow_ne_zero _ (by norm_num)
    exact mul_ne_zero hc (mul_ne_zero this hkpos.ne')
  have hη : (0 : ℝ) < Real.pi / (2 * k) := by positivity
  have hloc := fun m : Fin (2 * k) =>
    exists_simple_root_arc_R3AW hε hW (hzero_m m) (hderiv_m m) hη
  choose η' hη'pos hη'le δ hδpos hδε ϑ hϑ0 hϑC hϑprop huniq using hloc
  -- 紧致覆盖
  set a₀ : ℝ := θ₀ - Real.pi / (2 * k) with ha₀
  have hp2 : (0 : ℝ) < 2 * Real.pi := by positivity
  let O' : Set ℝ := ⋃ m : Fin (2 * k), Metric.ball (θm m) (η' m)
  have hO' : IsOpen O' := isOpen_iUnion fun _ => Metric.isOpen_ball
  have hWcont : ContinuousOn W (Ico 0 ε ×ˢ (univ : Set ℝ)) := by
    refine hW.continuousOn.mono ?_
    rintro q ⟨hq, -⟩
    change |q.1| < ε
    rw [abs_of_nonneg hq.1]
    exact hq.2
  have hzero : ∀ θ ∈ Icc a₀ (a₀ + 2 * Real.pi), W (0, θ) = 0 → θ ∈ O' := by
    intro θ hθ hW00
    rw [hW0] at hW00
    have hsin : Real.sin (k * (θ - θ₀)) = 0 := by
      rcases mul_eq_zero.mp hW00 with h | h
      · exact absurd h hc
      · exact h
    obtain ⟨j, hj⟩ := Real.sin_eq_zero_iff.mp hsin
    have hlo : (-1 : ℝ) < j := by
      by_contra hcon
      push Not at hcon
      have h1 : (k : ℝ) * (a₀ - θ₀) ≤ k * (θ - θ₀) := by
        apply mul_le_mul_of_nonneg_left _ hkpos.le
        linarith [hθ.1]
      have h2 : (k : ℝ) * (a₀ - θ₀) = -(Real.pi / 2) := by
        simp only [ha₀]
        field_simp
        ring
      have h3 : (j : ℝ) * Real.pi ≤ -Real.pi := by
        have := mul_le_mul_of_nonneg_right hcon Real.pi_pos.le
        linarith
      nlinarith [Real.pi_pos]
    have hhi : (j : ℝ) < 2 * k := by
      by_contra hcon
      push Not at hcon
      have h1 : (k : ℝ) * (θ - θ₀) ≤ k * (a₀ + 2 * Real.pi - θ₀) := by
        apply mul_le_mul_of_nonneg_left _ hkpos.le
        linarith [hθ.2]
      have h2 : (k : ℝ) * (a₀ + 2 * Real.pi - θ₀) = 2 * k * Real.pi - Real.pi / 2 := by
        simp only [ha₀]
        field_simp
        ring
      have h3 : 2 * (k : ℝ) * Real.pi ≤ (j : ℝ) * Real.pi :=
        mul_le_mul_of_nonneg_right hcon Real.pi_pos.le
      nlinarith [Real.pi_pos]
    have hj0 : 0 ≤ j := by
      have : (-1 : ℤ) < j := by exact_mod_cast hlo
      omega
    have hj2 : j < 2 * k := by exact_mod_cast hhi
    refine mem_iUnion.mpr ⟨⟨j.toNat, by omega⟩, ?_⟩
    have hθeq : θ = θm ⟨j.toNat, by omega⟩ := by
      have hjc : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hj0
      simp only [hθm, hjc]
      field_simp
      linarith
    rw [hθeq]
    exact Metric.mem_ball_self (hη'pos _)
  obtain ⟨κ, hκ, hκε, hcov⟩ :=
    exists_pos_radius_zero_mem_open_of_isCompact hε hWcont isCompact_Icc hO' hzero
  have hne : (Finset.univ : Finset (Fin (2 * k))).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  set δm : ℝ := Finset.univ.inf' hne δ with hδm
  have hδmpos : 0 < δm := (Finset.lt_inf'_iff hne).mpr fun m _ => hδpos m
  have hδmle : ∀ m, δm ≤ δ m := fun m => Finset.inf'_le _ (Finset.mem_univ m)
  set ρ₁ : ℝ := min (min κ δm) ε with hρ₁
  have hρ₁pos : 0 < ρ₁ := lt_min (lt_min hκ hδmpos) hε
  have hρ₁κ : ρ₁ ≤ κ := (min_le_left _ _).trans (min_le_left _ _)
  have hρ₁δ : ∀ m, ρ₁ ≤ δ m := fun m => ((min_le_left _ _).trans (min_le_right _ _)).trans (hδmle m)
  have hρ₁ε : ρ₁ ≤ ε := min_le_right _ _
  refine ⟨ρ₁, hρ₁pos, hρ₁ε, ϑ, hϑ0, fun m => ?_, fun m r hr => ?_, ?_, ?_⟩
  · refine (hϑC m).mono (Ioo_subset_Ioo ?_ ?_)
    · linarith [hρ₁δ m]
    · exact hρ₁δ m
  · have := (hϑprop m r (hr.trans_le (hρ₁δ m))).2
    exact this
  · intro m m' hmm r hr n heq
    have hr1 := hϑprop m r (hr.trans_le (hρ₁δ m))
    have hr2 := hϑprop m' r (hr.trans_le (hρ₁δ m'))
    have e1 : |ϑ m r - θm m| < η' m := hr1.1
    have e2 : |ϑ m' r - θm m'| < η' m' := hr2.1
    have h1 : η' m ≤ Real.pi / (2 * k) := hη'le m
    have h2 : η' m' ≤ Real.pi / (2 * k) := hη'le m'
    have habs : |((m : ℕ) - (m' : ℕ) - 2 * k * n : ℝ)| * (Real.pi / k) < Real.pi / k := by
      have hid : ((m : ℕ) - (m' : ℕ) - 2 * k * n : ℝ) * (Real.pi / k) =
          (ϑ m' r - θm m') - (ϑ m r - θm m) := by
        simp only [hθm]
        have : ϑ m r = ϑ m' r + 2 * Real.pi * n := heq
        rw [this]
        field_simp
        ring
      rw [← abs_of_pos (show 0 < Real.pi / k by positivity), ← abs_mul, hid,
        abs_of_pos (show 0 < Real.pi / k by positivity)]
      calc |ϑ m' r - θm m' - (ϑ m r - θm m)| ≤ |ϑ m' r - θm m'| + |ϑ m r - θm m| := abs_sub _ _
        _ < Real.pi / (2 * k) + Real.pi / (2 * k) := add_lt_add (e2.trans_le h2) (e1.trans_le h1)
        _ = Real.pi / k := by field_simp; ring
    have habs1 : |((m : ℕ) - (m' : ℕ) - 2 * k * n : ℝ)| < 1 := by
      have hpk : 0 < Real.pi / k := by positivity
      nlinarith
    have habsZ : |(((m : ℕ) : ℤ) - ((m' : ℕ) : ℤ) - 2 * (k : ℤ) * n)| < 1 := by
      exact_mod_cast habs1
    have hm : (m : ℕ) < 2 * k := m.2
    have hm' : (m' : ℕ) < 2 * k := m'.2
    have hmne : (m : ℕ) ≠ (m' : ℕ) := fun h => hmm (Fin.ext h)
    rw [abs_lt] at habsZ
    have hd : ((m : ℕ) : ℤ) - ((m' : ℕ) : ℤ) = 2 * (k : ℤ) * n := by omega
    rcases lt_trichotomy n 0 with hn | hn | hn
    · have : 2 * (k : ℤ) * n ≤ -(2 * (k : ℤ)) := by nlinarith
      omega
    · subst hn
      omega
    · have : 2 * (k : ℤ) ≤ 2 * (k : ℤ) * n := by nlinarith
      omega
  · intro r hr0 hrρ θ hθ
    set n := toIcoDiv hp2 a₀ θ with hn
    set θ' := θ - n • (2 * Real.pi) with hθ'
    have hθ'mem : θ' ∈ Ico a₀ (a₀ + 2 * Real.pi) := by
      have := toIcoMod_mem_Ico hp2 a₀ θ
      rwa [toIcoMod, ← hn] at this
    have hrε' : |r| < ε := by rw [abs_of_nonneg hr0]; exact hrρ.trans_le hρ₁ε
    have hWθ' : W (r, θ') = 0 := by
      have := (hper r hrε').sub_zsmul_eq (x := θ) n
      rw [hθ', this]
      exact hθ
    have hO'mem := hcov r ⟨hr0, hrρ.trans_le hρ₁κ⟩ θ' (Ico_subset_Icc_self hθ'mem) hWθ'
    obtain ⟨m, hm⟩ := mem_iUnion.mp hO'mem
    have hrδ : |r| < δ m := by rw [abs_of_nonneg hr0]; exact hrρ.trans_le (hρ₁δ m)
    have := huniq m r hrδ θ' (by simpa [Real.dist_eq] using hm) hWθ'
    refine ⟨m, n, ?_⟩
    rw [← this, hθ', zsmul_eq_mul]
    ring

end DifferentialGeometry.Analysis
