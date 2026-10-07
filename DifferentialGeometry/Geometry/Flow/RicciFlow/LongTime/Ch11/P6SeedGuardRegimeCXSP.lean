import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedTimeArithmeticCXSP

set_option autoImplicit false

/-!
# CX-SPINE G11：由 (c) 自身 smallness 生产 v6 guard 的时间 regime

r_n≤√t_n/(n+1) 与 positive antitone nr 足以说明：对任意固定 T，最终满足 nr(t_n)≤r_n
的项都在 T 之后。因此 guard 频繁时有原时间趋无穷的实际子列，否则最终 r_n<nr(t_n)。
不使用 scalar、non-Good、selected ceiling 或 r√Q 发散；也不需要先抽有界时间子列。
-/

open Set Filter
open scoped Topology

namespace GC.LongTime.Ch11

/-- (c) 的终点曲率发散直接给相对固定 anchor Q₀=H/r² 的 ratio，不使用 selected ceiling。 -/
theorem seed_endpoint_ratio_tendsto_CXSP {H : ℝ} (hH : 0 < H) {R r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n)
    (hhigh : Tendsto (fun n => R n * r n ^ 2) atTop atTop) :
    Tendsto (fun n => R n / (H * (r n ^ 2)⁻¹)) atTop atTop := by
  have heq : (fun n => R n / (H * (r n ^ 2)⁻¹)) =
      (fun n => (R n * r n ^ 2) / H) := by
    funext n
    field_simp [hH.ne', (hr n).ne']
  rw [heq]
  exact hhigh.atTop_div_const hH

/-- (c) 的小半径族中，v6 guard 成立的项最终超过任意固定时间。 -/
theorem seed_guard_eventually_late_CXSP {nr : ℝ → ℝ}
    (hpos : ∀ s, 0 ≤ s → 0 < nr s) (hanti : AntitoneOn nr (Ici 0))
    {t r : ℕ → ℝ} (ht : ∀ n, 0 ≤ t n)
    (hsmall : ∀ n, r n ≤ Real.sqrt (t n) / ((n : ℝ) + 1)) (B : ℝ) :
    ∀ᶠ n in atTop, nr (t n) ≤ r n → B ≤ t n := by
  let T := max B 0
  have hT : 0 ≤ T := le_max_right _ _
  have hnr : 0 < nr T := hpos T hT
  have hlim : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_gt_atTop (Real.sqrt T / nr T)] with n hn
  intro hguard
  by_contra hnot
  have htB : t n < B := lt_of_not_ge hnot
  have htT : t n ≤ T := htB.le.trans (le_max_left _ _)
  have hrad : nr T ≤ r n := (hanti (ht n) hT htT).trans hguard
  have hlow := mul_le_mul_of_nonneg_right hrad (by positivity : 0 ≤ (n : ℝ) + 1)
  have hu : r n * ((n : ℝ) + 1) ≤ Real.sqrt T :=
    ((le_div_iff₀ (by positivity)).mp (hsmall n)).trans (Real.sqrt_le_sqrt htT)
  have hbig := (div_lt_iff₀ hnr).mp hn
  nlinarith

/-- 任意 (c) 小半径族分为 guard 晚期子列，或最终进入 native 小种子；无 (b) selection 输入。 -/
theorem seed_guard_late_subsequence_or_native_CXSP {nr : ℝ → ℝ}
    (hpos : ∀ s, 0 ≤ s → 0 < nr s) (hanti : AntitoneOn nr (Ici 0))
    {t r : ℕ → ℝ} (ht : ∀ n, 0 ≤ t n)
    (hsmall : ∀ n, r n ≤ Real.sqrt (t n) / ((n : ℝ) + 1)) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ n, nr (t (φ n)) ≤ r (φ n)) ∧
      Tendsto (fun n => t (φ n)) atTop atTop) ∨
      ∀ᶠ n in atTop, r n < nr (t n) := by
  by_cases hfreq : ∃ᶠ n in atTop, nr (t n) ≤ r n
  · obtain ⟨φ, hφ, hguard⟩ := extraction_of_frequently_atTop hfreq
    refine Or.inl ⟨φ, hφ, hguard, tendsto_atTop.mpr ?_⟩
    intro B
    filter_upwards [hφ.tendsto_atTop.eventually
      (seed_guard_eventually_late_CXSP hpos hanti ht hsmall B)] with n hn
    exact hn (hguard n)
  · exact Or.inr (by simpa only [not_frequently, not_le] using hfreq)

/-- consumer：若 guard 最终始终成立，原时间本身趋无穷，无需重索引。 -/
example {nr : ℝ → ℝ} (hpos : ∀ s, 0 ≤ s → 0 < nr s)
    (hanti : AntitoneOn nr (Ici 0)) {t r : ℕ → ℝ} (ht : ∀ n, 0 ≤ t n)
    (hsmall : ∀ n, r n ≤ Real.sqrt (t n) / ((n : ℝ) + 1))
    (hguard : ∀ᶠ n in atTop, nr (t n) ≤ r n) : Tendsto t atTop atTop := by
  refine tendsto_atTop.mpr fun B => ?_
  filter_upwards [hguard, seed_guard_eventually_late_CXSP hpos hanti ht hsmall B] with n hg hn
  exact hn hg

end GC.LongTime.Ch11
