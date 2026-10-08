import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SepRhoPlusFixV2P6SF

/-!
# CX-WIRE：窗口 records 的 late recenter，实际消去逐 record 的小量前提

由同一 q 的 delta 衰减，内部选择 recenter 的晚期阈值；窗口的原始时刻超过 Tno/2，
而 Tno≥n+1，所以最终所有窗口 records 都满足该阈值。J6 仍用同一 n、同一 records、
同一 Qs_loc；没有把重索引后的序号替换进不等式。

haccuracy 仍是已有 profile 条件，actual q₀ 的该条件需要 C12-7′c 构造付款。
本文件只处理窗口支，不以窗口晚期性循环支付 young-cap 支；后者另由 early-volume 桥处理。
-/

set_option autoImplicit false
noncomputable section

open Set Filter DifferentialGeometry
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- 同一 profile 的 delta→0 实际生产 late recenter 阈值，不要求 t=0 的全局小量。 -/
theorem exists_late_recenter_CXW {q : CutoffParameters}
    (hdelta : Tendsto q.delta atTop (𝓝 0)) :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t → q.recenterConstant * q.delta t ≤ 1 / 2 := by
  have hlim : Tendsto (fun t => q.recenterConstant * q.delta t) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hdelta
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  exact ⟨max 1 T, lt_max_of_lt_left one_pos,
    fun t ht => (hT t ((le_max_right 1 T).trans ht)).le⟩

/-- 在 Tno/2 之后的全部实数同时付 late recenter；不预先挑选窗口 record。 -/
theorem eventually_recenter_on_late_windows_CXW {q : CutoffParameters}
    (hdelta : Tendsto q.delta atTop (𝓝 0)) {Tno : ℕ → ℝ}
    (hTno : Tendsto Tno atTop atTop) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, Tno n / 2 ≤ t →
      q.recenterConstant * q.delta t ≤ 1 / 2 := by
  obtain ⟨T, _hT, hlate⟩ := exists_late_recenter_CXW hdelta
  filter_upwards [hTno.eventually_ge_atTop (2 * T)] with n hn
  intro t ht
  exact hlate t (by linarith)

/-- 实际固定 q records 的 J6：delta 衰减 + 原窗口字段付款 hΛδ，无新全局 recenter。 -/
theorem j6_eventually_of_accuracy_delta_CXW
    {Ho : ℕ → RetainedCoreHistory.{u}} {q : CutoffParameters}
    {T₀ c σ L R Tno Tn : ℕ → ℝ}
    (recordsK : ∀ n (i : Fin (Ho n).eventCount),
      max (T₀ n) (c n * (σ n - L n / R n)) ≤ (Ho n).time i.succ →
        GeometricCutoffRecord (Ho n).toHistory i q)
    (hc : ∀ n, 0 < c n) (hTn : ∀ n, Tn n = Tno n / c n)
    (h2 : ∀ n, 2 * c n < Tno n) (hNT : ∀ n : ℕ, (n : ℝ) + 1 ≤ Tno n)
    (hR1 : ∀ n, 1 ≤ R n) (hL : ∀ n, Tn n - 1 ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hacc : ∀ u : ℝ, 0 ≤ u →
      q.delta u ^ 2 * q.neckRadius u < q.neckRadius (2 * u) / (u + 1))
    (hdelta : Tendsto q.delta atTop (𝓝 0))
    (hρc : ∀ n : ℕ, q.neckRadius (Tno n) ^ 2 ≤ c n / ((n : ℝ) + 1)) :
    ∀ᶠ n : ℕ in atTop, ∀ i hi b,
      ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n)
        (max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹) ≤
      ((recordsK n i hi).static b).neck.scale := by
  have hTno : Tendsto Tno atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith [hNT n]) tendsto_natCast_atTop_atTop
  filter_upwards [eventually_recenter_on_late_windows_CXW hdelta hTno] with n hn
  intro i hi b
  rw [← max_assoc, max_self]
  have hTno0 : 0 ≤ Tno n := by linarith [hc n, h2 n]
  have hlate : Tno n ≤ 2 * max (T₀ n) (c n * (σ n - L n / R n)) := by
    have hh := late_of_Ldomain_P6SF (hc n) (hTn n) (h2 n) (hR1 n) (hL n)
      (le_max_right (T₀ n) (c n * (σ n - L n / R n)))
    linarith
  apply hpastJ6_of_accuracy_P6SF (recordsK n) hanti hTno0 (Nat.cast_add_one_pos n)
    (hc n) (hρc n) hlate (hNT n) hacc ?_ i hi b
  intro j hj
  exact hn ((Ho n).time j.succ) (by linarith)

/-- 实际 consumer：抽取严格尾列，并将原序号的更强系数单调弱化为新 n+1；付 J6 的 ∀n 形。 -/
theorem j6_on_tail_of_accuracy_delta_CXW
    {Ho : ℕ → RetainedCoreHistory.{u}} {q : CutoffParameters}
    {T₀ c σ L R Tno Tn : ℕ → ℝ}
    (recordsK : ∀ n (i : Fin (Ho n).eventCount),
      max (T₀ n) (c n * (σ n - L n / R n)) ≤ (Ho n).time i.succ →
        GeometricCutoffRecord (Ho n).toHistory i q)
    (hc : ∀ n, 0 < c n) (hTn : ∀ n, Tn n = Tno n / c n)
    (h2 : ∀ n, 2 * c n < Tno n) (hNT : ∀ n : ℕ, (n : ℝ) + 1 ≤ Tno n)
    (hR1 : ∀ n, 1 ≤ R n) (hL : ∀ n, Tn n - 1 ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hacc : ∀ u : ℝ, 0 ≤ u →
      q.delta u ^ 2 * q.neckRadius u < q.neckRadius (2 * u) / (u + 1))
    (hdelta : Tendsto q.delta atTop (𝓝 0))
    (hρc : ∀ n : ℕ, q.neckRadius (Tno n) ^ 2 ≤ c n / ((n : ℝ) + 1)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ (n : ℕ) i hi b,
      ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c (φ n))
        (max (((n : ℝ) + 1) / c (φ n)) (q.neckRadius (Tno (φ n)) ^ 2)⁻¹) ≤
      ((recordsK (φ n) i hi).static b).neck.scale := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (j6_eventually_of_accuracy_delta_CXW recordsK hc hTn h2 hNT hR1 hL hanti hacc hdelta hρc)
  let φ : ℕ → ℕ := fun n => n + N
  refine ⟨φ, fun i j hij => Nat.add_lt_add_right hij N, ?_⟩
  intro n i hi b
  have hpaid := hN (n + N) (Nat.le_add_left N n) i hi b
  have hm : (n : ℝ) + 1 ≤ ((φ n : ℕ) : ℝ) + 1 := by
    dsimp only [φ]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hcpos := hc (φ n)
  have hd := div_le_div_of_nonneg_right hm hcpos.le
  have hmax := max_le_max hd
    (max_le_max hd (le_refl (q.neckRadius (Tno (φ n)) ^ 2)⁻¹))
  exact (mul_le_mul hm hmax (by positivity) (by positivity)).trans hpaid

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
