import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaK3WrapC11Q7

/-!
# 构造预算 `d_n` 与离散 level 请求的 reduction（O-CH11-KWRAP G2，后缀 `_C11Q7`）

R-C11-6 D-2 (i)(ii) / D-7（审稿 Q1(b)、Q2(R-b)）：

* **(i) δ → 0 不够**（`tendsto_not_budget_C11Q7`：两个趋零正序列，快者从第 1 项起严格在慢者之下）。须把请求
  包络放进 construction budget：`budgetSeq_C11Q7 β n = ¼·min(2^{−n}, {β_{j,ℓ} : 0 ≤ j ≤ ℓ ≤ n})`；
  `budget_construction_C11Q7`：`d_n > 0`、单调不增、趋零，`j ≤ ℓ ≤ n ⇒ d_n ≤ β_{j,ℓ}/4`（每个固定 `j` 从第
  `j` 块起得到支付）。`budget_window_C11Q7`：二进半时间窗 `s ∈ [t/2, t]`（`k(t) ≤ k(s)+1`）上 `δ(s) ≤ d_{k(s)+1}`
  ⇒ `δ(s) ≤ β_{j,k(t)}/4`（`j ≤ k(t)`）。
* **(ii) 离散 level**：`kappaLevel_C11Q7 A = min{m : A < 12·3^m}`（`Nat.find`）；严格保留
  （`lt_levelRep_C11Q7`）、`kappaLevel_le_iff_C11Q7 : level A ≤ m ↔ A < 12·3^m`、单调、边界
  `kappaLevel_boundary_C11Q7 : level(12·3^m) = m+1`；ceiling/log 实现核：`kappaLevel_eq_log_C11Q7`
  （`level A = max 0 (⌊log₃(A/12)⌋ + 1)`，是 floor + 1 **不是** ceiling）与 `clog_boundary_C11Q7`
  （`⌈log₃⌉` 在 `A = 12·3^m` 处给 `m`，只得 `A ≤ 12·3^m`）。
* **reduction lemma** `level_request_dominates_C11Q7`：chooser `req : ℕ → ι` 只在离散代表 `12·3^m` 处取值、
  **不假设单调**；只用请求有效性对参数向下封闭 ⇒ 代表请求 `req(level A)` 支配原请求。块版
  `level_block_supply_C11Q7`：块 `n` 的供给支配有限个代表请求 `{req m n : m ≤ n}` ⇒ 移动请求
  `Req(A, n)` 从块 `level A` 起都被支付（不靠 `RequestCofinal`）。
* **κ 实例**：`levelBarrier_C11Q7 A = Λ_W(12·3^{level A})`（只依赖 `level A`）；
  `weightedMinLevel_le_levelBarrier_C11Q7`（= reduction lemma 的实例，供 G1 wrapper 的 `hΛ`）；
  `surgeryActionBarrier_of_native_fineCap_level_C11Q7`（`hfine` 只在代表点上要求）；
  `budget_schedule_C11Q7`：`α := 代表点包络` 满足 `KappaFineScale`，且预算构造的 `δ ≤ d_{k(s)+1}` 给
  晚期比较 `s ≥ max(1, 2^{level A}) ⇒ δ(s) < α(A, s)`（S7 比较是晚期条件）。
  `α` 绑定 `diagonalAccuracy_C11S q.delta`（D-2 (iii)）不在本文件（GAPTOP2）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-! ## 1. 构造预算 `d_n` -/

/-- 预算的有限请求指标集 `{(j, ℓ) : j ≤ ℓ ≤ n}`。 -/
def budgetPairs_C11Q7 (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter (fun p => p.1 ≤ p.2)

theorem mem_budgetPairs_C11Q7 {n : ℕ} {p : ℕ × ℕ} :
    p ∈ budgetPairs_C11Q7 n ↔ p.1 ≤ p.2 ∧ p.2 ≤ n := by
  unfold budgetPairs_C11Q7
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  omega

theorem budgetPairs_nonempty_C11Q7 (n : ℕ) : (budgetPairs_C11Q7 n).Nonempty :=
  ⟨(0, 0), mem_budgetPairs_C11Q7.mpr ⟨le_rfl, Nat.zero_le n⟩⟩

theorem budgetPairs_mono_C11Q7 {n n' : ℕ} (h : n ≤ n') :
    budgetPairs_C11Q7 n ⊆ budgetPairs_C11Q7 n' := fun p hp => by
  rw [mem_budgetPairs_C11Q7] at hp ⊢
  exact ⟨hp.1, hp.2.trans h⟩

/-- **构造预算**（审稿 Q1(b)）`d_n = ¼·min(2^{−n}, {β_{j,ℓ} : 0 ≤ j ≤ ℓ ≤ n})`。 -/
def budgetSeq_C11Q7 (β : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  1 / 4 * min ((1 / 2 : ℝ) ^ n)
    ((budgetPairs_C11Q7 n).inf' (budgetPairs_nonempty_C11Q7 n) (fun p => β p.1 p.2))

theorem budgetSeq_pos_C11Q7 {β : ℕ → ℕ → ℝ} (hβ : ∀ j ℓ, 0 < β j ℓ) (n : ℕ) :
    0 < budgetSeq_C11Q7 β n := by
  have h1 : (0 : ℝ) < (1 / 2) ^ n := by positivity
  have h2 : 0 < (budgetPairs_C11Q7 n).inf' (budgetPairs_nonempty_C11Q7 n) (fun p => β p.1 p.2) :=
    (Finset.lt_inf'_iff _).mpr fun p _ => hβ p.1 p.2
  exact mul_pos (by norm_num) (lt_min h1 h2)

theorem budgetSeq_antitone_C11Q7 (β : ℕ → ℕ → ℝ) : Antitone (budgetSeq_C11Q7 β) := by
  intro n n' h
  unfold budgetSeq_C11Q7
  refine mul_le_mul_of_nonneg_left (min_le_min ?_ ?_) (by norm_num)
  · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  · exact Finset.inf'_mono _ (budgetPairs_mono_C11Q7 h) _

theorem budgetSeq_le_pow_C11Q7 (β : ℕ → ℕ → ℝ) (n : ℕ) :
    budgetSeq_C11Q7 β n ≤ (1 / 2 : ℝ) ^ n / 4 := by
  unfold budgetSeq_C11Q7
  have := min_le_left ((1 / 2 : ℝ) ^ n)
    ((budgetPairs_C11Q7 n).inf' (budgetPairs_nonempty_C11Q7 n) (fun p => β p.1 p.2))
  linarith

/-- 每个请求 `(j, ℓ)`（`j ≤ ℓ ≤ n`）在第 `n` 块被支付：`d_n ≤ β_{j,ℓ}/4`。 -/
theorem budgetSeq_le_C11Q7 (β : ℕ → ℕ → ℝ) {j ℓ n : ℕ} (hjℓ : j ≤ ℓ) (hℓn : ℓ ≤ n) :
    budgetSeq_C11Q7 β n ≤ β j ℓ / 4 := by
  unfold budgetSeq_C11Q7
  have hmem : (j, ℓ) ∈ budgetPairs_C11Q7 n := mem_budgetPairs_C11Q7.mpr ⟨hjℓ, hℓn⟩
  have h : (budgetPairs_C11Q7 n).inf' (budgetPairs_nonempty_C11Q7 n) (fun p => β p.1 p.2) ≤
      β j ℓ := Finset.inf'_le (fun p : ℕ × ℕ => β p.1 p.2) hmem
  have h2 := min_le_right ((1 / 2 : ℝ) ^ n)
    ((budgetPairs_C11Q7 n).inf' (budgetPairs_nonempty_C11Q7 n) (fun p => β p.1 p.2))
  linarith

theorem budgetSeq_tendsto_C11Q7 {β : ℕ → ℕ → ℝ} (hβ : ∀ j ℓ, 0 < β j ℓ) :
    Tendsto (budgetSeq_C11Q7 β) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).div_const 4
  rw [zero_div] at h
  exact squeeze_zero (fun n => (budgetSeq_pos_C11Q7 hβ n).le) (budgetSeq_le_pow_C11Q7 β) h

/-- **预算构造**（D-2 (i)）：有限最小值 ⇒ `d_n > 0`、单调不增、趋零，且每个固定 `j` 从第 `j` 块起被支付
（`j ≤ ℓ ≤ n ⇒ d_n ≤ β_{j,ℓ}/4`，特别 `d_n < β_{j,n}`）。 -/
theorem budget_construction_C11Q7 (β : ℕ → ℕ → ℝ) (hβ : ∀ j ℓ, 0 < β j ℓ) :
    (∀ n, 0 < budgetSeq_C11Q7 β n) ∧ Antitone (budgetSeq_C11Q7 β) ∧
      Tendsto (budgetSeq_C11Q7 β) atTop (𝓝 0) ∧
      (∀ j ℓ n, j ≤ ℓ → ℓ ≤ n → budgetSeq_C11Q7 β n ≤ β j ℓ / 4) ∧
      ∀ j n, j ≤ n → budgetSeq_C11Q7 β n < β j n := by
  refine ⟨budgetSeq_pos_C11Q7 hβ, budgetSeq_antitone_C11Q7 β, budgetSeq_tendsto_C11Q7 hβ,
    fun j ℓ n h1 h2 => budgetSeq_le_C11Q7 β h1 h2, fun j n h => ?_⟩
  have h1 := budgetSeq_le_C11Q7 β h le_rfl
  have h2 := hβ j n
  linarith

/-- **D-2 (i) 的反例**：`Tendsto δ 0` 不蕴含落在更快趋零的正请求之下（`δ_n = 2^{−n}`、`β_n = 4^{−n}`）。 -/
theorem tendsto_not_budget_C11Q7 :
    ∃ δ β : ℕ → ℝ, (∀ n, 0 < δ n) ∧ (∀ n, 0 < β n) ∧ Tendsto δ atTop (𝓝 0) ∧
      Tendsto β atTop (𝓝 0) ∧ ∀ n, 1 ≤ n → β n < δ n := by
  refine ⟨fun n => (1 / 2 : ℝ) ^ n, fun n => (1 / 4 : ℝ) ^ n, fun n => by positivity,
    fun n => by positivity, tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num),
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num), fun n hn => ?_⟩
  exact pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)

/-- **半时间窗支付**：块指标 `k` 满足 `s ∈ [t/2, t] ⇒ k(t) ≤ k(s)+1`，`δ(s) ≤ d_{k(s)+1}`（= 审稿包络
`min(d_{k(s)}, d_{k(s)+1})`）⇒ `j ≤ k(t)` 时 `δ(s) ≤ β_{j,k(t)}/4`。 -/
theorem budget_window_C11Q7 (β : ℕ → ℕ → ℝ) (k : ℝ → ℕ)
    (hk : ∀ t, 0 < t → ∀ s ∈ Icc (t / 2) t, k t ≤ k s + 1) {δ : ℝ → ℝ}
    (hδ : ∀ s, 0 < s → δ s ≤ budgetSeq_C11Q7 β (k s + 1)) {j : ℕ} {t : ℝ} (ht : 0 < t)
    (hj : j ≤ k t) : ∀ s ∈ Icc (t / 2) t, δ s ≤ β j (k t) / 4 := by
  intro s hs
  have hs0 : 0 < s := lt_of_lt_of_le (half_pos ht) hs.1
  exact (hδ s hs0).trans ((budgetSeq_antitone_C11Q7 β (hk t ht s hs)).trans
    (budgetSeq_le_C11Q7 β hj le_rfl))

/-- 二进块号（`ℕ` 值）：`(Int.clog 2 t).toNat`。 -/
def dyadicBlock_C11Q7 (t : ℝ) : ℕ := (blockIndex_C11Q5 t).toNat

theorem dyadicBlock_window_C11Q7 {t : ℝ} (ht : 0 < t) {s : ℝ} (hs : s ∈ Icc (t / 2) t) :
    dyadicBlock_C11Q7 s ≤ dyadicBlock_C11Q7 t ∧ dyadicBlock_C11Q7 t ≤ dyadicBlock_C11Q7 s + 1 := by
  have hs0 : 0 < s := lt_of_lt_of_le (half_pos ht) hs.1
  have h1 := blockIndex_le_C11Q5 hs0 hs.2
  have h2 := blockIndex_le_succ_C11Q5 ht (by linarith [hs.1] : t ≤ 2 * s)
  unfold dyadicBlock_C11Q7
  omega

/-! ## 2. 离散 level -/

theorem exists_lt_levelRep_C11Q7 (A : ℝ) : ∃ m : ℕ, A < 12 * 3 ^ m := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (A / 12) (by norm_num : (1 : ℝ) < 3)
  exact ⟨m, by linarith⟩

/-- **离散 level** `level(A) = min{m ∈ ℕ : A < 12·3^m}`。 -/
def kappaLevel_C11Q7 (A : ℝ) : ℕ := Nat.find (exists_lt_levelRep_C11Q7 A)

/-- 离散代表 `12·3^{level A}`。 -/
def levelRep_C11Q7 (A : ℝ) : ℝ := 12 * 3 ^ kappaLevel_C11Q7 A

/-- 严格保留：`A < 12·3^{level A}`。 -/
theorem lt_levelRep_C11Q7 (A : ℝ) : A < levelRep_C11Q7 A :=
  Nat.find_spec (exists_lt_levelRep_C11Q7 A)

theorem kappaLevel_le_iff_C11Q7 {A : ℝ} {m : ℕ} : kappaLevel_C11Q7 A ≤ m ↔ A < 12 * 3 ^ m := by
  constructor
  · intro h
    have h3 : (3 : ℝ) ^ kappaLevel_C11Q7 A ≤ 3 ^ m := pow_le_pow_right₀ (by norm_num) h
    have h4 := lt_levelRep_C11Q7 A
    unfold levelRep_C11Q7 at h4
    linarith
  · intro h
    exact Nat.find_min' (exists_lt_levelRep_C11Q7 A) h

/-- 最小性：`m < level A ⇒ 12·3^m ≤ A`。 -/
theorem le_of_lt_kappaLevel_C11Q7 {A : ℝ} {m : ℕ} (h : m < kappaLevel_C11Q7 A) :
    12 * 3 ^ m ≤ A := by
  by_contra hc
  exact absurd (kappaLevel_le_iff_C11Q7.mpr (not_le.mp hc)) (not_le.mpr h)

theorem kappaLevel_mono_C11Q7 : Monotone kappaLevel_C11Q7 := fun _ A' h =>
  kappaLevel_le_iff_C11Q7.mpr (lt_of_le_of_lt h (lt_levelRep_C11Q7 A'))

theorem levelRep_mono_C11Q7 : Monotone levelRep_C11Q7 := fun A A' h => by
  unfold levelRep_C11Q7
  have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (kappaLevel_mono_C11Q7 h)
  linarith

/-- **边界** `A = 12·3^m`：`level = m + 1`（严格 guard，不是 `m`）。 -/
theorem kappaLevel_boundary_C11Q7 (m : ℕ) : kappaLevel_C11Q7 (12 * 3 ^ m) = m + 1 := by
  apply le_antisymm
  · refine kappaLevel_le_iff_C11Q7.mpr ?_
    have := pow_pos (by norm_num : (0 : ℝ) < 3) m
    rw [pow_succ]
    linarith
  · by_contra h
    exact lt_irrefl _ (kappaLevel_le_iff_C11Q7.mp (Nat.lt_succ_iff.mp (not_le.mp h)))

/-- **log 实现核**：`A > 0` 时 `level A = max 0 (⌊log₃(A/12)⌋ + 1)`（`Int.log` = floor；是 floor + 1）。 -/
theorem kappaLevel_eq_log_C11Q7 {A : ℝ} (hA : 0 < A) :
    (kappaLevel_C11Q7 A : ℤ) = max 0 (Int.log 3 (A / 12) + 1) := by
  have hA12 : 0 < A / 12 := by positivity
  have h1 := Int.zpow_log_le_self (R := ℝ) (b := 3) (by norm_num) hA12
  have h2 := Int.lt_zpow_succ_log_self (R := ℝ) (b := 3) (by norm_num) (A / 12)
  simp only [Nat.cast_ofNat] at h1 h2
  rcases le_or_gt (Int.log 3 (A / 12) + 1) 0 with hneg | hpos
  · have h3 : (3 : ℝ) ^ (Int.log 3 (A / 12) + 1) ≤ 1 := by
      have := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hneg
      rwa [zpow_zero] at this
    have hlev : kappaLevel_C11Q7 A ≤ 0 := kappaLevel_le_iff_C11Q7.mpr (by norm_num; linarith)
    rw [Nat.le_zero.mp hlev, max_eq_left hneg]
    rfl
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, Int.log 3 (A / 12) = n :=
      ⟨(Int.log 3 (A / 12)).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [hn] at h1 h2
    have e2 : (3 : ℝ) ^ ((n : ℤ) + 1) = 3 ^ (n + 1) := by
      rw [← zpow_natCast]
      push_cast
      rfl
    rw [e2] at h2
    rw [zpow_natCast] at h1
    have hup : kappaLevel_C11Q7 A ≤ n + 1 := kappaLevel_le_iff_C11Q7.mpr (by linarith)
    have hlow : ¬ kappaLevel_C11Q7 A ≤ n := fun h => by
      have := kappaLevel_le_iff_C11Q7.mp h
      linarith
    have hlev : kappaLevel_C11Q7 A = n + 1 := by omega
    rw [hlev, hn, max_eq_right (by omega)]
    push_cast
    rfl

/-- **ceiling 实现的陷阱**：`A = 12·3^m` 处 `⌈log₃(A/12)⌉ = m`（只给 `A ≤ 12·3^m`），而 `level = m + 1`。 -/
theorem clog_boundary_C11Q7 (m : ℕ) :
    Int.clog 3 (12 * (3 : ℝ) ^ m / 12) = m ∧ kappaLevel_C11Q7 (12 * 3 ^ m) = m + 1 := by
  refine ⟨?_, kappaLevel_boundary_C11Q7 m⟩
  have h := Int.clog_zpow (R := ℝ) (b := 3) (by norm_num) (m : ℤ)
  simp only [Nat.cast_ofNat, zpow_natCast] at h
  rw [mul_div_cancel_left₀ _ (by norm_num : (12 : ℝ) ≠ 0)]
  exact h

/-! ## 3. reduction lemma：代表请求支配原请求 -/

/-- **离散代表 level 请求支配原请求**（D-2 (ii) / D-7）：chooser `req` 只在代表点 `12·3^m` 处有效
（`hreq`），**不假设 `req` 单调**；只用请求有效性对参数向下封闭（`hvalid`）⇒ `req(level A)` 对 `A` 有效。 -/
theorem level_request_dominates_C11Q7 {ι : Type*} (Good : ℝ → ι → Prop) (req : ℕ → ι)
    (hreq : ∀ m : ℕ, Good (12 * 3 ^ m) (req m))
    (hvalid : ∀ A A' x, A ≤ A' → Good A' x → Good A x) (A : ℝ) :
    Good A (req (kappaLevel_C11Q7 A)) :=
  hvalid A _ _ (lt_levelRep_C11Q7 A).le (hreq _)

/-- **块版（移动请求）**：块 `n` 的供给支配有限个代表请求 `{req m n : m ≤ n}`（`Dom` 对有效性向上传递）⇒
任何 `A` 的移动请求 `Req(A, n)` 从块 `level A` 起都被支付（固定请求的 cofinal 性不够，这里每块支配有限族）。 -/
theorem level_block_supply_C11Q7 {ι : Type*} (Good : ℕ → ℝ → ι → Prop) (Dom : ι → ι → Prop)
    (req : ℕ → ℕ → ι) (supply : ℕ → ι)
    (hreq : ∀ m n : ℕ, Good n (12 * 3 ^ m) (req m n))
    (hvalid : ∀ n A A' x, A ≤ A' → Good n A' x → Good n A x)
    (hDom : ∀ n A x y, Dom x y → Good n A y → Good n A x)
    (hsupply : ∀ n m, m ≤ n → Dom (supply n) (req m n)) :
    ∀ A n, kappaLevel_C11Q7 A ≤ n → Good n A (supply n) := fun A n hn =>
  hDom n A _ _ (hsupply n _ hn)
    (level_request_dominates_C11Q7 (Good n) (fun m => req m n) (fun m => hreq m n) (hvalid n) A)

/-! ## 4. κ 实例 -/

/-- 代表 level 的 K3 屏障高度 `Λ'(A) = Λ_W(12·3^{level A})`。 -/
def levelBarrier_C11Q7 (A : ℝ) : ℝ :=
  weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1)) (levelRep_C11Q7 A)

/-- `Λ'` 只依赖离散 level。 -/
theorem levelBarrier_eq_of_level_eq_C11Q7 {A A' : ℝ} (h : kappaLevel_C11Q7 A = kappaLevel_C11Q7 A')
    :
    levelBarrier_C11Q7 A = levelBarrier_C11Q7 A' := by
  unfold levelBarrier_C11Q7 levelRep_C11Q7
  rw [h]

/-- **代表请求支配原请求（κ 实例）**：`Λ_W(A) ≤ Λ'(A)`——`level_request_dominates_C11Q7` 取
`Good A x := Λ_W(A) ≤ x`、`req m := Λ_W(12·3^m)`，有效性向下封闭 = `kappaLevel_mono_C11Q6`。 -/
theorem weightedMinLevel_le_levelBarrier_C11Q7 (A : ℝ) :
    weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1)) A ≤
      levelBarrier_C11Q7 A :=
  level_request_dominates_C11Q7
    (fun A x => weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1)) A ≤ x)
    (fun m => weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1)) (12 * 3 ^ m))
    (fun _ => le_rfl) (fun _ _ _ h hx => (kappaLevel_mono_C11Q6 h).trans hx) A

/-- **K3（代表 level）**：`hfine` 只在代表屏障 `Λ'` 上要求（δ 请求只依赖 `(level A, k(t))`）⇒ 屏障 `Λ'`；
经 G1 wrapper 的 `hΛ := weightedMinLevel_le_levelBarrier_C11Q7` 进 κ 链。 -/
theorem surgeryActionBarrier_of_native_fineCap_level_C11Q7 {P : OrientedThreeStage.{u}}
    {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (hact : ∀ n i b, ActualCanonicalInsertion_C11Q5 ((N.records n i).static b))
    (hδ : ∀ s, 0 ≤ s → N.params.delta s ≤ δ s)
    (hfine : KappaFineScale_C11Q5 P g N.params α levelBarrier_C11Q7 N.Ctime) :
    SurgeryActionBarrier_C11Q F δ α N.params.neckRadius levelBarrier_C11Q7 :=
  surgeryActionBarrier_of_native_fineCap_C11Q5 N hact hδ
    (fun A _ => weightedMinLevel_pos_C11Q2 _ (levelRep_C11Q7 A)) hfine

/-- 代表 level 的块 δ 请求 `β_{m,ℓ} = δ_blk(Λ_W(12·3^m), ℓ)`（二进块 `ℓ ≥ 0`）。 -/
def levelBlockDelta_C11Q7 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (params : CutoffParameters) (Ctime : ℝ≥0) (m ℓ : ℕ) : ℝ :=
  fineCapDeltaBlock_C11Q5 P₀ g₀ params
    (weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1)) (12 * 3 ^ m)) Ctime ℓ

theorem levelBlockDelta_pos_C11Q7 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (params : CutoffParameters) (Ctime : ℝ≥0) (m ℓ : ℕ) :
    0 < levelBlockDelta_C11Q7 P₀ g₀ params Ctime m ℓ :=
  fineCapDeltaBlock_pos_C11Q5 _ _ _ _ _ _

theorem blockIndex_nonneg_C11Q7 {s : ℝ} (hs : 1 ≤ s) : 0 ≤ blockIndex_C11Q5 s := by
  by_contra h
  have hk : blockIndex_C11Q5 s ≤ -1 := by omega
  have h1 := le_blockTime_C11Q5 s
  have h2 : blockTime_C11Q5 (blockIndex_C11Q5 s) ≤ (2 : ℝ) ^ (-1 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) hk
  have h3 : (2 : ℝ) ^ (-1 : ℤ) = 1 / 2 := by norm_num
  rw [h3] at h2
  linarith

/-- 晚期：`s ≥ max(1, 2^{level A}) ⇒ level A ≤ k(s)`。 -/
theorem kappaLevel_le_dyadicBlock_C11Q7 {A s : ℝ} (hs : max 1 (2 ^ kappaLevel_C11Q7 A) ≤ s) :
    kappaLevel_C11Q7 A ≤ dyadicBlock_C11Q7 s := by
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hs
  have hs2 : (2 : ℝ) ^ kappaLevel_C11Q7 A ≤ s := (le_max_right _ _).trans hs
  have h0 := blockIndex_nonneg_C11Q7 hs1
  by_contra hc
  have hlt : blockIndex_C11Q5 s ≤ (kappaLevel_C11Q7 A : ℤ) - 1 := by
    unfold dyadicBlock_C11Q7 at hc
    omega
  have h1 := le_blockTime_C11Q5 s
  have h2 : blockTime_C11Q5 (blockIndex_C11Q5 s) ≤ (2 : ℝ) ^ ((kappaLevel_C11Q7 A : ℤ) - 1) :=
    zpow_le_zpow_right₀ (by norm_num) hlt
  have h3 : (2 : ℝ) ^ ((kappaLevel_C11Q7 A : ℤ) - 1) < 2 ^ kappaLevel_C11Q7 A := by
    rw [zpow_sub_one₀ (by norm_num), zpow_natCast]
    have := pow_pos (by norm_num : (0 : ℝ) < 2) (kappaLevel_C11Q7 A)
    linarith
  linarith

/-- **预算进 construction（κ 实例）**：`β = levelBlockDelta`（代表 level × 二进块），`δ(s) ≤ d_{k(s)+1}`。
(1) `α := 代表点包络 fineCapEnvelope(Λ')` 满足 `KappaFineScale`（`Λ = Λ'`）；(2) 晚期比较：
`s ≥ max(1, 2^{level A}) ⇒ δ(s) < α(A, s)`（每个固定 `A` 从块 `level A` 起被支付）。 -/
theorem budget_schedule_C11Q7 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (params : CutoffParameters) (Ctime : ℝ≥0) {δ : ℝ → ℝ}
    (hδ : ∀ s, 0 < s → δ s ≤
      budgetSeq_C11Q7 (levelBlockDelta_C11Q7 P₀ g₀ params Ctime) (dyadicBlock_C11Q7 s + 1)) :
    KappaFineScale_C11Q5 P₀ g₀ params
        (fun A s => fineCapEnvelope_C11Q5 P₀ g₀ params levelBarrier_C11Q7 Ctime A s)
        levelBarrier_C11Q7 Ctime ∧
      ∀ A s, max 1 (2 ^ kappaLevel_C11Q7 A) ≤ s →
        δ s < fineCapEnvelope_C11Q5 P₀ g₀ params levelBarrier_C11Q7 Ctime A s := by
  refine ⟨kappaFineScale_of_envelope_C11Q5 P₀ g₀ params levelBarrier_C11Q7 Ctime
    (fun _ _ _ _ => le_rfl), fun A s hs => ?_⟩
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hs
  have hs0 : 0 < s := by linarith
  have hlev := kappaLevel_le_dyadicBlock_C11Q7 hs
  have hk : ((dyadicBlock_C11Q7 s : ℕ) : ℤ) = blockIndex_C11Q5 s :=
    Int.toNat_of_nonneg (blockIndex_nonneg_C11Q7 hs1)
  have hd := hδ s hs0
  have e1 := budgetSeq_le_C11Q7 (levelBlockDelta_C11Q7 P₀ g₀ params Ctime) hlev
    (Nat.le_add_right (dyadicBlock_C11Q7 s) 1)
  have e2 := budgetSeq_le_C11Q7 (levelBlockDelta_C11Q7 P₀ g₀ params Ctime)
    (hlev.trans (Nat.le_add_right (dyadicBlock_C11Q7 s) 1)) le_rfl
  have p1 := levelBlockDelta_pos_C11Q7 P₀ g₀ params Ctime (kappaLevel_C11Q7 A) (dyadicBlock_C11Q7 s)
  have p2 := levelBlockDelta_pos_C11Q7 P₀ g₀ params Ctime (kappaLevel_C11Q7 A)
    (dyadicBlock_C11Q7 s + 1)
  have q1 : levelBlockDelta_C11Q7 P₀ g₀ params Ctime (kappaLevel_C11Q7 A) (dyadicBlock_C11Q7 s) =
      fineCapDeltaBlock_C11Q5 P₀ g₀ params (levelBarrier_C11Q7 A) Ctime (blockIndex_C11Q5 s) := by
    unfold levelBlockDelta_C11Q7 levelBarrier_C11Q7 levelRep_C11Q7
    rw [hk]
  have q2 : levelBlockDelta_C11Q7 P₀ g₀ params Ctime (kappaLevel_C11Q7 A)
      (dyadicBlock_C11Q7 s + 1) = fineCapDeltaBlock_C11Q5 P₀ g₀ params (levelBarrier_C11Q7 A)
        Ctime (blockIndex_C11Q5 s + 1) := by
    unfold levelBlockDelta_C11Q7 levelBarrier_C11Q7 levelRep_C11Q7
    push_cast
    rw [hk]
  have r1 : δ s < fineCapDeltaBlock_C11Q5 P₀ g₀ params (levelBarrier_C11Q7 A) Ctime
      (blockIndex_C11Q5 s) := by
    rw [← q1]
    linarith
  have r2 : δ s < fineCapDeltaBlock_C11Q5 P₀ g₀ params (levelBarrier_C11Q7 A) Ctime
      (blockIndex_C11Q5 s + 1) := by
    rw [← q2]
    linarith
  exact lt_min r1 r2

/-- 晚期比较的 `∀ᶠ` 形。 -/
theorem budget_schedule_eventually_C11Q7 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (params : CutoffParameters) (Ctime : ℝ≥0) {δ : ℝ → ℝ}
    (hδ : ∀ s, 0 < s → δ s ≤
      budgetSeq_C11Q7 (levelBlockDelta_C11Q7 P₀ g₀ params Ctime) (dyadicBlock_C11Q7 s + 1))
    (A : ℝ) : ∀ᶠ s in atTop,
      δ s < fineCapEnvelope_C11Q5 P₀ g₀ params levelBarrier_C11Q7 Ctime A s :=
  eventually_atTop.mpr ⟨max 1 (2 ^ kappaLevel_C11Q7 A),
    fun s hs => (budget_schedule_C11Q7 P₀ g₀ params Ctime hδ).2 A s hs⟩

/-! ## 5. 与 FINEPACK 的对齐与 consumer -/

/-- **对齐（FINEPACK A-guard）**：astra m-i 子句的严格 guard `A < 12·3^m`（`hev`）⟺ `level A ≤ m`——FINEPACK 的
块号就是 level 的上界，边界 `A = 12·3^m` 落入块 `m+1`。 -/
example {A : ℝ} {m : ℕ} : A < 12 * 3 ^ m ↔ kappaLevel_C11Q7 A ≤ m :=
  kappaLevel_le_iff_C11Q7.symm

/-- **对齐（FINEPACK 代表点请求）**：`k3BlockConsts_C11Q6 m` 的作用量 `Λ_W(12·3^m)·E` 支配 `Λ_W(A)·E`
（guard `A < 12·3^m`）——经 `level_request_dominates_C11Q7` 的 κ 实例 + level 单调，不用 chooser 单调。 -/
example {A E : ℝ} {m : ℕ} (h : A < 12 * 3 ^ m) (hE : 0 ≤ E) :
    weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1)) A * E ≤
      weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1)) (12 * 3 ^ m) * E := by
  have h1 := weightedMinLevel_le_levelBarrier_C11Q7 A
  have h3 : (3 : ℝ) ^ kappaLevel_C11Q7 A ≤ 3 ^ m :=
    pow_le_pow_right₀ (by norm_num) (kappaLevel_le_iff_C11Q7.mpr h)
  have h2 := kappaLevel_mono_C11Q6
    (show levelRep_C11Q7 A ≤ 12 * 3 ^ m by unfold levelRep_C11Q7; linarith)
  exact mul_le_mul_of_nonneg_right (h1.trans h2) hE

/-- **consumer（预算 ⇒ 包络 ⇒ hfine ⇒ K3，且晚期 δ < α）**：`budget_schedule_C11Q7` 的第一分量喂
`surgeryActionBarrier_of_native_fineCap_level_C11Q7`（`α` = 代表点包络），第二分量给晚期比较。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (hact : ∀ n i b, ActualCanonicalInsertion_C11Q5 ((N.records n i).static b))
    (hδN : ∀ s, 0 ≤ s → N.params.delta s ≤ δ s) {δc : ℝ → ℝ}
    (hδc : ∀ s, 0 < s → δc s ≤ budgetSeq_C11Q7
      (levelBlockDelta_C11Q7 P g N.params N.Ctime) (dyadicBlock_C11Q7 s + 1)) :
    SurgeryActionBarrier_C11Q F δ
      (fun A s => fineCapEnvelope_C11Q5 P g N.params levelBarrier_C11Q7 N.Ctime A s)
      N.params.neckRadius levelBarrier_C11Q7 ∧
    ∀ A, ∀ᶠ s in atTop,
      δc s < fineCapEnvelope_C11Q5 P g N.params levelBarrier_C11Q7 N.Ctime A s :=
  ⟨surgeryActionBarrier_of_native_fineCap_level_C11Q7 N hact hδN
    (budget_schedule_C11Q7 P g N.params N.Ctime hδc).1,
    budget_schedule_eventually_C11Q7 P g N.params N.Ctime hδc⟩

/-- **consumer（端到端，代表 level）**：KAPPA3 `nonempty_pre841Data_of_native_nodes_C11Q4` 的 binder 逐字，只把
`hfine` 的屏障换成代表屏障 `Λ' = levelBarrier_C11Q7`（δ 请求只在离散 level × 块上）⇒ 经 G1 hK3 wrapper
（`hΛ := weightedMinLevel_le_levelBarrier_C11Q7`，即代表请求支配原请求）得 `Pre841Data_C11K`。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (Cderiv : ℝ≥0)
    (hnode : ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, N.params.neckRadius t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          EventNodeData_C11Q4 P g Cderiv H N.params (N.records n) t x r (max A 1)
            nodeA nodeE nodeR nodeQ nodeRho)
    (hure : ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, N.params.neckRadius t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        ∀ a : Icc (0 : ℝ) H.horizon, (a : ℝ) = (t : ℝ) - (Real.sqrt 3 * r / 2) ^ 2 →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          UREBlockNodeData_C11Q4 P g Cderiv H N.params (N.records n) t x r A a
            nodeA nodeE nodeR nodeQ nodeRho)
    (hδ : ∀ s, 0 ≤ s → N.params.delta s ≤ δ s)
    (hact : ∀ n i b, ActualCanonicalInsertion_C11Q5 ((N.records n i).static b))
    (hfine : KappaFineScale_C11Q5 P g N.params α levelBarrier_C11Q7 N.Ctime)
    (hacc : LargerBallAccuracySupply_C11S δ α) {A κ' : ℝ} (hA : 0 < A) (hκ' : 0 < κ')
    (hsmallScale : ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) →
        2 * r ^ 2 < (t : ℝ) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < N.params.neckRadius v / 100 → ρ' < r / 100 →
          H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ' * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ')
    (ind : ℕ → ℕ)
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ)
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
      (r n))
    (hvol : ∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
      ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
        ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n))
    (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ t n) (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
      ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (ind n)).toHistory.activeStage (t n))
      ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (hst : ∀ n, s n ≤ t n)
    (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
    (hR : ∀ n, 0 < R n)
    (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (w : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hws : w ≤ s n),
        (s n : ℝ) - T / R n ≤ w →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage w)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hws) x,
      ∀ haw : aSeed n ≤ w,
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage w) w)
          ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage w)
            ((F.tower.history (ind n)).toHistory.activeStage_mono haw)
            ((F.tower.history (ind n)).toHistory.activeStage_mono (hws.trans (hst n))))
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage w) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hws)) <
          ENNReal.ofReal (A * r n)) :
    Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR) :=
  nonempty_pre841Data_of_native_nodes_K3_C11Q7 N Cderiv hnode hure
    (surgeryActionBarrier_of_native_fineCap_level_C11Q7 N hact hδ hfine)
    (fun A _ => weightedMinLevel_le_levelBarrier_C11Q7 A) hacc hA hκ' hsmallScale ind t p r hlate
      htime hsmall hvol aSeed haT hclock seedTrace s hst y R hR hradii hwin hdist

end GC.LongTime.Ch11
