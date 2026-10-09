import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StagePostCoverP6S2

/-!
# 左侧 bad points 与 localized rerun bad points（CX-STAGE）

R-C11-7 Q3(c), dispositions D-11：`left_bad_sequence_of_stage_class_P6S2` 的左坏点
没有 curvature ratio 或 seed-distance control。本文件把这两个层次分别命名，并证明
localized ⇒ arbitrary、逆向在抽象 scalar/distance 数据上不成立，以及两个层次各自可支付的
diagonal selection。抽象反例不声称来自 Ricci flow；它只排除纯量词逻辑的逆向。

`LeftLocalizedBadAt_CXST` 是尚待几何 producer 支付的目标规格，不是新 admission，
也不是 buffered witness transfer 的替代。它不包含 seed / κ / pinching / records。
时间与 point type 可依赖 history，故可直接取 `T = Icc 0 H.horizon`、
`X v = (H.stageAt v).Carrier`，并把 `Bad` 取为指定精度的 `¬ Good`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

/-- Arbitrary left bad point：只控制 time，`z` 没有空间或 scalar 限制。 -/
def LeftBadAt_CXST {T : Type u} {X : T → Type v} (time : T → ℝ)
    (Bad : ∀ t, X t → Prop) (σ : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ (t : T) (z : X t),
    σ - δ < time t ∧ time t < σ ∧ Bad t z

/-- Localized left bad point：time 与 curvature 精度可同时任意细化，且 seed-distance
满足 `leftShift_rerun_P6S2` 所需的固定 buffer；目标常数先于 δ、ε 固定。 -/
def LeftLocalizedBadAt_CXST {T : Type u} {X : T → Type v} (time : T → ℝ)
    (Bad : ∀ t, X t → Prop) (scalar : ∀ t, X t → ℝ)
    (seedDistance : ∀ t, X t → ℝ≥0∞) (σ R L : ℝ) (D0 : ℝ≥0∞) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε → ∃ (t : T) (z : X t),
    σ - δ < time t ∧ time t < σ ∧ Bad t z ∧
      |scalar t z / R - 1| < ε ∧
      seedDistance t z ≤ D0 + ENNReal.ofReal (L / (4 * Real.sqrt R))

/-- 遗忘 curvature / distance 得到弱层，不能反向补齐这两项。 -/
theorem LeftLocalizedBadAt_CXST.leftBadAt {T : Type u} {X : T → Type v}
    {time : T → ℝ} {Bad : ∀ t, X t → Prop} {scalar : ∀ t, X t → ℝ}
    {seedDistance : ∀ t, X t → ℝ≥0∞} {σ R L : ℝ} {D0 : ℝ≥0∞}
    (h : LeftLocalizedBadAt_CXST time Bad scalar seedDistance σ R L D0) :
    LeftBadAt_CXST time Bad σ := by
  intro δ hδ
  obtain ⟨t, z, ht, hs, hb, -, -⟩ := h δ hδ 1 one_pos
  exact ⟨t, z, ht, hs, hb⟩

/-- 两个 predicate 均有真实 inhabitant：常值 scalar 1 与零 seed-distance 的抽象模型。 -/
theorem localized_constant_model_CXST :
    LeftLocalizedBadAt_CXST (id : ℝ → ℝ) (fun _ (_ : Unit) => True)
      (fun _ _ => 1) (fun _ _ => 0) 0 1 1 0 := by
  intro δ hδ ε hε
  refine ⟨-δ / 2, (), ?_, ?_, trivial, ?_, ?_⟩
  · dsimp
    linarith
  · dsimp
    linarith
  · simpa using hε
  · exact zero_le

/-- 非逆向的 scalar obstruction：即使所有左点都 Bad，scalar 可始终为 0。 -/
theorem leftBadAt_not_localized_scalar_CXST :
    LeftBadAt_CXST (id : ℝ → ℝ) (fun _ (_ : Unit) => True) 0 ∧
      ¬ LeftLocalizedBadAt_CXST (id : ℝ → ℝ) (fun _ (_ : Unit) => True)
        (fun _ _ => 0) (fun _ _ => 0) 0 1 1 0 := by
  refine ⟨localized_constant_model_CXST.leftBadAt, ?_⟩
  intro h
  obtain ⟨t, z, -, -, -, hq, -⟩ := h 1 one_pos (1 / 2) (by norm_num)
  norm_num at hq

/-- 非逆向的 distance obstruction：ratio 恰为 1 仍不保证 seed-distance buffer。 -/
theorem leftBadAt_not_localized_distance_CXST :
    LeftBadAt_CXST (id : ℝ → ℝ) (fun _ (_ : Unit) => True) 0 ∧
      ¬ LeftLocalizedBadAt_CXST (id : ℝ → ℝ) (fun _ (_ : Unit) => True)
        (fun _ _ => 1) (fun _ _ => 1) 0 1 1 0 := by
  refine ⟨localized_constant_model_CXST.leftBadAt, ?_⟩
  intro h
  obtain ⟨t, z, -, -, -, -, hd⟩ := h 1 one_pos 1 one_pos
  norm_num at hd

/-- 弱层能支付任意正的 time budget，同时保留指定 open slab 下界。 -/
theorem LeftBadAt_CXST.exists_in_slab {T : Type u} {X : T → Type v}
    {time : T → ℝ} {Bad : ∀ t, X t → Prop} {a σ δ : ℝ}
    (h : LeftBadAt_CXST time Bad σ) (ha : a < σ) (hδ : 0 < δ) :
    ∃ (t : T) (z : X t), a < time t ∧ time t < σ ∧
      σ - time t < δ ∧ Bad t z := by
  obtain ⟨t, z, ht, hs, hb⟩ := h (min (σ - a) δ) (lt_min (sub_pos.mpr ha) hδ)
  have h1 := min_le_left (σ - a) δ
  have h2 := min_le_right (σ - a) δ
  exact ⟨t, z, by linarith, hs, by linarith, hb⟩

/-- D-11 的时间细化独立于 localization：弱层已能生产 `Rₙ (σₙ - vₙ) → 0`。
它没有生产 curvature ratio，也没有生产 seed-distance bound。 -/
theorem scaled_left_bad_sequence_CXST {T : ℕ → Type u} {X : ∀ n, T n → Type v}
    {time : ∀ n, T n → ℝ} {Bad : ∀ n t, X n t → Prop} {a σ R : ℕ → ℝ}
    (h : ∀ n, LeftBadAt_CXST (time n) (Bad n) (σ n))
    (ha : ∀ n, a n < σ n) (hR : ∀ n, 0 < R n) :
    ∃ (t : ∀ n, T n) (z : ∀ n, X n (t n)),
      (∀ n, a n < time n (t n) ∧ time n (t n) < σ n ∧ Bad n (t n) (z n)) ∧
      Tendsto (fun n => R n * (σ n - time n (t n))) atTop (𝓝 0) := by
  have key (n : ℕ) := (h n).exists_in_slab (ha n)
    (div_pos (by positivity : 0 < 1 / ((n : ℝ) + 1)) (hR n))
  choose t z ht hs hbudget hb using key
  refine ⟨t, z, fun n => ⟨ht n, hs n, hb n⟩, ?_⟩
  apply squeeze_zero (fun n => mul_nonneg (hR n).le (sub_nonneg.mpr (hs n).le))
    (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  have hh := (lt_div_iff₀ (hR n)).mp (hbudget n)
  nlinarith

/-- 固定 curvature 精度 `1/2` 已给重跑的 `R / 2 ≤ R'`；δ 还可同时支付 slab 与 window。
这是 localized 规格的实际算术消费，不声称该规格由 post-cover 生产。 -/
theorem LeftLocalizedBadAt_CXST.exists_rerun_parameters {T : Type u} {X : T → Type v}
    {time : T → ℝ} {Bad : ∀ t, X t → Prop} {scalar : ∀ t, X t → ℝ}
    {seedDistance : ∀ t, X t → ℝ≥0∞} {a σ R L : ℝ} {D0 : ℝ≥0∞}
    (h : LeftLocalizedBadAt_CXST time Bad scalar seedDistance σ R L D0)
    (ha : a < σ) (hR : 0 < R) (hL : 0 < L) :
    ∃ (t : T) (z : X t), a < time t ∧ time t < σ ∧ Bad t z ∧
      R / 2 ≤ scalar t z ∧ σ - time t ≤ L ^ 2 / (2 * R) ∧
      seedDistance t z ≤ D0 + ENNReal.ofReal (L / (4 * Real.sqrt R)) := by
  have hδ : 0 < min (σ - a) (L ^ 2 / (2 * R)) :=
    lt_min (sub_pos.mpr ha) (by positivity)
  obtain ⟨t, z, ht, hs, hb, hq, hd⟩ := h _ hδ (1 / 2) (by norm_num)
  have h1 := min_le_left (σ - a) (L ^ 2 / (2 * R))
  have h2 := min_le_right (σ - a) (L ^ 2 / (2 * R))
  have hlo := (abs_lt.mp hq).1
  have hhalf : (1 / 2 : ℝ) < scalar t z / R := by linarith
  have hh := (lt_div_iff₀ hR).mp hhalf
  exact ⟨t, z, by linarith, hs, hb, by linarith, by linarith, hd⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
