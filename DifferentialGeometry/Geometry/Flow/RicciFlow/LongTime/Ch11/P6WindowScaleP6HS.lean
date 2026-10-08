import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10CrossSlabProtCXJD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.EndpointAssemblyC11G
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterAgeObject_P6N

/-!
# CX-J10DIST `hscale` 的 producer 与窗口 neck 合同（O-CH11-HSCALE，后缀 `_P6HS`）

`exists_crossSlab_ceiling_CXJD` 的 PROVISIONAL binder `hscale`：窗口内（`a < time e⁺`）每个 event 的
`2·max{3/r², 2·Q_b·R} < static neck.scale`。两项分别来自：

* **3/r² 项（免费）**：K 单位（`c = r²` 重标度）下种子半径 `r = 1`，`R_k ≥ k+1 → ∞`、`Q_b ≥ 1`
  ⇒ 最终 `3/1² ≤ 2·Q_b·R_k`（`three_div_le_of_tendsto_P6HS`），`max` 塌成 `2·Q_b·R` 项；
  Ho 单位即 `R·r² → ∞`。不需要 records。
* **2·Q_b·R 项**：records 的精细 scale 下界 `inv_two_mul_delta_sq_lt_static_scale_C11G`
  （`Λδ(τ) ≤ 1/2` ⇒ `(2δ(τ)⁴ρ(τ)²)⁻¹ < scale`，`τ = time e⁺`）把它归结为 P6GEO `hsep` 形
  `4·max{3/r², 2Q_bR}·δ(τ)⁴ρ(τ)² ≤ 1`（G1a `hscale_of_fineBudget_P6HS`，PROVED）。
  `δ(τ) → 0` 由 HRECDELTA（`Tendsto q.delta atTop (𝓝 0)`）+ 窗口事件时刻 → ∞ 付
  （`eventually_windowDelta_le_rescale_P6HS`：Ho 时刻 `c·τ ≥ c·a → ∞`）。
  **缺口** = `R·ρ(τ)²` 有界：hOpen8 只给 Tn 时刻 `R ≤ ρ_K(Tn)⁻²`，`CutoffParameters` 对 `neckRadius`
  无单调/窗口比较，J6 `(n+1)·max((n+1)/c, Qs) ≤ scale` 与 J10 `c·Qs < R` 方向相反。
  ⇒ 合同 **`WindowNeckScaleBudget_P6HS`**：窗口事件时刻版 `R ≤ ρ_H(time e⁺)⁻²`（hOpen8 Tn 行的逐事件
  加强；owner = selection / P6GEO records）。G1b/G1c 在合同 + δ 衰减下产出 `hscale`（PROVISIONAL[合同]）。
* 证书：`not_windowBudget_of_TnLine_P6HS`（ℝ 反例：antitone ρ 在窗口内跳变，Tn 行与任意小 δ 下
  hsep 形仍失败）；`not_hscale_of_J6_J10_P6HS`（J6 ∧ J10 推不出 K 单位 `hscale`）。
* G2 `exists_crossSlab_ceiling_windowNeck_P6HS`：`exists_crossSlab_ceiling_CXJD` 的 `hscale` 槽由 G1b 以
  **同一** `records` witness 填上（同一 `ε₀`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-! ## G1a：精细 scale 下界 ⇒ `M < scale`（PROVED） -/

/-- **G1a（`_P6HS`，PROVED）**：单 history `H`、records 族（参数 `p`）；窗口内（`a < time e⁺`）每个
event `Λ·δ(τ) ≤ 1/2` 且 hsep 形 `2·M·δ(τ)⁴ρ(τ)² ≤ 1` ⇒ `M < static neck.scale`
（`inv_two_mul_delta_sq_lt_static_scale_C11G` 的窗口版；`M := 2·max{3/r², 2Q_bR}` 即 CXJD `hscale`）。 -/
theorem hscale_of_fineBudget_P6HS {H : ObservedHistory.{u}} {p : CutoffParameters} {T₀ a M : ℝ}
    (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e p)
    (hbud : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → a < H.time e.succ →
      p.recenterConstant * p.delta (H.time e.succ) ≤ 1 / 2 ∧
        2 * M * (p.delta (H.time e.succ) ^ 4 * p.neckRadius (H.time e.succ) ^ 2) ≤ 1) :
    ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b, a < H.time e.succ →
      M < ((records e he).static b).neck.scale := by
  intro e he b hae
  obtain ⟨hΛδ, hM⟩ := hbud e he hae
  have hlow := (records e he).inv_two_mul_delta_sq_lt_static_scale_C11G hΛδ b
  have hτ := H.time_nonneg e.succ
  have hpos : 0 < p.delta (H.time e.succ) ^ 4 * p.neckRadius (H.time e.succ) ^ 2 := by
    have h1 := p.delta_pos _ hτ
    have h2 := p.neckRadius_pos _ hτ
    positivity
  have h2 : M ≤ (2 * (p.delta (H.time e.succ) ^ 4 * p.neckRadius (H.time e.succ) ^ 2))⁻¹ := by
    rw [← one_div, le_div_iff₀ (by linarith [hpos])]
    linarith
  exact h2.trans_lt hlow

/-! ## 合同：窗口事件时刻 neck 界 -/

/-- **合同 `WindowNeckScaleBudget_P6HS`（PROVISIONAL；owner = selection / P6GEO records）**：窗口内
（`T₀ ≤ time e⁺`、`a < time e⁺`）每个 event 的时刻 `τ = time e⁺` 上 `R ≤ ρ_H(τ)⁻²`。
这是 hOpen8 现有 Tn 行 `R ≤ ρ_K(Tn)⁻²` 的逐事件加强。已有行推不出它：`CutoffParameters` 对
`neckRadius` 没有单调性或窗口比较，`τ ≠ Tn`（ℝ 反例 `not_windowBudget_of_TnLine_P6HS`）；
J6 / J10 只给 `scale` 的阈值下界和 `R` 的阈值下界，方向相反（`not_hscale_of_J6_J10_P6HS`）。 -/
def WindowNeckScaleBudget_P6HS (H : ObservedHistory.{u}) (p : CutoffParameters)
    (T₀ a R : ℝ) : Prop :=
  ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → a < H.time e.succ →
    R ≤ (p.neckRadius (H.time e.succ) ^ 2)⁻¹

/-- 合同的 inhabitant（形状非空）：`R ≤ 0` 时平凡成立。 -/
theorem windowNeckScaleBudget_of_nonpos_P6HS (H : ObservedHistory.{u}) (p : CutoffParameters)
    (T₀ a : ℝ) {R : ℝ} (hR : R ≤ 0) : WindowNeckScaleBudget_P6HS H p T₀ a R :=
  fun _ _ _ => hR.trans (inv_nonneg.mpr (sq_nonneg _))

/-! ## G1b：合同 + 窗口 δ 小 + 3/r² 项 ⇒ CXJD `hscale` 逐字（PROVISIONAL[合同]） -/

/-- **G1b（`_P6HS`）**：records + 合同 `WindowNeckScaleBudget_P6HS` + 窗口 δ 小（`Λδ ≤ 1/2`、
`8·Q_b·δ⁴ ≤ 1`）+ 3/r² 项 `3/r² ≤ 2Q_bR`（K 单位 `r = 1` 时由 `R ≥ 3/2`、`Q_b ≥ 1` 免费）
⇒ `exists_crossSlab_ceiling_CXJD` 的 `hscale` 逐字。 -/
theorem hscale_of_windowNeck_P6HS {H : ObservedHistory.{u}} {p : CutoffParameters}
    {T₀ a R r Qb : ℝ}
    (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e p)
    (hW : WindowNeckScaleBudget_P6HS H p T₀ a R)
    (hδ : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → a < H.time e.succ →
      p.recenterConstant * p.delta (H.time e.succ) ≤ 1 / 2 ∧
        8 * Qb * p.delta (H.time e.succ) ^ 4 ≤ 1)
    (h3 : 3 / r ^ 2 ≤ 2 * (Qb * R)) (hQb : 0 ≤ Qb) :
    ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b, a < H.time e.succ →
      2 * max (3 / r ^ 2) (2 * (Qb * R)) < ((records e he).static b).neck.scale := by
  refine hscale_of_fineBudget_P6HS (M := 2 * max (3 / r ^ 2) (2 * (Qb * R))) records
    (fun e he hae => ⟨(hδ e he hae).1, ?_⟩)
  have hτ := H.time_nonneg e.succ
  have hρ2 : 0 < p.neckRadius (H.time e.succ) ^ 2 := pow_pos (p.neckRadius_pos _ hτ) 2
  have hRρ : R * p.neckRadius (H.time e.succ) ^ 2 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (hW e he hae) hρ2.le
    rwa [inv_mul_cancel₀ hρ2.ne'] at h
  have h8 : 0 ≤ 8 * Qb * p.delta (H.time e.succ) ^ 4 :=
    mul_nonneg (by linarith) (pow_nonneg (p.delta_pos _ hτ).le 4)
  have hk := mul_le_mul_of_nonneg_left hRρ h8
  have hd := (hδ e he hae).2
  rw [max_eq_right h3]
  linarith

/-! ## G1c：序列层（δ 衰减）⇒ ∀ᶠ k `hscale`（PROVISIONAL[合同]） -/

/-- 窗口 δ 小的 K 单位桥：`q.delta → 0`（HRECDELTA `hδlim`）且 Ho 窗口底 `c_k·a_k → ∞` ⇒ 对重标度参数
`q.rescale_P6N c_k`，最终窗口内每个事件 `δ_K(τ) = q.delta(c_k τ) ≤ ε`。 -/
theorem eventually_windowDelta_le_rescale_P6HS (H : ℕ → ObservedHistory.{u}) {q : CutoffParameters}
    {c : ℕ → ℝ} (hc : ∀ k, 0 < c k) {a : ℕ → ℝ} (hδlim : Tendsto q.delta atTop (𝓝 0))
    (hca : Tendsto (fun k => c k * a k) atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ e : Fin (H k).eventCount, a k < (H k).time e.succ →
      (q.rescale_P6N (c k) (hc k)).delta ((H k).time e.succ) ≤ ε := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hδlim.eventually (gt_mem_nhds hε))
  filter_upwards [hca.eventually_ge_atTop T] with k hk e hae
  change q.delta (c k * (H k).time e.succ) ≤ ε
  exact (hT _ (hk.trans (mul_le_mul_of_nonneg_left hae.le (hc k).le))).le

/-- 窗口 δ 小的 Ho 单位桥（不重标度）：`q.delta → 0` 且窗口底 `a_k → ∞`。 -/
theorem eventually_windowDelta_le_P6HS (H : ℕ → ObservedHistory.{u}) {q : CutoffParameters}
    {a : ℕ → ℝ} (hδlim : Tendsto q.delta atTop (𝓝 0)) (ha : Tendsto a atTop atTop) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ e : Fin (H k).eventCount, a k < (H k).time e.succ →
      q.delta ((H k).time e.succ) ≤ ε := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hδlim.eventually (gt_mem_nhds hε))
  filter_upwards [ha.eventually_ge_atTop T] with k hk e hae
  exact (hT _ (hk.trans hae.le)).le

/-- 3/r² 项的免费来源（K 单位 `r = 1`）：`R_k → ∞`（如 `R_k ≥ k+1`）、`Q_b ≥ 1` ⇒ 最终
`3/1² ≤ 2·Q_b·R_k`。 -/
theorem three_div_le_of_tendsto_P6HS {R : ℕ → ℝ} {Qb : ℝ} (hQb : 1 ≤ Qb)
    (hRlim : Tendsto R atTop atTop) :
    ∀ᶠ k in atTop, 3 / (1 : ℝ) ^ 2 ≤ 2 * (Qb * R k) := by
  filter_upwards [hRlim.eventually_ge_atTop (3 / 2)] with k hk
  have h1 : (3 : ℝ) / 1 ^ 2 = 3 := by norm_num
  have h2 := mul_le_mul hQb hk (by norm_num) (by linarith)
  rw [h1]
  linarith

/-- **G1c（`_P6HS`，序列层）**：records 族（参数 `p k`，`recenterConstant ≤ Λ`）+ 窗口 δ → 0
（`hδW`，由 `eventually_windowDelta_le_rescale_P6HS` / `eventually_windowDelta_le_P6HS` 付）+ 合同
最终成立 + 3/r² 项最终成立 ⇒ 最终 CXJD `hscale`。 -/
theorem hscale_eventually_of_windowNeck_P6HS (H : ℕ → ObservedHistory.{u})
    {p : ℕ → CutoffParameters} {T₀ a R r : ℕ → ℝ} {Qb Λ : ℝ} (hQb : 1 ≤ Qb)
    (hΛ : ∀ k, (p k).recenterConstant ≤ Λ)
    (records : ∀ k (e : Fin (H k).eventCount), T₀ k ≤ (H k).time e.succ →
      GeometricCutoffRecord (H k) e (p k))
    (hδW : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ e : Fin (H k).eventCount,
      a k < (H k).time e.succ → (p k).delta ((H k).time e.succ) ≤ ε)
    (hW : ∀ᶠ k in atTop, WindowNeckScaleBudget_P6HS (H k) (p k) (T₀ k) (a k) (R k))
    (h3 : ∀ᶠ k in atTop, 3 / r k ^ 2 ≤ 2 * (Qb * R k)) :
    ∀ᶠ k in atTop, ∀ (e : Fin (H k).eventCount) (he : T₀ k ≤ (H k).time e.succ) b,
      a k < (H k).time e.succ →
      2 * max (3 / r k ^ 2) (2 * (Qb * R k)) < ((records k e he).static b).neck.scale := by
  have hΛ4 : 4 ≤ Λ := (p 0).recenterConstant_ge_four.trans (hΛ 0)
  have hε : 0 < min (1 / (2 * Λ)) (1 / (8 * Qb)) :=
    lt_min (div_pos one_pos (by linarith)) (div_pos one_pos (by linarith))
  filter_upwards [hδW _ hε, hW, h3] with k hk hWk h3k
  refine hscale_of_windowNeck_P6HS (records k) hWk (fun e _ hae => ?_) h3k (by linarith)
  have hτ := (H k).time_nonneg e.succ
  have hd0 := (p k).delta_pos _ hτ
  have hd1 := (p k).delta_lt_one _ hτ
  have hdε := hk e hae
  have hd2 : (p k).delta ((H k).time e.succ) * (2 * Λ) ≤ 1 :=
    (le_div_iff₀ (by linarith)).mp (hdε.trans (min_le_left _ _))
  have hd3 : (p k).delta ((H k).time e.succ) * (8 * Qb) ≤ 1 :=
    (le_div_iff₀ (by linarith)).mp (hdε.trans (min_le_right _ _))
  have hd4 : (p k).delta ((H k).time e.succ) ^ 4 ≤ (p k).delta ((H k).time e.succ) := by
    have h3' : (p k).delta ((H k).time e.succ) ^ 3 ≤ 1 := pow_le_one₀ hd0.le hd1.le
    calc (p k).delta ((H k).time e.succ) ^ 4
        = (p k).delta ((H k).time e.succ) * (p k).delta ((H k).time e.succ) ^ 3 := by ring
      _ ≤ (p k).delta ((H k).time e.succ) * 1 := mul_le_mul_of_nonneg_left h3' hd0.le
      _ = (p k).delta ((H k).time e.succ) := mul_one _
  have hΛk := mul_le_mul_of_nonneg_right (hΛ k) hd0.le
  have h8 := mul_le_mul_of_nonneg_left hd4 (show (0 : ℝ) ≤ 8 * Qb by linarith)
  exact ⟨by linarith, by linarith⟩

/-- **G1c′（K 单位装配，`_P6HS`）**：`H k` 上的 records 用重标度参数 `q.rescale_P6N c_k`（`c_k = r_k²`），
种子半径 `1`；HRECDELTA `hδlim` + Ho 窗口底 `c_k a_k → ∞` + `R_k → ∞` + `Q_b ≥ 1` + 合同最终成立
⇒ 最终 CXJD `hscale`（`r = 1` 形）。唯一 PROVISIONAL 项 = 合同 `hW`。 -/
theorem hscale_eventually_rescale_P6HS (H : ℕ → ObservedHistory.{u}) {q : CutoffParameters}
    {c : ℕ → ℝ} (hc : ∀ k, 0 < c k) {T₀ a R : ℕ → ℝ} {Qb : ℝ} (hQb : 1 ≤ Qb)
    (records : ∀ k (e : Fin (H k).eventCount), T₀ k ≤ (H k).time e.succ →
      GeometricCutoffRecord (H k) e (q.rescale_P6N (c k) (hc k)))
    (hδlim : Tendsto q.delta atTop (𝓝 0)) (hca : Tendsto (fun k => c k * a k) atTop atTop)
    (hRlim : Tendsto R atTop atTop)
    (hW : ∀ᶠ k in atTop,
      WindowNeckScaleBudget_P6HS (H k) (q.rescale_P6N (c k) (hc k)) (T₀ k) (a k) (R k)) :
    ∀ᶠ k in atTop, ∀ (e : Fin (H k).eventCount) (he : T₀ k ≤ (H k).time e.succ) b,
      a k < (H k).time e.succ →
      2 * max (3 / (1 : ℝ) ^ 2) (2 * (Qb * R k)) < ((records k e he).static b).neck.scale :=
  hscale_eventually_of_windowNeck_P6HS H (p := fun k => q.rescale_P6N (c k) (hc k))
    (r := fun _ => 1) (Λ := q.recenterConstant) hQb (fun _ => le_rfl) records
    (fun _ hε => eventually_windowDelta_le_rescale_P6HS H hc hδlim hca hε) hW
    (three_div_le_of_tendsto_P6HS hQb hRlim)

/-! ## 证书：已有行推不出合同 / hscale -/

/-- **证书 1（`_P6HS`）**：hOpen8 的 Tn 行 `R = ρ(Tn)⁻²` 加任意小 `δ(τ) = d` 推不出窗口事件 `τ < Tn` 的
hsep 形：取 antitone `ρ = 1_{t<1} + d²·1_{t≥1}`（Perelman 阶梯型），`Tn = 1`、`τ = 0`，
`4·(2Q_bR)·d⁴ρ(0)² = 8Q_b > 1`。 -/
theorem not_windowBudget_of_TnLine_P6HS {Qb d : ℝ} (hQb : 1 ≤ Qb) (hd0 : 0 < d) (hd1 : d < 1) :
    ∃ ρ : ℝ → ℝ, Antitone ρ ∧ (∀ t, 0 < ρ t) ∧ ρ 1 = d ^ 2 ∧
      1 < 4 * (2 * (Qb * (ρ 1 ^ 2)⁻¹)) * (d ^ 4 * ρ 0 ^ 2) := by
  refine ⟨fun t => if t < 1 then 1 else d ^ 2, ?_, ?_, ite_eq_right (lt_irrefl _), ?_⟩
  · intro x y hxy
    change (if y < 1 then (1 : ℝ) else d ^ 2) ≤ (if x < 1 then (1 : ℝ) else d ^ 2)
    split_ifs <;> first | exact le_rfl | nlinarith
  · intro t
    change 0 < (if t < 1 then (1 : ℝ) else d ^ 2)
    split_ifs <;> first | exact one_pos | exact pow_pos hd0 2
  · have h1 : (if (1 : ℝ) < 1 then (1 : ℝ) else d ^ 2) = d ^ 2 := ite_eq_right (lt_irrefl _)
    have h0 : (if (0 : ℝ) < 1 then (1 : ℝ) else d ^ 2) = 1 := ite_eq_left one_pos
    change 1 < 4 * (2 * (Qb * ((if (1 : ℝ) < 1 then (1 : ℝ) else d ^ 2) ^ 2)⁻¹)) *
      (d ^ 4 * (if (0 : ℝ) < 1 then (1 : ℝ) else d ^ 2) ^ 2)
    rw [h1, h0]
    have hk : ((d ^ 2) ^ 2)⁻¹ * d ^ 4 = 1 := by
      rw [show (d ^ 2) ^ 2 = d ^ 4 by ring]
      exact inv_mul_cancel₀ (pow_ne_zero _ hd0.ne')
    have hk2 : Qb * (((d ^ 2) ^ 2)⁻¹ * d ^ 4) = Qb := by rw [hk, mul_one]
    have h11 : (1 : ℝ) ^ 2 = 1 := one_pow 2
    rw [h11, mul_one]
    linarith

/-- **证书 2（`_P6HS`）**：J6 records 下界 `(n+1)·max((n+1)/c, Qs) ≤ scale_Ho` 与 J10 `c·Qs < R`
推不出 K 单位 `hscale`（`scale_K = c·scale_Ho`，`r = 1`）：`R` 没有上界（`c = Qs = scale = 1`、`R = 2`）。 -/
theorem not_hscale_of_J6_J10_P6HS (Qb : ℝ) :
    ∃ (c Qs sc R : ℝ) (n : ℕ), 0 < c ∧ ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c) Qs ≤ sc ∧
      c * Qs < R ∧ ¬ (2 * max (3 / (1 : ℝ) ^ 2) (2 * (Qb * R)) < c * sc) := by
  refine ⟨1, 1, 1, 2, 0, one_pos, by norm_num, by norm_num, fun h => ?_⟩
  have h1 := le_max_left (3 / (1 : ℝ) ^ 2) (2 * (Qb * 2))
  have h2 : (3 : ℝ) / 1 ^ 2 = 3 := by norm_num
  linarith

namespace ObservedHistory

/-- **G2（`_P6HS`）**：`exists_crossSlab_ceiling_CXJD` 逐字，只把 `hscale` 槽换成 G1b 的前提
（合同 `WindowNeckScaleBudget_P6HS`、窗口 δ 小、3/r² 项）；证明里 `hscale` 由
`hscale_of_windowNeck_P6HS` 以**同一** `records` witness 产出，喂回 CXJD（同一 `ε₀`）。 -/
theorem exists_crossSlab_ceiling_windowNeck_P6HS :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg Cball Qb T K ℓ D : ℝ} (_ : 0 ≤ C2')
    (H : ObservedHistory.{u}) {Tn aSeed a σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn)
    {pT : (H.stageAt Tn).Carrier} {r : ℝ}
    (_ : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (_ : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a₀ : ℝ} (_ : 0 ≤ a₀)
    (_ : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (hσT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (H.stageAt σ).Carrier) {R : ℝ} (L : ℝ) (_ : 0 < R)
    (_ : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hσT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (_ : max (max Cball Cg) 1 ≤ Qb) (_ : 2 * Ctime' * Qb * T ≤ 1) (_ : aSeed ≤ a)
    (haσ : a ≤ σ) (_ : H.activeStage σ < Fin.last H.eventCount)
    (_ : (σ : ℝ) - L ^ 2 / R ≤ a) (_ : (σ : ℝ) - a ≤ T / R) (_ : 1 ≤ R * a)
    {z : (H.stageAt σ).Carrier}
    (_ : metricScalarAt (H.stageMetric (H.activeStage σ) σ) z ≤ Cball * R)
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage σ) (H.activeStage_mono haσ) z)
    (_ : 0 < ℓ) (_ : K * ℓ ^ 2 ≤ 1) (_ : ℓ ≤ r / 50) (_ : 1 / r ^ 2 ≤ K)
    (_ : 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ K)
    (_ : ℓ ≤ localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))
    (_ : 2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / Real.sqrt R)
    {q : CutoffParameters} {T₀ : ℝ} (_ : T₀ ≤ (a : ℝ))
    (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e q)
    (_ : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ →
      (H.event e).old = (H.event e).transition.trace.retainedCore)
    (_ : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (_ : StandardCap.transitionEnd + 10 < q.modelRadius)
    (_ : q.modelAccuracy ≤ ε₀) (_ : 2 ≤ q.modelOrder)
    (_ : WindowNeckScaleBudget_P6HS H q T₀ (a : ℝ) R)
    (_ : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → (a : ℝ) < H.time e.succ →
      q.recenterConstant * q.delta (H.time e.succ) ≤ 1 / 2 ∧
        8 * Qb * q.delta (H.time e.succ) ^ 4 ≤ 1)
    (_ : 3 / r ^ 2 ≤ 2 * (Qb * R))
    (_ : z ∈ riemannianBallOf (H.stageMetric (H.activeStage σ) σ) y (D / Real.sqrt R))
    (_ : riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
        (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
          (H.activeStage_mono hσT)) y ≠ ⊤)
    (_ : D / Real.sqrt R + 8 / ℓ * (T / R) < L / 2 / Real.sqrt R),
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ σ),
        metricScalarAt (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ≤
          2 * (Qb * R) := by
  obtain ⟨ε₀, hε₀, hB⟩ := exists_crossSlab_ceiling_CXJD.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro eps C1' C2' Ctime' Cg Cball Qb T K ℓ D hC2 H Tn aSeed a σ haT pT r hsmall hclock seedTrace
    a₀ ha₀ hpin hσT has y R L hR hgood hQb hstep haS haσ hσlast haL hdepth hRa z hz A hℓ hKℓ hℓr hKr
    hKC hℓρ hρL q T₀ hT₀ records hOld hcan hDm hacc hm hW hδw h3r hzy hdσ hnum
  exact hB hC2 H haT hsmall hclock seedTrace ha₀ hpin hσT has y L hR hgood hQb hstep haS haσ hσlast
    haL hdepth hRa hz A hℓ hKℓ hℓr hKr hKC hℓρ hρL hT₀ records hOld hcan hDm hacc hm
    (hscale_of_windowNeck_P6HS records hW hδw h3r
      ((zero_le_one.trans (le_max_right _ _)).trans hQb)) hzy hdσ hnum

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
