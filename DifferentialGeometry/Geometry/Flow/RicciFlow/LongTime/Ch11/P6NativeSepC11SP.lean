import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeSepBandC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeSepRadialC11SP

/-!
# O-CH11-NATIVE-SEP G5：SEP′（NR 两两核 `hSEP` 的结论，陈述补全 (i)(ii)(iii) 后）PROVED（后缀 `_C11SP`）

`sep_of_records_C11SP`：结论逐字 = `P6NativeNRC11SP.lean` G3b `hSEP` binder 的结论段（413–419 行：
`∀ y₂, RegularCrossing_{e₂} y y₂ → ∀ b₂ z₂, TE < ‖z₂‖ → ‖z₂‖ ≤ TE + 10 →
scale(e₂,b₂) ≤ 4·(B·Q) → window(e₂,b₂) z₂ ≠ y₂`）。前提 = `hSEP` 语境的结构性部分（trace `A : e₁⁺ → e₂⁻`、
`A.point e₁.succ =
window(e₁,b) x`、canonical windows、`modelAccuracy ≤ 1/2`、`2 ≤ modelOrder`）+ G0 块的陈述补全：
(i) `T(e₂⁺) − T(e₁⁺) ≤ θ/Q`；(ii) `e₂` 的 record δ 小（`δ_α·(8√(5C)·Dx + 40000 + 2Rc) ≤ 1`，`C` = M3 常数）；
(iii) `16·(B·θ) ≤ 1`。`hSEP` 的前件（`t` 时刻窗口控制）不用（G0 O2）。

证明 = Perelman II Lemma 4.5 的 chart-reach：G1 `sep_static_C11SP`（`window(e₁,b) x` = `e₂` backward
neck 在 stage `e₁.succ` 的 chart 点，高度 `≤ 1 + (static δ₂)⁻¹`；chart 像不含 `e₁` 的 cap tip）+
G2 M3（`3/5 ≤ C·q₁·r₂²`）+ M4（`d(window x, tip) ≤ √(3/2)/√q₁·‖x‖`，`P6NativeSepRadialC11SP`）+
M2（band 出口长度 `(δ₂⁻¹ − h₀)·r₂/√2`，`P6NativeSepBandC11SP`）⇒ tip 在 chart 像里，矛盾。
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry.Geometry
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace GeometricCutoffRecord

/-- 闭合不等式（纯实数）：`3/5 ≤ C·(s²·r²)`、`8·k·Dx ≤ δ⁻¹`（`k² = 5C`）、`δ⁻¹ ≥ 4`、`h₀ ≤ 1 + δ⁻¹/4`、
`‖x‖ < Dx` ⇒ `√(3/2)/s·‖x‖ < (δ⁻¹ − h₀)·r/√2`。 -/
theorem sep_closing_C11SP {C s r Dx X h₀ dinv : ℝ} (hC : 0 < C) (hs : 0 < s) (hr : 0 < r)
    (hM3 : 3 / 5 ≤ C * (s ^ 2 * r ^ 2)) (hX : 0 ≤ X) (hXD : X < Dx)
    (hd : 8 * Real.sqrt (5 * C) * Dx ≤ dinv) (hd4 : 4 ≤ dinv) (hh₀ : h₀ ≤ 1 + dinv / 4) :
    Real.sqrt (3 / 2) / s * X < (dinv - h₀) * r / Real.sqrt 2 := by
  have hk := Real.sqrt_nonneg (5 * C)
  have hk2 : Real.sqrt (5 * C) ^ 2 = 5 * C := Real.sq_sqrt (by positivity)
  have h3 := Real.sqrt_nonneg 3
  have h32 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hDx : 0 < Dx := hX.trans_lt hXD
  -- `u·k ≥ √3`，`u = r·s`
  have huk : Real.sqrt 3 ≤ r * s * Real.sqrt (5 * C) := by
    have hsq : (3 : ℝ) ≤ (r * s * Real.sqrt (5 * C)) ^ 2 := by
      have he : (r * s * Real.sqrt (5 * C)) ^ 2 = 5 * (C * (s ^ 2 * r ^ 2)) := by
        rw [mul_pow, hk2]
        ring
      rw [he]
      linarith
    calc Real.sqrt 3 ≤ Real.sqrt ((r * s * Real.sqrt (5 * C)) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = r * s * Real.sqrt (5 * C) := Real.sqrt_sq (by positivity)
  have hgap : 4 * Real.sqrt (5 * C) * Dx ≤ dinv - h₀ := by linarith
  have hkey : Real.sqrt 3 * X < (dinv - h₀) * (r * s) := by
    have h1 : Real.sqrt 3 * X < Real.sqrt 3 * (4 * Dx) := by
      have : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      nlinarith
    have h2' : Real.sqrt 3 * (4 * Dx) ≤ 4 * Dx * (r * s * Real.sqrt (5 * C)) := by nlinarith
    have h3' : 4 * Dx * (r * s * Real.sqrt (5 * C)) ≤ (dinv - h₀) * (r * s) := by
      have hrs : 0 < r * s := mul_pos hr hs
      nlinarith
    linarith
  have hsplit : Real.sqrt (3 / 2) = Real.sqrt 3 / Real.sqrt 2 :=
    Real.sqrt_div (by norm_num) 2
  rw [hsplit]
  have hdiff : (dinv - h₀) * r / Real.sqrt 2 - Real.sqrt 3 / Real.sqrt 2 / s * X =
      ((dinv - h₀) * (r * s) - Real.sqrt 3 * X) / (Real.sqrt 2 * s) := by
    field_simp
  have hpos : 0 < ((dinv - h₀) * (r * s) - Real.sqrt 3 * X) / (Real.sqrt 2 * s) :=
    div_pos (by linarith) (mul_pos h2 hs)
  linarith

/-- **G5（PROVED）SEP′**：结论逐字 = G3b `hSEP` 的结论段；前提 = `hSEP` 语境结构性部分 + 陈述补全
(i)(ii)(iii)（见模块注释）。`C` = M3 的绝对常数。 -/
theorem sep_of_records_C11SP :
    ∃ C : ℝ, 0 < C ∧
    ∀ {H : ObservedHistory.{u}} {p : CutoffParameters}
      (records : ∀ i, GeometricCutoffRecord H i p),
      (∀ i b, ((records i).static b).hasCanonicalWindow) →
      p.modelAccuracy ≤ 1 / 2 → 2 ≤ p.modelOrder →
    ∀ (B Q θ Dx : ℝ), 0 < Q → 0 ≤ θ → 16 * (B * θ) ≤ 1 →
    ∀ (e₁ e₂ : Fin H.eventCount) (hl : e₁.succ ≤ e₂.castSucc)
      (y : (H.stage e₂.castSucc).Carrier) (A : BackwardPointTrace H e₁.succ e₂.castSucc hl y)
      (b : (H.event e₁).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point e₁.succ le_rfl hl = ((records e₁).static b).window x →
      ‖x.val‖ < Dx → Dx ≤ p.modelRadius →
      H.time e₂.succ - H.time e₁.succ ≤ θ / Q →
      (∀ α, (records e₂).delta α *
        (8 * Real.sqrt (5 * C) * Dx + 40000 + 2 * p.recenterConstant) ≤ 1) →
      (∀ (y₂ : (H.stage e₂.succ).Carrier), (H.event e₂).RegularCrossing y y₂ →
        ∀ (b₂ : (H.event e₂).RetainedBoundaryIndex) (z₂ : standardCapWindow
            p.modelRadius),
          StandardCap.transitionEnd < ‖z₂.val‖ → ‖z₂.val‖ ≤ StandardCap.transitionEnd + 10 →
          ((records e₂).static b₂).neck.scale ≤ 4 * (B * Q) →
          ((records e₂).static b₂).window z₂ ≠ y₂) := by
  obtain ⟨C, hC, hM3⟩ := exists_scale_match_C11SP.{u}
  refine ⟨C, hC, ?_⟩
  intro H p records hcan hε hm B Q θ Dx hQ hθ hBθ e₁ e₂ hl y A b x hanchor hxD hDx hT2 hδ
    y₂ hcross b₂ z₂ _ _ hscale heq
  set G₁ := records e₁ with hG₁
  set G₂ := records e₂ with hG₂
  set α := b₂.1.1 with hα
  set δ₂ := G₂.delta α with hδ₂def
  have hδpos : 0 < δ₂ := G₂.delta_pos α
  have hRc4 : 4 ≤ p.recenterConstant := p.recenterConstant_ge_four
  have hk := Real.sqrt_nonneg (5 * C)
  have hDx0 : 0 < Dx := (norm_nonneg x.val).trans_lt hxD
  have hδb : δ₂ * (8 * Real.sqrt (5 * C) * Dx + 40000 + 2 * p.recenterConstant) ≤ 1 := hδ α
  have hexp : δ₂ * (8 * Real.sqrt (5 * C) * Dx + 40000 + 2 * p.recenterConstant) =
      δ₂ * (8 * Real.sqrt (5 * C) * Dx) + 40000 * δ₂ + 2 * (p.recenterConstant * δ₂) := by ring
  have hn1 : 0 ≤ δ₂ * (8 * Real.sqrt (5 * C) * Dx) := by positivity
  have hn2 : 0 ≤ p.recenterConstant * δ₂ := by positivity
  have hRc : p.recenterConstant * δ₂ ≤ 1 / 2 := by linarith
  have hδ40 : δ₂ ≤ 1 / 40000 := by linarith
  have hkD : 0 ≤ 8 * Real.sqrt (5 * C) * Dx := by positivity
  have hdinv : 8 * Real.sqrt (5 * C) * Dx + 40000 + 2 * p.recenterConstant ≤ δ₂⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hδpos]
    rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
    linarith
  -- 时间前提
  have hhalf := G₂.time_sub_le_half_nominalRadius_sq_C11SP (j := e₁) b₂ hQ hθ hBθ hscale hRc hT2
  have hr : 0 < G₂.nominalRadius ⟨α⟩ := G₂.nominal_pos ⟨α⟩
  have hT : H.time e₂.succ - (G₂.nominalRadius ⟨α⟩) ^ 2 < H.time e₁.succ := by
    nlinarith [pow_pos hr 2]
  have hlt : H.time e₁.succ < H.time e₂.succ :=
    H.time_strictMono (lt_of_le_of_lt hl (Fin.castSucc_lt_succ (i := e₂)))
  have hx0 : (0 : ThreeSpace) ∈ standardCapWindow p.modelRadius := by
    change ‖(0 : ThreeSpace)‖ < p.modelRadius + 1
    rw [norm_zero]
    linarith [p.modelRadius_pos]
  -- G1 静态核
  obtain ⟨hji, hn, w, hw, hpx, hne⟩ :=
    G₁.sep_static_C11SP hl G₂ A b x hanchor hx0 hcross b₂ z₂ heq hT
  -- 高度：`|w| ≤ h₀ := 1 + (static δ₂)⁻¹ ≤ 1 + δ₂⁻¹/4 ≤ δ₂⁻¹`
  have h4 : ((G₂.static b₂).delta)⁻¹ ≤ δ₂⁻¹ / 4 := by
    have h4' : ((G₂.static b₂).delta)⁻¹ ≤ (4 * δ₂)⁻¹ := by
      rw [G₂.recenter_delta b₂]
      exact inv_anti₀ (by positivity) (by nlinarith)
    have h4'' : (4 * δ₂)⁻¹ = δ₂⁻¹ / 4 := by
      rw [mul_inv]
      ring
    linarith
  have hwδ : |w.1.2| ≤ δ₂⁻¹ := by linarith
  have hh₀L : 1 + ((G₂.static b₂).delta)⁻¹ < δ₂⁻¹ := by linarith
  -- M3
  have hxR : ‖x.val‖ < p.modelRadius := hxD.trans_le hDx
  have hscale3 := hM3 G₁ G₂ b α (hcan e₁ b) hε hm hδ40 hji hlt hhalf hn w hwδ x hxR hpx
  -- M4
  have hM4 := (G₁.static b).window_tip_dist_le_C11SP (hcan e₁ b) hε x hxR hx0
  -- 闭合
  have hq1 : 0 < (G₁.static b).neck.scale := (G₁.static b).neck.scale_pos
  have hs : 0 < Real.sqrt (G₁.static b).neck.scale := Real.sqrt_pos.mpr hq1
  have hs2 : Real.sqrt (G₁.static b).neck.scale ^ 2 = (G₁.static b).neck.scale :=
    Real.sq_sqrt hq1.le
  have hclose := sep_closing_C11SP (C := C) (s := Real.sqrt (G₁.static b).neck.scale)
    (r := G₂.nominalRadius ⟨α⟩) (Dx := Dx) (X := ‖x.val‖) (h₀ := 1 + ((G₂.static b₂).delta)⁻¹)
    (dinv := δ₂⁻¹) hC hs hr (by rw [hs2]; exact hscale3) (norm_nonneg _) hxD (by linarith)
    (by linarith) (by linarith)
  have hdist : riemannianEDistOf (H.event e₁).outputMetric
      ((G₂.backward α).stageChart ⟨e₁.val + 1, by omega⟩
        (by change e₁.val + 1 ≤ e₂.val; omega) hn w)
      ((G₁.static b).window ⟨0, hx0⟩) <
      ENNReal.ofReal ((δ₂⁻¹ - (1 + ((G₂.static b₂).delta)⁻¹)) * G₂.nominalRadius ⟨α⟩ /
        Real.sqrt 2) := by
    rw [hpx]
    exact hM4.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by
      have := hclose
      have h0 : 0 ≤ Real.sqrt (3 / 2) / Real.sqrt (G₁.static b).neck.scale * ‖x.val‖ := by
        positivity
      linarith)).mpr hclose)
  obtain ⟨w', hw'⟩ := G₂.mem_backwardNeck_range_of_dist_lt_C11SP α hδ40 hji hlt hhalf hn w hw
    hh₀L hdist
  exact hne w' hw'

end GeometricCutoffRecord

/-- **consumer（G3b 语境型对齐）**：`H : RetainedCoreHistory`、records 在 `H.toHistory` 上（G3b 的形），
`hSEP` binder（任意前件 `Pre`）由 SEP′ 给出；结论段逐字取自 `P6NativeNRC11SP.lean` 414–419 行
（末行去掉 binder 的 `) →`）。 -/
example : ∃ C : ℝ, 0 < C ∧
    ∀ (H : RetainedCoreHistory.{u}) {p : CutoffParameters}
      (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      (∀ i b, ((records i).static b).hasCanonicalWindow) →
      p.modelAccuracy ≤ 1 / 2 → 2 ≤ p.modelOrder →
    ∀ (B Q θ Dx : ℝ), 0 < Q → 0 ≤ θ → 16 * (B * θ) ≤ 1 →
    ∀ (e₁ e₂ : Fin H.eventCount) (hl : e₁.succ ≤ e₂.castSucc)
      (y : (H.stage e₂.castSucc).Carrier)
      (A : BackwardPointTrace H.toHistory e₁.succ e₂.castSucc hl y)
      (b : (H.toHistory.event e₁).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point e₁.succ le_rfl hl = ((records e₁).static b).window x →
      ‖x.val‖ < Dx → Dx ≤ p.modelRadius →
      H.time e₂.succ - H.time e₁.succ ≤ θ / Q →
      (∀ α, (records e₂).delta α *
        (8 * Real.sqrt (5 * C) * Dx + 40000 + 2 * p.recenterConstant) ≤ 1) →
    ∀ Pre : Prop, Pre →
      (∀ (y₂ : (H.stage e₂.succ).Carrier), (H.toHistory.event e₂).RegularCrossing y y₂ →
        ∀ (b₂ : (H.toHistory.event e₂).RetainedBoundaryIndex) (z₂ : standardCapWindow
            p.modelRadius),
          StandardCap.transitionEnd < ‖z₂.val‖ → ‖z₂.val‖ ≤ StandardCap.transitionEnd + 10 →
          ((records e₂).static b₂).neck.scale ≤ 4 * (B * Q) →
          ((records e₂).static b₂).window z₂ ≠ y₂) := by
  obtain ⟨C, hC, h⟩ := GeometricCutoffRecord.sep_of_records_C11SP.{u}
  exact ⟨C, hC, fun H p records hcan hε hm B Q θ Dx hQ hθ hBθ e₁ e₂ hl y A b x hanchor hxD hDx
    hT2 hδ _ _ => h (H := H.toHistory) records hcan hε hm B Q θ Dx hQ hθ hBθ e₁ e₂ hl y A b x
      hanchor hxD hDx hT2 hδ⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
