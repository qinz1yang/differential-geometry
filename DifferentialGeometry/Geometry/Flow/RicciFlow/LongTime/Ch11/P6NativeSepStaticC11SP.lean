import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CapWindowDisjC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticNeckChildCore
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Backward

/-!
# O-CH11-NATIVE-SEP G1：NR 两两核 `hSEP` 的静态片（M1 + M5，后缀 `_C11SP`，无 binder）

G0 判定 `hSEP`（`P6NativeNRC11SP.lean` G3b）BLOCKED：原陈述缺 `T(e₂⁺) − T(e₁⁺)` 上界，且需 Perelman II
Lemma 4.5 的 chart-reach（M2–M4）。本文件交其中**静态**部分（PROVED，只用 record / event 结构字段）：

* M5b `not_regularCrossing_window_tip_C11SP`：record `e₁` 的 static cap window 的 tip（`window 0`）不是
  `e₁` 处任何点的 regular crossing 像（`tip_interior` + `cap_eq` + `core_cap_intersection` +
  `Capping.boundary_eq` + cap 单射：tip 是 cap 内点，不在 attaching sphere 上）。
* M5a `exists_neckChart_of_regularCrossing_window_C11SP`：若 `y` 在 `e₂` 处 regular-cross 到
  `window(e₂,b₂) z₂`（任意 `z₂`，buffer 条件不需要），则 `y` = record neck `b₂.1.1` 的 chart 点，高度
  `|z| ≤ 1 + (static δ)⁻¹`（retained collar 情形经 `staticNeckChart_eq_neckChart` 平移；cap∩core 情形
  是 core 边界球，高度 `±1`）。
* M1 `backwardTrace_point_eq_stageChart_C11SP`：终点在 `e₂` backward neck chart 里的 trace，在
  backward neck 覆盖的每个 stage 上都等于 `B.stageChart`（`B.crossing` + regular crossing 左唯一）。
* M5 `stageChart_ne_window_tip_C11SP`：跨过 `T(e₁⁺)` 的 backward neck，其 stage `e₁.succ` 上的 chart
  像不含 `e₁` 的 cap tip。
* 合成 `sep_static_C11SP`：在 `hSEP` 的语境（trace `A : e₁⁺ → e₂⁻`、`A.point e₁.succ = window(e₁,b) x`、
  `RegularCrossing_{e₂} y y₂`、`window(e₂,b₂) z₂ = y₂`）加时间前提 `T(e₂⁺) − r₂² < T(e₁⁺)`
  （`r₂` = record `e₂` 的 nominal radius）⇒ `window(e₁,b) x` 是 `e₂` backward neck 在 stage `e₁.succ`
  的 chart 点（高度界同 M5a），而该 chart 像不含 `e₁` 的 cap tip。剩下的 M2–M4（chart 像含从
  `window(e₁,b) x` 到 tip 的整条径向路径）是解析部分，见 `state-O-CH11-NATIVE-SEP.md` HANDOVER。
* 时间前提的来源 `time_sub_le_half_nominalRadius_sq_C11SP`：`T(e₂⁺) − T(e₁⁺) ≤ θ/Q`、`16·(B·θ) ≤ 1`、
  static scale `≤ 4BQ`、`Rc·δ ≤ 1/2`（`recenter_scale_comparison`、`scale_eq`）⇒
  `T(e₂⁺) − T(e₁⁺) ≤ r₂²/2`（即 backward neck 时间参数 `v₁ ∈ [−1/2, 0]`），从而 `< r₂²`。
-/

set_option autoImplicit false

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {parameters : CutoffParameters}

/-- **M5b（PROVED）**：record static cap window 的 tip 不是该 event 的 regular crossing 像。 -/
theorem not_regularCrossing_window_tip_C11SP {j : Fin H.eventCount}
    (G : GeometricCutoffRecord H j parameters) (b : (H.event j).RetainedBoundaryIndex)
    (hx : (0 : ThreeSpace) ∈ standardCapWindow parameters.modelRadius)
    (p : (H.stage j.castSucc).Carrier) :
    ¬ (H.event j).RegularCrossing p ((G.static b).window ⟨0, hx⟩) := by
  rintro ⟨o, -, -, ho⟩
  obtain ⟨k, hk1, hk⟩ := (G.static b).witness.tip_interior
  have hP := (H.event j).transition.trace.presentation.injective
  have htip : (G.static b).window ⟨0, hx⟩ =
      (G.static b).inclusion (G.static b).witness.tip :=
    congrArg (G.static b).inclusion ((G.static b).witness.window_tip hx)
  have hcore : (H.event j).transition.trace.capping.coreInclusion o.1 =
      (H.event j).transition.trace.capping.cap b.1 k := by
    apply hP
    rw [(H.event j).oldOutput_eq o, (G.static b).cap_eq k, ho, htip, hk]
  have hmem : (H.event j).transition.trace.capping.cap b.1 k ∈
      Set.range (H.event j).transition.trace.capping.coreInclusion ∩
        Set.range ((H.event j).transition.trace.capping.cap b.1) :=
    ⟨⟨o.1, hcore⟩, ⟨k, rfl⟩⟩
  rw [(H.event j).transition.trace.capping.core_cap_intersection] at hmem
  obtain ⟨ζ, hζ⟩ := hmem
  have hb := (H.event j).transition.trace.capping.boundary_eq b.1
    (((H.event j).transition.trace.capping.attaching b.1).symm ζ)
  rw [Homeomorph.apply_symm_apply] at hb
  have hkk : sphereToThreeBall (((H.event j).transition.trace.capping.attaching b.1).symm ζ) =
      k := ((H.event j).transition.trace.capping.capEmbedding b.1).injective (hb.trans hζ)
  have hnorm : ‖(sphereToThreeBall
      (((H.event j).transition.trace.capping.attaching b.1).symm ζ)).1‖ = 1 :=
    mem_sphere_zero_iff_norm.mp
      (((H.event j).transition.trace.capping.attaching b.1).symm ζ).2
  rw [hkk] at hnorm
  linarith

/-- **M5a（PROVED）**：regular-cross 到 record static cap window 点的 incoming 点是 record neck
`b.1.1` 的 chart 点，高度 `≤ 1 + (static δ)⁻¹`（window 点任意，不需要 buffer 条件）。 -/
theorem exists_neckChart_of_regularCrossing_window_C11SP {i : Fin H.eventCount}
    (G : GeometricCutoffRecord H i parameters) (b : (H.event i).RetainedBoundaryIndex)
    (z : standardCapWindow parameters.modelRadius) {y : (H.stage i.castSucc).Carrier}
    (hy : (H.event i).RegularCrossing y ((G.static b).window z)) :
    ∃ w : neckBuffer (G.delta b.1.1), ((G.neck b.1.1).chart w).1 = y ∧
      |w.1.2| ≤ 1 + ((G.static b).delta)⁻¹ := by
  obtain ⟨o, -, hoy, ho⟩ := hy
  have hP := (H.event i).transition.trace.presentation.injective
  have hC := (H.event i).transition.trace.capping.coreEmbedding.injective
  have hO := (H.event i).oldOutput_eq o
  rw [ho] at hO
  have hsδ : 0 < ((G.static b).delta)⁻¹ := inv_pos.mpr (G.static b).neck.delta_pos
  rcases (G.static b).window_mem_cases_C11SP z with ⟨r, hr⟩ | ⟨k, hk⟩
  · have h1 : o.1 = ((G.static b).retainedPoint r).1 := hC (hP (hO.trans hr.symm))
    have hrb : r.1 ∈ neckBuffer (G.static b).delta := by
      constructor <;> linarith [r.2.1, r.2.2]
    refine ⟨⟨(r.1.1, (if b.1.2 then (1 : ℝ) else -1) * (1 + r.1.2)),
      G.recenter_in_buffer b ⟨r.1, hrb⟩⟩, ?_, ?_⟩
    · rw [← G.staticNeckChart_eq_neckChart b ⟨r.1, hrb⟩,
        ← (G.static b).retained_point_eq r hrb, ← h1]
      exact hoy
    · change |(if b.1.2 then (1 : ℝ) else -1) * (1 + r.1.2)| ≤ _
      have hr0 : 0 ≤ r.1.2 := r.2.1
      have hr1 : r.1.2 < ((G.static b).delta)⁻¹ := r.2.2
      cases b.1.2
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [abs_le]
        constructor <;> linarith
      · simp only [↓reduceIte]
        rw [abs_le]
        constructor <;> linarith
  · have h1 : (H.event i).transition.trace.capping.coreInclusion o.1 =
        (H.event i).transition.trace.capping.cap b.1 k := hP (hO.trans hk.symm)
    have hmem : (H.event i).transition.trace.capping.coreInclusion o.1 ∈
        Set.range (H.event i).transition.trace.capping.coreInclusion ∩
          Set.range ((H.event i).transition.trace.capping.cap b.1) :=
      ⟨⟨o.1, rfl⟩, ⟨k, h1.symm⟩⟩
    rw [(H.event i).transition.trace.capping.core_cap_intersection] at hmem
    obtain ⟨ζ, hζ⟩ := hmem
    have h2 : (H.event i).transition.trace.tubes.coreBoundarySphere b.1 ζ = o.1 := hC hζ
    have hw := G.tube_in_buffer b.1.1 (ζ, TubeSystem.boundaryLevel b.1.2)
    refine ⟨⟨_, hw⟩, ?_, ?_⟩
    · have h := G.tube_eq b.1.1 (ζ, TubeSystem.boundaryLevel b.1.2) hw
      rw [← h, ← hoy, ← h2]
      rfl
    · have hlev : |((TubeSystem.boundaryLevel b.1.2 : Icc (-2 : ℝ) 2) : ℝ)| = 1 := by
        cases b.1.2 <;> simp [TubeSystem.boundaryLevel]
      change |((TubeSystem.boundaryLevel b.1.2 : Icc (-2 : ℝ) 2) : ℝ)| ≤ _
      rw [hlev]
      linarith

end GeometricCutoffRecord

namespace IncomingBackwardNeck

variable {H : ObservedHistory.{u}}

/-- **M1（PROVED）**：终点 `y = neck.chart w` 的 backward trace，在 backward neck 覆盖的每个
event stage `m.castSucc`（`j.succ ≤ m.castSucc`，`m ≤ i`，`T(i⁺) − r² < T(m⁺)`）上等于 `B.stageChart m`。 -/
theorem backwardTrace_point_eq_stageChart_C11SP {i j : Fin H.eventCount}
    {δ : ℝ} {k : ℕ} {neck : NormalizedNeck (H.event i).terminal.metric δ k} {r : ℝ}
    (B : IncomingBackwardNeck H i neck r) (w : neckBuffer δ)
    {hl : j.succ ≤ i.castSucc} {y : (H.stage i.castSucc).Carrier}
    (A : BackwardPointTrace H j.succ i.castSucc hl y) (hy : (neck.chart w).1 = y) :
    ∀ (d : ℕ) (m : Fin H.eventCount), i.val - m.val = d →
      ∀ (hjm : j.succ ≤ m.castSucc) (hmi : m.val ≤ i.val)
        (ham : H.time i.succ - r ^ 2 < H.time m.succ),
      A.point m.castSucc hjm (Fin.castSucc_le_castSucc_iff.mpr hmi) =
        B.stageChart m hmi ham w := by
  intro d
  induction d with
  | zero =>
    intro m hd hjm hmi ham
    have hmi' : m = i := Fin.ext (by omega)
    subst hmi'
    exact A.endpoint_eq.trans (hy.symm.trans (B.terminal_chart ham w).symm)
  | succ d ih =>
    intro m hd hjm hmi ham
    have hlt : m.val < i.val := by omega
    let m' : Fin H.eventCount := ⟨m.val + 1, by omega⟩
    have hmm' : m.succ ≤ m'.castSucc := le_rfl
    have hm'd : i.val - m'.val = d := by
      change i.val - (m.val + 1) = d
      omega
    have ham' : H.time i.succ - r ^ 2 < H.time m'.succ :=
      ham.trans (H.time_strictMono (Fin.succ_lt_succ_iff.mpr (Fin.lt_def.mpr
        (Nat.lt_succ_self m.val))))
    have hjm' : j.succ ≤ m'.castSucc :=
      hjm.trans ((Fin.castSucc_lt_succ (i := m)).le.trans hmm')
    have hm'i : m'.val ≤ i.val := by
      change m.val + 1 ≤ i.val
      omega
    have hih := ih m' hm'd hjm' hm'i ham'
    have hsl : m.succ ≤ i.castSucc := hmm'.trans (Fin.castSucc_le_castSucc_iff.mpr hm'i)
    have hA := A.crossing m hjm hsl
    have hB := B.crossing m hlt ham ham' w
    have hA' : (H.event m).RegularCrossing
        (A.point m.castSucc hjm ((Fin.castSucc_lt_succ (i := m)).le.trans hsl))
        (B.stageChart m' hm'i ham' w) := by
      rw [← hih]
      exact hA
    exact (H.event m).regularCrossing_left_unique hA' hB

end IncomingBackwardNeck

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {parameters : CutoffParameters}

/-- **M5（PROVED）**：跨过 `T(j⁺)` 的（更晚 event `i` 的）backward neck，其 stage `j.succ` 上的 chart
像不含 record `j` 的 static cap tip。 -/
theorem stageChart_ne_window_tip_C11SP {i j : Fin H.eventCount} (hji : j.val < i.val)
    (G : GeometricCutoffRecord H j parameters) (b : (H.event j).RetainedBoundaryIndex)
    (hx : (0 : ThreeSpace) ∈ standardCapWindow parameters.modelRadius)
    {δ : ℝ} {k : ℕ} {neck : NormalizedNeck (H.event i).terminal.metric δ k} {r : ℝ}
    (B : IncomingBackwardNeck H i neck r) (ha : H.time i.succ - r ^ 2 < H.time j.succ)
    (hn : H.time i.succ - r ^ 2 <
      H.time (⟨j.val + 1, by omega⟩ : Fin H.eventCount).succ)
    (w : neckBuffer δ) :
    B.stageChart ⟨j.val + 1, by omega⟩ (by change j.val + 1 ≤ i.val; omega) hn w ≠
      (G.static b).window ⟨0, hx⟩ := by
  intro h
  have hc := B.crossing j hji ha hn w
  rw [h] at hc
  exact G.not_regularCrossing_window_tip_C11SP b hx _ hc

/-- **时间前提（PROVED，(iii) 的算术）**：`T(i⁺) − T(j⁺) ≤ θ/Q`、`16·(Bq·θ) ≤ 1`、static scale `≤ 4·Bq·Q`、
`Rc·δ_α ≤ 1/2` ⇒ `T(i⁺) − T(j⁺) ≤ r_α²/2`（`r_α` = nominal radius，`α = b.1.1`；
`recenter_scale_comparison` 给 record scale `≤ 2·` static scale，`scale_eq` 给
`r_α² = (record scale)⁻¹`）。 -/
theorem time_sub_le_half_nominalRadius_sq_C11SP {i j : Fin H.eventCount}
    (G : GeometricCutoffRecord H i parameters) (b : (H.event i).RetainedBoundaryIndex)
    {Bq Q θ : ℝ} (hQ : 0 < Q) (hθ : 0 ≤ θ) (hBθ : 16 * (Bq * θ) ≤ 1)
    (hscale : (G.static b).neck.scale ≤ 4 * (Bq * Q))
    (hRc : parameters.recenterConstant * G.delta b.1.1 ≤ 1 / 2)
    (hT : H.time i.succ - H.time j.succ ≤ θ / Q) :
    H.time i.succ - H.time j.succ ≤ (G.nominalRadius ⟨b.1.1⟩) ^ 2 / 2 := by
  have hsr : 0 < (G.neck b.1.1).scale := (G.neck b.1.1).scale_pos
  have hcmp := (abs_le.mp ((G.recenter_scale_comparison b).trans hRc)).1
  have h1 : 1 / 2 * (G.neck b.1.1).scale ≤ (G.static b).neck.scale := by
    have h := (le_div_iff₀ hsr).mp (show (1 / 2 : ℝ) ≤ (G.static b).neck.scale /
      (G.neck b.1.1).scale by linarith)
    linarith
  have h3 : (G.neck b.1.1).scale ≤ 8 * (Bq * Q) := by linarith
  have hr2 : (G.nominalRadius ⟨b.1.1⟩) ^ 2 = ((G.neck b.1.1).scale)⁻¹ := by
    rw [G.scale_eq b.1.1, inv_inv]
  have h4 : θ * 2 * (G.neck b.1.1).scale ≤ Q := by
    nlinarith [mul_le_mul_of_nonneg_left h3 hθ]
  have h5 : θ * 2 ≤ Q / (G.neck b.1.1).scale := (le_div_iff₀ hsr).mpr h4
  refine hT.trans ?_
  rw [hr2, div_le_div_iff₀ hQ (by norm_num : (0 : ℝ) < 2), ← div_eq_inv_mul]
  exact h5

/-- **合成（PROVED，SEP 的静态核）**：`hSEP` 语境（trace `A : e₁⁺ → e₂⁻`，`A.point e₁.succ = window(e₁,b) x`，
`RegularCrossing_{e₂} y y₂`，`window(e₂,b₂) z₂ = y₂`）+ 时间前提 `T(e₂⁺) − r₂² < T(e₁⁺)` ⇒
`window(e₁,b) x` 是 `e₂` 的 backward neck `B := G₂.backward b₂.1.1` 在 stage `e₁.succ` 的 chart 点
（高度 `≤ 1 + (static δ₂)⁻¹`），
而 `B` 在该 stage 的 chart 像**不含** `e₁` 的 cap tip。SEP′ 只差 chart-reach（M2–M4）。 -/
theorem sep_static_C11SP {e₁ e₂ : Fin H.eventCount} (hl : e₁.succ ≤ e₂.castSucc)
    (G₁ : GeometricCutoffRecord H e₁ parameters) (G₂ : GeometricCutoffRecord H e₂ parameters)
    {y : (H.stage e₂.castSucc).Carrier} (A : BackwardPointTrace H e₁.succ e₂.castSucc hl y)
    (b : (H.event e₁).RetainedBoundaryIndex) (x : standardCapWindow parameters.modelRadius)
    (hanchor : A.point e₁.succ le_rfl hl = (G₁.static b).window x)
    (hx0 : (0 : ThreeSpace) ∈ standardCapWindow parameters.modelRadius)
    {y₂ : (H.stage e₂.succ).Carrier} (hcross : (H.event e₂).RegularCrossing y y₂)
    (b₂ : (H.event e₂).RetainedBoundaryIndex) (z₂ : standardCapWindow parameters.modelRadius)
    (heq : (G₂.static b₂).window z₂ = y₂)
    (hT : H.time e₂.succ - (G₂.nominalRadius ⟨b₂.1.1⟩) ^ 2 < H.time e₁.succ) :
    ∃ (hji : e₁.val < e₂.val) (hn : H.time e₂.succ - (G₂.nominalRadius ⟨b₂.1.1⟩) ^ 2 <
        H.time (⟨e₁.val + 1, by omega⟩ : Fin H.eventCount).succ)
      (w : neckBuffer (G₂.delta b₂.1.1)),
      |w.1.2| ≤ 1 + ((G₂.static b₂).delta)⁻¹ ∧
      (G₂.backward b₂.1.1).stageChart ⟨e₁.val + 1, by omega⟩
          (by change e₁.val + 1 ≤ e₂.val; omega) hn w = (G₁.static b).window x ∧
      ∀ w' : neckBuffer (G₂.delta b₂.1.1),
        (G₂.backward b₂.1.1).stageChart ⟨e₁.val + 1, by omega⟩
            (by change e₁.val + 1 ≤ e₂.val; omega) hn w' ≠
          (G₁.static b).window ⟨0, hx0⟩ := by
  have hji : e₁.val < e₂.val := by
    have h := Fin.le_def.mp hl
    simp only [Fin.val_succ, Fin.val_castSucc] at h
    omega
  rw [← heq] at hcross
  obtain ⟨w, hwy, hw⟩ := G₂.exists_neckChart_of_regularCrossing_window_C11SP b₂ z₂ hcross
  let nx : Fin H.eventCount := ⟨e₁.val + 1, by omega⟩
  have hn : H.time e₂.succ - (G₂.nominalRadius ⟨b₂.1.1⟩) ^ 2 < H.time nx.succ :=
    hT.trans (H.time_strictMono (Fin.succ_lt_succ_iff.mpr (Fin.lt_def.mpr
      (Nat.lt_succ_self e₁.val))))
  have hnx : nx.val ≤ e₂.val := by
    change e₁.val + 1 ≤ e₂.val
    omega
  have hM1 := (G₂.backward b₂.1.1).backwardTrace_point_eq_stageChart_C11SP w A hwy
    (e₂.val - nx.val) nx rfl le_rfl hnx hn
  refine ⟨hji, hn, w, hw, ?_, fun w' => ?_⟩
  · exact hM1.symm.trans hanchor
  · exact G₁.stageChart_ne_window_tip_C11SP hji b hx0 (G₂.backward b₂.1.1) hT hn w'

end GeometricCutoffRecord

/-- **consumer**：(i)(ii)(iii) 形前提经 `time_sub_le_half_nominalRadius_sq_C11SP` 给时间前提，再由
`sep_static_C11SP`：只要 `e₂` backward neck 在 stage `e₁.succ` 的 chart 像含 `e₁` 的 cap tip（M2–M4 的
chart-reach 结论），`hSEP` 的最内层结论 `window(e₂,b₂) z₂ ≠ y₂` 成立。 -/
example {H : ObservedHistory.{u}} {parameters : CutoffParameters} {e₁ e₂ : Fin H.eventCount}
    (hl : e₁.succ ≤ e₂.castSucc)
    (G₁ : GeometricCutoffRecord H e₁ parameters) (G₂ : GeometricCutoffRecord H e₂ parameters)
    {y : (H.stage e₂.castSucc).Carrier} (A : BackwardPointTrace H e₁.succ e₂.castSucc hl y)
    (b : (H.event e₁).RetainedBoundaryIndex) (x : standardCapWindow parameters.modelRadius)
    (hanchor : A.point e₁.succ le_rfl hl = (G₁.static b).window x)
    (hx0 : (0 : ThreeSpace) ∈ standardCapWindow parameters.modelRadius)
    {y₂ : (H.stage e₂.succ).Carrier} (hcross : (H.event e₂).RegularCrossing y y₂)
    (b₂ : (H.event e₂).RetainedBoundaryIndex) (z₂ : standardCapWindow parameters.modelRadius)
    {Bq Q θ : ℝ} (hQ : 0 < Q) (hθ : 0 ≤ θ) (hBθ : 16 * (Bq * θ) ≤ 1)
    (hscale : (G₂.static b₂).neck.scale ≤ 4 * (Bq * Q))
    (hRc : parameters.recenterConstant * G₂.delta b₂.1.1 ≤ 1 / 2)
    (hT2 : H.time e₂.succ - H.time e₁.succ ≤ θ / Q)
    (hreach : ∀ (hji : e₁.val < e₂.val) (hn : H.time e₂.succ -
        (G₂.nominalRadius ⟨b₂.1.1⟩) ^ 2 < H.time (⟨e₁.val + 1, by omega⟩ : Fin H.eventCount).succ),
      (G₁.static b).window ⟨0, hx0⟩ ∈ Set.range ((G₂.backward b₂.1.1).stageChart
        ⟨e₁.val + 1, by omega⟩ (by change e₁.val + 1 ≤ e₂.val; omega) hn)) :
    (G₂.static b₂).window z₂ ≠ y₂ := by
  intro heq
  have hr : 0 < G₂.nominalRadius ⟨b₂.1.1⟩ := G₂.nominal_pos ⟨b₂.1.1⟩
  have hhalf := G₂.time_sub_le_half_nominalRadius_sq_C11SP (j := e₁) b₂ hQ hθ hBθ hscale hRc hT2
  have hT : H.time e₂.succ - (G₂.nominalRadius ⟨b₂.1.1⟩) ^ 2 < H.time e₁.succ := by
    nlinarith [pow_pos hr 2]
  obtain ⟨hji, hn, -, -, -, hne⟩ :=
    G₁.sep_static_C11SP hl G₂ A b x hanchor hx0 hcross b₂ z₂ heq hT
  obtain ⟨w', hw'⟩ := hreach hji hn
  exact hne w' hw'

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
