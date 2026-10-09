import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KappaBridgeMarginP6B2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.EarlierGoodTraceLocal_P6N

/-!
# P6 距离线 G1：合同冻结（O-CH11-DIST，后缀 `_C11D`）

外审 R-C11-2 D-5 / D-7 / D-8
（`docs/geometrization/chapter8/out/dispositions-R-C11-2-p6-w1-open-items.md`）的距离链
`严格内部曲率界 → 端点球与保护条件 → 光滑积分 (D3) + surgery 无捷径 (D4) → (D1) → 固定 A_*`
在 `ObservedHistory` 层的**纯逻辑装配**。(D3) / (D4) 在这里是显式前提（stage 级的 inline ∀-陈述，
不打包成新 `Prop`）；G2 / G3 用树内引理生产它们：

* (D3) 积分形 = 树内 `riemannianEDistOf_le_add_of_endpoint_ricci_on_interval`
  （`Estimates/Distance/FixedEndpoints.lean:30`，Perelman I.8.3(b)，`m = 3`：两端 `ℓ`-球 `Ric ≤ (3/ℓ²) g`
  ⇒ `d_a ≤ d_b + (8/ℓ)(b − a)`）——G2 adapter 到 stage slab，`ℓ ≍ Q^{-1/2}` ⇒ 速率 `Λ = c √Q`。
* (D4) = 树内 `MetricCutCapEvent.oldTerminal_edist_le_of_outside_canonical_cap_windows`
  （`ST/EventCapNoShortcut.lean:846`：端点在 canonical cap window 内区外 ⇒ `d_term ≤ d_out`）
  + terminal 极限（`t ↑ τ` 时 `d_t ≤ d_term + o(1)`）——G3。

本文件的声明（`H : ObservedHistory`）：
1. `edist_le_of_stage_bounds_C11D`：抽象链——两族 stage 点 `P_k, Q_k`；末 stage 的光滑前提 `hsmooth`
   （(D3) 形）+ 每个 event 的跨越前提 `hevent`（`d_{k}(t) ≤ d_{k+1}(τ) + Λ(τ − t)`，
   = (D3) 到 `τ⁻` + (D4)）⇒ `d_i(v) ≤ d_j(s) + Λ(s − v)`。
2. `le_add_of_smooth_of_terminal_approx_C11D`：`hevent` 的 ENNReal 极限装配——(D3) 在 `[t, t']`（`t' < τ`）
   + terminal 逼近（`∀ δ > 0, ∃ t' ∈ [t, τ), d(t') ≤ X + δ`）⇒ `d(t) ≤ X + Λ(τ − t)`
   （`X = d_out`，由 (D4)）。
3. `edist_trace_le_of_stage_bounds_C11D`：链对 seed trace 与 `x` 的 backward trace 的特化。
4. **`hdist_rel_of_stage_bounds_C11D`（主目标，相对形）**：输出恰是 P6CON L9
   `hasSpatialCanonicalTimeControl_on_window_traces_P6N` 的 `hdist`：
   `d_v(seed(v), x_v) ≤ d_s(O, y) + L/√Q`；
   数值条件 `Rad/√Q + Λ θ/Q ≤ L/√Q`（`Λ = c√Q` 时即 `Rad + c θ ≤ L`，`L → ∞` 免费）。
5. `hD1_of_stage_bounds_C11D`（绝对形 (D1)，序列层）：中心界 `y_n ∈ B_{s_n}(O_n, A₀ r_n)`（selection 输出
   `(A + 1) r`）+ 速率 `Λ_n = c_{D,T} √R_n` ⇒ `d < A₀ r_n + (D + c T)/√R_n`，即 P6B2
   `hdist_fixed_of_D1_P6B2` 的 `hD1` 形（`C = D + c T`）。
6. `hdist_fixed_of_stage_bounds_C11D`（`GC.LongTime.Ch11`，F 层）：5 + `hdist_fixed_of_D1_P6B2` ⇒ 固定
   `A_* = A₀ + 1` 的 `hdist`（= `tracedKappa_of_window_margin_P6B2` 的 `hdist`）。

相对形 vs 绝对形（P6CON G4 发现，lead 02:2x 补充）：D-5 的绝对形**推不出**相对形；两者都由 1–3 的同一条链
给出——相对形不需要中心界，绝对形 = 相对形 + 中心界。consumer：文件末 `example`（4 ⇒ L9）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped NNReal Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

variable (H : ObservedHistory.{u})

/-! ## 1. 抽象链（stage 点族） -/

/-- **抽象距离链（`_C11D`）**：stage 下标 `i ≤ j`、两族 stage 点 `P_k, Q_k`（`i ≤ k ≤ j`）、速率 `Λ ≥ 0`、
窗口 `[v, s]`（`time i ≤ v`、`v` 早于 `i` 的下一个 event、`time j ≤ s`）。前提：
* `hsmooth`（末 stage `j` 的 (D3) 积分形）：`t ∈ [max(v, time j), s]` ⇒ `d_{j,t} ≤ d_{j,s} + Λ(s − t)`；
* `hevent`（event `e`，`i ≤ e⁻`、`e⁺ ≤ j`；= (D3) 到 `τ⁻` + (D4) 无捷径）：
  `t ∈ [max(v, time e⁻), time e⁺)` ⇒ `d_{e⁻,t} ≤ d_{e⁺, time e⁺} + Λ(time e⁺ − t)`。
结论：`d_{i,v}(P_i, Q_i) ≤ d_{j,s}(P_j, Q_j) + Λ(s − v)`。证明：对 `j − k` 归纳，逐 event 叠加。 -/
theorem edist_le_of_stage_bounds_C11D {i j : Fin (H.eventCount + 1)} (hij : i ≤ j)
    (P Q : ∀ k : Fin (H.eventCount + 1), i ≤ k → k ≤ j → (H.stage k).Carrier)
    {v s Λ : ℝ} (hΛ : 0 ≤ Λ) (hiv : H.time i ≤ v)
    (hvi : ∀ e : Fin H.eventCount, i = e.castSucc → v < H.time e.succ)
    (hvs : v ≤ s) (hjs : H.time j ≤ s)
    (hsmooth : ∀ t : ℝ, v ≤ t → H.time j ≤ t → t ≤ s →
      riemannianEDistOf (H.stageMetric j t) (P j hij le_rfl) (Q j hij le_rfl) ≤
        riemannianEDistOf (H.stageMetric j s) (P j hij le_rfl) (Q j hij le_rfl) +
          ENNReal.ofReal (Λ * (s - t)))
    (hevent : ∀ (e : Fin H.eventCount) (he1 : i ≤ e.castSucc) (he2 : e.succ ≤ j) (t : ℝ),
      v ≤ t → H.time e.castSucc ≤ t → t < H.time e.succ →
      riemannianEDistOf (H.stageMetric e.castSucc t)
          (P e.castSucc he1 (e.castSucc_lt_succ.le.trans he2))
          (Q e.castSucc he1 (e.castSucc_lt_succ.le.trans he2)) ≤
        riemannianEDistOf (H.stageMetric e.succ (H.time e.succ))
            (P e.succ (he1.trans e.castSucc_lt_succ.le) he2)
            (Q e.succ (he1.trans e.castSucc_lt_succ.le) he2) +
          ENNReal.ofReal (Λ * (H.time e.succ - t))) :
    riemannianEDistOf (H.stageMetric i v) (P i le_rfl hij) (Q i le_rfl hij) ≤
      riemannianEDistOf (H.stageMetric j s) (P j hij le_rfl) (Q j hij le_rfl) +
        ENNReal.ofReal (Λ * (s - v)) := by
  have key : ∀ n : ℕ, ∀ (k : Fin (H.eventCount + 1)) (hk1 : i ≤ k) (hk2 : k ≤ j),
      (j : ℕ) - k = n → ∀ t : ℝ, v ≤ t → H.time k ≤ t → t ≤ s →
      (∀ e : Fin H.eventCount, k = e.castSucc → t < H.time e.succ) →
      riemannianEDistOf (H.stageMetric k t) (P k hk1 hk2) (Q k hk1 hk2) ≤
        riemannianEDistOf (H.stageMetric j s) (P j hij le_rfl) (Q j hij le_rfl) +
          ENNReal.ofReal (Λ * (s - t)) := by
    intro n
    induction n with
    | zero =>
      intro k hk1 hk2 hn t hvt hkt hts _
      obtain rfl : k = j := le_antisymm hk2 (Fin.le_iff_val_le_val.2 (by omega))
      exact hsmooth t hvt hkt hts
    | succ n ih =>
      intro k hk1 hk2 hn t hvt hkt hts hnext
      have hlt : (k : ℕ) < H.eventCount := by
        have := j.isLt
        omega
      obtain ⟨e, rfl⟩ : ∃ e : Fin H.eventCount, k = e.castSucc := ⟨⟨k, hlt⟩, Fin.ext rfl⟩
      have he2 : e.succ ≤ j := by
        rw [Fin.le_iff_val_le_val, Fin.val_succ]
        simp only [Fin.val_castSucc] at hn
        omega
      have htτ : t < H.time e.succ := hnext e rfl
      have hτs : H.time e.succ ≤ s := (H.time_strictMono.monotone he2).trans hjs
      have h1 := hevent e hk1 he2 t hvt hkt htτ
      have h2 := ih e.succ (hk1.trans e.castSucc_lt_succ.le) he2
        (by simp only [Fin.val_succ, Fin.val_castSucc] at hn ⊢; omega) (H.time e.succ)
        (hvt.trans htτ.le) le_rfl hτs (fun e' he' => by
          rw [he']
          exact H.time_strictMono e'.castSucc_lt_succ)
      calc _ ≤ _ := h1
        _ ≤ (riemannianEDistOf (H.stageMetric j s) (P j hij le_rfl) (Q j hij le_rfl) +
              ENNReal.ofReal (Λ * (s - H.time e.succ))) +
            ENNReal.ofReal (Λ * (H.time e.succ - t)) := add_le_add h2 le_rfl
        _ = riemannianEDistOf (H.stageMetric j s) (P j hij le_rfl) (Q j hij le_rfl) +
              ENNReal.ofReal (Λ * (s - t)) := by
          rw [add_assoc, ← ENNReal.ofReal_add (mul_nonneg hΛ (by linarith))
            (mul_nonneg hΛ (by linarith))]
          congr 2
          ring
  exact key _ i le_rfl hij rfl v le_rfl hiv hvs hvi

/-! ## 2. `hevent` 的极限装配（(D3) 到 `τ⁻` + terminal 逼近） -/

/-- **(D3) + terminal 逼近 ⇒ event 跨越界（`_C11D`）**：`f(t') = d_{t'}(p, q)`（pre stage）。若
(D3) 对每个 `t' ∈ [t, τ)` 给 `f t ≤ f t' + Λ(t' − t)`，且 terminal 逼近对每个 `δ > 0` 给某
`t' ∈ [t, τ)` 使 `f t' ≤ X + δ`（G3：`X = d_term ≤ d_out`，(D4)），则 `f t ≤ X + Λ(τ − t)`。 -/
theorem le_add_of_smooth_of_terminal_approx_C11D {f : ℝ → ℝ≥0∞} {X : ℝ≥0∞} {t τ Λ : ℝ}
    (hΛ : 0 ≤ Λ)
    (hsm : ∀ t' ∈ Ico t τ, f t ≤ f t' + ENNReal.ofReal (Λ * (t' - t)))
    (hterm : ∀ δ : ℝ, 0 < δ → ∃ t' ∈ Ico t τ, f t' ≤ X + ENNReal.ofReal δ) :
    f t ≤ X + ENNReal.ofReal (Λ * (τ - t)) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨t', ht', hf⟩ := hterm ε (by exact_mod_cast hε)
  have hmono : ENNReal.ofReal (Λ * (t' - t)) ≤ ENNReal.ofReal (Λ * (τ - t)) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by linarith [ht'.2]) hΛ)
  calc f t ≤ f t' + ENNReal.ofReal (Λ * (t' - t)) := hsm t' ht'
    _ ≤ (X + ENNReal.ofReal ε) + ENNReal.ofReal (Λ * (τ - t)) := add_le_add hf hmono
    _ = X + ENNReal.ofReal (Λ * (τ - t)) + ε := by
      rw [ENNReal.ofReal_coe_nnreal]
      ring

/-! ## 3. trace 特化 -/

/-- **trace 形的距离链（`_C11D`）**：seed trace（`aSeed → T`）与 `x` 的 backward trace（`v → s`）在窗口
`[v, s]` 的每个 stage 上的点；`hsmooth`（末 stage (D3)）+ `hevent`（每个 event 的 (D3)+(D4) 跨越）⇒
`d_v(seed(v), x_v) ≤ d_s(seed(s), x) + Λ(s − v)`。 -/
theorem edist_trace_le_of_stage_bounds_C11D
    {T aSeed s v : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ T) (hsT : s ≤ T) (hav : aSeed ≤ v)
    (hvs : v ≤ s) {p : (H.stageAt T).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    {x : (H.stageAt s).Carrier}
    (tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hsmooth : ∀ t : ℝ, (v : ℝ) ≤ t → H.time (H.activeStage s) ≤ t → t ≤ s →
      riemannianEDistOf (H.stageMetric (H.activeStage s) t)
          (seedTrace.point (H.activeStage s) (H.activeStage_mono (hav.trans hvs))
            (H.activeStage_mono hsT)) x ≤
        riemannianEDistOf (H.stageMetric (H.activeStage s) s)
            (seedTrace.point (H.activeStage s) (H.activeStage_mono (hav.trans hvs))
              (H.activeStage_mono hsT)) x +
          ENNReal.ofReal (Λ * ((s : ℝ) - t)))
    (hevent : ∀ (e : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ e.castSucc)
      (h2 : e.succ ≤ H.activeStage T) (h3 : H.activeStage v ≤ e.castSucc)
      (h4 : e.succ ≤ H.activeStage s) (t : ℝ),
      (v : ℝ) ≤ t → H.time e.castSucc ≤ t → t < H.time e.succ →
      riemannianEDistOf (H.stageMetric e.castSucc t)
          (seedTrace.point e.castSucc h1 (e.castSucc_lt_succ.le.trans h2))
          (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) ≤
        riemannianEDistOf (H.stageMetric e.succ (H.time e.succ))
            (seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2)
            (tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4) +
          ENNReal.ofReal (Λ * (H.time e.succ - t))) :
    riemannianEDistOf (H.stageMetric (H.activeStage v) v)
        (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
          (H.activeStage_mono (hvs.trans hsT)))
        (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs)) ≤
      riemannianEDistOf (H.stageMetric (H.activeStage s) s)
          (seedTrace.point (H.activeStage s) (H.activeStage_mono (hav.trans hvs))
            (H.activeStage_mono hsT)) x +
        ENNReal.ofReal (Λ * ((s : ℝ) - v)) := by
  have hvi : ∀ e : Fin H.eventCount, H.activeStage v = e.castSucc →
      (v : ℝ) < H.time e.succ := by
    intro e he
    have hlt : (H.activeStage v : ℕ) < H.eventCount := by
      rw [he]
      exact e.isLt
    have h := H.activeStage_before_next v hlt
    have heq : (⟨(H.activeStage v : ℕ) + 1, by omega⟩ : Fin (H.eventCount + 1)) = e.succ := by
      apply Fin.ext
      simp only [he, Fin.val_castSucc, Fin.val_succ]
    rwa [heq] at h
  have hchain := H.edist_le_of_stage_bounds_C11D (H.activeStage_mono hvs)
    (fun k hk1 hk2 => seedTrace.point k ((H.activeStage_mono hav).trans hk1)
      (hk2.trans (H.activeStage_mono hsT)))
    (fun k hk1 hk2 => tr.point k hk1 hk2) hΛ (H.activeStage_time_le v) hvi
    (show (v : ℝ) ≤ s from hvs) (H.activeStage_time_le s)
    (fun t h1 h2 h3 => by
      rw [tr.endpoint_eq]
      exact hsmooth t h1 h2 h3)
    (fun e he1 he2 t h1 h2 h3 => hevent e _ _ he1 he2 t h1 h2 h3)
  rwa [tr.endpoint_eq] at hchain

/-! ## 4. 主目标：相对形 `hdist`（P6CON L9 的前提形） -/

/-- **相对形 `hdist`（`_C11D`，主目标）**：`U = B_s(y, Rad/√Q)`、窗口 `[s − θ/Q, s]`、速率 `Λ`
（`Λ = c√Q`：`ℓ ≍ Q^{-1/2}`）。前提 = 每个 `x ∈ U` 的末 stage (D3) `hsmooth` 与每条窗口 trace 的
event 跨越 `hevent`（(D3)+(D4)）+ 数值 `Rad/√Q + Λ θ/Q ≤ L/√Q`。结论**逐字**是
`hasSpatialCanonicalTimeControl_on_window_traces_P6N` 的 `hdist`：
`d_v(seed(v), x_v) ≤ d_s(O, y) + L/√Q`（`O = seed(s)`）。不需中心界。 -/
theorem hdist_rel_of_stage_bounds_C11D
    {T aSeed s : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ T) (hsT : s ≤ T) (has : aSeed ≤ s)
    {p : (H.stageAt T).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (y : (H.stageAt s).Carrier) {Q L θ Rad Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hnum : Rad / Real.sqrt Q + Λ * (θ / Q) ≤ L / Real.sqrt Q)
    (hsmooth : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ t : ℝ, (s : ℝ) - θ / Q ≤ t → H.time (H.activeStage s) ≤ t → t ≤ s →
      riemannianEDistOf (H.stageMetric (H.activeStage s) t)
          (seedTrace.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hsT))
          x ≤
        riemannianEDistOf (H.stageMetric (H.activeStage s) s)
            (seedTrace.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hsT))
            x +
          ENNReal.ofReal (Λ * ((s : ℝ) - t)))
    (hevent : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : aSeed ≤ v) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
      ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x,
      ∀ (e : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ e.castSucc)
        (h2 : e.succ ≤ H.activeStage T) (h3 : H.activeStage v ≤ e.castSucc)
        (h4 : e.succ ≤ H.activeStage s) (t : ℝ),
        (v : ℝ) ≤ t → H.time e.castSucc ≤ t → t < H.time e.succ →
      riemannianEDistOf (H.stageMetric e.castSucc t)
          (seedTrace.point e.castSucc h1 (e.castSucc_lt_succ.le.trans h2))
          (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) ≤
        riemannianEDistOf (H.stageMetric e.succ (H.time e.succ))
            (seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2)
            (tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4) +
          ENNReal.ofReal (Λ * (H.time e.succ - t))) :
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
      ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hsT)))
            (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs)) ≤
          riemannianEDistOf (H.stageMetric (H.activeStage s) s)
              (seedTrace.point (H.activeStage s) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt Q) := by
  intro x hx v hav hvs hθv tr
  have hchain := H.edist_trace_le_of_stage_bounds_C11D haT hsT hav hvs seedTrace tr hΛ
    (fun t h1 h2 h3 => hsmooth x hx t (hθv.trans h1) h2 h3)
    (fun e h1 h2 h3 h4 t ht1 ht2 ht3 => hevent x hx v hav hvs hθv tr e h1 h2 h3 h4 t ht1 ht2 ht3)
  have hyx : riemannianEDistOf (H.stageMetric (H.activeStage s) s) y x <
      ENNReal.ofReal (Rad / Real.sqrt Q) := hx
  have hRad : 0 ≤ Rad / Real.sqrt Q :=
    le_of_lt (ENNReal.ofReal_pos.1 (lt_of_le_of_lt zero_le hyx))
  have hsv : (s : ℝ) - v ≤ θ / Q := by linarith
  have hsv0 : 0 ≤ (s : ℝ) - v := sub_nonneg.2 (show (v : ℝ) ≤ s from hvs)
  calc _ ≤ _ := hchain
    _ ≤ (riemannianEDistOf (H.stageMetric (H.activeStage s) s)
            (seedTrace.point (H.activeStage s) (H.activeStage_mono has)
              (H.activeStage_mono hsT)) y +
          ENNReal.ofReal (Rad / Real.sqrt Q)) + ENNReal.ofReal (Λ * ((s : ℝ) - v)) :=
        add_le_add ((riemannianEDistOf_triangle _ _ y x).trans
          (add_le_add le_rfl hyx.le)) le_rfl
    _ = riemannianEDistOf (H.stageMetric (H.activeStage s) s)
            (seedTrace.point (H.activeStage s) (H.activeStage_mono has)
              (H.activeStage_mono hsT)) y +
          ENNReal.ofReal (Rad / Real.sqrt Q + Λ * ((s : ℝ) - v)) := by
        rw [add_assoc, ENNReal.ofReal_add hRad (mul_nonneg hΛ hsv0)]
    _ ≤ _ := add_le_add le_rfl (ENNReal.ofReal_le_ofReal (le_trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsv hΛ)) hnum))

end ObservedHistory

/-! ## 5. 绝对形 (D1)（序列层，P6B2 `hD1` 形） -/

/-- **绝对形 (D1)（`_C11D`）**：历史序列 `Hs n`、seed trace（`aSeed n → t n`）、坏点 `(s n, y n)`、
尺度 `R n > 0`。前提：中心界 `hcenter`（`y_n ∈ B_{s_n}(O_n, A₀ r_n)`；selection 给 `A₀ = A + 1`）；
速率 `hrate`：对每个 `D, T > 0` 有 `c = c_{D,T} ≥ 0`，eventually 对 `U_n = B(y_n, D/√R_n)` 与窗口
`[s_n − T/R_n, s_n]` 成立末 stage (D3) 与 event 跨越（速率 `Λ_n = c √R_n`）。结论 = P6B2
`hdist_fixed_of_D1_P6B2` 的 `hD1`：`d_v(O_v, x_v) < A₀ r_n + C/√R_n`，`C = D + c T`。 -/
theorem hD1_of_stage_bounds_C11D (Hs : ℕ → ObservedHistory.{u}) {A₀ : ℝ}
    (t : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (p : ∀ n, ((Hs n).stageAt (t n)).Carrier) (r : ℕ → ℝ)
    (aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (haT : ∀ n, aSeed n ≤ t n)
    (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
      ((Hs n).activeStage (t n)) ((Hs n).activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (hst : ∀ n, s n ≤ t n) (has : ∀ n, aSeed n ≤ s n)
    (y : ∀ n, ((Hs n).stageAt (s n)).Carrier) (R : ℕ → ℝ) (hR : ∀ᶠ n in atTop, 0 < R n)
    (hcenter : ∀ᶠ n in atTop, y n ∈ riemannianBallOf
      ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n))
      ((seedTrace n).point ((Hs n).activeStage (s n)) ((Hs n).activeStage_mono (has n))
        ((Hs n).activeStage_mono (hst n))) (A₀ * r n))
    (hrate : ∀ D T : ℝ, 0 < D → 0 < T → ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ τ : ℝ, (s n : ℝ) - T / R n ≤ τ → (Hs n).time ((Hs n).activeStage (s n)) ≤ τ →
          τ ≤ s n →
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ)
            ((seedTrace n).point ((Hs n).activeStage (s n)) ((Hs n).activeStage_mono (has n))
              ((Hs n).activeStage_mono (hst n))) x ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n))
              ((seedTrace n).point ((Hs n).activeStage (s n))
                ((Hs n).activeStage_mono (has n)) ((Hs n).activeStage_mono (hst n))) x +
            ENNReal.ofReal (c * Real.sqrt (R n) * ((s n : ℝ) - τ))) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h1 : (Hs n).activeStage (aSeed n) ≤ e.castSucc)
          (h2 : e.succ ≤ (Hs n).activeStage (t n)) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)) (τ : ℝ),
          (v : ℝ) ≤ τ → (Hs n).time e.castSucc ≤ τ → τ < (Hs n).time e.succ →
        riemannianEDistOf ((Hs n).stageMetric e.castSucc τ)
            ((seedTrace n).point e.castSucc h1 (e.castSucc_lt_succ.le.trans h2))
            (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) ≤
          riemannianEDistOf ((Hs n).stageMetric e.succ ((Hs n).time e.succ))
              ((seedTrace n).point e.succ (h1.trans e.castSucc_lt_succ.le) h2)
              (tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4) +
            ENNReal.ofReal (c * Real.sqrt (R n) * ((Hs n).time e.succ - τ)))) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvs : v ≤ s n), (s n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
        ((Hs n).activeStage_mono hvs) x,
      ∀ hav : aSeed n ≤ v,
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
            ((seedTrace n).point ((Hs n).activeStage v) ((Hs n).activeStage_mono hav)
              ((Hs n).activeStage_mono (hvs.trans (hst n))))
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvs)) <
          ENNReal.ofReal (A₀ * r n + C / Real.sqrt (R n)) := by
  intro D T hD hT
  obtain ⟨c, hc, hev⟩ := hrate D T hD hT
  refine ⟨D + c * T, ?_⟩
  filter_upwards [hev, hR, hcenter] with n hn hRn hcn
  obtain ⟨hsm, hevt⟩ := hn
  intro x hx v hvs hθv tr hav
  have hsqrt : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hRn
  have hΛ : 0 ≤ c * Real.sqrt (R n) := mul_nonneg hc hsqrt.le
  have hchain := (Hs n).edist_trace_le_of_stage_bounds_C11D (haT n) (hst n) hav hvs
    (seedTrace n) tr hΛ (fun τ h1 h2 h3 => hsm x hx τ (hθv.trans h1) h2 h3)
    (fun e h1 h2 h3 h4 τ hτ1 hτ2 hτ3 => hevt x hx v hav hvs hθv tr e h1 h2 h3 h4 τ hτ1 hτ2 hτ3)
  have hyx : riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n) x <
      ENNReal.ofReal (D / Real.sqrt (R n)) := hx
  have hOy := hcn
  change riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) _ (y n) <
      ENNReal.ofReal (A₀ * r n) at hOy
  have hA : 0 ≤ A₀ * r n := le_of_lt (ENNReal.ofReal_pos.1 (lt_of_le_of_lt zero_le hOy))
  have hDn : 0 ≤ D / Real.sqrt (R n) := div_nonneg hD.le hsqrt.le
  have hsv0 : 0 ≤ (s n : ℝ) - v := sub_nonneg.2 (show (v : ℝ) ≤ s n from hvs)
  have hsv : (s n : ℝ) - v ≤ T / R n := by linarith
  have hrateT : c * Real.sqrt (R n) * ((s n : ℝ) - v) ≤ c * T / Real.sqrt (R n) := by
    have h1 : c * Real.sqrt (R n) * ((s n : ℝ) - v) ≤ c * Real.sqrt (R n) * (T / R n) :=
      mul_le_mul_of_nonneg_left hsv hΛ
    have h2 : c * Real.sqrt (R n) * (T / R n) = c * T / Real.sqrt (R n) := by
      have h := Real.sqrt_div_self' (x := R n)
      calc c * Real.sqrt (R n) * (T / R n) = c * T * (Real.sqrt (R n) / R n) := by ring
        _ = c * T * (1 / Real.sqrt (R n)) := by rw [h]
        _ = c * T / Real.sqrt (R n) := by ring
    linarith
  calc _ ≤ _ := hchain
    _ ≤ (riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n))
            ((seedTrace n).point ((Hs n).activeStage (s n))
              ((Hs n).activeStage_mono (has n)) ((Hs n).activeStage_mono (hst n))) (y n) +
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n) x) +
          ENNReal.ofReal (c * Real.sqrt (R n) * ((s n : ℝ) - v)) :=
        add_le_add (riemannianEDistOf_triangle _ _ (y n) x) le_rfl
    _ < (ENNReal.ofReal (A₀ * r n) + ENNReal.ofReal (D / Real.sqrt (R n))) +
          ENNReal.ofReal (c * Real.sqrt (R n) * ((s n : ℝ) - v)) :=
        ENNReal.add_lt_add_right ENNReal.ofReal_ne_top (ENNReal.add_lt_add hOy hyx)
    _ = ENNReal.ofReal (A₀ * r n + D / Real.sqrt (R n) +
          c * Real.sqrt (R n) * ((s n : ℝ) - v)) := by
        rw [ENNReal.ofReal_add (add_nonneg hA hDn) (mul_nonneg hΛ hsv0),
          ENNReal.ofReal_add hA hDn]
    _ ≤ ENNReal.ofReal (A₀ * r n + (D + c * T) / Real.sqrt (R n)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [add_div]
        linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

/-! ## 6. 固定 `A_*`（F 层，P6B bridge 出口） -/

namespace GC.LongTime.Ch11

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **固定 `A_*` 的 `hdist`（`_C11D`，P6B bridge 出口）**：`hD1_of_stage_bounds_C11D` + P6B2
`hdist_fixed_of_D1_P6B2`（`Q r² → ∞`）⇒ `A_* = A₀ + 1`、与 `D, T` 无关的 `hdist`，逐字是
`tracedKappa_of_window_margin_P6B2` 的 `hdist`（`Astar := A₀ + 1`）。 -/
theorem hdist_fixed_of_stage_bounds_C11D {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {A₀ : ℝ} (ind : ℕ → ℕ)
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ)
    (hr : ∀ n, 0 < r n)
    (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ t n)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
      ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (ind n)).toHistory.activeStage (t n))
      ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (hst : ∀ n, s n ≤ t n) (has : ∀ n, aSeed n ≤ s n)
    (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
    (hR : ∀ᶠ n in atTop, 0 < R n)
    (hX : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hcenter : ∀ᶠ n in atTop, y n ∈ riemannianBallOf
      ((F.tower.history (ind n)).toHistory.stageMetric
        ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n))
      ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono (has n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono (hst n))) (A₀ * r n))
    (hrate : ∀ D T : ℝ, 0 < D → 0 < T → ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ τ : ℝ, (s n : ℝ) - T / R n ≤ τ →
          (F.tower.history (ind n)).toHistory.time
            ((F.tower.history (ind n)).toHistory.activeStage (s n)) ≤ τ → τ ≤ s n →
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage (s n)) τ)
            ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage (s n))
              ((F.tower.history (ind n)).toHistory.activeStage_mono (has n))
              ((F.tower.history (ind n)).toHistory.activeStage_mono (hst n))) x ≤
          riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
              ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n))
              ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage (s n))
                ((F.tower.history (ind n)).toHistory.activeStage_mono (has n))
                ((F.tower.history (ind n)).toHistory.activeStage_mono (hst n))) x +
            ENNReal.ofReal (c * Real.sqrt (R n) * ((s n : ℝ) - τ))) ∧
      (∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
          (_hav : aSeed n ≤ v) (hvs : v ≤ s n), (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
          ((F.tower.history (ind n)).toHistory.activeStage v)
          ((F.tower.history (ind n)).toHistory.activeStage (s n))
          ((F.tower.history (ind n)).toHistory.activeStage_mono hvs) x,
        ∀ (e : Fin (F.tower.history (ind n)).toHistory.eventCount)
          (h1 : (F.tower.history (ind n)).toHistory.activeStage (aSeed n) ≤ e.castSucc)
          (h2 : e.succ ≤ (F.tower.history (ind n)).toHistory.activeStage (t n))
          (h3 : (F.tower.history (ind n)).toHistory.activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (F.tower.history (ind n)).toHistory.activeStage (s n)) (τ : ℝ),
          (v : ℝ) ≤ τ → (F.tower.history (ind n)).toHistory.time e.castSucc ≤ τ →
          τ < (F.tower.history (ind n)).toHistory.time e.succ →
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric e.castSucc τ)
            ((seedTrace n).point e.castSucc h1 (e.castSucc_lt_succ.le.trans h2))
            (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) ≤
          riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric e.succ
                ((F.tower.history (ind n)).toHistory.time e.succ))
              ((seedTrace n).point e.succ (h1.trans e.castSucc_lt_succ.le) h2)
              (tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4) +
            ENNReal.ofReal (c * Real.sqrt (R n) *
              ((F.tower.history (ind n)).toHistory.time e.succ - τ)))) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hvs : v ≤ s n),
        (s n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage v)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hvs) x,
      ∀ hav : aSeed n ≤ v,
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage v) v)
          ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage v)
            ((F.tower.history (ind n)).toHistory.activeStage_mono hav)
            ((F.tower.history (ind n)).toHistory.activeStage_mono (hvs.trans (hst n))))
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage v) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hvs)) <
          ENNReal.ofReal ((A₀ + 1) * r n) :=
  hdist_fixed_of_D1_P6B2 ind t p r hr aSeed haT seedTrace s hst y R hR hX
    (hD1_of_stage_bounds_C11D (fun n => (F.tower.history (ind n)).toHistory) t p r aSeed haT
      seedTrace s hst has y R hR hcenter hrate)

end GC.LongTime.Ch11

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

variable (H : ObservedHistory.{u})

/-- **consumer（G1）**：相对形 `hdist_rel_of_stage_bounds_C11D` 的输出直接喂 P6CON L9
`hasSpatialCanonicalTimeControl_on_window_traces_P6N`：selection 末项 `hgood` + 窗口 (D3)/(D4) 链 ⇒
窗口 trace 点（`R ≥ 4Q`）全 Good（`hdist` 前提由本文件生产，不再是黑箱）。 -/
example {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    {T aSeed s : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ T) (hsT : s ≤ T) (has : aSeed ≤ s)
    {p : (H.stageAt T).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (y : (H.stageAt s).Carrier) {Q L θ Rad Λ : ℝ} (hQ : 0 < Q) (hΛ : 0 ≤ Λ)
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ s),
      (s : ℝ) - L ^ 2 / Q ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage s) s)
              (seedTrace.point (H.activeStage s) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt Q) →
        4 * Q ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hθ : θ ≤ L ^ 2) (hwin : (aSeed : ℝ) ≤ s - θ / Q)
    (hnum : Rad / Real.sqrt Q + Λ * (θ / Q) ≤ L / Real.sqrt Q)
    (hsmooth : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ t : ℝ, (s : ℝ) - θ / Q ≤ t → H.time (H.activeStage s) ≤ t → t ≤ s →
      riemannianEDistOf (H.stageMetric (H.activeStage s) t)
          (seedTrace.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hsT))
          x ≤
        riemannianEDistOf (H.stageMetric (H.activeStage s) s)
            (seedTrace.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hsT))
            x +
          ENNReal.ofReal (Λ * ((s : ℝ) - t)))
    (hevent : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : aSeed ≤ v) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
      ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x,
      ∀ (e : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ e.castSucc)
        (h2 : e.succ ≤ H.activeStage T) (h3 : H.activeStage v ≤ e.castSucc)
        (h4 : e.succ ≤ H.activeStage s) (t : ℝ),
        (v : ℝ) ≤ t → H.time e.castSucc ≤ t → t < H.time e.succ →
      riemannianEDistOf (H.stageMetric e.castSucc t)
          (seedTrace.point e.castSucc h1 (e.castSucc_lt_succ.le.trans h2))
          (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) ≤
        riemannianEDistOf (H.stageMetric e.succ (H.time e.succ))
            (seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2)
            (tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4) +
          ENNReal.ofReal (Λ * (H.time e.succ - t))) :
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ (v : Icc (0 : ℝ) H.horizon) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
      ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x,
        4 * Q ≤ metricScalarAt (H.stageMetric (H.activeStage v) v)
          (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs)) →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v
          (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvs)) :=
  H.hasSpatialCanonicalTimeControl_on_window_traces_P6N haT hsT has seedTrace y hQ hgood hθ hwin
    (H.hdist_rel_of_stage_bounds_C11D haT hsT has seedTrace y hΛ hnum hsmooth hevent)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
