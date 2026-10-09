import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.SmoothDistortionC11D
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCapNoShortcut
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventDistanceScalar

/-!
# P6 距离线 G3：(D4) surgery 无捷径 + terminal 极限 ⇒ event 跨越界（O-CH11-DIST，后缀 `_C11D`）

R-C11-2 D-8 的 (D4)：`d_{τ⁻}(pm, qm) ≤ d_{τ⁺}(pp, qp)`，端点在保护区、左右识别属同一实际 surgery。
**树内已有核心**：`MetricCutCapEvent.oldTerminal_edist_le_of_outside_canonical_cap_windows`
（`ST/EventCapNoShortcut.lean:846`）：
`d_term(oldTerminal u, oldTerminal z) ≤ d_out(oldOutput u, oldOutput z)`，
前提 = D-8 证明核的四项：presented static caps `S b` 带 canonical window（collar 长度 / 横截面 = 标准帽
window 半径 `D > transitionEnd + 10`、精度 `ε ≤ 1/2`）、`E.old = retainedCore`（真实度量识别 = `old_metric_eq`
+ 同一 event 的 `oldTerminal / oldOutput`）、端点在 window 内区 `‖x‖ ≤ transitionEnd + 10` 之外（分离性 /
保护条件）。证明核即 D-8 所述：minimizing 曲线避开 inner window（`minimizing_curve_avoids_inner_window`），
整条落在 `range oldOutput` 内部，等距拉回到 terminal。`e_τ = 0`，不需 `Σ e_τ = o(r_n)`。

本文件：
* `terminal_edist_approx_C11D`（terminal 极限，`τ⁻`）：`t ↑ τ` 时 `d_{g(t)}(x, y) ≤ d_term(x, y) + δ`
  eventually（树内 `TerminalLimitMetric.eventually_riemannianEDistOf_lt` 的 `≤ + δ` 形）。
* **`surgery_no_shortcut_C11D`（(D4) 合同，history 层）**：event `e` 的 regular crossing
  `pm ↦ pp`、`qm ↦ qp`（同一实际 surgery 的左右识别）+ 保护 ⇒
  `∀ δ > 0, ∀ᶠ t ↑ τ, d_{e⁻,t}(pm, qm) ≤ d_{e⁺,τ}(pp, qp) + δ`。
* **`event_crossing_bound_C11D`**：(D3)（G2，`(t, τ)` 上端点 `ℓ`-球 Ricci 界）+ (D4) ⇒ G1 `hevent` 的单 event 形
  `d_{e⁻,t} ≤ d_{e⁺,τ} + (8/ℓ)(τ − t)`（经 G1 `le_add_of_smooth_of_terminal_approx_C11D`）。
* **`hevent_of_records_C11D`**：G1 `hdist_rel_of_stage_bounds_C11D` 的 `hevent` 前提，由 late records
  （`∀ e, T₀ ≤ time e⁺ → GeometricCutoffRecord`，P6N 约定）+ canonical windows + 端点保护 + 端点 Ricci 界给出。
* astra `DistanceData` 核对：`terminal_edist_le_mul_of_hasUniformDistanceScalar_C11D`——
  `HasUniformDistanceScalar C`（`PreparedSpatialState.DistanceData.full`）只给**乘法**形
  `d_term ≤ C · d_out`（对全部 old 点，无保护），**不是** (D4)（`C = 1`、保护端点）；沿窗口内多次 surgery
  会累乘 `C^k`，不能替代 (D4)。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

/-! ## terminal 极限 -/

/-- **terminal 极限（`_C11D`）**：incoming slab `G`、terminal limit metric `L`，
`x, y ∈ terminalRegularOpen`：
`∀ δ > 0`，eventually（`t ↑ s`）`d_{G(t)}(x, y) ≤ d_L(x, y) + δ`（`d_L = ⊤` 平凡）。 -/
theorem terminal_edist_approx_C11D {P : OrientedThreeStage.{u}} {a s : ℝ}
    {G : P.IncomingSlab a s} (L : G.TerminalLimitMetric) (x y : G.terminalRegularOpen)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t in 𝓝[<] s, riemannianEDistOf (G.flow.base.metric t) (x : P.Carrier) (y : P.Carrier) ≤
      riemannianEDistOf L.metric x y + ENNReal.ofReal δ := by
  by_cases htop : riemannianEDistOf L.metric x y = ⊤
  · refine Filter.Eventually.of_forall fun t => ?_
    rw [htop, top_add]
    exact le_top
  · have heq : ENNReal.ofReal ((riemannianEDistOf L.metric x y).toReal + δ) =
        riemannianEDistOf L.metric x y + ENNReal.ofReal δ := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hδ.le, ENNReal.ofReal_toReal htop]
    have hlt : riemannianEDistOf L.metric x y <
        ENNReal.ofReal ((riemannianEDistOf L.metric x y).toReal + δ) := by
      rw [heq]
      exact ENNReal.lt_add_right htop (ENNReal.ofReal_pos.2 hδ).ne'
    filter_upwards [L.eventually_riemannianEDistOf_lt x y hlt] with t ht
    rw [heq] at ht
    exact ht.le

/-! ## (D4) 合同 -/

/-- **(D4) surgery 无捷径（`_C11D`，history 层）**：event `e`（`τ = time e⁺`）、presented static caps `S b`
（canonical window，`ε ≤ 1/2`，`D > transitionEnd + 10`）、`old = retainedCore`；`pm ↦ pp`、`qm ↦ qp` 是
同一 event 的 regular crossing（= backward trace 的左右识别），`pp, qp` 在每个 cap window 的内区
`‖x‖ ≤ transitionEnd + 10` 之外（保护条件）⇒ `∀ δ > 0`，eventually（`t ↑ τ`）
`d_{e⁻,t}(pm, qm) ≤ d_{e⁺,τ}(pp, qp) + δ`。 -/
theorem surgery_no_shortcut_C11D (H : ObservedHistory.{u}) (e : Fin H.eventCount)
    {fixed : StaticCapScaffold} {Dc εc : ℝ} {mc : ℕ}
    (S : ∀ b : (H.event e).RetainedBoundaryIndex,
      (H.event e).PresentedStaticCap fixed Dc mc εc b)
    (hOld : (H.event e).old = (H.event e).transition.trace.retainedCore)
    (hcanonical : ∀ b, (S b).hasCanonicalWindow) (hε : εc ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < Dc)
    {pm qm : (H.stage e.castSucc).Carrier} {pp qp : (H.stage e.succ).Carrier}
    (hp : (H.event e).RegularCrossing pm pp) (hq : (H.event e).RegularCrossing qm qp)
    (hpprot : ∀ b, pp ∉ (S b).window ''
      {x : standardCapWindow Dc | ‖x.val‖ ≤ StandardCap.transitionEnd + 10})
    (hqprot : ∀ b, qp ∉ (S b).window ''
      {x : standardCapWindow Dc | ‖x.val‖ ≤ StandardCap.transitionEnd + 10})
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t in 𝓝[<] H.time e.succ,
      riemannianEDistOf (H.stageMetric e.castSucc t) pm qm ≤
        riemannianEDistOf (H.stageMetric e.succ (H.time e.succ)) pp qp + ENNReal.ofReal δ := by
  obtain ⟨u, -, hu1, hu2⟩ := hp
  obtain ⟨w, -, hw1, hw2⟩ := hq
  subst hu1 hw1 hu2 hw2
  have hD4 := (H.event e).oldTerminal_edist_le_of_outside_canonical_cap_windows S hOld
    hcanonical hε hD u w hpprot hqprot
  have hout : H.stageMetric e.succ (H.time e.succ) = (H.event e).outputMetric := by
    rw [H.stageMetric_initial, H.event_output]
  rw [hout]
  filter_upwards [terminal_edist_approx_C11D (H.event e).terminal ((H.event e).oldTerminal u)
    ((H.event e).oldTerminal w) hδ] with t ht
  rw [stageMetric_castSucc_apply]
  rw [(H.event e).oldTerminal_eq u, (H.event e).oldTerminal_eq w] at ht
  exact ht.trans (add_le_add hD4 le_rfl)

/-! ## (D3) + (D4) ⇒ event 跨越界 -/

/-- **event 跨越界（`_C11D`）**：`time e⁻ ≤ t < τ = time e⁺`；(D3) 前提（`(t, τ)` 上 `pm, qm` 的 `ℓ`-球
`Ric ≤ (3/ℓ²) g`）+ (D4)（`surgery_no_shortcut_C11D` 的前提）⇒
`d_{e⁻,t}(pm, qm) ≤ d_{e⁺,τ}(pp, qp) + (8/ℓ)(τ − t)`（= G1 `hevent` 的单 event 形）。 -/
theorem event_crossing_bound_C11D (H : ObservedHistory.{u}) (e : Fin H.eventCount)
    {fixed : StaticCapScaffold} {Dc εc : ℝ} {mc : ℕ}
    (S : ∀ b : (H.event e).RetainedBoundaryIndex,
      (H.event e).PresentedStaticCap fixed Dc mc εc b)
    (hOld : (H.event e).old = (H.event e).transition.trace.retainedCore)
    (hcanonical : ∀ b, (S b).hasCanonicalWindow) (hε : εc ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < Dc)
    {pm qm : (H.stage e.castSucc).Carrier} {pp qp : (H.stage e.succ).Carrier}
    (hp : (H.event e).RegularCrossing pm pp) (hq : (H.event e).RegularCrossing qm qp)
    (hpprot : ∀ b, pp ∉ (S b).window ''
      {x : standardCapWindow Dc | ‖x.val‖ ≤ StandardCap.transitionEnd + 10})
    (hqprot : ∀ b, qp ∉ (S b).window ''
      {x : standardCapWindow Dc | ‖x.val‖ ≤ StandardCap.transitionEnd + 10})
    {t ℓ : ℝ} (hℓ : 0 < ℓ) (ht1 : H.time e.castSucc ≤ t) (ht2 : t < H.time e.succ)
    (hRic : ∀ t' ∈ Ioo t (H.time e.succ), ∀ z : (H.stage e.castSucc).Carrier,
      ∀ ξ : TangentSpace ThreeModel z,
      (riemannianEDistOf (H.stageMetric e.castSucc t') pm z < ENNReal.ofReal ℓ ∨
        riemannianEDistOf (H.stageMetric e.castSucc t') qm z < ENNReal.ofReal ℓ) →
      ricciTensor (H.stageMetric e.castSucc t') z ξ ξ ≤
        (3 / ℓ ^ 2) * (H.stageMetric e.castSucc t').inner z ξ ξ) :
    riemannianEDistOf (H.stageMetric e.castSucc t) pm qm ≤
      riemannianEDistOf (H.stageMetric e.succ (H.time e.succ)) pp qp +
        ENNReal.ofReal ((8 / ℓ) * (H.time e.succ - t)) := by
  refine le_add_of_smooth_of_terminal_approx_C11D
    (f := fun t' => riemannianEDistOf (H.stageMetric e.castSucc t') pm qm)
    (div_nonneg (by norm_num) hℓ.le) ?_ ?_
  · intro t' ht'
    refine H.smooth_distance_distortion_C11D e.castSucc hℓ ht'.1 ht1 ?_
      (ht'.2.le.trans (H.time_le_horizon_at e.succ)) pm qm
      (fun τ hτ => hRic τ ⟨hτ.1, hτ.2.trans ht'.2⟩)
    intro e' he'
    obtain rfl : e = e' := Fin.castSucc_injective _ he'
    exact ht'.2
  · intro δ hδ
    obtain ⟨t', hf, ht'⟩ := ((H.surgery_no_shortcut_C11D e S hOld hcanonical hε hD hp hq
      hpprot hqprot hδ).and (Ioo_mem_nhdsLT ht2)).exists
    exact ⟨t', ⟨ht'.1.le, ht'.2⟩, hf⟩

/-! ## G1 `hevent` 的生产（trace 层） -/

/-- **G1 `hevent` 的生产（`_C11D`）**：late records
`records e : T₀ ≤ time e⁺ → GeometricCutoffRecord H e q`
（P6N 约定）+ canonical windows `hcan` + `old = retainedCore` + `q.modelAccuracy ≤ 1/2`、
`transitionEnd + 10 < q.modelRadius`；端点保护 `hprot`（seed trace 与 `x` 的 trace 在 `e⁺` 的点在 cap window
内区外）；端点 Ricci 界 `hRic`（`e⁻` 上 `(max(v, time e⁻), τ)` 内）；`T₀ ≤ s − θ/Q` ⇒
`hdist_rel_of_stage_bounds_C11D` 的 `hevent`（速率 `Λ = 8/ℓ`）。 -/
theorem hevent_of_records_C11D (H : ObservedHistory.{u})
    {T aSeed s : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ T)
    {p : (H.stageAt T).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (y : (H.stageAt s).Carrier) {Q θ Rad ℓ T₀ : ℝ} (hℓ : 0 < ℓ) (hT₀ : T₀ ≤ (s : ℝ) - θ / Q)
    {q : CutoffParameters}
    (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e q)
    (hOld : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ →
      (H.event e).old = (H.event e).transition.trace.retainedCore)
    (hcan : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (hacc : q.modelAccuracy ≤ 1 / 2) (hDm : StandardCap.transitionEnd + 10 < q.modelRadius)
    (hprot : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : aSeed ≤ v) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
      ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x,
      ∀ (e : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ e.castSucc)
        (h2 : e.succ ≤ H.activeStage T) (h3 : H.activeStage v ≤ e.castSucc)
        (h4 : e.succ ≤ H.activeStage s), (v : ℝ) < H.time e.succ →
      ∀ (he : T₀ ≤ H.time e.succ) b,
        seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
            ((records e he).static b).window ''
              {z : standardCapWindow q.modelRadius | ‖z.val‖ ≤ StandardCap.transitionEnd + 10} ∧
          tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
            ((records e he).static b).window ''
              {z : standardCapWindow q.modelRadius | ‖z.val‖ ≤ StandardCap.transitionEnd + 10})
    (hRic : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : aSeed ≤ v) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
      ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x,
      ∀ (e : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ e.castSucc)
        (h2 : e.succ ≤ H.activeStage T) (h3 : H.activeStage v ≤ e.castSucc)
        (h4 : e.succ ≤ H.activeStage s) (t' : ℝ),
        (v : ℝ) < t' → H.time e.castSucc < t' → t' < H.time e.succ →
      ∀ z : (H.stage e.castSucc).Carrier, ∀ ξ : TangentSpace ThreeModel z,
        (riemannianEDistOf (H.stageMetric e.castSucc t')
            (seedTrace.point e.castSucc h1 (e.castSucc_lt_succ.le.trans h2)) z <
            ENNReal.ofReal ℓ ∨
          riemannianEDistOf (H.stageMetric e.castSucc t')
            (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z < ENNReal.ofReal ℓ) →
        ricciTensor (H.stageMetric e.castSucc t') z ξ ξ ≤
          (3 / ℓ ^ 2) * (H.stageMetric e.castSucc t').inner z ξ ξ) :
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
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
          ENNReal.ofReal (8 / ℓ * (H.time e.succ - t)) := by
  intro x hx v hav hvs hθv tr e h1 h2 h3 h4 t hvt ht1 ht2
  have hvτ : (v : ℝ) < H.time e.succ := lt_of_le_of_lt hvt ht2
  have he : T₀ ≤ H.time e.succ := hT₀.trans (hθv.trans hvτ.le)
  have hpr := hprot x hx v hav hvs hθv tr e h1 h2 h3 h4 hvτ he
  exact H.event_crossing_bound_C11D e (records e he).static (hOld e he) (hcan e he) hacc hDm
    (seedTrace.crossing e _ _) (tr.crossing e h3 h4) (fun b => (hpr b).1) (fun b => (hpr b).2)
    hℓ ht1 ht2 (fun t' ht' z ξ hz =>
      hRic x hx v hav hvs hθv tr e h1 h2 h3 h4 t' (lt_of_le_of_lt hvt ht'.1)
        (lt_of_le_of_lt ht1 ht'.1) ht'.2 z ξ hz)

/-! ## astra `DistanceData` 核对（乘法形，不是 (D4)） -/

/-- **astra `HasUniformDistanceScalar` 的距离含义（`_C11D`）**：`E.HasUniformDistanceScalar C`
（`PreparedSpatialState.DistanceData.full` / `PreparedSpatialChain.tower_hasUniformDistanceScalar`）⇒
对全部 old 点 `d_term(oldTerminal z, oldTerminal w) ≤ C · d_out(oldOutput z, oldOutput w)`。只是乘法形
（常数 `C`、无保护），(D4) 要 `C = 1` 的保护端点版；沿测试窗内 `k` 次 surgery 累乘 `C^k`，故
`DistanceData` **不能**替代 (D4)。 -/
theorem terminal_edist_le_mul_of_hasUniformDistanceScalar_C11D {P Q : OrientedThreeStage.{u}}
    {a s : ℝ} (E : MetricCutCapEvent P Q a s) {C : ℝ≥0} (hE : E.HasUniformDistanceScalar C)
    (z w : E.old) :
    riemannianEDistOf E.terminal.metric (E.oldTerminal z) (E.oldTerminal w) ≤
      (C : ℝ≥0∞) * riemannianEDistOf E.outputMetric (E.oldOutput z) (E.oldOutput w) := by
  refine ENNReal.le_of_forall_nnreal_lt fun N hN => ?_
  obtain ⟨G, hG, hLip⟩ := hE (E.oldTerminal w) N
  have hzN : min (riemannianEDistOf E.terminal.metric (E.oldTerminal z) (E.oldTerminal w))
      (N : ℝ≥0∞) = N := min_eq_right hN.le
  have hGz : G (E.oldOutput z) = (N : ℝ) := by
    rw [hG z, hzN]
    rfl
  have hGw : G (E.oldOutput w) = 0 := by
    rw [hG w, riemannianEDistOf_self, min_eq_left zero_le]
    rfl
  have h := hLip (E.oldOutput z) (E.oldOutput w)
  rw [hGz, hGw, edist_dist, Real.dist_eq, sub_zero, abs_of_nonneg N.coe_nonneg,
    ENNReal.ofReal_coe_nnreal] at h
  exact h

/-- **consumer（G3）**：G2 `hsmooth` + G3 `hevent`（late records + 端点保护 + 端点 Ricci / `|Rm|` 界）喂 G1
主目标 `hdist_rel_of_stage_bounds_C11D` ⇒ P6CON L9 的相对形 `hdist`（速率 `Λ = 8/ℓ`）。 -/
example (H : ObservedHistory.{u})
    {T aSeed s : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ T) (hsT : s ≤ T) (has : aSeed ≤ s)
    {p : (H.stageAt T).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (y : (H.stageAt s).Carrier) {Q L θ Rad ℓ K T₀ : ℝ} (hℓ : 0 < ℓ) (hKℓ : K * ℓ ^ 2 ≤ 1)
    (hT₀ : T₀ ≤ (s : ℝ) - θ / Q)
    (hnum : Rad / Real.sqrt Q + 8 / ℓ * (θ / Q) ≤ L / Real.sqrt Q)
    {q : CutoffParameters}
    (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e q)
    (hOld : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ →
      (H.event e).old = (H.event e).transition.trace.retainedCore)
    (hcan : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (hacc : q.modelAccuracy ≤ 1 / 2) (hDm : StandardCap.transitionEnd + 10 < q.modelRadius)
    (hRm : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ t : ℝ, (s : ℝ) - θ / Q < t → H.time (H.activeStage s) < t → t < s →
      ∀ z : (H.stageAt s).Carrier,
        (riemannianEDistOf (H.stageMetric (H.activeStage s) t)
            (seedTrace.point (H.activeStage s) (H.activeStage_mono has)
              (H.activeStage_mono hsT)) z < ENNReal.ofReal ℓ ∨
          riemannianEDistOf (H.stageMetric (H.activeStage s) t) x z < ENNReal.ofReal ℓ) →
        Real.sqrt (normSq0S (H.stageMetric (H.activeStage s) t) z 4
          (metricRm04At (H.stageMetric (H.activeStage s) t) z)) ≤ K)
    (hprot : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : aSeed ≤ v) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
      ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x,
      ∀ (e : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ e.castSucc)
        (h2 : e.succ ≤ H.activeStage T) (h3 : H.activeStage v ≤ e.castSucc)
        (h4 : e.succ ≤ H.activeStage s), (v : ℝ) < H.time e.succ →
      ∀ (he : T₀ ≤ H.time e.succ) b,
        seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
            ((records e he).static b).window ''
              {z : standardCapWindow q.modelRadius | ‖z.val‖ ≤ StandardCap.transitionEnd + 10} ∧
          tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
            ((records e he).static b).window ''
              {z : standardCapWindow q.modelRadius | ‖z.val‖ ≤ StandardCap.transitionEnd + 10})
    (hRic : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : aSeed ≤ v) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
      ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x,
      ∀ (e : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ e.castSucc)
        (h2 : e.succ ≤ H.activeStage T) (h3 : H.activeStage v ≤ e.castSucc)
        (h4 : e.succ ≤ H.activeStage s) (t' : ℝ),
        (v : ℝ) < t' → H.time e.castSucc < t' → t' < H.time e.succ →
      ∀ z : (H.stage e.castSucc).Carrier, ∀ ξ : TangentSpace ThreeModel z,
        (riemannianEDistOf (H.stageMetric e.castSucc t')
            (seedTrace.point e.castSucc h1 (e.castSucc_lt_succ.le.trans h2)) z <
            ENNReal.ofReal ℓ ∨
          riemannianEDistOf (H.stageMetric e.castSucc t')
            (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z < ENNReal.ofReal ℓ) →
        ricciTensor (H.stageMetric e.castSucc t') z ξ ξ ≤
          (3 / ℓ ^ 2) * (H.stageMetric e.castSucc t').inner z ξ ξ) :
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
            ENNReal.ofReal (L / Real.sqrt Q) :=
  H.hdist_rel_of_stage_bounds_C11D haT hsT has seedTrace y (div_nonneg (by norm_num) hℓ.le)
    hnum (H.hsmooth_of_rmNorm_le_C11D haT hsT has seedTrace y hℓ hKℓ hRm)
    (H.hevent_of_records_C11D haT seedTrace y hℓ hT₀ records hOld hcan hacc hDm hprot hRic)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
