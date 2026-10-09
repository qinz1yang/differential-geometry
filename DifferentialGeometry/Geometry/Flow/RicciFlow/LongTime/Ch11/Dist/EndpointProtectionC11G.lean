import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.SurgeryNoShortcutC11D
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.AnalyticAdmissibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialWindowBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodContinuationLeaves
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCrossingJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PresentedStaticCapHistory
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

/-!
# P6 几何输入 G1：端点保护（O-CH11-P6GEO，后缀 `_C11G`）

DIST G3 `hevent_of_records_C11D` 的显式前提 `hprot`：窗口内每个 event `e` 处，种子 trace 与 `x` 的
trace 在 `e⁺` 的点都**不在** cap window 内区 `S_b.window '' {‖x‖ ≤ transitionEnd + 10}`（R-C11-2 D-8 的
"保护端点"，树内 (D4) `EventCapNoShortcut:846` 的前提）。本文件把它归约到两类可供给的输入：

* **`¬CapWindowPoint` 路**（简报指定的归约链）：
  - `capWindowPoint_of_ageZero_C11G`：`k = e⁺`、singleton trace、age `0`（`t = time e⁺`）、`0 ≤ θcap` 时，
    "`z = window x`、`‖x‖ < Dcap + 1`" 就是 `CapWindowPoint records e⁺ z (time e⁺) Dcap θcap`；
  - `not_mem_capWindow_inner_of_not_ageZero_C11G`：age-0 cap 点不存在 + `transitionEnd + 9 < Dcap`
    ⇒ 不在内区。**注**：简报写 `Dcap ≥ transitionEnd + 9`；`≥` 只给 `‖x‖ ≥ transitionEnd + 10`，排除不了
    闭内区的边界，故用**严格** `<`（P6 序列里 `Dcap = D n → ∞`，无代价）。
  - `hprot_of_not_ageZeroCapPoint_C11G`：DIST `hprot` 的逐字形 ⇐ 两个 trace 点的 age-0 非 cap 条件。
* **cap 标量 ≈ neck.scale 路**（"`¬CapWindowPoint` 本身"的来源）：
  - `exists_capWindow_scalar_lower_C11G`：canonical window（`ε ≤ ε₀`、阶 `≥ 2`）上
    `scale/2 ≤ R_out(window x)`（`‖x‖ < D`；树内 `StandardCap` 的
    `exists_uniform_window_image_scalar_lower_bound_of_scaled_pullback`）；
  - `exists_not_ageZeroCapPoint_of_scalar_lt_C11G`：`R_out(z) < scale_b/2`（每个 `b`）⇒ age-0 非 cap；
  - `GeometricCutoffRecord.inv_two_mul_sq_lt_static_scale_C11G`：单 record 版
    `(2ρ(τ)²)⁻¹ < static scale`（`Λ δ(τ) ≤ 1/2`；树内 family 版
    `IsCanonicalCutoffRecordFamily.inv_two_mul_sq_lt_static_scale` 的逐 record 形）。
* **trace 点在 `e⁺` 的标量**：
  - 种子端 `seed_scalar_le_of_smallParabolic_C11G`：K0（`hasSmallParabolicCurvature`，`aSeed = T − r²`）
    ⇒ 种子 trace 在 `[aSeed, T]` 每个 stage 时刻 `R ≤ 3/r²`（含 `e⁺` 的 output 度量）；
  - 另一端 `scalar_succ_le_of_slab_C11G`：`e⁻` slab 上 `(max(v, time e⁻), time e⁺)` 内 `R ≤ B`
    ⇒ `e⁺` 点 `R ≤ B`（`TerminalLimitMetric.tendsto_scalar` + `RegularCrossing.scalar_eq`）。
* 装配：`exists_hprot_of_scalar_lt_C11G`（标量 `< scale/2` ⇒ `hprot`）与
  **`exists_hprot_of_seed_slab_scalar_C11G`**（K0 + slab 标量 `≤ B` + `2 max(3/r², B) < scale`
  ⇒ `hprot`）。

consumer（文件末 `example`）：后者喂 DIST `hevent_of_records_C11D`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

/-! ## cap 标量 ≈ neck.scale -/

/-- **canonical window 的标量下界（`_C11G`）**：存在绝对常数 `ε₀ > 0`，canonical window（精度 `ε ≤ ε₀`、
阶 `m ≥ 2`）的 presented static cap 上 `scale/2 ≤ R_out(window x)`（`‖x‖ < D`）。 -/
theorem exists_capWindow_scalar_lower_C11G :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
        {fixed : StaticCapScaffold} {D : ℝ} {m : ℕ} {ε : ℝ}, ε ≤ ε₀ → 2 ≤ m →
        ∀ {b : E.RetainedBoundaryIndex} (S : E.PresentedStaticCap fixed D m ε b),
          S.hasCanonicalWindow → ∀ x : standardCapWindow D, ‖x.val‖ < D →
            S.neck.scale / 2 ≤ metricScalarAt E.outputMetric (S.window x) := by
  obtain ⟨ε₀, hε₀, hb⟩ :=
    StandardCap.exists_uniform_window_image_scalar_lower_bound_of_scaled_pullback
  refine ⟨ε₀, hε₀, ?_⟩
  intro P Q a s E fixed D m ε hε hm b S hcan x hx
  obtain ⟨x₀, δ, k, d, w, -, hinner, -⟩ := hcan
  exact hb w hε hm E.outputMetric S.window S.window_smooth S.neck.scale S.neck.scale_pos hinner
    x hx

/-- **age-0 非 cap ⇐ 标量（`_C11G`）**：record `R`（精度 `≤ ε₀`、阶 `≥ 2`、canonical windows），
`Dcap + 1 ≤ modelRadius`；`R_out(z) < scale_b/2`（每个 `b`）⇒ `z` 不是任何 `b` 的 window 点
`‖x‖ < Dcap + 1`。 -/
theorem exists_not_ageZeroCapPoint_of_scalar_lt_C11G :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {H : ObservedHistory.{u}} {e : Fin H.eventCount} {q : CutoffParameters}
        (R : GeometricCutoffRecord H e q), q.modelAccuracy ≤ ε₀ → 2 ≤ q.modelOrder →
        (∀ b, (R.static b).hasCanonicalWindow) → ∀ {Dcap : ℝ}, Dcap + 1 ≤ q.modelRadius →
        ∀ z : (H.stage e.succ).Carrier,
          (∀ b, metricScalarAt (H.event e).outputMetric z < (R.static b).neck.scale / 2) →
          ¬ ∃ (b : (H.event e).RetainedBoundaryIndex) (x : standardCapWindow q.modelRadius),
            z = (R.static b).window x ∧ ‖x.val‖ < Dcap + 1 := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_capWindow_scalar_lower_C11G.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro H e q R hacc hm hcan Dcap hD z hz
  rintro ⟨b, x, rfl, hx⟩
  have hlow := h (H.event e) hacc hm (R.static b) (hcan b) x (lt_of_lt_of_le hx hD)
  linarith [hz b]

/-- **单 record 的 scale 下界（`_C11G`）**：`Λ · δ(time e⁺) ≤ 1/2` ⇒ 每个 static cap
`(2 ρ(time e⁺)²)⁻¹ < scale`（family 版 `IsCanonicalCutoffRecordFamily.inv_two_mul_sq_lt_static_scale`
取 `ρ₀ = ρ(time e⁺)`、`δ₀ = δ(time e⁺)`，证明同）。 -/
theorem GeometricCutoffRecord.inv_two_mul_sq_lt_static_scale_C11G {H : ObservedHistory.{u}}
    {i : Fin H.eventCount} {p : CutoffParameters} (R : GeometricCutoffRecord H i p)
    (hΛδ : p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2)
    (b : (H.event i).RetainedBoundaryIndex) :
    (2 * p.neckRadius (H.time i.succ) ^ 2)⁻¹ < (R.static b).neck.scale := by
  have ht : 0 ≤ H.time i.succ := H.time_nonneg i.succ
  have hn := R.nominal_small ⟨b.1.1⟩
  have hnpos := R.nominal_pos ⟨b.1.1⟩
  have hδ := p.delta_pos _ ht
  have hδ1 := p.delta_lt_one _ ht
  have hρ := p.neckRadius_pos _ ht
  have hr : R.nominalRadius ⟨b.1.1⟩ < p.neckRadius (H.time i.succ) := by
    refine hn.trans_le ?_
    have h2 : p.delta (H.time i.succ) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hNlow : (p.neckRadius (H.time i.succ) ^ 2)⁻¹ < (R.neck b.1.1).scale := by
    rw [R.scale_eq b.1.1]
    exact inv_strictAnti₀ (pow_pos hnpos 2) (by nlinarith)
  have hNpos : 0 < (R.neck b.1.1).scale := (inv_pos.mpr (pow_pos hρ 2)).trans hNlow
  have hΛδα : p.recenterConstant * R.delta b.1.1 ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (R.delta_le b.1.1)
      (by linarith [p.recenterConstant_ge_four])).trans hΛδ
  have hhalf : 1 / 2 ≤ (R.static b).neck.scale / (R.neck b.1.1).scale := by
    have := (abs_le.mp ((R.recenter_scale_comparison b).trans hΛδα)).1
    linarith
  have hS : (R.neck b.1.1).scale / 2 ≤ (R.static b).neck.scale := by
    rw [le_div_iff₀ hNpos] at hhalf
    linarith
  have h2 : (2 * p.neckRadius (H.time i.succ) ^ 2)⁻¹ =
      (p.neckRadius (H.time i.succ) ^ 2)⁻¹ / 2 := by
    rw [mul_inv, div_eq_mul_inv]
    ring
  rw [h2]
  linarith

/-! ## `¬CapWindowPoint` 归约链 -/

/-- **age-0 cap 点 ⇒ `CapWindowPoint`（`_C11G`）**：`k = e⁺`、`A = singleton`、`t = time e⁺`、
`0 ≤ θcap`：若 `z = window_b x`、`‖x‖ < Dcap + 1`，则 `CapWindowPoint records e⁺ z (time e⁺) Dcap θcap`。
（逆否：`¬CapWindowPoint` 在事件时刻 ⇒ age-0 非 cap。） -/
theorem RetainedCoreHistory.capWindowPoint_of_ageZero_C11G (H : RetainedCoreHistory.{u})
    {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (e : Fin H.eventCount) (z : (H.stage e.succ).Carrier) {Dcap θcap : ℝ} (hθ : 0 ≤ θcap)
    (hz : ∃ (b : (H.toHistory.event e).RetainedBoundaryIndex)
      (x : standardCapWindow p.modelRadius),
      z = ((records e).static b).window x ∧ ‖x.val‖ < Dcap + 1) :
    H.CapWindowPoint records e.succ z (H.time e.succ) Dcap θcap := by
  obtain ⟨b, x, hzx, hx⟩ := hz
  unfold RetainedCoreHistory.CapWindowPoint
  refine ⟨e, le_rfl, BackwardPointTrace.singleton H.toHistory e.succ z, b, x, hzx, hx, ?_⟩
  rw [sub_self]
  exact mul_nonneg hθ (inv_nonneg.mpr ((records e).static b).neck.scale_pos.le)

/-- **age-0 非 cap ⇒ 不在内区（`_C11G`）**：`transitionEnd + 9 < Dcap`、`z` 不是任何 window 点
`‖x‖ < Dcap + 1` ⇒ `z ∉ window_b '' {‖x‖ ≤ transitionEnd + 10}`。 -/
theorem not_mem_capWindow_inner_of_not_ageZero_C11G {H : ObservedHistory.{u}}
    {e : Fin H.eventCount} {q : CutoffParameters} (R : GeometricCutoffRecord H e q) {Dcap : ℝ}
    (hD : StandardCap.transitionEnd + 9 < Dcap) {z : (H.stage e.succ).Carrier}
    (hnot : ¬ ∃ (b : (H.event e).RetainedBoundaryIndex) (x : standardCapWindow q.modelRadius),
      z = (R.static b).window x ∧ ‖x.val‖ < Dcap + 1)
    (b : (H.event e).RetainedBoundaryIndex) :
    z ∉ (R.static b).window ''
      {x : standardCapWindow q.modelRadius | ‖x.val‖ ≤ StandardCap.transitionEnd + 10} := by
  rintro ⟨x, hx, hzx⟩
  have hx' : ‖x.val‖ ≤ StandardCap.transitionEnd + 10 := hx
  exact hnot ⟨b, x, hzx.symm, by linarith⟩

/-- **`¬CapWindowPoint` ⇒ 不在内区（`_C11G`，RetainedCoreHistory 全 records 形）**：
`¬ CapWindowPoint records e⁺ z (time e⁺) Dcap θcap`、`0 ≤ θcap`、`transitionEnd + 9 < Dcap` ⇒ 保护。 -/
theorem RetainedCoreHistory.not_mem_capWindow_inner_of_not_capWindowPoint_C11G
    (H : RetainedCoreHistory.{u}) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (e : Fin H.eventCount) (z : (H.stage e.succ).Carrier) {Dcap θcap : ℝ} (hθ : 0 ≤ θcap)
    (hD : StandardCap.transitionEnd + 9 < Dcap)
    (hnot : ¬ H.CapWindowPoint records e.succ z (H.time e.succ) Dcap θcap)
    (b : (H.toHistory.event e).RetainedBoundaryIndex) :
    z ∉ ((records e).static b).window ''
      {x : standardCapWindow p.modelRadius | ‖x.val‖ ≤ StandardCap.transitionEnd + 10} :=
  not_mem_capWindow_inner_of_not_ageZero_C11G (records e) hD
    (fun hz => hnot (H.capWindowPoint_of_ageZero_C11G records e z hθ hz)) b

/-! ## trace 点在 `e⁺` 的标量 -/

namespace ObservedHistory

/-- `stageMetric e⁺ (time e⁺) = outputMetric`。 -/
theorem stageMetric_succ_time_C11G (H : ObservedHistory.{u}) (e : Fin H.eventCount) :
    H.stageMetric e.succ (H.time e.succ) = (H.event e).outputMetric := by
  rw [H.stageMetric_initial, H.event_output]

/-- **`e⁺` 点的标量 ⇐ `e⁻` slab（`_C11G`）**：`pm ↦ pp` 是 event `e` 的 regular crossing，
eventually（`t ↑ time e⁺`）`R(g_{e⁻}(t), pm) ≤ B` ⇒ `R_out(pp) ≤ B`（terminal 极限 + crossing 等距）。 -/
theorem scalar_succ_le_of_eventually_C11G (H : ObservedHistory.{u}) (e : Fin H.eventCount)
    {pm : (H.stage e.castSucc).Carrier} {pp : (H.stage e.succ).Carrier}
    (hc : (H.event e).RegularCrossing pm pp) {B : ℝ}
    (hev : ∀ᶠ t in 𝓝[<] H.time e.succ, metricScalarAt (H.stageMetric e.castSucc t) pm ≤ B) :
    metricScalarAt (H.event e).outputMetric pp ≤ B := by
  let p' : (H.event e).incoming.terminalRegularOpen :=
    ⟨pm, hc.mem_terminalRegularRegion (H.event e)⟩
  have hc' : (H.event e).RegularCrossing p'.val pp := hc
  have hlim := (H.event e).terminal.tendsto_scalar p'
  have hle : metricScalarAt (H.event e).terminal.metric p' ≤ B := by
    refine le_of_tendsto hlim ?_
    filter_upwards [hev] with t ht
    rw [stageMetric_castSucc_apply] at ht
    exact ht
  rw [← hc'.scalar_eq (H.event e)]
  exact hle

/-- **`e⁺` 点的标量 ⇐ 窗口内 `e⁻` slab 界（`_C11G`）**：`v < time e⁺`，`(max(v, time e⁻), time e⁺)` 内
`R(g_{e⁻}(t'), pm) ≤ B`（DIST `hRic` 的时刻 binder 形）⇒ `R_out(pp) ≤ B`。 -/
theorem scalar_succ_le_of_slab_C11G (H : ObservedHistory.{u}) (e : Fin H.eventCount)
    {pm : (H.stage e.castSucc).Carrier} {pp : (H.stage e.succ).Carrier}
    (hc : (H.event e).RegularCrossing pm pp) {v B : ℝ} (hv : v < H.time e.succ)
    (hslab : ∀ t' : ℝ, v < t' → H.time e.castSucc < t' → t' < H.time e.succ →
      metricScalarAt (H.stageMetric e.castSucc t') pm ≤ B) :
    metricScalarAt (H.event e).outputMetric pp ≤ B := by
  have hlt : max v (H.time e.castSucc) < H.time e.succ :=
    max_lt hv (H.time_strictMono e.castSucc_lt_succ)
  refine H.scalar_succ_le_of_eventually_C11G e hc ?_
  filter_upwards [Ioo_mem_nhdsLT hlt] with t ht
  exact hslab t (lt_of_le_of_lt (le_max_left _ _) ht.1)
    (lt_of_le_of_lt (le_max_right _ _) ht.1) ht.2

/-- **种子端标量（K0，`_C11G`）**：`hasSmallParabolicCurvature H T p r`、`aSeed = T − r²` ⇒ 种子 trace
在 `[aSeed, T]` 的每个时刻 `τ`（stage `k = activeStage τ`）`R ≤ 3/r²`（`√3 r`-控制 + `r'²|R| ≤ 9`）。 -/
theorem seed_scalar_le_of_smallParabolic_C11G (H : ObservedHistory.{u})
    {T aSeed : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ T) {p : (H.stageAt T).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature H T p r)
    (hclock : (aSeed : ℝ) = (T : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (τ : Icc (0 : ℝ) H.horizon) (h1 : aSeed ≤ τ) (h2 : τ ≤ T) (k : Fin (H.eventCount + 1))
    (hk : H.activeStage τ = k) (hk1 : H.activeStage aSeed ≤ k) (hk2 : k ≤ H.activeStage T) :
    metricScalarAt (H.stageMetric k τ) (seedTrace.point k hk1 hk2) ≤ 3 / r ^ 2 := by
  obtain ⟨hr, a, hat, ha, htr⟩ := hsmall
  obtain rfl : a = aSeed := Subtype.ext (ha.trans hclock.symm)
  have hpp : p ∈ riemannianBallOf (H.stageMetric (H.activeStage T) T) p r := by
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  obtain ⟨A, hA⟩ := htr p hpp
  obtain rfl : A = seedTrace := Subsingleton.elim _ _
  subst hk
  have hb := hA.1 τ h1 h2
  have hr3 : Real.sqrt 3 * r ≠ 0 := by positivity
  have habs := scalar_abs_le_div_sq_of_rm_bound _ _ hr3 hb
  have hdim : (Module.finrank ℝ ThreeSpace : ℝ) = 3 := by simp
  have hsq : (Real.sqrt 3 * r) ^ 2 = 3 * r ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  rw [hdim, hsq] at habs
  have h9 : (3 : ℝ) ^ 2 / (3 * r ^ 2) = 3 / r ^ 2 := by
    field_simp
  rw [h9] at habs
  exact (le_abs_self _).trans habs

end ObservedHistory

/-! ## DIST `hprot` 的生产 -/

namespace ObservedHistory

/-- **`hprot` ⇐ age-0 非 cap（`_C11G`）**：DIST `hevent_of_records_C11D` 的 `hprot` 逐字形，由两个
trace 点（种子 trace / `x` 的 trace 在 `e⁺`）的 age-0 非 cap 条件（`‖x‖ < Dcap + 1`）与
`transitionEnd + 9 < Dcap` 给出。 -/
theorem hprot_of_not_ageZeroCapPoint_C11G (H : ObservedHistory.{u})
    {T aSeed s : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ T)
    {p : (H.stageAt T).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (y : (H.stageAt s).Carrier) {Q θ Rad T₀ Dcap : ℝ} {q : CutoffParameters}
    (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e q)
    (hD : StandardCap.transitionEnd + 9 < Dcap)
    (hnot : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
      ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : aSeed ≤ v) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
      ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s) (H.activeStage_mono hvs) x,
      ∀ (e : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ e.castSucc)
        (h2 : e.succ ≤ H.activeStage T) (h3 : H.activeStage v ≤ e.castSucc)
        (h4 : e.succ ≤ H.activeStage s), (v : ℝ) < H.time e.succ →
      ∀ he : T₀ ≤ H.time e.succ,
        (¬ ∃ (b : (H.event e).RetainedBoundaryIndex) (z : standardCapWindow q.modelRadius),
          seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2 =
            ((records e he).static b).window z ∧ ‖z.val‖ < Dcap + 1) ∧
        ¬ ∃ (b : (H.event e).RetainedBoundaryIndex) (z : standardCapWindow q.modelRadius),
          tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 =
            ((records e he).static b).window z ∧ ‖z.val‖ < Dcap + 1) :
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
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
              {z : standardCapWindow q.modelRadius | ‖z.val‖ ≤ StandardCap.transitionEnd + 10} := by
  intro x hx v hav hvs hθv tr e h1 h2 h3 h4 hvτ he b
  have hn := hnot x hx v hav hvs hθv tr e h1 h2 h3 h4 hvτ he
  exact ⟨not_mem_capWindow_inner_of_not_ageZero_C11G (records e he) hD hn.1 b,
    not_mem_capWindow_inner_of_not_ageZero_C11G (records e he) hD hn.2 b⟩

/-- **`hprot` ⇐ 标量（`_C11G`）**：存在绝对常数 `ε₀ > 0`；records 精度 `≤ ε₀`、阶 `≥ 2`、
`transitionEnd + 10 < modelRadius`、canonical windows；两个 trace 点在 `e⁺` 的 output 标量
`< scale_b/2`（每个 `b`）⇒ DIST `hprot`（取 `Dcap = modelRadius − 1`）。 -/
theorem exists_hprot_of_scalar_lt_C11G :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (H : ObservedHistory.{u}) {T aSeed s : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ T)
        {p : (H.stageAt T).Carrier}
        (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
          (H.activeStage_mono haT) p)
        (y : (H.stageAt s).Carrier) {Q θ Rad T₀ : ℝ} {q : CutoffParameters}
        (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e q),
        (∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b,
          ((records e he).static b).hasCanonicalWindow) →
        q.modelAccuracy ≤ ε₀ → 2 ≤ q.modelOrder →
        StandardCap.transitionEnd + 10 < q.modelRadius →
        (∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
          ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : aSeed ≤ v) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
          ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s)
            (H.activeStage_mono hvs) x,
          ∀ (e : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ e.castSucc)
            (h2 : e.succ ≤ H.activeStage T) (h3 : H.activeStage v ≤ e.castSucc)
            (h4 : e.succ ≤ H.activeStage s), (v : ℝ) < H.time e.succ →
          ∀ (he : T₀ ≤ H.time e.succ) b,
            metricScalarAt (H.event e).outputMetric
                (seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2) <
              ((records e he).static b).neck.scale / 2 ∧
            metricScalarAt (H.event e).outputMetric
                (tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4) <
              ((records e he).static b).neck.scale / 2) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
          ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : aSeed ≤ v) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
          ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s)
            (H.activeStage_mono hvs) x,
          ∀ (e : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ e.castSucc)
            (h2 : e.succ ≤ H.activeStage T) (h3 : H.activeStage v ≤ e.castSucc)
            (h4 : e.succ ≤ H.activeStage s), (v : ℝ) < H.time e.succ →
          ∀ (he : T₀ ≤ H.time e.succ) b,
            seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
                ((records e he).static b).window ''
                  {z : standardCapWindow q.modelRadius |
                    ‖z.val‖ ≤ StandardCap.transitionEnd + 10} ∧
              tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
                ((records e he).static b).window ''
                  {z : standardCapWindow q.modelRadius |
                    ‖z.val‖ ≤ StandardCap.transitionEnd + 10} := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_not_ageZeroCapPoint_of_scalar_lt_C11G.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro H T aSeed s haT p seedTrace y Q θ Rad T₀ q records hcan hacc hm hDm hscal
  have hD : StandardCap.transitionEnd + 9 < q.modelRadius - 1 := by linarith
  have hD1 : q.modelRadius - 1 + 1 ≤ q.modelRadius := by linarith
  refine H.hprot_of_not_ageZeroCapPoint_C11G haT seedTrace y records hD ?_
  intro x hx v hav hvs hθv tr e h1 h2 h3 h4 hvτ he
  have hs := hscal x hx v hav hvs hθv tr e h1 h2 h3 h4 hvτ he
  exact ⟨h (records e he) hacc hm (hcan e he) hD1 _ fun b => (hs b).1,
    h (records e he) hacc hm (hcan e he) hD1 _ fun b => (hs b).2⟩

/-- **`hprot` ⇐ K0 + slab 标量（`_C11G`，G1 主装配）**：存在 `ε₀ > 0`；records 条件同上；
种子端 K0（`hasSmallParabolicCurvature H T p r`、`aSeed = T − r²`）；`x` 的 trace 在每个 `e⁻` slab
`(max(v, time e⁻), time e⁺)` 内 `R ≤ B`（与 DIST `hRic` 同 binder）；`2 max(3/r², B) < scale_b`
⇒ DIST `hprot`。 -/
theorem exists_hprot_of_seed_slab_scalar_C11G :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (H : ObservedHistory.{u}) {T aSeed s : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ T)
        {p : (H.stageAt T).Carrier} {r : ℝ},
        GC.LongTime.hasSmallParabolicCurvature H T p r → (aSeed : ℝ) = (T : ℝ) - r ^ 2 →
        ∀ (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
          (H.activeStage_mono haT) p)
        (y : (H.stageAt s).Carrier) {Q θ Rad T₀ B : ℝ} {q : CutoffParameters}
        (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e q),
        (∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b,
          ((records e he).static b).hasCanonicalWindow) →
        q.modelAccuracy ≤ ε₀ → 2 ≤ q.modelOrder →
        StandardCap.transitionEnd + 10 < q.modelRadius →
        (∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b,
          2 * max (3 / r ^ 2) B < ((records e he).static b).neck.scale) →
        (∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
          ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : aSeed ≤ v) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
          ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s)
            (H.activeStage_mono hvs) x,
          ∀ (e : Fin H.eventCount) (h3 : H.activeStage v ≤ e.castSucc)
            (h4 : e.succ ≤ H.activeStage s) (t' : ℝ),
            (v : ℝ) < t' → H.time e.castSucc < t' → t' < H.time e.succ →
            metricScalarAt (H.stageMetric e.castSucc t')
              (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) ≤ B) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
          ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : aSeed ≤ v) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
          ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s)
            (H.activeStage_mono hvs) x,
          ∀ (e : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ e.castSucc)
            (h2 : e.succ ≤ H.activeStage T) (h3 : H.activeStage v ≤ e.castSucc)
            (h4 : e.succ ≤ H.activeStage s), (v : ℝ) < H.time e.succ →
          ∀ (he : T₀ ≤ H.time e.succ) b,
            seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
                ((records e he).static b).window ''
                  {z : standardCapWindow q.modelRadius |
                    ‖z.val‖ ≤ StandardCap.transitionEnd + 10} ∧
              tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
                ((records e he).static b).window ''
                  {z : standardCapWindow q.modelRadius |
                    ‖z.val‖ ≤ StandardCap.transitionEnd + 10} := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_hprot_of_scalar_lt_C11G.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro H T aSeed s haT p r hsmall hclock seedTrace y Q θ Rad T₀ B q records hcan hacc hm hDm
    hscale hslab
  refine h H haT seedTrace y records hcan hacc hm hDm ?_
  intro x hx v hav hvs hθv tr e h1 h2 h3 h4 hvτ he b
  have hsc := hscale e he b
  have hmax1 : 3 / r ^ 2 ≤ max (3 / r ^ 2) B := le_max_left _ _
  have hmax2 : B ≤ max (3 / r ^ 2) B := le_max_right _ _
  refine ⟨?_, ?_⟩
  · -- 种子端：K0 在 `τ = time e⁺`
    have hτ1 : aSeed ≤ H.stageTime e.succ := by
      have hav' : (aSeed : ℝ) ≤ v := hav
      change (aSeed : ℝ) ≤ H.time e.succ
      exact hav'.trans hvτ.le
    have hτ2 : H.stageTime e.succ ≤ T := by
      change H.time e.succ ≤ (T : ℝ)
      exact (H.time_strictMono.monotone h2).trans (H.activeStage_time_le T)
    have hseed := H.seed_scalar_le_of_smallParabolic_C11G haT hsmall hclock seedTrace
      (H.stageTime e.succ) hτ1 hτ2 e.succ (H.activeStage_stageTime e.succ)
      (h1.trans e.castSucc_lt_succ.le) h2
    change metricScalarAt (H.stageMetric e.succ (H.time e.succ)) _ ≤ _ at hseed
    rw [H.stageMetric_succ_time_C11G e] at hseed
    linarith
  · -- 另一端：`e⁻` slab ⇒ `e⁺`
    have hpt := H.scalar_succ_le_of_slab_C11G e (tr.crossing e h3 h4) hvτ
      (fun t' h₁ h₂ h₃ => hslab x hx v hav hvs hθv tr e h3 h4 t' h₁ h₂ h₃)
    linarith

end ObservedHistory

/-- **consumer（G1）**：G1 主装配的 `hprot` 喂 DIST `hevent_of_records_C11D`（`T₀ ≤ s − θ/Q`、
`hacc`、`hDm`、`hOld`、`hRic` 原样）⇒ G1 `hevent`（速率 `8/ℓ`）。 -/
example : ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (H : ObservedHistory.{u}) {T aSeed s : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ T)
      {p : (H.stageAt T).Carrier} {r : ℝ},
      GC.LongTime.hasSmallParabolicCurvature H T p r → (aSeed : ℝ) = (T : ℝ) - r ^ 2 →
      ∀ (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
        (H.activeStage_mono haT) p)
      (y : (H.stageAt s).Carrier) {Q θ Rad ℓ T₀ B : ℝ} {q : CutoffParameters},
      0 < ℓ → T₀ ≤ (s : ℝ) - θ / Q →
      ∀ (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e q),
      (∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b,
        ((records e he).static b).hasCanonicalWindow) →
      q.modelAccuracy ≤ ε₀ → q.modelAccuracy ≤ 1 / 2 → 2 ≤ q.modelOrder →
      StandardCap.transitionEnd + 10 < q.modelRadius →
      (∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b,
        2 * max (3 / r ^ 2) B < ((records e he).static b).neck.scale) →
      (∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
        ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : aSeed ≤ v) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
        ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s)
          (H.activeStage_mono hvs) x,
        ∀ (e : Fin H.eventCount) (h3 : H.activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ H.activeStage s) (t' : ℝ),
          (v : ℝ) < t' → H.time e.castSucc < t' → t' < H.time e.succ →
          metricScalarAt (H.stageMetric e.castSucc t')
            (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) ≤ B) →
      (∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
        ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : aSeed ≤ v) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
        ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s)
          (H.activeStage_mono hvs) x,
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
            (3 / ℓ ^ 2) * (H.stageMetric e.castSucc t').inner z ξ ξ) →
      ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) y (Rad / Real.sqrt Q),
        ∀ (v : Icc (0 : ℝ) H.horizon) (_hav : aSeed ≤ v) (hvs : v ≤ s), (s : ℝ) - θ / Q ≤ v →
        ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage s)
          (H.activeStage_mono hvs) x,
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
  obtain ⟨ε₀, hε₀, h⟩ := ObservedHistory.exists_hprot_of_seed_slab_scalar_C11G.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro H T aSeed s haT p r hsmall hclock seedTrace y Q θ Rad ℓ T₀ B q hℓ hT₀ records hcan
    hacc0 hacc hm hDm hscale hslab hRic
  exact H.hevent_of_records_C11D haT seedTrace y hℓ hT₀ records
    (fun e he => (records e he).old_eq_retained) hcan hacc hDm
    (h H haT hsmall hclock seedTrace y records hcan hacc0 hm hDm hscale hslab) hRic

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
