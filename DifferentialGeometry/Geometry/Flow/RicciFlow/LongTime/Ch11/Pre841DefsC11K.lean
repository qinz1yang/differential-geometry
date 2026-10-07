import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness
import DifferentialGeometry.Geometry.Collapse.ScaleInvariance

/-!
# 外审 D-9.6 / R-C11-2 D-2、D-3 的 data-level `Pre841` 包（S-CH11-PRE841 G1，后缀 `_C11K`）

外审 R-C11-1 §9.6：存在**同一个** `κ_A > 0`，使对每个固定的归一化空间尺度与后向深度，eventually
（`κ` **不随 `n, D, L, B` 恶化**），所有满足局部包含 / unscathed / 曲率控制条件的测试抛物球都有
`Vol_{ĝ_n(τ)} B(z, ϱ) ≥ κ_A ϱ³`（`0 < ϱ ≤ L`）。放 data-level `Pre841` 包，**不继承**
`AnalyticSurgeryProfile`（普通 profile 已含 S8，继承会把 S8 的循环藏进结构字段）。
R-C11-2 处置 D-R-C11-2-2（内容）与 D-R-C11-2-3（量词形 (K-seq)）进一步冻结：

* **(K-seq)** `∃ κ_A > 0, ∀ D L B > 0, ∀ᶠ n, ∀ 合格测试球, Vol ≥ κ_A ϱ³ (0 < ϱ ≤ L)`；eventually 下标可依赖
  `D, L, B`，**不可**依赖测试点 / 时刻 / `ϱ`；`∀ L B ∃ κ_{L,B}` **不接受**；测试球深度备到 `B + L²`
  （中心时刻 `v ≥ t n − B/R n`，球自带后向深度 `ϱ²/R n ≤ L²/R n`）。
* **内容（D-2）**：同一物理 history 的 records 与识别、native 高曲率区的 canonical / 时间导数 /
  梯度控制、年龄兼容的 pinching 与标量下界、足以证 K3 的精细帽几何与参数小性；**不含**种子假设
  （随调用输入）、不含 S8 / P6 结论、不继承 `AnalyticSurgeryProfile`。

## 结构（两层）
* `Pre841NativeData_C11K H`：D-2 的 native 内容，参数只有历史序列 `H : ℕ → ObservedHistory`；
* `Pre841Data_C11K H t y R hR`：`native` + (K-seq) 的 κ 字段（`kappa` / `kappa_pos` / `volume_ge`）。
  `t n`（基点时刻）、`y n`（基点）、`R n > 0`（重标度因子，`ĝ_n(τ) = scaleMetric (R n) (hR n)
  (stageMetric … v)`，`v = t n + τ/R n`）= P6B / P6D 已用的同一组对象。`D, L, B` 是字段内约束变量。

## 字段 ↔ 条款
* `native.records` / `canonical_windows`：同一物理 history 的 records（含 retained 识别、精细 neck 阶数
  与精度、`protected_interior`、`backward` 等 `GeometricCutoffRecord` 字段）与 canonical window；
* `native.canonical`：高曲率区（`R > ρ(t)⁻²`）有 `SpatialCanonicalWitness`（`rm_bound` / `scalar_bounds` /
  `gradient` 即梯度控制，`capTubeHasNeckChart` 即 cap 的 neck chart）；
* `native.time_derivative_event / _final`：event slab 与 final slab 上 `R > ρ(t)⁻² ⇒ |∂ₜR| ≤ Ctime R²`；
* `native.scalar_lower` / `pinching`：年龄兼容（`−3/(2(t + a))`，`InFixedHamiltonIveyRegion … (a + t)`）；
* `native.recent_cutoff_smallness` / `delta_*` / `epsilon_*`：参数小性（K3 的前提）；
* `volume_ge`：局部包含 = `x ∈ B_{t n}(y n, D/√R n)` 的 backward trace `tr`，`z = tr.point …`；
  unscathed + 曲率控制 = `isParabolicallyRmControlledBall v z (ϱ/√R n)`（`HistoryParabolicBall:77`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-- **D-2 的 native 内容**（data-level；不含种子假设、不含 S8 / P6 结论、不继承
`AnalyticSurgeryProfile`）。字段逐条取自 profile 的对应字段（history 形），去掉
`largerBallAccuracy*` / `larger_ball_scalar_control`（S7 / S8）。 -/
structure Pre841NativeData_C11K (H : ℕ → ObservedHistory.{u}) where
  /-- 同一物理 history 的 cutoff 参数。 -/
  params : CutoffParameters
  /-- 同一物理 history 的 records（含 retained 识别与精细帽几何）。 -/
  records : ∀ n (i : Fin (H n).eventCount), GeometricCutoffRecord (H n) i params
  /-- 每个 record 的每个 static cap 有 canonical window。 -/
  canonical_windows : ∀ n i b, ((records n i).static b).hasCanonicalWindow
  radius_antitone : AntitoneOn params.neckRadius (Ici 0)
  /-- 参数小性：`δ` 单调下降到 `0`。 -/
  delta_antitone : AntitoneOn params.delta (Ici 0)
  delta_tendsto : Tendsto params.delta atTop (𝓝 0)
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_small : epsilon < 1 / 100
  C1 : ℝ
  C2 : ℝ
  C1_ge_one : 1 ≤ C1
  C2_ge_one : 1 ≤ C2
  /-- native 高曲率区（`R > ρ(t)⁻²`）的 canonical witness（含梯度控制）。 -/
  canonical : ∀ (n : ℕ) (t : Icc (0 : ℝ) (H n).horizon) (x : ((H n).stageAt t).Carrier),
    (params.neckRadius t ^ 2)⁻¹ < metricScalarAt ((H n).stageMetric ((H n).activeStage t) t) x →
    ∃ W : SpatialCanonicalWitness ((H n).stageMetric ((H n).activeStage t) t) epsilon C1 C2 x,
      W.capTubeHasNeckChart epsilon
  Ctime : ℝ≥0
  /-- event slab 上的时间导数控制。 -/
  time_derivative_event : ∀ n (j : Fin (H n).eventCount) (y : ((H n).stage j.castSucc).Carrier)
      (t : ℝ), t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ) →
      (params.neckRadius t ^ 2)⁻¹ < ((H n).event j).incoming.flow.scalar t y →
      |derivWithin (fun v => ((H n).event j).incoming.flow.scalar v y) (Iic t) t| ≤
        Ctime * ((H n).event j).incoming.flow.scalar t y ^ 2
  /-- final slab 上的时间导数控制。 -/
  time_derivative_final : ∀ n (h : (H n).time (Fin.last (H n).eventCount) < (H n).horizon)
      (y : ((H n).stage (Fin.last (H n).eventCount)).Carrier) (t : ℝ),
      t ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (H n).horizon →
      (params.neckRadius t ^ 2)⁻¹ < ((H n).finalSlab h).flow.scalar t y →
      |derivWithin (fun v => ((H n).finalSlab h).flow.scalar v y) (Iic t) t| ≤
        Ctime * ((H n).finalSlab h).flow.scalar t y ^ 2
  /-- 年龄兼容的标量下界。 -/
  scalarShift : ℝ
  scalarShift_pos : 0 < scalarShift
  scalar_lower : ∀ (n : ℕ) (t : Icc (0 : ℝ) (H n).horizon) (x : ((H n).stageAt t).Carrier),
    -3 / (2 * ((t : ℝ) + scalarShift)) ≤
      metricScalarAt ((H n).stageMetric ((H n).activeStage t) t) x
  /-- 年龄兼容的 Hamilton–Ivey pinching。 -/
  pinchingShift : ℝ
  pinchingShift_pos : 0 < pinchingShift
  pinching : ∀ (n : ℕ) (t : Icc (0 : ℝ) (H n).horizon) (x : ((H n).stageAt t).Carrier),
    InFixedHamiltonIveyRegion ((H n).stageMetric ((H n).activeStage t) t)
      (pinchingShift + (t : ℝ)) x
  /-- 参数小性（K3 的前提）：近期手术的 nominal 半径相对 `ρ(t)` 任意小。 -/
  recent_cutoff_smallness : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧
    ∀ t, T ≤ t → ∀ n (i : Fin (H n).eventCount),
      (H n).time i.succ ∈ Icc (t / 2) t →
      ∀ h, (records n i).nominalRadius h ≤ ε * params.neckRadius t

/-- **`Pre841Data_C11K`**（D-2 内容 + (K-seq)）：`native` + 同一 `κ_A > 0`，`∀ D L B`，eventually，
所有合格测试抛物球 `Vol_ĝ B(z, ϱ) ≥ κ_A ϱ³`（`0 < ϱ ≤ L`）。 -/
structure Pre841Data_C11K (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) where
  /-- D-2 的 native 内容。 -/
  native : Pre841NativeData_C11K H
  /-- 同一个 `κ_A`（在 `D, L, B, n` 之前给出）。 -/
  kappa : ℝ
  /-- `κ_A > 0`。 -/
  kappa_pos : 0 < kappa
  /-- (K-seq)：`∀ D L B > 0`，eventually（下标可依赖 `D, L, B`，不依赖测试点 / 时刻 / `ϱ`）。 -/
  volume_ge : ∀ D L B : ℝ, 0 < D → 0 < L → 0 < B → ∀ᶠ n in atTop,
    ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
        (D / Real.sqrt (R n)),
    ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - B / R n ≤ v →
    ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
      ((H n).activeStage_mono hvt) x,
    ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
      (H n).isParabolicallyRmControlledBall v
        (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
        (ϱ / Real.sqrt (R n)) →
      ENNReal.ofReal (kappa * ϱ ^ 3) ≤
        ballVolume (scaleMetric (R n) (hR n) ((H n).stageMetric ((H n).activeStage v) v))
          (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) ϱ

namespace Pre841NativeData_C11K

variable {H : ℕ → ObservedHistory.{u}}

/-- native 内容沿子列 `ψ` 重新索引（所有字段都是 `∀ n` 形）。 -/
def comp (N : Pre841NativeData_C11K H) (ψ : ℕ → ℕ) :
    Pre841NativeData_C11K (fun n => H (ψ n)) where
  params := N.params
  records := fun n i => N.records (ψ n) i
  canonical_windows := fun n i b => N.canonical_windows (ψ n) i b
  radius_antitone := N.radius_antitone
  delta_antitone := N.delta_antitone
  delta_tendsto := N.delta_tendsto
  epsilon := N.epsilon
  epsilon_pos := N.epsilon_pos
  epsilon_small := N.epsilon_small
  C1 := N.C1
  C2 := N.C2
  C1_ge_one := N.C1_ge_one
  C2_ge_one := N.C2_ge_one
  canonical := fun n => N.canonical (ψ n)
  Ctime := N.Ctime
  time_derivative_event := fun n => N.time_derivative_event (ψ n)
  time_derivative_final := fun n => N.time_derivative_final (ψ n)
  scalarShift := N.scalarShift
  scalarShift_pos := N.scalarShift_pos
  scalar_lower := fun n => N.scalar_lower (ψ n)
  pinchingShift := N.pinchingShift
  pinchingShift_pos := N.pinchingShift_pos
  pinching := fun n => N.pinching (ψ n)
  recent_cutoff_smallness := fun ε hε => by
    obtain ⟨T, hT, h⟩ := N.recent_cutoff_smallness ε hε
    exact ⟨T, hT, fun t ht n i hi => h t ht (ψ n) i hi⟩

end Pre841NativeData_C11K

namespace Pre841Data_C11K

variable {H : ℕ → ObservedHistory.{u}} {t : ∀ n, Icc (0 : ℝ) (H n).horizon}
  {y : ∀ n, ((H n).stageAt (t n)).Carrier} {R : ℕ → ℝ} {hR : ∀ n, 0 < R n}

/-- **`κ` 向下单调**：把 `κ_A` 换成更小的正数仍是 `Pre841` 数据（`native` 不变）。 -/
def weaken (d : Pre841Data_C11K H t y R hR) {κ' : ℝ} (hκ' : 0 < κ') (hle : κ' ≤ d.kappa) :
    Pre841Data_C11K H t y R hR where
  native := d.native
  kappa := κ'
  kappa_pos := hκ'
  volume_ge := fun D L B hD hL hB =>
    (d.volume_ge D L B hD hL hB).mono fun n hn x hx v hvt hv tr ϱ hϱ0 hϱL hball =>
      (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hle (by positivity))).trans
        (hn x hx v hvt hv tr ϱ hϱ0 hϱL hball)

/-- **`(D, L, B)` 单调**：`(D, L, B)` 处的 eventually 陈述蕴含更小 `(D₀, L₀, B₀)` 处的陈述（同一
`n`），故 `κ` 确实不随 `D, L, B` 恶化。 -/
theorem volume_ge_anti (d : Pre841Data_C11K H t y R hR) {D D₀ L L₀ B B₀ : ℝ}
    (hD₀ : 0 < D₀) (hL₀ : 0 < L₀) (hB₀ : 0 < B₀) (hD : D₀ ≤ D) (hL : L₀ ≤ L) (hB : B₀ ≤ B) :
    ∀ᶠ n in atTop,
    ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
        (D₀ / Real.sqrt (R n)),
    ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - B₀ / R n ≤ v →
    ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
      ((H n).activeStage_mono hvt) x,
    ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L₀ →
      (H n).isParabolicallyRmControlledBall v
        (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
        (ϱ / Real.sqrt (R n)) →
      ENNReal.ofReal (d.kappa * ϱ ^ 3) ≤
        ballVolume (scaleMetric (R n) (hR n) ((H n).stageMetric ((H n).activeStage v) v))
          (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) ϱ :=
  (d.volume_ge D L B (hD₀.trans_le hD) (hL₀.trans_le hL) (hB₀.trans_le hB)).mono
    fun n hn x hx v hvt hv tr ϱ hϱ0 hϱL hball =>
      hn x (riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right hD (Real.sqrt_nonneg _)) hx)
        v hvt (by linarith [div_le_div_of_nonneg_right hB (hR n).le]) tr ϱ hϱ0 (hϱL.trans hL)
        hball

/-- **子列 / 平移**（设计表 9.6 行的 "eventually ⇒ 平移子列 `n ↦ n + N`" adapter）：沿任意
`ψ → ∞` 重新索引仍是 `Pre841` 数据，`κ` 不变。 -/
def comp (d : Pre841Data_C11K H t y R hR) (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop) :
    Pre841Data_C11K (fun n => H (ψ n)) (fun n => t (ψ n)) (fun n => y (ψ n))
      (fun n => R (ψ n)) (fun n => hR (ψ n)) where
  native := d.native.comp ψ
  kappa := d.kappa
  kappa_pos := d.kappa_pos
  volume_ge := fun D L B hD hL hB => hψ.eventually (d.volume_ge D L B hD hL hB)

/-- `comp` 不改 `κ`。 -/
theorem comp_kappa (d : Pre841Data_C11K H t y R hR) (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop) :
    (d.comp ψ hψ).kappa = d.kappa := rfl

/-- **条件 inhabitant**【同构：与 `Pre841AlignC11K.exists_tracedKappa` 互逆（至多差存在性的
`ρnc`）】：给定 native 内容 `N`，P6B / P6D 的 trace-local `hkappa` 形 ⇒ `Pre841`。`hkappa` 与
`TracedRegionAncientLimitTimeControl_P6L` 的同名前提逐字同形（`∀ D T`、eventually、尺度
`≤ ρnc n`），`ρnc n √R n → ∞` 让每个 `ϱ ≤ L` eventually 落进 `ϱ/√R n ≤ ρnc n`；体积由 history
度量换到 `ĝ`（`le_ballVolume_scaleMetric_iff`）。`κ` 原样保留。 -/
def ofTracedKappa (N : Pre841NativeData_C11K H) {κ : ℝ} (hκ : 0 < κ) {ρnc : ℕ → ℝ}
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
        ((H n).activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
        (H n).isParabolicallyRmControlledBall v
          (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          ballVolume ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'') :
    Pre841Data_C11K H t y R hR where
  native := N
  kappa := κ
  kappa_pos := hκ
  volume_ge := fun D L B hD hL hB => by
    filter_upwards [hkappa D B hD hB, hradii.eventually_ge_atTop L] with n hn hρ
    intro x hx v hvt hv tr ϱ hϱ0 hϱL hball
    have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hR n)
    have hr : ϱ / Real.sqrt (R n) ≤ ρnc n := by
      rw [div_le_iff₀ hsR]
      linarith
    have h := hn x hx v hvt hv tr (ϱ / Real.sqrt (R n)) (div_pos hϱ0 hsR) hr hball
    have hfin : Module.finrank ℝ ThreeSpace = 3 := by simp
    have hconv := (le_ballVolume_scaleMetric_iff hfin (R n) (hR n)).2 h
    rwa [mul_div_cancel₀ _ hsR.ne'] at hconv

end Pre841Data_C11K

end GC.LongTime.Ch11
