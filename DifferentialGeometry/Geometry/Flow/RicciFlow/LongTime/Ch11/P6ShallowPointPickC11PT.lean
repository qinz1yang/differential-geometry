import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KSWFixedWindowC11KS2

/-!
# SHALLOW T1：driver 中心邻域合同付 U 侧（O-CH11-PICKT1 G1，后缀 `_C11PT`）

**G0 结论（本车道主要结论）**：T1 壳 `hsliceR_lateHI_core_short_C11KS` 的 U 侧前提 `hUl` 只有 **1 个调用点**（壳末尾
`intro w hw hzw hRw; refine e13 …`），用来付 `KSW_C11KS θ₀` 的逐点 `hU`；`ksw_of_shortSLT_C11KS` 只在非 CWP
分支、在**它自己结论里的 `w`** 上消费 `hU`（∀ `w`：`d_v(tr x₁, w) < Dd/√R_n`、seed 余量 `L/2`、`R(v, w) ≥ R_n`、
`¬CWP w`）。壳不选点；chain 在 ShortSLT 内部（`hnot` ⇒ chain capture），不用 U 数据。⇒ 这个调用点是"真的任意 `w`"
（= 结论的全称 `w`）。把 `PickedBallTop_C11PB Λ Rad′` gate 在这个 `w` 上，`hpick(w) ∧ Λ ≤ QB` 会直接推出该 `w` 的结论，
等于把目标写成 binder；"链上每点二次选点"也不行。**故 T1 壳改 point-picking 形不是正确修法**；repair target 改为
**driver 中心选点**（lead 裁定 (b)，20:4x）。

**本文件（G1，PROVISIONAL[合同]）**：
* 合同 `PickedCenterNeighborhood_C11PT`（Perelman 12.1 Step 1 型，单个中心 `(σ_n, y_n)` 一次）：在中心邻域
  `P_n`（slice 时刻 `v ∈ [σ − Tc/R_n, σ]`、`x₁ ∈ B_σ(y, Dw/√R_n)` 的 backward trace 周围 `B_v(tr x₁,
      Dc/√R_n)`、
  窗口 `[v − θ/R_n, v]`）上，`R > qthr` 的点有 spatial canonical witness、梯度界 `|∇R| ≤ Cgrad R^{3/2}`，
  且受控小球 κ-noncollapsed。**合同不含任何曲率上界**（不是 BCBD 型），故不与 T1 结论循环。
* `kswHU_of_pickedCenter_C11PT`（PROVED）：每个合格 `w` 的球 `B_v(w, Rad/√R(v,w))` ⊆ `B_v(tr x₁,
    (Dd+Rad)/√R_n)`、
  窗口 `[v − θ₀/R(v,w), v]` ⊆ `[v − θ₀/R_n, v]` ⇒ 合同逐点付清 KSW 的 `hU`。
* `hsliceR_lateHI_core_pickedCenter_C11PT`：T1 壳结论逐字（`Kh := (K n).toHistory`），`hUl` 换成合同
  （`Dc := Dd + Rad`、`Tc := −σ₁`、`θ := θ₀`、`qthr := Cg·R_n`、`ρ := ρV n`），`hK` 由
      `ksw_pos_C11KS2`（PROVED）付；
  其余 binder 不动。consumer `shallowSliceRC_of_pickedCenter_C11PT`：T1 条件形（`ShallowSliceRC_C11SH`），
  `hUVC` 换成合同族 `hPC`。
* 与 lead 规格的偏差：lead 写的"`P_n` 内无更坏点 `R ≤ Λ·R_n`"**不放进 G1 合同**——hUl 的付款不用它（未用到的假设），
  而且带上它，T1 非 CWP 分支会被合同直接推出（等于在中心尺度把目标写成 binder）。它属于 G2 producer 合同
  （曲率选点路线的中间量），见 G2 文件。

非循环：只 import `P6KSWFixedWindowC11KS2`（→ T1 壳、KSW G1/KSW2 链）；不经 hscalU / hclosG / M4 `hclosC` /
hUVC 的 M4 生产链 / CanonicalLateCore / hspine（审计做传递依赖名字扫描）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

section Contract

/-- **中心邻域合同（`_C11PT`，PROVISIONAL[合同]；owner = driver 中心选点，G2 producer 合同）**：
Perelman 12.1 Step 1 型。中心 `(σ, y)`、尺度 `Rn`；`P = P(y, σ, Dc/√Rn, (Tc + θ)/Rn)` 的 trace 形：
对 event `j′` slab 内的 slice 时刻 `v ∈ [σ − Tc/Rn, σ]`、`x₁ ∈ B_σ(y, Dw/√Rn)` 的 backward trace `tr`、
`x ∈ B_v(tr x₁, Dc/√Rn)`：
(1) `R(v, x) > qthr` ⇒ spatial canonical witness（neck chart）；
(2) 窗口 `v′ ∈ (time j′⁻, v)`、`v − θ/Rn ≤ v′`、`R(v′, x) > qthr` ⇒ `|∇R| ≤ Cgrad R^{3/2}`；
(3) `τ ∈ [v − θ/Rn, v] ∩ (time j′⁻,
    time j′⁺)` 处半径 `b ≤ ρ` 的 parabolically controlled ball κ-noncollapsed。
**不含曲率上界**：这是"区域内高曲率点都是好点"（canonical nbhd assumption 在 backward 区域上），不是 BCBD。 -/
def PickedCenterNeighborhood_C11PT (Dw Dc Tc θ Rn qthr ρ κ ε C1 C2 : ℝ) (Cgrad : ℝ≥0)
    (K : RetainedCoreHistory.{u}) (σ : Icc (0 : ℝ) K.toHistory.horizon)
    (y : (K.toHistory.stageAt σ).Carrier) : Prop :=
  ∀ (j' : Fin K.eventCount) (v : ℝ), K.time j'.castSucc < v → v < K.time j'.succ →
    (σ : ℝ) - Tc / Rn ≤ v → v ≤ σ →
  ∀ x₁ ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
      (Dw / Real.sqrt Rn),
  ∀ (hjσ : j'.castSucc ≤ K.toHistory.activeStage σ)
    (tr : BackwardPointTrace K.toHistory j'.castSucc (K.toHistory.activeStage σ) hjσ x₁),
  ∀ x ∈ riemannianBallOf ((K.toHistory.event j').incoming.flow.base.metric v)
      (tr.point j'.castSucc le_rfl hjσ) (Dc / Real.sqrt Rn),
    (qthr < (K.toHistory.event j').incoming.flow.scalar v x →
      ∃ W : SpatialCanonicalWitness ((K.toHistory.event j').incoming.flow.base.metric v)
        ε C1 C2 x, W.capTubeHasNeckChart ε) ∧
    (∀ v' ∈ Ioo (K.time j'.castSucc) v, v - θ / Rn ≤ v' →
      qthr < (K.toHistory.event j').incoming.flow.scalar v' x →
      ∀ ξ : TangentSpace ThreeModel x,
        |scalarDifferential (K.toHistory.event j').incoming.flow v' x ξ| ≤
          Cgrad * (K.toHistory.event j').incoming.flow.scalar v' x *
            Real.sqrt ((K.toHistory.event j').incoming.flow.scalar v' x) *
            Real.sqrt (((K.toHistory.event j').incoming.flow.base.metric v').inner x ξ ξ)) ∧
    (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
      v - θ / Rn ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
      K.time j'.castSucc < τ → (τ : ℝ) < K.time j'.succ →
      ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz x →
      ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
            (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
            (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b))

/-- **inhabitant（`_C11PT`）**：`Dc = 0` 时邻域球空，合同平凡成立（定义一致性检查）。 -/
theorem pickedCenterNeighborhood_zero_C11PT (Dw Tc θ Rn qthr ρ κ ε C1 C2 : ℝ) (Cgrad : ℝ≥0)
    (K : RetainedCoreHistory.{u}) (σ : Icc (0 : ℝ) K.toHistory.horizon)
    (y : (K.toHistory.stageAt σ).Carrier) :
    PickedCenterNeighborhood_C11PT Dw 0 Tc θ Rn qthr ρ κ ε C1 C2 Cgrad K σ y := by
  intro j' v _ _ _ _ x₁ _ hjσ tr x hx
  exfalso
  have hx' : riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v)
      (tr.point j'.castSucc le_rfl hjσ) x < ENNReal.ofReal (0 / Real.sqrt Rn) := hx
  rw [zero_div, ENNReal.ofReal_zero] at hx'
  exact ENNReal.not_lt_zero hx'

end Contract

section Payment

/-- **合同逐点付 KSW 的 `hU`（`_C11PT`，PROVED）**：中心邻域合同（`Dc = Dd + Rad`、`qthr = Cg·Rn`、窗口 `θ₀`）
⇒ 合格 `w`（`d_v(tr x₁, w) < Dd/√Rn`、`Rn ≤ q := R(v, w)`）处 KSW `hU` 三项（半径 `Rad`、窗口 `v − θ₀/q`、
阈值 `Cg·Rn`、κ 半径 `ρ`）。证明 = 球包含 `B_v(w, Rad/√q) ⊆ B_v(tr x₁, (Dd+Rad)/√Rn)`（三角不等式，`q ≥ Rn`）
+ 窗口包含 `θ₀/q ≤ θ₀/Rn`。 -/
theorem kswHU_of_pickedCenter_C11PT {Dw Dd Rad Tc θ₀ Rn Cg ρ κ ε C1 C2 : ℝ} {Cgrad : ℝ≥0}
    {K : RetainedCoreHistory.{u}} {σ : Icc (0 : ℝ) K.toHistory.horizon}
    {y : (K.toHistory.stageAt σ).Carrier} (hθ₀ : 0 ≤ θ₀) (hRn : 0 < Rn)
    (hPC : PickedCenterNeighborhood_C11PT Dw (Dd + Rad) Tc θ₀ Rn (Cg * Rn) ρ κ ε C1 C2 Cgrad
      K σ y)
    (j' : Fin K.eventCount) (v : ℝ) (hv1 : K.time j'.castSucc < v) (hv2 : v < K.time j'.succ)
    (hvT : (σ : ℝ) - Tc / Rn ≤ v) (hvσ : v ≤ σ)
    (x₁ : (K.toHistory.stage (K.toHistory.activeStage σ)).Carrier)
    (hx₁ : x₁ ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
      (Dw / Real.sqrt Rn))
    (hjσ : j'.castSucc ≤ K.toHistory.activeStage σ)
    (tr : BackwardPointTrace K.toHistory j'.castSucc (K.toHistory.activeStage σ) hjσ x₁)
    (w : (K.stage j'.castSucc).Carrier)
    (hzw : riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v)
      (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt Rn))
    (hRw : Rn ≤ (K.toHistory.event j').incoming.flow.scalar v w) :
    (∀ x ∈ riemannianBallOf ((K.toHistory.event j').incoming.flow.base.metric v) w
          (Rad / Real.sqrt ((K.toHistory.event j').incoming.flow.scalar v w)),
      Cg * Rn < (K.toHistory.event j').incoming.flow.scalar v x →
      ∃ W : SpatialCanonicalWitness ((K.toHistory.event j').incoming.flow.base.metric v)
        ε C1 C2 x, W.capTubeHasNeckChart ε) ∧
    (∀ x ∈ riemannianBallOf ((K.toHistory.event j').incoming.flow.base.metric v) w
          (Rad / Real.sqrt ((K.toHistory.event j').incoming.flow.scalar v w)),
      ∀ v' ∈ Ioo (K.time j'.castSucc) v,
      v - θ₀ / (K.toHistory.event j').incoming.flow.scalar v w ≤ v' →
      Cg * Rn < (K.toHistory.event j').incoming.flow.scalar v' x →
      ∀ ξ : TangentSpace ThreeModel x,
        |scalarDifferential (K.toHistory.event j').incoming.flow v' x ξ| ≤
          Cgrad * (K.toHistory.event j').incoming.flow.scalar v' x *
            Real.sqrt ((K.toHistory.event j').incoming.flow.scalar v' x) *
            Real.sqrt (((K.toHistory.event j').incoming.flow.base.metric v').inner x ξ ξ)) ∧
    (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
      v - θ₀ / (K.toHistory.event j').incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
      K.time j'.castSucc < τ → (τ : ℝ) < K.time j'.succ →
      ∀ z ∈ riemannianBallOf ((K.toHistory.event j').incoming.flow.base.metric v) w
            (Rad / Real.sqrt ((K.toHistory.event j').incoming.flow.scalar v w)),
      ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
      ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
            (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
            (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b)) := by
  have hθq : θ₀ / (K.toHistory.event j').incoming.flow.scalar v w ≤ θ₀ / Rn :=
    div_le_div_of_nonneg_left hθ₀ hRn hRw
  have hsub : ∀ x ∈ riemannianBallOf ((K.toHistory.event j').incoming.flow.base.metric v) w
      (Rad / Real.sqrt ((K.toHistory.event j').incoming.flow.scalar v w)),
      x ∈ riemannianBallOf ((K.toHistory.event j').incoming.flow.base.metric v)
        (tr.point j'.castSucc le_rfl hjσ) ((Dd + Rad) / Real.sqrt Rn) := by
    intro x hx
    have hx' : riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v) w x <
        ENNReal.ofReal (Rad / Real.sqrt ((K.toHistory.event j').incoming.flow.scalar v w)) := hx
    have hRad : 0 < Rad / Real.sqrt ((K.toHistory.event j').incoming.flow.scalar v w) :=
      ENNReal.ofReal_pos.mp (zero_le.trans_lt hx')
    have hRad0 : 0 ≤ Rad := by
      by_contra hneg
      have : Rad / Real.sqrt ((K.toHistory.event j').incoming.flow.scalar v w) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (not_le.mp hneg).le (Real.sqrt_nonneg _)
      linarith
    have hDd : 0 < Dd / Real.sqrt Rn := ENNReal.ofReal_pos.mp (zero_le.trans_lt hzw)
    have hRq : Rad / Real.sqrt ((K.toHistory.event j').incoming.flow.scalar v w) ≤
        Rad / Real.sqrt Rn :=
      div_le_div_of_nonneg_left hRad0 (Real.sqrt_pos.2 hRn) (Real.sqrt_le_sqrt hRw)
    change riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v)
      (tr.point j'.castSucc le_rfl hjσ) x < ENNReal.ofReal ((Dd + Rad) / Real.sqrt Rn)
    calc riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v)
          (tr.point j'.castSucc le_rfl hjσ) x
        ≤ riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w +
          riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v) w x :=
          riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal (Dd / Real.sqrt Rn) + ENNReal.ofReal (Rad / Real.sqrt Rn) :=
          ENNReal.add_lt_add hzw (hx'.trans_le (ENNReal.ofReal_le_ofReal hRq))
      _ = ENNReal.ofReal ((Dd + Rad) / Real.sqrt Rn) := by
          rw [← ENNReal.ofReal_add hDd.le (hRad.le.trans hRq), add_div]
  refine ⟨fun x hx hC => (hPC j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x (hsub x hx)).1 hC,
    fun x hx v' hv' hθ' hC => (hPC j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x (hsub x hx)).2.1 v' hv'
      (by linarith) hC,
    fun τ hτ1 hτ2 hτ3 hτ4 z hz zz hzz b hb hbρ hctl =>
      (hPC j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr z (hsub z hz)).2.2 τ (by linarith) hτ2 hτ3 hτ4 zz
        hzz b hb hbρ hctl⟩

end Payment

section T1

/-- **T1 核心形 ⇐ 中心邻域合同（`_C11PT`，PROVISIONAL[合同 `PickedCenterNeighborhood_C11PT`]）**：
`hsliceR_lateHI_core_short_C11KS` 的结论逐字（`Kh :=
    (K n).toHistory`）；`hK` 由 `ksw_pos_C11KS2 hθ₀`（PROVED）付；
U 侧 `hUl`（对每个合格 `w`、半径 `Rad`、窗口 `θ₀/R(v,w)`）换成**每个 `n` 一次**的中心邻域合同
（`Dc := Dd + Rad`、`Tc := −σ₁`、`θ := θ₀`、`qthr := Cg·R_n`、`ρ := ρV n`），由
    `kswHU_of_pickedCenter_C11PT`
逐点付清；其余 binder 不动。 -/
theorem ObservedHistory.hsliceR_lateHI_core_pickedCenter_C11PT
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {Cg : ℝ} (hCg : 1 ≤ Cg) {η₃ Lc : ℝ}
    (hη₃ : 0 < η₃) (hLc : 0 < Lc)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (htj : ∀ n, t n < (K n).time (j n).succ)
    {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount))
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (y : ∀ n, ((K n).toHistory.stageAt
        (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n)
    (hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
 :
    ∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ Rad : ℝ, 0 ≤ QB ∧
      Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
      ∀ l : Filter ℕ, l ≤ atTop → ∀ σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw : ℝ, 0 < Dw →
      (∀ᶠ n in l,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) + σ₁ / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
                ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) →
      (∀ᶠ n in l, PickedCenterNeighborhood_C11PT Dw (Dd + Rad) (-σ₁) θ₀ (R n) (Cg * R n) (ρV n) κ
        ε C1 C2 Cgrad (K n) (σ n) (y n)) →
      ∀ᶠ n in l,
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) + σ₁ / R n ≤ v →
        (v : ℝ) ≤ σ n + σ₂ / R n → (K n).toHistory.time ((K n).toHistory.activeStage v) < v →
      ∀ tr₁ : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvt) x₁,
        metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          (tr₁.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono hvt))
              ≤ A * R n →
        ∃ CWP : ((K n).toHistory.stage ((K n).toHistory.activeStage v)).Carrier → Prop,
          (∀ w, riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              (tr₁.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → ¬ CWP w →
            R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
                w → ∀ x,
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) w x <
              ENNReal.ofReal ((2 * Dd * Real.sqrt A + 1) /
                Real.sqrt (metricScalarAt ((K n).toHistory.stageMetric
                    ((K n).toHistory.activeStage v) v) w)) →
            metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) x ≤
              QB * metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
                  w) ∧
          (∀ w, riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              (tr₁.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → CWP w →
            ∃ (Ξ : standardCapWindow D₂ → ((K n).toHistory.stage
                ((K n).toHistory.activeStage v)).Carrier)
              (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
              Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dcap + 1 ∧
              ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
                τw ∈ Icc (0 : ℝ) (1 / 2) ∧
                ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
                  metricDerivNorm m (localPullMetric (scaleMetric lam hlam
                      ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)) Ξ hΞ)
                    ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
                    (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃) := by
  intro A Dd hA hDd
  obtain ⟨QB, Dcap, D₂, Rad, hQB, hD₂, hcore⟩ :=
    ObservedHistory.hsliceR_lateHI_core_short_C11KS (C1 := C1) (C2 := C2) (Cgrad := Cgrad)
      (ksw_pos_C11KS2 hθ₀) hεle hκ hphi hCg hη₃ hLc htj recordsF hHI hcanK hδF hacc hrad hord
      hscaleK hbirthA hpinchK0 hslabK (fun n => (K n).toHistory) rfl σ y R hσ hRpos hqR hT₀ Tn
      aSeed haT hsT has pT seedTrace L hL hwin ρV hρV A Dd hA hDd
  refine ⟨QB, Dcap, D₂, Rad, hQB, hD₂, fun l hl σ₁ σ₂ h12 hσ₂ Dw hDw hdl hPC => ?_⟩
  refine hcore l hl σ₁ σ₂ h12 hσ₂ Dw hDw hdl ?_
  filter_upwards [hPC] with n hn
  intro j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr _ _ w _ hzw hRw
  have hσ2R : σ₂ / R n < 0 := div_neg_of_neg_of_pos hσ₂ (hRpos n)
  have hvT : (σ n : ℝ) - -σ₁ / R n ≤ v := by
    rw [neg_div, sub_neg_eq_add]
    exact hvσ1
  exact kswHU_of_pickedCenter_C11PT hθ₀.le (hRpos n) hn j' v hv1 hv2 hvT (by linarith) x₁ hx₁
    hjσ tr w hzw hRw

/-- **SHALLOW T1 ⇐ 中心邻域合同（consumer，`_C11PT`，PROVISIONAL[合同族 `hPC`]）**：
`shallowSliceRC_of_ksw_short_C11KS` 的副本，`hK := ksw_pos_C11KS2 hθ₀`、`Kh :=
    (K n).toHistory`，U 侧 `hUVC`
换成中心邻域合同族 `hPC`（量词前缀与 `hUVC` 逐字：`Rad σ₁ σ₂ φ Dw Dd T Kc` + traced-region 前提）；
证明 = 本文件核心形 + `hdistQC`（同原壳）。 -/
theorem ObservedHistory.shallowSliceRC_of_pickedCenter_C11PT
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {Cg : ℝ} (hCg : 1 ≤ Cg) {η₃ Lc : ℝ}
    (hη₃ : 0 < η₃) (hLc : 0 < Lc)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (htj : ∀ n, t n < (K n).time (j n).succ)
    {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount))
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (y : ∀ n, ((K n).toHistory.stageAt
        (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n)
    (hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    (hdistQC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
                ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (hPC : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
        (2 * Dw / Real.sqrt (R n)) (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      PickedCenterNeighborhood_C11PT Dw (Dd + Rad) (-σ₁) θ₀ (R n) (Cg * R n) (ρV n) κ ε C1 C2
        Cgrad (K n) (σ n) (y n)) :
    ObservedHistory.ShallowSliceRC_C11SH η₃ Lc (fun n => (K n).toHistory) σ y R := by
  intro A Dd hA hDd
  obtain ⟨QB, Dcap, D₂, Rad, hQB, hD₂, hcore⟩ :=
    ObservedHistory.hsliceR_lateHI_core_pickedCenter_C11PT (C1 := C1) (C2 := C2) (Cgrad := Cgrad)
      hθ₀ hεle hκ hphi hCg hη₃ hLc htj recordsF hHI hcanK hδF hacc hrad hord hscaleK hbirthA
      hpinchK0 hslabK σ y R hσ hRpos hqR hT₀ Tn aSeed haT hsT has pT seedTrace L hL hwin ρV hρV
      A Dd hA hDd
  refine ⟨QB, Dcap, D₂, hQB, hD₂, fun φ hφ σ₁ σ₂ h12 hσ₂ Dw hDw T Kc hT hKc htr => ?_⟩
  refine hcore (map φ atTop) hφ.tendsto_atTop σ₁ σ₂ h12 hσ₂ Dw hDw ?_
    (hPC Rad σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr)
  filter_upwards [hdistQC φ hφ Dw T Kc hDw (by linarith) hKc htr] with n hn
  intro x hx v hav hvs hv tr
  refine hn x hx v hav hvs ?_ tr
  have h1 : -T / R n ≤ σ₁ / R n := div_le_div_of_nonneg_right (by linarith) (hRpos n).le
  rw [sub_eq_add_neg, ← neg_div]
  linarith

/-- consumer：中心邻域合同的 inhabitant（`Dc = Dd + Rad = 0`）逐点付 KSW `hU`——`Rad = −Dd` 时 U 球
`B_v(w, Rad/√q)` 为空，三项平凡；检查 `kswHU_of_pickedCenter_C11PT` 与合同的接口对齐。 -/
example {Dw Dd Tc θ₀ Rn Cg ρ κ ε C1 C2 : ℝ} {Cgrad : ℝ≥0}
    {K : RetainedCoreHistory.{u}} {σ : Icc (0 : ℝ) K.toHistory.horizon}
    {y : (K.toHistory.stageAt σ).Carrier} (hθ₀ : 0 ≤ θ₀) (hRn : 0 < Rn)
    (j' : Fin K.eventCount) (v : ℝ) (hv1 : K.time j'.castSucc < v) (hv2 : v < K.time j'.succ)
    (hvT : (σ : ℝ) - Tc / Rn ≤ v) (hvσ : v ≤ σ)
    (x₁ : (K.toHistory.stage (K.toHistory.activeStage σ)).Carrier)
    (hx₁ : x₁ ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
      (Dw / Real.sqrt Rn))
    (hjσ : j'.castSucc ≤ K.toHistory.activeStage σ)
    (tr : BackwardPointTrace K.toHistory j'.castSucc (K.toHistory.activeStage σ) hjσ x₁)
    (w : (K.stage j'.castSucc).Carrier)
    (hzw : riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v)
      (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt Rn))
    (hRw : Rn ≤ (K.toHistory.event j').incoming.flow.scalar v w) :=
  kswHU_of_pickedCenter_C11PT (Rad := -Dd) (Cg := Cg) (ρ := ρ) (κ := κ) (ε := ε) (C1 := C1)
    (C2 := C2) (Cgrad := Cgrad) hθ₀ hRn
    (by
      have e : Dd + -Dd = 0 := by ring
      rw [e]
      exact pickedCenterNeighborhood_zero_C11PT Dw Tc θ₀ Rn (Cg * Rn) ρ κ ε C1 C2 Cgrad K σ y)
    j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr w hzw hRw

end T1

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
