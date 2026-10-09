import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TerminalBCDKernelP6BT

/-!
# BCDT 局域化的 K 层 kernel（O-CH11-FOOT3 G1，后缀 `_P6F3`；R-C11-15 D-7）

R-C11-15 Q3 §2/§3：BCDT `hlocBCD_of_supplies_P6BT` 的 `hkappa`（全 incoming slab、所有中心）与
`hderiv`（全局 `EventSlabsDerivative` / `DerivativeBoundBefore` / `GradientBoundBefore`）是
**全域** supply，与实际所需的局域数据错位。本文件把两层全域化撤回：
* P6WB `exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal_window_P6WB` 本身已是局域
  合同（κ：`z ∈ U`、`τ ∈ [t − Bw/R, t]`；`hslabs` / `hder` / `hgrad`：U 点 / U 出发的 backward trace、
  窗口 guard、阈值 `q`）。全域化只发生在 P6LS3（`EventSlabsDerivative` + `DerivativeBoundBefore`）
  与 BCDT kernel（κ 全 slab 全中心、`GradientBoundBefore`）。
* **`RetainedCoreHistory.slice_scalar_bound_localDeriv_P6F3`**：P6LS3
  `slice_scalar_bound_of_not_capWindowPoint_window_pinch_P6LS3` 的副本，导数前提换回 P6WB 局域形：
  早先 slab 只沿 **U 出发的 backward trace**、窗口 `v − Bw/R(v, w) ≤ v′`、阈值 `q < R` 处要求
  `|∂ₜR| ≤ Ctime·R²`（prefix 搬运 = `backwardPointTraceOfPrefix`）；当前 slab 只在 `x ∈ U`、同窗口、
  同阈值处要求。κ / 梯度沿用 P6LS3 已有的局域形。结论逐字同 P6LS3。
* **`RetainedCoreHistory.terminal_scalar_bound_local_P6F3`**：BCDT terminal kernel
  `terminal_scalar_bound_P6BT` 的局域版：κ / `∂ₜR`（早先 slab 沿 trace + 当前 slab）/ `∇R` 只在
  `∀ᶠ t → s⁻`、`U_t = B_t(x, 2·Rad/√R_k)`、`τ, v′ ∈ [t − 3·Bw/R_k, t]`、阈值 `q` 上要求；不再要求
  `qd`（阈值直接用 `q`）。结论逐字同 `terminal_scalar_bound_P6BT`（`B_ḡ(x, A/√R_k)` 上 `R_ḡ ≤ 2Q·R_k`）。
非循环：只 import BCDT kernel（P6LS3 / P6WB 链）；不含 HU / hclosG / hscalU / CanonicalLateCore / hspine。
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

/-- **非 CWP 分支（单切片，K 层，局域导数，`_P6F3`）**：P6LS3
`slice_scalar_bound_of_not_capWindowPoint_window_pinch_P6LS3` 的副本；全局
`K.EventSlabsDerivative Ctime qd j.castSucc` + `DerivativeBoundBefore Ctime qd v` 换成 P6WB 的局域形：
早先 slab `i`（`i⁻ < j⁻`）只沿 **U 出发的 backward trace** `B : first → j⁻`、窗口
`v − Bw/R(v, w) ≤ v′`、阈值 `q < R` 处要求 `|∂ₜR| ≤ Ctime·R²`；当前 slab 只在 `x ∈ U`、同窗口、
同阈值处要求。结论逐字同 P6LS3。 -/
theorem RetainedCoreHistory.slice_scalar_bound_localDeriv_P6F3
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) (A : ℝ) (hA : 0 < A)
    (Cq : ℝ) :
    ∃ Q Λ Dcap Rrad ζ₀ Rad Bw : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧
    Dcap ≤ Rrad ∧ 0 < ζ₀ ∧ 0 < Bw ∧
    ∀ (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount) {p : CutoffParameters} (T₀ : ℝ)
      (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
        GeometricCutoffRecord K.toHistory i p),
      (∀ i hT b, ((records i hT).static b).hasCanonicalWindow) →
      Rrad ≤ p.modelRadius → 2 ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
      (∀ i : Fin K.eventCount, Perelman.PhiAlmostNonnegative
        (K.toHistory.event i).incoming.flow
        (Ico (K.time i.castSucc) (K.time i.succ) ∩ Ici T₀) phi) →
    ∀ (v : ℝ), K.time j.castSucc < v → v < K.time j.succ →
    ∀ (w : (K.stage j.castSucc).Carrier) (q ρ : ℝ),
      T₀ ≤ v - Bw / (K.toHistory.event j).incoming.flow.scalar v w →
      0 < q → q ≤ Cq * (K.toHistory.event j).incoming.flow.scalar v w →
      Λ ≤ (K.toHistory.event j).incoming.flow.scalar v w →
      Λ ≤ (K.toHistory.event j).incoming.flow.scalar v w * v →
      Λ ≤ ρ * Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w) →
    ∀ U : Set (K.stage j.castSucc).Carrier,
      (∀ x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
        (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)), x ∈ U) →
      (∀ x ∈ U, q < (K.toHistory.event j).incoming.flow.scalar v x →
        ∃ W : SpatialCanonicalWitness ((K.toHistory.event j).incoming.flow.base.metric v)
          ε C1 C2 x, W.capTubeHasNeckChart ε) →
      (∀ (first : Fin (K.eventCount + 1)) (hfl : first ≤ j.castSucc),
        ∀ z ∈ U, ∀ (B : BackwardPointTrace K.toHistory first j.castSucc hfl z)
          (i : Fin K.eventCount) (hf : first ≤ i.castSucc) (hij : i.castSucc < j.castSucc),
        ∀ v' ∈ Ioo (K.time i.castSucc) (K.time i.succ),
          v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
          q < (K.toHistory.event i).incoming.flow.scalar v' (B.point i.castSucc hf hij.le) →
          |derivWithin (fun w' => (K.toHistory.event i).incoming.flow.scalar w'
              (B.point i.castSucc hf hij.le)) (Iic v') v'| ≤
            Ctime * (K.toHistory.event i).incoming.flow.scalar v'
              (B.point i.castSucc hf hij.le) ^ 2) →
      (∀ x ∈ U, ∀ v' ∈ Ioo (K.time j.castSucc) v,
        v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
        q < (K.toHistory.event j).incoming.flow.scalar v' x →
        |derivWithin (fun w' => (K.toHistory.event j).incoming.flow.scalar w' x) (Iic v') v'| ≤
          Ctime * (K.toHistory.event j).incoming.flow.scalar v' x ^ 2) →
      (∀ x ∈ U, ∀ v' ∈ Ioo (K.time j.castSucc) v,
        v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
        q < (K.toHistory.event j).incoming.flow.scalar v' x →
        ∀ ξ : TangentSpace ThreeModel x,
          |scalarDifferential (K.toHistory.event j).incoming.flow v' x ξ| ≤
            Cgrad * (K.toHistory.event j).incoming.flow.scalar v' x *
              Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v' x) *
              Real.sqrt (((K.toHistory.event j).incoming.flow.base.metric v').inner x ξ ξ)) →
      (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
        v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
        K.time j.castSucc < τ → (τ : ℝ) < K.time j.succ →
        ∀ z ∈ U, ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
              (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
              (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b)) →
      (¬ ∃ (i : Fin K.eventCount) (hT : T₀ ≤ K.time i.succ) (hl : i.succ ≤ j.castSucc)
        (B : BackwardPointTrace K.toHistory i.succ j.castSucc hl w)
        (b : (K.toHistory.event i).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
        B.point i.succ le_rfl hl = ((records i hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
          v - K.time i.succ ≤ 1 / 2 * (((records i hT).static b).neck.scale)⁻¹) →
      ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
          (A / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
        (K.toHistory.event j).incoming.flow.scalar v z ≤
          Q * (K.toHistory.event j).incoming.flow.scalar v w := by
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, hQ, hΛ, hD, hDR, hζ₀, hBw, hmain⟩ :=
    RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal_window_P6WB
      hεle κ C1 C2 hκ Ctime Cgrad hphi A hA Cq (1 / 2) (by norm_num)
  refine ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, hQ, hΛ, hD, hDR, hζ₀, hBw, ?_⟩
  intro K j p T₀ records hcan hR hord hacc hpinch v hv1 hv2 w q ρ hT₀ hq hqC hΛR hΛt hΛρ U hU hW
    hslabL hderL hgrad hnc hnot
  have hncB := K.tested_noncollapse_eventPrefix_P6M j (κ := κ) (ρ := ρ)
    (a := v - Bw / (K.toHistory.event j).incoming.flow.scalar v w) (t := v) U hnc
    (K.prefixAt_time_last _)
  exact hmain (K.prefixAt j.castSucc) (K.prefixAt_time_last _) (K.toHistory.event j).incoming
    (K.event_initial j) hv1 hv2 w q ρ hq hqC hΛR hΛt
    T₀ hT₀ (fun i hT => K.geometricCutoffRecordOfPrefix j.castSucc
      (records (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i) hT))
    (fun i hT b => hcan (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i) hT b) hR hord hacc U hU
    hW
    (fun i first hf z hz Btr v' hv' hwin hRv' =>
      hslabL _ _ z hz (K.backwardPointTraceOfPrefix j.castSucc Btr)
        (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i)
        (Fin.le_def.mpr (Fin.le_def.mp hf)) (Fin.lt_def.mpr i.isLt) v' hv' hwin hRv')
    (fun x hx v' hv' hwin hRv' => hderL x hx v' hv' hwin hRv') hgrad
    (fun i v' hv' ξ => hpinch (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i) v'
      ⟨hv'.1, hT₀.trans hv'.2⟩ ξ)
    (fun v' hv' ξ => hpinch j v' ⟨hv'.1, hT₀.trans hv'.2⟩ ξ) hncB hΛρ
    (by
      rintro ⟨i, hT, hl, Btr, b, x, h1, h2, h3⟩
      exact hnot ⟨Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i, hT,
        Fin.le_def.mpr (Fin.le_def.mp hl), K.backwardPointTraceOfPrefix j.castSucc Btr, b, x, h1,
        h2, h3⟩)

/-- `√a ≤ 2√b`（`a ≤ 4b`；BCDT 私有引理的副本）。 -/
private theorem sqrt_le_two_mul_sqrt_P6F3 {a b : ℝ} (h : a ≤ 4 * b) :
    Real.sqrt a ≤ 2 * Real.sqrt b := by
  have h4 : Real.sqrt (4 * b) = 2 * Real.sqrt b := by
    rw [Real.sqrt_mul (by norm_num) b, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [← h4]
  exact Real.sqrt_le_sqrt h

/-- **terminal kernel 局域版（`_P6F3`）**：`terminal_scalar_bound_P6BT` 的副本，κ / `∂ₜR` / `∇R` 只在
`∀ᶠ t → s⁻`（`s = time j.succ`）、`U_t = B_t(x, 2·Rad/√R_k)`、时间 `∈ [t − 3·Bw/R_k, t]`、阈值 `q`
上要求：
* `hslabL`：早先 slab `i`（`i⁻ < j⁻`）沿 U_t 点出发的 backward trace，`|∂ₜR| ≤ Cder·R²`；
* `hderL`：当前 slab、`z ∈ U_t`，`|∂ₜR| ≤ Cder·R²`；
* `hgradL`：当前 slab、`z ∈ U_t`，`|∇R| ≤ Cgrad·R^{3/2}`；
* `hkappaL`：`τ ∈ [t − 3Bw/R_k, t] ∩ slab`、中心 `z ∈ U_t`（`HEq zz z`）、`0 < b ≤ ρ` 的 tested κ。
不再要求 `qd`。结论逐字同 BCDT kernel。 -/
theorem RetainedCoreHistory.terminal_scalar_bound_local_P6F3 {ε : ℝ}
    (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ)
    (hκ : 0 < κ) (Cder Cgrad : ℝ≥0) {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (A : ℝ) (hA : 0 < A) (Cq : ℝ) :
    ∃ Q Λ Dcap Rrad ζ₀ Rad Bw : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ 0 < ζ₀ ∧ 0 < Bw ∧
    ∀ (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount) {p : CutoffParameters} (T₀ : ℝ)
      (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
        GeometricCutoffRecord K.toHistory i p),
      (∀ i hT b, ((records i hT).static b).hasCanonicalWindow) →
      Rrad ≤ p.modelRadius → 2 ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
      (∀ i : Fin K.eventCount, Perelman.PhiAlmostNonnegative
        (K.toHistory.event i).incoming.flow (Ico (K.time i.castSucc) (K.time i.succ)) phi) →
    ∀ (x : (K.toHistory.event j).incoming.terminalRegularOpen) (Rk q ρ : ℝ),
      metricScalarAt (K.toHistory.event j).terminal.metric x = Rk → 0 < Rk →
      0 < q → q ≤ Cq * Rk →
      2 * Λ ≤ Rk → 4 * Λ ≤ Rk * K.time j.succ → 2 * Λ ≤ ρ * Real.sqrt Rk →
      T₀ ≤ K.time j.succ - 3 * Bw / Rk →
      (∀ᶠ t in 𝓝[<] K.time j.succ,
        ∀ (first : Fin (K.eventCount + 1)) (hfl : first ≤ j.castSucc),
        ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric t) x.1
            (2 * Rad / Real.sqrt Rk),
        ∀ (B : BackwardPointTrace K.toHistory first j.castSucc hfl z)
          (i : Fin K.eventCount) (hf : first ≤ i.castSucc) (hij : i.castSucc < j.castSucc),
        ∀ v' ∈ Ioo (K.time i.castSucc) (K.time i.succ), t - 3 * Bw / Rk ≤ v' →
          q < (K.toHistory.event i).incoming.flow.scalar v' (B.point i.castSucc hf hij.le) →
          |derivWithin (fun w' => (K.toHistory.event i).incoming.flow.scalar w'
              (B.point i.castSucc hf hij.le)) (Iic v') v'| ≤
            Cder * (K.toHistory.event i).incoming.flow.scalar v'
              (B.point i.castSucc hf hij.le) ^ 2) →
      (∀ᶠ t in 𝓝[<] K.time j.succ,
        ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric t) x.1
            (2 * Rad / Real.sqrt Rk),
        ∀ v' ∈ Ioo (K.time j.castSucc) t, t - 3 * Bw / Rk ≤ v' →
          q < (K.toHistory.event j).incoming.flow.scalar v' z →
          |derivWithin (fun w' => (K.toHistory.event j).incoming.flow.scalar w' z) (Iic v') v'| ≤
            Cder * (K.toHistory.event j).incoming.flow.scalar v' z ^ 2) →
      (∀ᶠ t in 𝓝[<] K.time j.succ,
        ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric t) x.1
            (2 * Rad / Real.sqrt Rk),
        ∀ v' ∈ Ioo (K.time j.castSucc) t, t - 3 * Bw / Rk ≤ v' →
          q < (K.toHistory.event j).incoming.flow.scalar v' z →
          ∀ ξ : TangentSpace ThreeModel z,
            |scalarDifferential (K.toHistory.event j).incoming.flow v' z ξ| ≤
              Cgrad * (K.toHistory.event j).incoming.flow.scalar v' z *
                Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v' z) *
                Real.sqrt (((K.toHistory.event j).incoming.flow.base.metric v').inner z ξ ξ)) →
      (∀ᶠ t in 𝓝[<] K.time j.succ, ∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
        t - 3 * Bw / Rk ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        K.time j.castSucc < τ → (τ : ℝ) < K.time j.succ →
        ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric t) x.1
            (2 * Rad / Real.sqrt Rk),
        ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
              (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
              (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b)) →
      (∀ᶠ t in 𝓝[<] K.time j.succ, ∀ x' : (K.stage j.castSucc).Carrier,
        riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric t) x.1 x' <
            ENNReal.ofReal (2 * Rad / Real.sqrt Rk) →
        q < (K.toHistory.event j).incoming.flow.scalar t x' →
        ∃ W : SpatialCanonicalWitness ((K.toHistory.event j).incoming.flow.base.metric t)
          ε C1 C2 x', W.capTubeHasNeckChart ε) →
      (∀ᶠ t in 𝓝[<] K.time j.succ, ¬ ∃ (i : Fin K.eventCount) (hT : T₀ ≤ K.time i.succ)
        (hl : i.succ ≤ j.castSucc) (B : BackwardPointTrace K.toHistory i.succ j.castSucc hl x.1)
        (b : (K.toHistory.event i).RetainedBoundaryIndex) (w : standardCapWindow p.modelRadius),
        B.point i.succ le_rfl hl = ((records i hT).static b).window w ∧ ‖w.val‖ < Dcap + 1 ∧
          t - K.time i.succ ≤ 1 / 2 * (((records i hT).static b).neck.scale)⁻¹) →
      ∀ z ∈ riemannianBallOf (K.toHistory.event j).terminal.metric x (A / Real.sqrt Rk),
        metricScalarAt (K.toHistory.event j).terminal.metric z ≤ 2 * Q * Rk := by
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, hQ, hΛ, -, -, hζ₀, hBw, hmain⟩ :=
    RetainedCoreHistory.slice_scalar_bound_localDeriv_P6F3 hεle κ C1 C2 hκ Cder Cgrad hphi
      (2 * A) (by positivity) (2 * Cq)
  refine ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, hQ, hΛ, hζ₀, hBw, ?_⟩
  intro K j p T₀ records hcan hRr hord hacc hpinch x Rk q ρ hRx hRk hq hqC hΛR hΛt hΛρ
    hT₀ hslabE hderE hgradE hncE hW hnot z hz
  have hs : K.time j.castSucc < K.time j.succ := K.time_strictMono Fin.castSucc_lt_succ
  have hs0 : 0 < K.time j.succ := by
    by_contra hneg
    have : Rk * K.time j.succ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hRk.le (not_lt.mp hneg)
    linarith
  have hBR : 0 < Bw / Rk := div_pos hBw hRk
  have hxlim := (K.toHistory.event j).terminal.tendsto_metricScalarAt x
  rw [hRx] at hxlim
  have hxev := hxlim (Ioo_mem_nhds (show Rk / 2 < Rk by linarith) (show Rk < 2 * Rk by linarith))
  apply le_of_tendsto ((K.toHistory.event j).terminal.tendsto_metricScalarAt z)
  filter_upwards [Ioo_mem_nhdsLT hs,
    Ioo_mem_nhdsLT (show K.time j.succ / 2 < K.time j.succ by linarith),
    Ioo_mem_nhdsLT (show K.time j.succ - Bw / Rk < K.time j.succ by linarith), hxev,
    (K.toHistory.event j).terminal.eventually_riemannianEDistOf_lt x z hz, hW, hnot,
    hslabE, hderE, hgradE, hncE]
    with t ht1 ht2 ht3 hRt hdt hWt hnott hslt hdert hgradt hnct
  have hRt' : Rk / 2 < (K.toHistory.event j).incoming.flow.scalar t x.1 ∧
      (K.toHistory.event j).incoming.flow.scalar t x.1 < 2 * Rk := hRt
  set Rt := (K.toHistory.event j).incoming.flow.scalar t x.1 with hRtdef
  have hRt0 : 0 < Rt := by linarith [hRt'.1]
  have hsRt : 0 < Real.sqrt Rt := Real.sqrt_pos.mpr hRt0
  have hsRk : 0 < Real.sqrt Rk := Real.sqrt_pos.mpr hRk
  have hkt : Real.sqrt Rk ≤ 2 * Real.sqrt Rt :=
    sqrt_le_two_mul_sqrt_P6F3 (by linarith [hRt'.1])
  have htk : Real.sqrt Rt ≤ 2 * Real.sqrt Rk :=
    sqrt_le_two_mul_sqrt_P6F3 (by linarith [hRt'.2])
  have hpinchW : ∀ i : Fin K.eventCount, Perelman.PhiAlmostNonnegative
      (K.toHistory.event i).incoming.flow
      (Ico (K.time i.castSucc) (K.time i.succ) ∩ Ici T₀) phi :=
    fun i t' ht' => hpinch i t' ht'.1
  have hBt : Bw / Rt ≤ 2 * Bw / Rk := by
    rw [div_le_div_iff₀ hRt0 hRk]
    nlinarith [hRt'.1]
  have h3B : 3 * Bw / Rk = Bw / Rk + 2 * Bw / Rk := by ring
  have hT₀t : T₀ ≤ t - Bw / Rt := by
    linarith [ht3.1]
  have hwinT : t - 3 * Bw / Rk ≤ t - Bw / Rt := by
    linarith
  have hCq : 0 ≤ Cq := by
    by_contra hneg
    have : Cq * Rk < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) hRk
    linarith
  have hqC' : q ≤ 2 * Cq * Rt := by
    nlinarith [mul_le_mul_of_nonneg_left hRt'.1.le hCq]
  have hΛt' : Λ ≤ Rt * t := by
    have h1 : Rk / 2 * (K.time j.succ / 2) ≤ Rt * t :=
      mul_le_mul hRt'.1.le ht2.1.le (by linarith) hRt0.le
    nlinarith
  have hρ0 : 0 < ρ := by
    by_contra hneg
    have : ρ * Real.sqrt Rk ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) hsRk.le
    linarith
  have hΛρ' : Λ ≤ ρ * Real.sqrt Rt := by
    have : ρ * Real.sqrt Rk ≤ ρ * (2 * Real.sqrt Rt) := mul_le_mul_of_nonneg_left hkt hρ0.le
    nlinarith
  have hU : ∀ w ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric t) x.1
      (Rad / Real.sqrt Rt), w ∈ riemannianBallOf
        ((K.toHistory.event j).incoming.flow.base.metric t) x.1 (2 * Rad / Real.sqrt Rk) := by
    intro w hw
    rcases le_or_gt 0 Rad with hRad | hRad
    · refine lt_of_lt_of_le hw (ENNReal.ofReal_le_ofReal ?_)
      rw [div_le_div_iff₀ hsRt hsRk]
      nlinarith [mul_le_mul_of_nonneg_left hkt hRad]
    · have h0 : ENNReal.ofReal (Rad / Real.sqrt Rt) = 0 :=
        ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg hRad.le hsRt.le)
      have hw' : riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric t) x.1 w <
          ENNReal.ofReal (Rad / Real.sqrt Rt) := hw
      rw [h0] at hw'
      exact absurd hw' (not_lt_zero)
  have hzt : z.1 ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric t) x.1
      (2 * A / Real.sqrt Rt) := by
    refine lt_of_lt_of_le hdt (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_div_iff₀ hsRk hsRt]
    nlinarith [mul_le_mul_of_nonneg_left htk hA.le]
  have hb := hmain K j T₀ records hcan hRr hord hacc hpinchW t ht1.1 ht1.2 x.1 q ρ hT₀t hq hqC'
    (by linarith [hRt'.1]) hΛt' hΛρ'
    (riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric t) x.1
      (2 * Rad / Real.sqrt Rk)) hU
    (fun w hw hqw => hWt w hw hqw)
    (fun first hfl z' hz' B i hf hij v' hv' hwin hqv =>
      hslt first hfl z' hz' B i hf hij v' hv' (hwinT.trans hwin) hqv)
    (fun z' hz' v' hv' hwin hqv => hdert z' hz' v' hv' (hwinT.trans hwin) hqv)
    (fun z' hz' v' hv' hwin hqv ξ => hgradt z' hz' v' hv' (hwinT.trans hwin) hqv ξ)
    (fun τ hτ1 hτ2 hτ3 hτ4 z' hz' zz hzz b hb0 hbρ hctrl =>
      hnct τ (hwinT.trans hτ1) hτ2 hτ3 hτ4 z' hz' zz hzz b hb0 hbρ hctrl)
    hnott z.1 hzt
  change (K.toHistory.event j).incoming.flow.scalar t z.1 ≤ 2 * Q * Rk
  have hQ0 : 0 ≤ Q := by linarith
  calc (K.toHistory.event j).incoming.flow.scalar t z.1 ≤ Q * Rt := hb
    _ ≤ Q * (2 * Rk) := mul_le_mul_of_nonneg_left hRt'.2.le hQ0
    _ = 2 * Q * Rk := by ring

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
