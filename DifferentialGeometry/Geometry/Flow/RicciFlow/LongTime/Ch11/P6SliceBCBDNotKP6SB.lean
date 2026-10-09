import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDThetaP6SB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.EndpointProtectionC11G

/-!
# 切片 BCBD 的 surgery 避让 `hnotK`（小年龄）⇐ cap 出生时刻的 trace ceiling + 尺度分离
（O-CH11-SLICE-BCBD G4，后缀 `_P6SB`）

G3 把 kernel 帧 `hnotK` 的年龄上界降到 `θ₀/scale`。本文件把小年龄 `hnotK` 归约到两条不含 J10 的输入：
* `hceil`（cap 出生时刻的 trace ceiling）：对每个 cap 配置（event `i`、`yG` 从 `i⁺` 到 `j⁻` 的任意 trace `A`、
  年龄 `≤ θ·scale⁻¹`），`R_out(A(i⁺)) ≤ M`。这里 `R_out` 是 event `i` 的 output metric，即 stage `i⁺` 在
  `time i⁺` 的度量（`stageMetric_succ_time_C11G`）。
* `hsep`（尺度分离，与登记的 (SEP′) 同形，常数不同）：同一配置下 `2·M < scale`。
* 静态 cap 标量下界用树内 `exists_capWindow_scalar_lower_C11G`：canonical window（精度 `≤ ε₀`、阶 `≥ 2`）
  上 `scale/2 ≤ R_out(window x)`（`‖x‖ < modelRadius`）。
主定理 `hnotK_of_capCeiling_P6SB`（PROVED，纯组合）：结论 = G3 `sliceBCBD_kernel_fresh_theta_P6SB` 的
`hnotK` 槽（取 `θ := fun _ => θ₀`）。
**`hceil` 的预定来源（未在本文件做）**：CXJD `scalar_le_two_mul_crossSlab_ceiling_CXJD`，取 `z = y`、
`Cball = 1`、`Qb = max Cg 1`、`a = time i⁺`、`T = c⋆/Qb`，得 `M = 2·Qb·R`。深度条件
`t − time i⁺ ≤ T/R` 由年龄 `≤ θ₀/scale` 加 `R ≤ (T/θ₀)·scale` 给出（又一个 (SEP′) 型分离）。
剩下的工作是 trace 帧搬运、数值（`ℓ, K, hKC, hℓρ, hρL, hnum`），以及 `hprotC` 在 `a = time i⁺` 处的实例。
这样 surgery 避让不再需要全局 `EventSlabsDerivative`（旧 producer `hnotK_of_diagonal_cws_P6SN` 需要它）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **小年龄 `hnotK` ⇐ cap 出生时刻 trace ceiling + 尺度分离（`_P6SB`，PROVED）**：`ε₀` 为
`exists_capWindow_scalar_lower_C11G` 的绝对精度阈值；结论 = kernel 帧 `hnotK`（年龄上界 `θ n·scale⁻¹`）。 -/
theorem hnotK_of_capCeiling_P6SB :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t T₀ : ℕ → ℝ}
      {p : ℕ → CutoffParameters}
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)}
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} {θ M : ℕ → ℝ},
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n, (p n).modelAccuracy ≤ ε₀) → (∀ n, 2 ≤ (p n).modelOrder) →
      (∀ n : ℕ, ((n : ℝ) + 1) + 1 ≤ (p n).modelRadius) →
      (∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        t n - (K n).time i.succ ≤ θ n * (((recordsK n i hi).static b).neck.scale)⁻¹ →
        metricScalarAt ((K n).toHistory.event i).outputMetric (A.point i.succ le_rfl hl) ≤
          M n) →
      (∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (j n).castSucc →
        t n - (K n).time i.succ ≤ θ n * (((recordsK n i hi).static b).neck.scale)⁻¹ →
        2 * M n < ((recordsK n i hi).static b).neck.scale) →
      ∀ n, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          t n - (K n).time i.succ ≤ θ n * (((recordsK n i hi).static b).neck.scale)⁻¹ := by
  obtain ⟨ε₀, hε₀, hlow⟩ := exists_capWindow_scalar_lower_C11G.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro K j t T₀ p recordsK yG θ M hcan hacc hord hrad hceil hsep n
  rintro ⟨i, hi, hl, A, b, x, h1, h2, h3⟩
  have hx : ‖x.val‖ < (p n).modelRadius := lt_of_lt_of_le h2 (hrad n)
  have hS := hlow ((K n).toHistory.event i) (hacc n) (hord n) ((recordsK n i hi).static b)
    (hcan n i hi b) x hx
  rw [← h1] at hS
  have hC := hceil n i hi hl A b h3
  have hP := hsep n i hi b hl h3
  linarith

/-- consumer：主定理（θ 常值 `θ₀`）的结论喂 G3 `hnotK_theta_mono_P6SB`，得到任意更小年龄 `θ₁ ≤ θ₀` 的
`hnotK`（`θ₁` 常值时 = G3 `sliceBCBD_kernel_fresh_theta_P6SB` 的 `hnotK` 槽形）。 -/
example
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t T₀ : ℕ → ℝ}
    {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} {θ₀ θ₁ : ℝ} (h01 : θ₁ ≤ θ₀) {M : ℕ → ℝ}
    (hcan : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n, (p n).modelAccuracy ≤ Classical.choose hnotK_of_capCeiling_P6SB.{u})
    (hord : ∀ n, 2 ≤ (p n).modelOrder)
    (hrad : ∀ n : ℕ, ((n : ℝ) + 1) + 1 ≤ (p n).modelRadius)
    (hceil : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (hl : i.succ ≤ (j n).castSucc)
      (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      metricScalarAt ((K n).toHistory.event i).outputMetric (A.point i.succ le_rfl hl) ≤ M n)
    (hsep : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      2 * M n < ((recordsK n i hi).static b).neck.scale) :
    ∀ n, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (hl : i.succ ≤ (j n).castSucc)
      (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
        ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
        t n - (K n).time i.succ ≤ θ₁ * (((recordsK n i hi).static b).neck.scale)⁻¹ :=
  hnotK_theta_mono_P6SB (θ₁ := fun _ => θ₁) (θ₂ := fun _ => θ₀) (fun _ => h01)
    ((Classical.choose_spec hnotK_of_capCeiling_P6SB.{u}).2 (θ := fun _ => θ₀) hcan hacc hord
      hrad hceil hsep)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
