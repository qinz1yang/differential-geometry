import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CwsUniformP6SN

/-!
# diagonal 参数 `Rn` 抬到 `n + 2`：`hrad2` 由 diagonal 付（O-CH11-SLICE-BCBD2 G2，后缀 `_P6SB2`）

SLICE-BCBD G7 / G8 主定理（`sliceBCBD_kernel_fresh_sep_P6SB` / `…_seq_P6SB`）的 kernel 帧前提
`hrad2 : ∀ n, (n + 1) + 1 ≤ (p n).modelRadius` 比 SEPTN diagonal 包（`cws_uniform_of_diagonal_P6SN`，
`n + 1 ≤ Rn n`）强一格。本文件**不改冻结 kernel 窗口半径**，只把 diagonal 序列 `Rn` 换成
`Rn' n := max (Rn n) ((n + 1) + 1)`：
* `cws_uniform_of_diagonal_rad2_P6SB2`（PROVED）：SN 包逐字，只把 `n + 1 ≤ Rn n` 换成 `(n + 1) + 1 ≤ Rn n`；
* `hnotK_of_diagonal_cws_rad2_P6SB2`（PROVED）：SN consumer 同样孪生；
* `kernelParams_of_diagonal_P6SB2`（PROVED）：diagonal 条件 `accuracy ≤ ζ n`、`Rn n ≤ radius`、
  `m₀ n ≤ order`
  ⇒ G7 的 `hacc / hrad2 / hord` 三个 kernel 槽逐字。
consumer `example`：diagonal 包 ⇒ G7 `hrad2` 槽（类型逐字）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **diagonal 包，`Rn ≥ n + 2` 版（`_P6SB2`，PROVED）**：`cws_uniform_of_diagonal_P6SN` 逐字，只把
`(n + 1) ≤ Rn n` 换成 `(n + 1) + 1 ≤ Rn n`。证明：取 SN 的 `Rn`，令 `Rn' n := max (Rn n) ((n + 1) + 1)`；
`Rn' n ≤ radius ⇒ Rn n ≤ radius`，其余逐字转发。 -/
theorem cws_uniform_of_diagonal_rad2_P6SB2 :
    ∃ c : ℝ, 0 < c ∧ ∀ C : ℝ≥0, ∃ (Cb Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n, 0 < Cb n ∧ Cb n ≤ 1 / ((n : ℝ) + 1) ^ 2) ∧
      (∀ n, 0 < ζ n ∧ ζ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n, 0 < δ₀ n ∧ δ₀ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, ((n : ℝ) + 1) + 1 ≤ Rn n) ∧ (∀ n : ℕ, n + 2 ≤ m₀ n) ∧
      ∀ {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ},
      (∀ n, (K n).time (j n).castSucc < t n) → (∀ n, t n < (K n).time (j n).succ) →
      ∀ {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
        {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
          GeometricCutoffRecord (K n).toHistory i (p n)},
      (∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) → ∀ {a₀ : ℝ},
      (∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ δ₀ n) →
      (∀ n, (p n).modelAccuracy ≤ ζ n) → (∀ n, Rn n ≤ (p n).modelRadius) →
      (∀ n, m₀ n ≤ (p n).modelOrder) →
      (∀ n, (K n).EventSlabsDerivative C (Q n) (Fin.last (K n).eventCount)) →
      (∀ n i hi b, max (Q n) 1 ≤ Cb n * ((recordsK n i hi).static b).neck.scale) →
      (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
      ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc) (z : ((K n).stage (j n).castSucc).Carrier)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl z)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x →
        ‖x.val‖ < ((n : ℝ) + 1) + 1 →
        t n - (K n).time i.succ ≤
          (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹ →
        c * ((recordsK n i hi).static b).neck.scale ≤
          ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z := by
  obtain ⟨c, hc, hall⟩ := cws_uniform_of_diagonal_P6SN.{u}
  refine ⟨c, hc, fun C => ?_⟩
  obtain ⟨Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ, _hRn, hm₀, hdiag⟩ := hall C
  refine ⟨Cb, fun n => max (Rn n) (((n : ℝ) + 1) + 1), ζ, δ₀, m₀, hCb, hζ, hδ,
    fun n => le_max_right _ _, hm₀, ?_⟩
  intro K j t hjt htj Q T₀ p pF recordsK recordsF a₀ hHI hcanK hδF hacc hrad hord hslabK hbirth
    hbirthA
  exact hdiag hjt htj recordsF hHI hcanK hδF hacc
    (fun n => (le_max_left _ _).trans (hrad n)) hord hslabK hbirth hbirthA

/-- **consumer 孪生（`_P6SB2`，PROVED）**：`hnotK_of_diagonal_cws_P6SN` 逐字，diagonal `Rn ≥ n + 2`
（`Rn' := max Rn (n + 2)`，同 G2 主引理做法）。 -/
theorem hnotK_of_diagonal_cws_rad2_P6SB2 :
    ∃ c : ℝ, 0 < c ∧ ∀ C : ℝ≥0, ∃ (Cb Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n, 0 < Cb n ∧ Cb n ≤ 1 / ((n : ℝ) + 1) ^ 2) ∧
      (∀ n, 0 < ζ n ∧ ζ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n, 0 < δ₀ n ∧ δ₀ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, ((n : ℝ) + 1) + 1 ≤ Rn n) ∧ (∀ n : ℕ, n + 2 ≤ m₀ n) ∧
      ∀ {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ},
      (∀ n, (K n).time (j n).castSucc < t n) → (∀ n, t n < (K n).time (j n).succ) →
      ∀ {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
        {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
          GeometricCutoffRecord (K n).toHistory i (p n)},
      (∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) → ∀ {a₀ : ℝ},
      (∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ δ₀ n) →
      (∀ n, (p n).modelAccuracy ≤ ζ n) → (∀ n, Rn n ≤ (p n).modelRadius) →
      (∀ n, m₀ n ≤ (p n).modelOrder) →
      (∀ n, (K n).EventSlabsDerivative C (Q n) (Fin.last (K n).eventCount)) →
      (∀ n i hi b, max (Q n) 1 ≤ Cb n * ((recordsK n i hi).static b).neck.scale) →
      (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
      ∀ {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} {R : ℕ → ℝ},
      (∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (j n).castSucc →
        t n - (K n).time i.succ ≤ (((recordsK n i hi).static b).neck.scale)⁻¹ →
        R n < c * ((recordsK n i hi).static b).neck.scale) →
      ∀ n, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
          (hl : i.succ ≤ (j n).castSucc)
          (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
          (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
          (x : standardCapWindow (p n).modelRadius),
          A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
            ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
            t n - (K n).time i.succ ≤
              (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹ := by
  obtain ⟨c, hc, hall⟩ := hnotK_of_diagonal_cws_P6SN.{u}
  refine ⟨c, hc, fun C => ?_⟩
  obtain ⟨Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ, _hRn, hm₀, hdiag⟩ := hall C
  refine ⟨Cb, fun n => max (Rn n) (((n : ℝ) + 1) + 1), ζ, δ₀, m₀, hCb, hζ, hδ,
    fun n => le_max_right _ _, hm₀, ?_⟩
  intro K j t hjt htj Q T₀ p pF recordsK recordsF a₀ hHI hcanK hδF hacc hrad hord hslabK hbirth
    hbirthA yG R hRn' hsep
  exact hdiag hjt htj recordsF hHI hcanK hδF hacc (fun n => (le_max_left _ _).trans (hrad n)) hord
    hslabK hbirth hbirthA hRn' hsep

/-- **diagonal ⇒ G7 kernel 槽（`_P6SB2`，PROVED）**：`accuracy ≤ ζ n ≤ 1/(n+1)`、
`(n + 1) + 1 ≤ Rn n ≤ radius`、`n + 2 ≤ m₀ n ≤ order` ⇒ `sliceBCBD_kernel_fresh_sep_P6SB` 的
`hacc / hrad2 / hord` 逐字。 -/
theorem kernelParams_of_diagonal_P6SB2 {ζ Rn : ℕ → ℝ} {m₀ : ℕ → ℕ} {p : ℕ → CutoffParameters}
    (hζ : ∀ n, 0 < ζ n ∧ ζ n ≤ 1 / ((n : ℝ) + 1)) (hRn : ∀ n : ℕ, ((n : ℝ) + 1) + 1 ≤ Rn n)
    (hm₀ : ∀ n : ℕ, n + 2 ≤ m₀ n) (hacc : ∀ n, (p n).modelAccuracy ≤ ζ n)
    (hrad : ∀ n, Rn n ≤ (p n).modelRadius) (hord : ∀ n, m₀ n ≤ (p n).modelOrder) :
    (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, ((n : ℝ) + 1) + 1 ≤ (p n).modelRadius) ∧
      (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) :=
  ⟨fun n => (hacc n).trans (hζ n).2, fun n => (hRn n).trans (hrad n),
    fun n => (hm₀ n).trans (hord n)⟩

/-- consumer：diagonal 包（`Rn ≥ n + 2` 版）的参数条件 ⇒ G7 / G8 的 `hrad2` 槽（类型逐字）、`hacc`、`hord`。 -/
example : ∃ c : ℝ, 0 < c ∧ ∀ _ : ℝ≥0, ∃ (ζ Rn : ℕ → ℝ) (m₀ : ℕ → ℕ),
    ∀ p : ℕ → CutoffParameters, (∀ n, (p n).modelAccuracy ≤ ζ n) →
      (∀ n, Rn n ≤ (p n).modelRadius) → (∀ n, m₀ n ≤ (p n).modelOrder) →
      (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) ∧
        (∀ n : ℕ, ((n : ℝ) + 1) + 1 ≤ (p n).modelRadius) ∧
        (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) := by
  obtain ⟨c, hc, hall⟩ := cws_uniform_of_diagonal_rad2_P6SB2.{u}
  refine ⟨c, hc, fun C => ?_⟩
  obtain ⟨_, Rn, ζ, _, m₀, _, hζ, _, hRn, hm₀, _⟩ := hall C
  exact ⟨ζ, Rn, m₀, fun p hacc hrad hord =>
    kernelParams_of_diagonal_P6SB2 hζ hRn hm₀ hacc hrad hord⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
