import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KernelBodyTruncP6KT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HIPropagationP6HP

/-!
# kernel (B) 行 / CXJD 族在 kernel 帧的 body 内来源（O-CH11-KERNB-A6，后缀 `_A6K`）

分析车道 A6 的 PROVED adapter：kernel body（`NotKBodyT_P6KT`）的字段 + 极少的调用点行 ⇒ G9″
（`sliceBCBD_kernel_fresh_sep_noProtC_aligned_P6SB3`）形 CXJD 族与 rings 形 (B) 行的若干分量。
* `hOldX_kernel_A6K` / `hT₀X_zero_A6K`：kernel 帧 `K n : RetainedCoreHistory`，`toHistory` 的
  `old := retainedCore`（RetainedCoreTower 定义）⇒ `T₀X := 0`、`hT₀X`、`hOldX` 无前提；
* `hpin_kernel_A6K`：G9″ `hpin`（年龄 `a₀ + s`）⇐ body `recordsF` / `hHI` + 行 `0 < a₀`；
* `hRa_kernel_A6K`：G9″ `hRa`（`1 ≤ R·aSeed`）⇐ body `hRlt` + 行 `1 ≤ aSeed`；
* `hhalf_of_room_one_A6K` / `hwinF_of_room_one_A6K`：body `hroom` 在 `r := 1`（调用点实参）⇒
  rings `hhalf` 与 G9″ `hwinF`；
* `hfin_ev_of_le_ofReal_A6K`：body `hdistσ` ⇒ `hdσ` / `hfinX` 的 eventually 形；
* `hDm_ev_of_rad_A6K`：body `hrad` ⇒ `hDmX` 的 eventually 形；
* `hsep_of_scaleK_A6K` / `hsepX_of_scaleK_A6K`：body `hscaleK` + 行 `∀ᶠ n, R n ≤ Q n` ⇒
  对全部 kernel records 的 scale 分离（rings `hsepX` 形为推论）。
无新 Prop / 结构 / 合同；无 sorry / axiom。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **`hOldX`（kernel 帧，PROVED）**：`RetainedCoreHistory.toHistory` 的事件 `old` 按定义是
`retainedCore`，故对任意阈值 `T₀X` 成立（G9″ / rings `hOldX` 槽）。 -/
theorem hOldX_kernel_A6K (K : ℕ → RetainedCoreHistory.{u}) (T₀X : ℕ → ℝ) :
    ∀ n (e : Fin (K n).toHistory.eventCount), T₀X n ≤ (K n).toHistory.time e.succ →
      ((K n).toHistory.event e).old = ((K n).toHistory.event e).transition.trace.retainedCore :=
  fun _ _ _ => rfl

/-- **`hT₀X`（`T₀X := 0`，PROVED）**：seed 时刻非负。 -/
theorem hT₀X_zero_A6K {Kh : ℕ → ObservedHistory.{u}} (aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) :
    ∀ n, (fun _ : ℕ => (0 : ℝ)) n ≤ aSeed n :=
  fun n => (aSeed n).2.1

/-- **G9″ `hpin`（PROVED ⇐ body `recordsF` / `hHI` + 行 `0 < a₀`）**：HIPROP 传播。 -/
theorem hpin_kernel_A6K (K : ℕ → RetainedCoreHistory.{u}) {pF : ℕ → CutoffParameters}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) {a₀ : ℕ → ℝ}
    (ha₀ : ∀ n, 0 < a₀ n)
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x) :
    ∀ n (s : Icc (0 : ℝ) (K n).toHistory.horizon) (x : ((K n).toHistory.stageAt s).Carrier),
      InFixedHamiltonIveyRegion
        ((K n).toHistory.stageMetric ((K n).toHistory.activeStage s) s) (a₀ n + s) x :=
  fun n s x =>
    ObservedHistory.hiActive_of_records_P6HP (K n).toHistory (recordsF n) (ha₀ n) (hHI n) s x

/-- **G9″ `hRa`（PROVED ⇐ body `hRlt` + 行 `1 ≤ aSeed`）**。 -/
theorem hRa_kernel_A6K {Kh : ℕ → ObservedHistory.{u}} (aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (R : ℕ → ℝ) (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n) (h1 : ∀ n, 1 ≤ (aSeed n : ℝ)) :
    ∀ n, 1 ≤ R n * aSeed n := fun n => by
  have hR : (1 : ℝ) ≤ R n := by
    have := hRlt n
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  exact one_le_mul_of_one_le_of_one_le hR (h1 n)

/-- **rings `hhalf`（PROVED ⇐ body `hroom` 在 `r := 1`）**。 -/
theorem hhalf_of_room_one_A6K {Kh : ℕ → ObservedHistory.{u}}
    (σ Tn : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (R L : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hroom : ∀ n, (Tn n : ℝ) - (1 : ℝ) ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) :
    ∀ n, (Tn n : ℝ) - 1 ^ 2 / 2 ≤ σ n := fun n => by
  have h0 : 0 ≤ L n ^ 2 / R n := div_nonneg (sq_nonneg _) (hRpos n).le
  linarith [hroom n]

/-- **G9″ `hwinF`（`r = 1`，PROVED ⇐ body `hroom` + `L → ∞`）**。 -/
theorem hwinF_of_room_one_A6K {Kh : ℕ → ObservedHistory.{u}}
    (σ Tn : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (R L : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hL : Tendsto L atTop atTop)
    (hroom : ∀ n, (Tn n : ℝ) - (1 : ℝ) ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) :
    ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - 1 ^ 2 / 2 ≤ (σ n : ℝ) - T / R n := by
  intro T _
  filter_upwards [hL.eventually_ge_atTop (max T 1)] with n hn
  have hL1 : 1 ≤ L n := le_trans (le_max_right _ _) hn
  have hLT : T ≤ L n := le_trans (le_max_left _ _) hn
  have hsq : T ≤ L n ^ 2 := by nlinarith
  have hdiv : T / R n ≤ L n ^ 2 / R n := div_le_div_of_nonneg_right hsq (hRpos n).le
  linarith [hroom n]

/-- **`hdσ` / `hfinX` 的 eventually 形（PROVED ⇐ body `hdistσ`）**：
`d + ofReal a ≤ ofReal b` ⇒ `d ≠ ⊤`。 -/
theorem hfin_ev_of_le_ofReal_A6K {d : ℕ → ℝ≥0∞} {a b : ℕ → ℝ}
    (h : ∀ᶠ n in atTop, d n + ENNReal.ofReal (a n) ≤ ENNReal.ofReal (b n)) :
    ∀ᶠ n in atTop, d n ≠ ⊤ :=
  h.mono fun _ hn => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans le_self_add hn)

/-- **`hDmX` 的 eventually 形（PROVED ⇐ body `hrad`）**。 -/
theorem hDm_ev_of_rad_A6K {p : ℕ → CutoffParameters}
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) :
    ∀ᶠ n in atTop, StandardCap.transitionEnd + 10 < (p n).modelRadius := by
  obtain ⟨N, hN⟩ := exists_nat_gt (StandardCap.transitionEnd + 10)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith [hrad n]

/-- **scale 分离（PROVED ⇐ body `hscaleK` + 行 `∀ᶠ n, R n ≤ Q n`）**：对全部 kernel records
`M·R n < scale`（无时间条件）。 -/
theorem hsep_of_scaleK_A6K {K : ℕ → RetainedCoreHistory.{u}} {T₀ Q : ℕ → ℝ}
    {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hRQ : ∀ᶠ n in atTop, R n ≤ Q n) :
    ∀ M : ℝ, ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
      M * R n < ((recordsK n i hi).static b).neck.scale := by
  intro M
  obtain ⟨N, hN⟩ := exists_nat_gt M
  filter_upwards [hRQ, eventually_ge_atTop N] with n hRQn hn
  intro i hi b
  have hS := hscaleK n i hi b
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hn' : M < (n : ℝ) + 1 := by linarith
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hm1 : (n : ℝ) + 1 ≤ max ((n : ℝ) + 1) (Q n) := le_max_left _ _
  have hmQ : Q n ≤ max ((n : ℝ) + 1) (Q n) := le_max_right _ _
  have hm0 : 0 < max ((n : ℝ) + 1) (Q n) := lt_of_lt_of_le hn0 hm1
  rcases le_or_gt M 0 with hM | hM
  · have hMR : M * R n ≤ 0 := by nlinarith [hRpos n]
    have hpos : 0 < ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) := mul_pos hn0 hm0
    linarith
  · calc M * R n ≤ M * max ((n : ℝ) + 1) (Q n) :=
          mul_le_mul_of_nonneg_left (hRQn.trans hmQ) hM.le
      _ < ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) := mul_lt_mul_of_pos_right hn' hm0
      _ ≤ _ := hS

/-- **rings `hsepX` 形（PROVED，推论）**：时间条件 `aSeed < time i⁺` 下的同一分离。 -/
theorem hsepX_of_scaleK_A6K {K : ℕ → RetainedCoreHistory.{u}} {T₀ Q : ℕ → ℝ}
    {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hRQ : ∀ᶠ n in atTop, R n ≤ Q n) (aS : ℕ → ℝ) :
    ∀ M : ℝ, ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
      aS n < (K n).time i.succ → M * R n < ((recordsK n i hi).static b).neck.scale :=
  fun M => (hsep_of_scaleK_A6K hscaleK R hRpos hRQ M).mono fun _ hn i hi b _ => hn i hi b

/-- consumer：rings 形 `hsepX` 由 adapter 付（`aS := aSeed`）。 -/
example {K : ℕ → RetainedCoreHistory.{u}} {T₀ Q : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hRQ : ∀ᶠ n in atTop, R n ≤ Q n)
    (aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) :
    ∀ M : ℝ, ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
      (aSeed n : ℝ) < (K n).time i.succ → M * R n < ((recordsK n i hi).static b).neck.scale :=
  hsepX_of_scaleK_A6K hscaleK R hRpos hRQ (fun n => aSeed n)

/-- consumer：`T₀X := 0` 三件（`hT₀X` / `hOldX`）在 kernel 帧同时给出。 -/
example (K : ℕ → RetainedCoreHistory.{u})
    (aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) :
    (∀ n, (fun _ : ℕ => (0 : ℝ)) n ≤ aSeed n) ∧
    ∀ n (e : Fin (K n).toHistory.eventCount),
      (fun _ : ℕ => (0 : ℝ)) n ≤ (K n).toHistory.time e.succ →
      ((K n).toHistory.event e).old = ((K n).toHistory.event e).transition.trace.retainedCore :=
  ⟨hT₀X_zero_A6K aSeed, hOldX_kernel_A6K K _⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
