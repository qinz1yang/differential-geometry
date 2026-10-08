import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CwsUniformP6SN

/-!
# final 版 diagonal (CWS) producer：cap-window 步的 `hnotK` final 孪生（O-CH11-FINCOND G3，后缀 `_P6FC`）

SEPTN G3 `cws_uniform_of_diagonal_P6SN` / `hnotK_of_diagonal_cws_P6SN` 只陈述 event-interior 坏点
（`time (j n).castSucc < t n < time (j n).succ`）。final 侧合同（`hgapJF` / `hgapJF_cond` /
`hgapJF_condW`）的 cap-window 合取项是常数无关的 `¬∃` 形（坏点 `σ` 在 final slab：
`time last < t < horizon`，trace 终点 stage `Fin.last`），需 final 孪生：
* `cws_uniform_of_diagonal_final_P6FC`：树内 `exists_scalar_lower_bound_of_cap_window_trace_late_P6LL`
  对 stage `k`、incoming slab `Gk` 泛型，取 `k := Fin.last`、`s := horizon`、
  `Gk := (finalSlab _).restrictIncoming …`（`final_initial`）。**与 event 版共用同一 diagonal 序列**
  `Cb Rn ζ δ₀ m₀`（同一 `choose`，联合陈述 event ∧ final），因而 jointD 已选的 diagonal 参数同时服务 final 支。
* `hnotK_of_diagonal_cws_final_P6FC`：diagonal 包 + final (SEP′) `hsepF`（`η := c`）⇒ final 版 `hnotK`
  （结论 = `hgapJF` 的 cap-window 合取项在 `t = σ`、`yG' = yG` 处的形）。
**Ccap(η₁)**：本 producer 只用标准解统一标量下界 `c`（与 `n`、常数 `C1 C2` 无关），cap-window 步在坏点精度
`η₁` 处是空真反驳（`¬∃`），不产生 cap witness ⇒ **不需要** `Ccap(η₁)` / `2·Ccap(ηf)` / `1000·Ccap(ηf)` 项
（CEIL2 watch W1 不触发）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **(CWS) 统一 `η` 的 diagonal 版，event ∧ final（`_P6FC`）**：`cws_uniform_of_diagonal_P6SN` 的联合版——
同一 `c > 0` 与同一序列 `Cb Rn ζ δ₀ m₀`（只依赖 `(C, n)`），event 支结论逐字 = SN 版；final 支：坏点
`time last < t < horizon`，trace 终点 stage `Fin.last`，标量取在 final slab `G n`（形状等式 `hG`）上，导数界
`hderF`（`G n` 在 `horizon` 前，阈值 `Q n`）。 -/
theorem cws_uniform_of_diagonal_final_P6FC :
    ∃ c : ℝ, 0 < c ∧ ∀ C : ℝ≥0, ∃ (Cb Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n, 0 < Cb n ∧ Cb n ≤ 1 / ((n : ℝ) + 1) ^ 2) ∧
      (∀ n, 0 < ζ n ∧ ζ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n, 0 < δ₀ n ∧ δ₀ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ Rn n) ∧ (∀ n : ℕ, n + 2 ≤ m₀ n) ∧
      (∀ {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ},
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
          ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) ∧
      (∀ {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ}
        (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n)
        (htK : ∀ n, t n < (K n).horizon)
        {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
          ((K n).time (Fin.last (K n).eventCount)) (K n).horizon},
        (∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
          ((htl n).trans (htK n)) le_rfl) →
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
      (∀ n, (G n).DerivativeBoundBefore C (Q n) (K n).horizon) →
      (∀ n i hi b, max (Q n) 1 ≤ Cb n * ((recordsK n i hi).static b).neck.scale) →
      (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
      ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ Fin.last (K n).eventCount)
        (z : ((K n).stage (Fin.last (K n).eventCount)).Carrier)
        (A : BackwardPointTrace (K n).toHistory i.succ (Fin.last (K n).eventCount) hl z)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x →
        ‖x.val‖ < ((n : ℝ) + 1) + 1 →
        t n - (K n).time i.succ ≤
          (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹ →
        c * ((recordsK n i hi).static b).neck.scale ≤ (G n).flow.scalar (t n) z) := by
  obtain ⟨c, hc, hB⟩ :=
    RetainedCoreHistory.exists_scalar_lower_bound_of_cap_window_trace_late_P6LL.{u}
  refine ⟨c, hc, fun C => ?_⟩
  have hθ0 : ∀ n : ℕ, 0 < 1 - 1 / ((n : ℝ) + 2) := fun n => by
    have : (1 : ℝ) / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    linarith
  have hθ1 : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) < 1 := fun n => by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  choose Cb hCb h2 using fun n : ℕ => hB (1 - 1 / ((n : ℝ) + 2)) (hθ0 n) (hθ1 n) C
  choose Rn hRn m₀ hm₀ ζ δ₀ hζ hζh hδ h4 using fun n : ℕ => h2 n ((n : ℝ) + 1) (by positivity)
  refine ⟨fun n => min (Cb n) (1 / ((n : ℝ) + 1) ^ 2), fun n => max (Rn n) ((n : ℝ) + 1),
    fun n => min (ζ n) (1 / ((n : ℝ) + 1)), fun n => min (δ₀ n) (1 / ((n : ℝ) + 1)),
    fun n => max (m₀ n) (n + 2), fun n => ⟨lt_min (hCb n) (by positivity), min_le_right _ _⟩,
    fun n => ⟨lt_min (hζ n) (by positivity), min_le_right _ _⟩,
    fun n => ⟨lt_min (hδ n) (by positivity), min_le_right _ _⟩,
    fun n => le_max_right _ _, fun n => le_max_right _ _, ?_, ?_⟩
  · -- event 支：SN 版证明逐字
    intro K j t hjt htj Q T₀ p pF recordsK recordsF a₀ hHI hcanK hδF hacc hrad hord hslabK hbirth
      hbirthA n i hi hl z A b x hx hxn hage
    set q := ((recordsK n i hi).static b).neck.scale with hqdef
    have hq : 0 < q := ((recordsK n i hi).static b).neck.scale_pos
    have hjc : (K n).time i.succ ≤ (K n).time (j n).castSucc := (K n).time_strictMono.monotone hl
    have hage0 : 0 ≤ t n - (K n).time i.succ := by linarith [hjt n]
    have hqage : q * (t n - (K n).time i.succ) ≤ 1 - 1 / ((n : ℝ) + 2) := by
      have h1 := mul_le_mul_of_nonneg_left hage hq.le
      rwa [show q * ((1 - 1 / ((n : ℝ) + 2)) * q⁻¹) = 1 - 1 / ((n : ℝ) + 2) by
        field_simp] at h1
    have hqcan : 0 < max (Q n) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hder : (K n).EventSlabsDerivative C (max (Q n) 1) (j n).castSucc :=
      fun j' hj' => derivativeBoundBefore_mono_qcan_P6SN _ (le_max_left _ _)
        (hslabK n j' (hj'.trans_le (Fin.le_last _)))
    have hcur : ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore C (max (Q n) 1)
        (t n) :=
      ((K n).toHistory.event (j n)).incoming.derivativeBoundBefore_mono (htj n).le
        (derivativeBoundBefore_mono_qcan_P6SN _ (le_max_left _ _)
          (hslabK n (j n) (Fin.castSucc_lt_last (j n))))
    have hbirth' : max (Q n) 1 ≤ Cb n * q :=
      (hbirth n i hi b).trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hq.le)
    have hmain := h4 n (K n) (recordsK n) (hcanK n) ((le_max_left _ _).trans (hrad n))
      (le_trans (le_max_left _ _) (hord n)) ((hacc n).trans (min_le_left _ _)) (recordsF n)
      (δ₀ n) (fun i' hi' => (hδF n i' hi').trans (min_le_left _ _)) le_rfl (max (Q n) 1) a₀
      (1 - 1 / ((n : ℝ) + 2)) hqcan le_rfl (fun x => (hHI n x).1) (fun x => (hHI n x).2)
      (j n).castSucc ((K n).time (j n).succ) ((K n).toHistory.event (j n)).incoming
      ((K n).event_initial (j n)) hder (t n) (hjt n) (htj n) hcur i hi hl z A b x hx hage hxn
      hbirth' (hbirthA n i hi b)
    exact scalar_ge_of_age_factor_P6SN hc hq hage0
      (lt_of_le_of_lt hqage (hθ1 n)) hmain
  · -- final 支：`k := Fin.last`、`s := horizon`、`Gk := G n`
    intro K t htl htK G hG Q T₀ p pF recordsK recordsF a₀ hHI hcanK hδF hacc hrad hord hslabK hderF
      hbirth hbirthA n i hi hl z A b x hx hxn hage
    set q := ((recordsK n i hi).static b).neck.scale with hqdef
    have hq : 0 < q := ((recordsK n i hi).static b).neck.scale_pos
    have hjc : (K n).time i.succ ≤ (K n).time (Fin.last (K n).eventCount) :=
      (K n).time_strictMono.monotone hl
    have hage0 : 0 ≤ t n - (K n).time i.succ := by linarith [htl n]
    have hqage : q * (t n - (K n).time i.succ) ≤ 1 - 1 / ((n : ℝ) + 2) := by
      have h1 := mul_le_mul_of_nonneg_left hage hq.le
      rwa [show q * ((1 - 1 / ((n : ℝ) + 2)) * q⁻¹) = 1 - 1 / ((n : ℝ) + 2) by
        field_simp] at h1
    have hqcan : 0 < max (Q n) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hder : (K n).EventSlabsDerivative C (max (Q n) 1) (Fin.last (K n).eventCount) :=
      fun j' hj' => derivativeBoundBefore_mono_qcan_P6SN _ (le_max_left _ _) (hslabK n j' hj')
    have hcur : (G n).DerivativeBoundBefore C (max (Q n) 1) (t n) :=
      (G n).derivativeBoundBefore_mono (htK n).le
        (derivativeBoundBefore_mono_qcan_P6SN _ (le_max_left _ _) (hderF n))
    have hGi : (G n).flow.base.metric ((K n).time (Fin.last (K n).eventCount)) =
        (K n).initialMetric (Fin.last (K n).eventCount) := by
      rw [hG n]
      exact (K n).final_initial ((htl n).trans (htK n))
    have hbirth' : max (Q n) 1 ≤ Cb n * q :=
      (hbirth n i hi b).trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hq.le)
    have hmain := h4 n (K n) (recordsK n) (hcanK n) ((le_max_left _ _).trans (hrad n))
      (le_trans (le_max_left _ _) (hord n)) ((hacc n).trans (min_le_left _ _)) (recordsF n)
      (δ₀ n) (fun i' hi' => (hδF n i' hi').trans (min_le_left _ _)) le_rfl (max (Q n) 1) a₀
      (1 - 1 / ((n : ℝ) + 2)) hqcan le_rfl (fun x => (hHI n x).1) (fun x => (hHI n x).2)
      (Fin.last (K n).eventCount) (K n).horizon (G n) hGi hder (t n) (htl n) (htK n) hcur i hi hl
      z A b x hx hage hxn hbirth' (hbirthA n i hi b)
    exact scalar_ge_of_age_factor_P6SN hc hq hage0
      (lt_of_le_of_lt hqage (hθ1 n)) hmain

/-- **final (SEP′) + (CWS) ⇒ final `hnotK`（`_P6FC`）**：`hnotK_of_capWindowScalar_P6R2` 的 final 孪生
（trace 终点 `Fin.last`，标量在 `G n` 上）。 -/
theorem hnotK_final_of_capWindowScalar_P6FC {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ}
    {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier} {R : ℕ → ℝ}
    (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n)) {η : ℝ}
    (hcws : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (hl : i.succ ≤ Fin.last (K n).eventCount)
      (z : ((K n).stage (Fin.last (K n).eventCount)).Carrier)
      (A : BackwardPointTrace (K n).toHistory i.succ (Fin.last (K n).eventCount) hl z)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x →
      ‖x.val‖ < ((n : ℝ) + 1) + 1 →
      t n - (K n).time i.succ ≤
        (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      η * ((recordsK n i hi).static b).neck.scale ≤ (G n).flow.scalar (t n) z)
    (hsepF : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
      i.succ ≤ Fin.last (K n).eventCount →
      t n - (K n).time i.succ ≤ (((recordsK n i hi).static b).neck.scale)⁻¹ →
      R n < η * ((recordsK n i hi).static b).neck.scale) :
    ∀ n, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ Fin.last (K n).eventCount)
        (A : BackwardPointTrace (K n).toHistory i.succ (Fin.last (K n).eventCount) hl (yG n))
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          t n - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹ := by
  rintro n ⟨i, hi, hl, A, b, x, hx, hxn, hage⟩
  have h1 := hcws n i hi hl (yG n) A b x hx hxn hage
  have hs : 0 < ((recordsK n i hi).static b).neck.scale :=
    ((recordsK n i hi).static b).neck.scale_pos
  have hsinv : 0 < (((recordsK n i hi).static b).neck.scale)⁻¹ := inv_pos.mpr hs
  have hn2 : 0 ≤ 1 / ((n : ℝ) + 2) := by positivity
  have hage' : t n - (K n).time i.succ ≤ (((recordsK n i hi).static b).neck.scale)⁻¹ := by
    refine hage.trans ?_
    nlinarith
  have h2 := hsepF n i hi b hl hage'
  rw [hRn n] at h2
  linarith

/-- **consumer：diagonal 包 + final (SEP′) ⇒ final `hnotK`（`_P6FC`）**：
`hnotK_of_diagonal_cws_P6SN` 的 final 孪生（与 event 版共用 `c` 与 diagonal 序列，见
`cws_uniform_of_diagonal_final_P6FC`）；
结论 = final 合同 cap-window 合取项的 `¬∃` 形（`t = σ`）。只剩 final (SEP′) `hsepF`（`η = c`）与 diagonal 参数条件。 -/
theorem hnotK_of_diagonal_cws_final_P6FC :
    ∃ c : ℝ, 0 < c ∧ ∀ C : ℝ≥0, ∃ (Cb Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n, 0 < Cb n ∧ Cb n ≤ 1 / ((n : ℝ) + 1) ^ 2) ∧
      (∀ n, 0 < ζ n ∧ ζ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n, 0 < δ₀ n ∧ δ₀ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ Rn n) ∧ (∀ n : ℕ, n + 2 ≤ m₀ n) ∧
      ∀ {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ}
        (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n)
        (htK : ∀ n, t n < (K n).horizon)
        {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
          ((K n).time (Fin.last (K n).eventCount)) (K n).horizon},
        (∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
          ((htl n).trans (htK n)) le_rfl) →
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
      (∀ n, (G n).DerivativeBoundBefore C (Q n) (K n).horizon) →
      (∀ n i hi b, max (Q n) 1 ≤ Cb n * ((recordsK n i hi).static b).neck.scale) →
      (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
      ∀ {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier} {R : ℕ → ℝ},
      (∀ n, R n = (G n).flow.scalar (t n) (yG n)) →
      (∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ Fin.last (K n).eventCount →
        t n - (K n).time i.succ ≤ (((recordsK n i hi).static b).neck.scale)⁻¹ →
        R n < c * ((recordsK n i hi).static b).neck.scale) →
      ∀ n, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
          (hl : i.succ ≤ Fin.last (K n).eventCount)
          (A : BackwardPointTrace (K n).toHistory i.succ (Fin.last (K n).eventCount) hl (yG n))
          (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
          (x : standardCapWindow (p n).modelRadius),
          A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
            ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
            t n - (K n).time i.succ ≤
              (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹ := by
  obtain ⟨c, hc, hall⟩ := cws_uniform_of_diagonal_final_P6FC.{u}
  refine ⟨c, hc, fun C => ?_⟩
  obtain ⟨Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ, hRn, hm₀, -, hdiagF⟩ := hall C
  refine ⟨Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ, hRn, hm₀, ?_⟩
  intro K t htl htK G hG Q T₀ p pF recordsK recordsF a₀ hHI hcanK hδF hacc hrad hord hslabK hderF
    hbirth hbirthA yG R hRn' hsepF
  exact hnotK_final_of_capWindowScalar_P6FC recordsK hRn'
    (hdiagF htl htK hG recordsF hHI hcanK hδF hacc hrad hord hslabK hderF hbirth hbirthA) hsepF

/-- consumer（共用序列）：联合版的 event 支逐字给出 SN 版 `hcws` 形（同一 `c`、同一序列），final 支给
final `hnotK`——同一 diagonal 选择同时服务 event / final 两支。 -/
example : ∃ c : ℝ, 0 < c :=
  cws_uniform_of_diagonal_final_P6FC.{0}.imp fun _ h => h.1

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
