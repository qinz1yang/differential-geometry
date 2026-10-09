import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CwsUniformP6SN

/-!
# P5L 对角 hnotK producer 的截断孪生（O-CH11-KTRUNC2b，后缀 `_P6KT2`）

`cws_uniform_of_diagonal_P6SN` / `hnotK_of_diagonal_cws_P6SN`（P6CwsUniformP6SN :61 / :170）的孪生：
hslabK `EventSlabsDerivative … (Fin.last)` →
截断形 `DerivativeBoundBefore … (min (time j'.succ) (tK n))`
+ 连接前提 `∀ n, t n ≤ tK n`。证明里 hslabK 只在 `hder`（slab `j' < j n`，终点 `≤ time (j n)⁻ < t n`）
与 `hcur`（当前 slab 到 `t n`）使用，时间全 `≤ t n ≤ tK n`，故 min 取左 / `le_min` 即接上。
供 Joint D 形（P6JointNoJ10P6JB :678 / :1755）截断孪生的 `hdiag`。生成器 `gen/gen_diag.py`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **截断孪生（`_P6KT2`，KTRUNC2b）**：`cws_uniform_of_diagonal_P6SN` 的 hslabK 换截断形 +
连接前提 `t n ≤ tK n`；`hder` / `hcur` 只用 `≤ t n` 的 slab，故截断形即足。原 docstring：
 **(CWS) 统一 `η` 的 diagonal 版（`_P6SN`）**：`c > 0`（标准解统一标量下界 `c₀/2`，与 `n` 无关），
对每个 `C = Ctime` 存在只依赖 `(C, n)` 的序列 `Cb Rn m₀ ζ δ₀`（`Θₙ = 1 − 1/(n+2)`、`D = n+1`）：K 数据
若满足 diagonal 精度条件，则 `hcws`（`η := c`）逐字成立。序列同时蕴含主形 `hacc / hrad / hord / hδF /
hscaleK` 的强度。 -/
theorem cws_uniform_of_diagonal_T_P6KT2 :
    ∃ c : ℝ, 0 < c ∧ ∀ C : ℝ≥0, ∃ (Cb Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n, 0 < Cb n ∧ Cb n ≤ 1 / ((n : ℝ) + 1) ^ 2) ∧
      (∀ n, 0 < ζ n ∧ ζ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n, 0 < δ₀ n ∧ δ₀ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ Rn n) ∧ (∀ n : ℕ, n + 2 ≤ m₀ n) ∧
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
      ∀ {tK : ℕ → ℝ}, (∀ n, t n ≤ tK n) →
      (∀ n (j' : Fin (K n).eventCount),
        ((K n).toHistory.event j').incoming.DerivativeBoundBefore C (Q n)
          (min ((K n).time j'.succ) (tK n))) →
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
    fun n => le_max_right _ _, fun n => le_max_right _ _, ?_⟩
  intro K j t hjt htj Q T₀ p pF recordsK recordsF a₀ hHI hcanK hδF hacc hrad hord tK htK hslabK
    hbirth hbirthA n i hi hl z A b x hx hxn hage
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
    fun j' hj' => derivativeBoundBefore_mono_qcan_P6SN _ (le_max_left _ _) (by
      have hs : j'.succ ≤ (j n).castSucc := by
        rw [Fin.lt_def, Fin.val_castSucc, Fin.val_castSucc] at hj'
        rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
        omega
      have h2 : (K n).time j'.succ ≤ tK n :=
        (((K n).time_strictMono.monotone hs).trans (hjt n).le).trans (htK n)
      have h3 := hslabK n j'
      rwa [min_eq_left h2] at h3)
  have hcur : ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore C (max (Q n) 1)
      (t n) :=
    ((K n).toHistory.event (j n)).incoming.derivativeBoundBefore_mono
      (le_min (htj n).le (htK n))
      (derivativeBoundBefore_mono_qcan_P6SN _ (le_max_left _ _) (hslabK n (j n)))
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

/-- **截断孪生（`_P6KT2`，KTRUNC2b）**：`hnotK_of_diagonal_cws_P6SN` 经 cws 截断孪生。原 docstring：
 **consumer：diagonal 包 + (SEP′) ⇒ closed 主形 `hnotK`（`_P6SN`）**：`hnotK_of_capWindowScalar_P6R2` 的
(CWS) `hcws` 由 `cws_uniform_of_diagonal_P6SN`（`η := c`）供给；只剩 (SEP′) `hsep`（`η = c`）与 diagonal
参数条件。 -/
theorem hnotK_of_diagonal_cws_T_P6KT2 :
    ∃ c : ℝ, 0 < c ∧ ∀ C : ℝ≥0, ∃ (Cb Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n, 0 < Cb n ∧ Cb n ≤ 1 / ((n : ℝ) + 1) ^ 2) ∧
      (∀ n, 0 < ζ n ∧ ζ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n, 0 < δ₀ n ∧ δ₀ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ Rn n) ∧ (∀ n : ℕ, n + 2 ≤ m₀ n) ∧
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
      ∀ {tK : ℕ → ℝ}, (∀ n, t n ≤ tK n) →
      (∀ n (j' : Fin (K n).eventCount),
        ((K n).toHistory.event j').incoming.DerivativeBoundBefore C (Q n)
          (min ((K n).time j'.succ) (tK n))) →
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
  obtain ⟨c, hc, hall⟩ := cws_uniform_of_diagonal_T_P6KT2.{u}
  refine ⟨c, hc, fun C => ?_⟩
  obtain ⟨Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ, hRn, hm₀, hdiag⟩ := hall C
  refine ⟨Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ, hRn, hm₀, ?_⟩
  intro K j t hjt htj Q T₀ p pF recordsK recordsF a₀ hHI hcanK hδF hacc hrad hord tK htK hslabK
    hbirth hbirthA yG R hRn' hsep
  exact RetainedCoreHistory.hnotK_of_capWindowScalar_P6R2 recordsK hRn'
    (hdiag hjt htj recordsF hHI hcanK hδF hacc hrad hord htK hslabK hbirth hbirthA) hsep

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
