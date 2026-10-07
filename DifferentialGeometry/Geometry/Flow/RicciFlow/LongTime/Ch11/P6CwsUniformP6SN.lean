import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.CapWindowAgeBoundLate_P6LL
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NotKResidualP6R2

/-!
# (CWS) 的统一 `η`：标准解统一标量下界 + diagonal 参数（S-CH11-SEPTN G3，后缀 `_P6SN`）

`hnotK_of_capWindowScalar_P6R2` 的 (CWS) binder `hcws`：late cap-window 点（`‖x‖ < n + 2`，年龄
`≤ (1 − 1/(n+2))/scale`）在 `t n` 的标量下界 `η·scale ≤ R(t n, z)`，`η` 对 `n`、窗口半径、年龄一致。

**结论：统一正标量下界存在，`η = c` 与 `n` 无关；与 `n` 相关的只是"标准解近似精度"，用 diagonal 参数处理。**
* 树内标准解：`exists_standard_scalar_lower_bound`（`c₀ / (1 − t) ≤ R`，对所有 `S x t ∈ [0,1)`）
  ⇒ `exists_scalar_lower_bound_of_cap_window_trace_late_P6LL`：**`c = c₀/2` 对 `Θ` 一致**，结论
  `c·scale ≤ (1 − scale·age)·R(t, z)`（`Θ` 只进入存在的常数 `Cbirth(Θ)`、`R(Θ,D)`、`m₀(Θ,D)`、`ζ₀(Θ,D)`、
  `δ₀(Θ,D)`——标准解 `[0, Θ]` 上 `C²` 比较的精度，`Θ → 1` 时可以任意差）。
* `age·scale ≤ Θₙ < 1` 且 `R > 0` ⇒ `(1 − scale·age)·R ≤ R` ⇒ `c·scale ≤ R`
  （`scalar_ge_of_age_factor_P6SN`）。
* **diagonal 选取**（`cws_uniform_of_diagonal_P6SN`）：`Θₙ := 1 − 1/(n+2)`、`D := n+1` 代入树内引理，
  `choose` 出只依赖 `(C = Ctime, n)` 的序列 `Cb Rn m₀ ζ δ₀`（**先于任何 K 数据**）；K 数据供给端须满足
  `accuracy ≤ ζ n`、`Rn n ≤ modelRadius`、`m₀ n ≤ modelOrder`、`late delta ≤ δ₀ n`、
  `max (Q n) 1 ≤ Cb n·scale`（出生尺度）。序列再与 `1/(n+1)`、`n+1`、`n+2`、`1/(n+1)²` 取 min / max，
  使 diagonal 条件蕴含主形 `hacc / hrad / hord / hδF / hscaleK`（`hscaleK_of_diag_P6SN`）。
* consumer `hnotK_of_diagonal_cws_P6SN`：diagonal 包 + (SEP′) `hsep`（`η := c`）⇒ closed 主形 `hnotK`
  （经 `hnotK_of_capWindowScalar_P6R2`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- `c·q ≤ (1 − q·age)·R` 且 `0 ≤ age`、`q·age < 1`、`c, q > 0` ⇒ `c·q ≤ R`。 -/
theorem scalar_ge_of_age_factor_P6SN {c q age R : ℝ} (hc : 0 < c) (hq : 0 < q)
    (hage0 : 0 ≤ age) (hage1 : q * age < 1) (h : c * q ≤ (1 - q * age) * R) : c * q ≤ R := by
  have h1 : 0 < 1 - q * age := by linarith
  have hcq : 0 < c * q := mul_pos hc hq
  have hR : 0 < R := by
    by_contra hR
    have := mul_nonpos_of_nonneg_of_nonpos h1.le (not_lt.mp hR)
    linarith
  have hqa : 0 ≤ q * age := mul_nonneg hq.le hage0
  nlinarith [mul_nonneg hqa hR.le]

/-- `qcan` 放大（阈值变大）保持 `DerivativeBoundBefore`。 -/
theorem derivativeBoundBefore_mono_qcan_P6SN {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) {Ctime : ℝ≥0} {q q' t₀ : ℝ} (hq : q ≤ q')
    (h : G.DerivativeBoundBefore Ctime q t₀) : G.DerivativeBoundBefore Ctime q' t₀ :=
  fun y t ht hR => h y t ht (lt_of_le_of_lt hq hR)

/-- **(CWS) 统一 `η` 的 diagonal 版（`_P6SN`）**：`c > 0`（标准解统一标量下界 `c₀/2`，与 `n` 无关），
对每个 `C = Ctime` 存在只依赖 `(C, n)` 的序列 `Cb Rn m₀ ζ δ₀`（`Θₙ = 1 − 1/(n+2)`、`D = n+1`）：K 数据
若满足 diagonal 精度条件，则 `hcws`（`η := c`）逐字成立。序列同时蕴含主形 `hacc / hrad / hord / hδF /
hscaleK` 的强度。 -/
theorem cws_uniform_of_diagonal_P6SN :
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


/-- diagonal 出生尺度 `max Q 1 ≤ Cb·S`（`Cb ≤ 1/(n+1)²`，`S > 0`）蕴含主形 `hscaleK`：
`(n+1)·max (n+1) Q ≤ S`。 -/
theorem hscaleK_of_diag_P6SN {Cb Q S : ℝ} {n : ℕ} (hCb : Cb ≤ 1 / ((n : ℝ) + 1) ^ 2)
    (hS : 0 < S) (h : max Q 1 ≤ Cb * S) : ((n : ℝ) + 1) * max ((n : ℝ) + 1) Q ≤ S := by
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hn2 : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
  have h1 : Cb * S ≤ S / ((n : ℝ) + 1) ^ 2 := by
    rw [← one_div_mul_eq_div]
    exact mul_le_mul_of_nonneg_right hCb hS.le
  have h2 : ((n : ℝ) + 1) ^ 2 * max Q 1 ≤ S := by
    have := h.trans h1
    rw [le_div_iff₀ hn2] at this
    linarith
  have hm1 : (1 : ℝ) ≤ max Q 1 := le_max_right _ _
  have hmQ : Q ≤ max Q 1 := le_max_left _ _
  have h3 : max ((n : ℝ) + 1) Q ≤ ((n : ℝ) + 1) * max Q 1 :=
    max_le (by nlinarith) (by nlinarith)
  calc ((n : ℝ) + 1) * max ((n : ℝ) + 1) Q ≤ ((n : ℝ) + 1) * (((n : ℝ) + 1) * max Q 1) :=
        mul_le_mul_of_nonneg_left h3 (by linarith)
    _ = ((n : ℝ) + 1) ^ 2 * max Q 1 := by ring
    _ ≤ S := h2

/-- **consumer：diagonal 包 + (SEP′) ⇒ closed 主形 `hnotK`（`_P6SN`）**：`hnotK_of_capWindowScalar_P6R2` 的
(CWS) `hcws` 由 `cws_uniform_of_diagonal_P6SN`（`η := c`）供给；只剩 (SEP′) `hsep`（`η = c`）与 diagonal
参数条件。 -/
theorem hnotK_of_diagonal_cws_P6SN :
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
  obtain ⟨c, hc, hall⟩ := cws_uniform_of_diagonal_P6SN.{u}
  refine ⟨c, hc, fun C => ?_⟩
  obtain ⟨Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ, hRn, hm₀, hdiag⟩ := hall C
  refine ⟨Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ, hRn, hm₀, ?_⟩
  intro K j t hjt htj Q T₀ p pF recordsK recordsF a₀ hHI hcanK hδF hacc hrad hord hslabK hbirth
    hbirthA yG R hRn' hsep
  exact RetainedCoreHistory.hnotK_of_capWindowScalar_P6R2 recordsK hRn'
    (hdiag hjt htj recordsF hHI hcanK hδF hacc hrad hord hslabK hbirth hbirthA) hsep

/-- consumer（`hscaleK_of_diag_P6SN`）：diagonal 出生尺度条件 ⇒ 主形 `hscaleK`（`(n+1)·max (n+1) (Q n) ≤
scale`）。 -/
example {K : ℕ → RetainedCoreHistory.{u}} {T₀ Q : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)} {Cb : ℕ → ℝ}
    (hCb : ∀ n : ℕ, Cb n ≤ 1 / ((n : ℝ) + 1) ^ 2)
    (hbirth : ∀ n i hi b, max (Q n) 1 ≤ Cb n * ((recordsK n i hi).static b).neck.scale) :
    ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale :=
  fun n i hi b => hscaleK_of_diag_P6SN (hCb n) ((recordsK n i hi).static b).neck.scale_pos
    (hbirth n i hi b)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
