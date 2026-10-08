import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SurgeryParamCompatP6PC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KRouteNoJ10CeilP6JG

/-!
# J10GEN3 G2：scale separation `hsepX` ⇐ `SurgeryParamCompat_P6PC`（O-CH11-J10GEN3，后缀 `_P6JG3`）

J10 删除后，J10GEN G1b / J10GEN2A 的无 J10 driver 都把 `hsepX`（`∀ M, ∀ᶠ n`，窗口 event 的 neck scale
`> M·R_n`）放在合同 ∃ 元组末尾，与 records-X **同一 witness**。本文件给它的 producer：
* `paramCompat_of_eq_P6JG3`（PROVED）：合同只看 `δ`、`ρ` ⇒ `p.delta = q.delta`、`p.neckRadius = q.neckRadius`
  时 q 版合同下传到 p（KNOM 同一 witness 的 hP5L 等式正是这个形）；
* `hsepX_of_paramCompat_P6JG3`（PROVISIONAL[合同 + `hTn` + `hδ`]）：逐 n 的
  `hscale_of_paramCompat_P6PC`（PARAMCOMPAT，`r := 1`）对**所有** `Q_b` 成立（`hδ` 是 `∀ Q_b, ∀ᶠ n`，
  即窗口 δ → 0 + `Λδ ≤ 1/2`）+ `R → ∞` ⇒ `hsepX`（取 `Q_b := max M 0 / 4 + 1`）；
* `hsepX_of_paramCompat_rescale_P6JG3`：K 单位（records 参数 `q.rescale_P6N c`、seed clock
  `aSeed = Tn − 1²`、`1 ≤ aSeed ≤ a` ⇒ `θ = 2`）；
* `hsepX_of_paramCompat_witness_P6JG3`：同一 witness 形（records 参数 `p n`，q 版合同 + δ/ρ 等式）。
binder 来源：`hpc` = PARAMCOMPAT 合同（owner chain / successor 存在性）；`hTn` = hOpen8 的 Tn 行
`R ≤ ρ(Tn)⁻²`；`hδ` = HRECDELTA 型窗口 δ → 0。无 `Q < R`、无 `qcan < R`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **合同沿 δ/ρ 等式下传（`_P6JG3`，PROVED）**：`SurgeryParamCompat_P6PC` 只依赖 `delta` 与 `neckRadius`。 -/
theorem paramCompat_of_eq_P6JG3 {p q : CutoffParameters} {θ : ℝ}
    (hq : SurgeryParamCompat_P6PC q θ) (hd : p.delta = q.delta) (hr : p.neckRadius = q.neckRadius) :
    SurgeryParamCompat_P6PC p θ := by
  unfold SurgeryParamCompat_P6PC
  rw [hd, hr]
  exact hq

/-- 算术核：`2·max(3, 2·Q_b·R) < s`、`Q_b = max M 0 / 4 + 1`、`0 ≤ R` ⇒ `M·R < s`。 -/
theorem mul_lt_of_two_max_lt_P6JG3 {M R s : ℝ} (hR : 0 ≤ R)
    (h : 2 * max (3 / (1 : ℝ) ^ 2) (2 * ((max M 0 / 4 + 1) * R)) < s) : M * R < s := by
  have hmx : 2 * ((max M 0 / 4 + 1) * R) ≤ max (3 / (1 : ℝ) ^ 2) (2 * ((max M 0 / 4 + 1) * R)) :=
    le_max_right _ _
  have hM : M * R ≤ max M 0 * R := mul_le_mul_of_nonneg_right (le_max_left _ _) hR
  nlinarith

/-- **`hsepX` ⇐ PARAMCOMPAT（`_P6JG3`，PROVISIONAL[`hpc` 合同 / `hTn` / `hδ`]）**：逐 n
`hscale_of_paramCompat_P6PC`（`r := 1`、`Q_b := max M 0 / 4 + 1`）+ `R → ∞`。结论 = J10GEN G1b /
J10GEN2A driver 的 `hsepX` 槽形（`a n` 取 seed 起点）。 -/
theorem hsepX_of_paramCompat_P6JG3 {Hs : ℕ → ObservedHistory.{u}} {pX : ℕ → CutoffParameters}
    {θ : ℝ} (hθ : 0 ≤ θ) {T₀X a Tn R : ℕ → ℝ}
    (recordsX : ∀ n (e : Fin (Hs n).eventCount), T₀X n ≤ (Hs n).time e.succ →
      GeometricCutoffRecord (Hs n) e (pX n))
    (hpc : ∀ n, SurgeryParamCompat_P6PC (pX n) θ) (hTn0 : ∀ n, 0 ≤ Tn n)
    (hwin : ∀ n, Tn n ≤ θ * a n) (hTn : ∀ n, R n ≤ ((pX n).neckRadius (Tn n) ^ 2)⁻¹)
    (hδ : ∀ Qb : ℝ, 0 ≤ Qb → ∀ᶠ n in atTop, ∀ e : Fin (Hs n).eventCount,
      T₀X n ≤ (Hs n).time e.succ → a n < (Hs n).time e.succ →
      (pX n).recenterConstant * (pX n).delta ((Hs n).time e.succ) ≤ 1 / 2 ∧
        8 * Qb * (pX n).delta ((Hs n).time e.succ) ^ 2 ≤ 1)
    (hRlim : Tendsto R atTop atTop) :
    ∀ M : ℝ, ∀ᶠ n in atTop, ∀ (e : Fin (Hs n).eventCount)
      (he : T₀X n ≤ (Hs n).time e.succ) b, a n < (Hs n).time e.succ →
        M * R n < ((recordsX n e he).static b).neck.scale := by
  intro M
  have hQ0 : (0 : ℝ) ≤ max M 0 / 4 := div_nonneg (le_max_right _ _) (by norm_num)
  have hQb0 : (0 : ℝ) ≤ max M 0 / 4 + 1 := by linarith
  filter_upwards [hδ (max M 0 / 4 + 1) hQb0, hRlim.eventually_ge_atTop (3 / 2)] with n hδn hRn
  intro e he b hae
  have h3 : 3 / (1 : ℝ) ^ 2 ≤ 2 * ((max M 0 / 4 + 1) * R n) := by
    norm_num
    nlinarith
  have hs := hscale_of_paramCompat_P6PC (r := 1) (recordsX n) (hpc n) hθ (hTn0 n) (hwin n) (hTn n)
    hδn h3 hQb0 e he b hae
  exact mul_lt_of_two_max_lt_P6JG3 (by linarith) hs

/-- **K 单位（`_P6JG3`，PROVISIONAL[`hpc` / `hTn` / `hδ`]）**：records 参数 `q.rescale_P6N c`（`q` 的合同经
`paramCompat_rescale_P6PC` 下传），seed clock `aSeed = Tn − 1²`、`1 ≤ aSeed ≤ a` ⇒ `θ = 2` 窗口比。 -/
theorem hsepX_of_paramCompat_rescale_P6JG3 {Hs : ℕ → ObservedHistory.{u}}
    {q : ℕ → CutoffParameters} {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) {T₀X aSeed a Tn R : ℕ → ℝ}
    (recordsX : ∀ n (e : Fin (Hs n).eventCount), T₀X n ≤ (Hs n).time e.succ →
      GeometricCutoffRecord (Hs n) e ((q n).rescale_P6N (c n) (hc n)))
    (hpc : ∀ n, SurgeryParamCompat_P6PC (q n) 2) (hclock : ∀ n, aSeed n = Tn n - 1 ^ 2)
    (h1 : ∀ n, 1 ≤ aSeed n) (has : ∀ n, aSeed n ≤ a n)
    (hTn : ∀ n, R n ≤ (((q n).rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹)
    (hδ : ∀ Qb : ℝ, 0 ≤ Qb → ∀ᶠ n in atTop, ∀ e : Fin (Hs n).eventCount,
      T₀X n ≤ (Hs n).time e.succ → a n < (Hs n).time e.succ →
      ((q n).rescale_P6N (c n) (hc n)).recenterConstant *
          ((q n).rescale_P6N (c n) (hc n)).delta ((Hs n).time e.succ) ≤ 1 / 2 ∧
        8 * Qb * ((q n).rescale_P6N (c n) (hc n)).delta ((Hs n).time e.succ) ^ 2 ≤ 1)
    (hRlim : Tendsto R atTop atTop) :
    ∀ M : ℝ, ∀ᶠ n in atTop, ∀ (e : Fin (Hs n).eventCount)
      (he : T₀X n ≤ (Hs n).time e.succ) b, a n < (Hs n).time e.succ →
        M * R n < ((recordsX n e he).static b).neck.scale := by
  have hTn0 : ∀ n, 0 ≤ Tn n := fun n => by
    have h := hclock n
    have h' := h1 n
    rw [one_pow] at h
    linarith
  exact hsepX_of_paramCompat_P6JG3 (by norm_num) recordsX
    (fun n => paramCompat_rescale_P6PC (hpc n) (c n) (hc n)) hTn0
    (fun n => window_le_two_mul_P6PC (hclock n) (h1 n) (has n)) hTn hδ hRlim

/-- **同一 witness 形（`_P6JG3`，PROVISIONAL[`hpc` / `hTn` / `hδ`]）**：records 参数 `p n` 与 q 版合同只经
`δ` / `ρ` 等式相连（KNOM hP5L witness 的 `p.delta = q.delta ∧ p.neckRadius = q.neckRadius`）。 -/
theorem hsepX_of_paramCompat_witness_P6JG3 {Hs : ℕ → ObservedHistory.{u}}
    {p q : ℕ → CutoffParameters} {θ : ℝ} (hθ : 0 ≤ θ) {T₀X a Tn R : ℕ → ℝ}
    (recordsX : ∀ n (e : Fin (Hs n).eventCount), T₀X n ≤ (Hs n).time e.succ →
      GeometricCutoffRecord (Hs n) e (p n))
    (hpq : ∀ n, (p n).delta = (q n).delta ∧ (p n).neckRadius = (q n).neckRadius)
    (hpc : ∀ n, SurgeryParamCompat_P6PC (q n) θ) (hTn0 : ∀ n, 0 ≤ Tn n)
    (hwin : ∀ n, Tn n ≤ θ * a n) (hTn : ∀ n, R n ≤ ((p n).neckRadius (Tn n) ^ 2)⁻¹)
    (hδ : ∀ Qb : ℝ, 0 ≤ Qb → ∀ᶠ n in atTop, ∀ e : Fin (Hs n).eventCount,
      T₀X n ≤ (Hs n).time e.succ → a n < (Hs n).time e.succ →
      (p n).recenterConstant * (p n).delta ((Hs n).time e.succ) ≤ 1 / 2 ∧
        8 * Qb * (p n).delta ((Hs n).time e.succ) ^ 2 ≤ 1)
    (hRlim : Tendsto R atTop atTop) :
    ∀ M : ℝ, ∀ᶠ n in atTop, ∀ (e : Fin (Hs n).eventCount)
      (he : T₀X n ≤ (Hs n).time e.succ) b, a n < (Hs n).time e.succ →
        M * R n < ((recordsX n e he).static b).neck.scale :=
  hsepX_of_paramCompat_P6JG3 hθ recordsX
    (fun n => paramCompat_of_eq_P6JG3 (hpc n) (hpq n).1 (hpq n).2) hTn0 hwin hTn hδ hRlim

/-- **consumer（`_P6JG3`）**：G2 的 `hsepX` 直接喂 J10GEN G1b `hscale_ev_of_sep_P6JG`（CXJD `hscale` 的
eventual 形，`∀ Q_b`），即 hceilQ 链所需的全部 scale 输入由 PARAMCOMPAT 付。 -/
theorem hscale_ev_of_paramCompat_P6JG3 {r Qb : ℝ} (hr : 0 < r) (hQb : 0 ≤ Qb)
    {Hs : ℕ → ObservedHistory.{u}} {pX : ℕ → CutoffParameters} {θ : ℝ} (hθ : 0 ≤ θ)
    (aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon) {T₀X Tn R : ℕ → ℝ}
    (recordsX : ∀ n (e : Fin (Hs n).eventCount), T₀X n ≤ (Hs n).time e.succ →
      GeometricCutoffRecord (Hs n) e (pX n))
    (hpc : ∀ n, SurgeryParamCompat_P6PC (pX n) θ) (hTn0 : ∀ n, 0 ≤ Tn n)
    (hwin : ∀ n, Tn n ≤ θ * aSeed n) (hTn : ∀ n, R n ≤ ((pX n).neckRadius (Tn n) ^ 2)⁻¹)
    (hδ : ∀ Qb : ℝ, 0 ≤ Qb → ∀ᶠ n in atTop, ∀ e : Fin (Hs n).eventCount,
      T₀X n ≤ (Hs n).time e.succ → (aSeed n : ℝ) < (Hs n).time e.succ →
      (pX n).recenterConstant * (pX n).delta ((Hs n).time e.succ) ≤ 1 / 2 ∧
        8 * Qb * (pX n).delta ((Hs n).time e.succ) ^ 2 ≤ 1)
    (hRlim : Tendsto R atTop atTop) :
    ∀ᶠ n in atTop, ∀ (e : Fin (Hs n).eventCount) (he : T₀X n ≤ (Hs n).time e.succ) b,
      (aSeed n : ℝ) < (Hs n).time e.succ →
      2 * max (3 / r ^ 2) (2 * (Qb * R n)) < ((recordsX n e he).static b).neck.scale :=
  ObservedHistory.hscale_ev_of_sep_P6JG hr hQb Hs aSeed R hRlim pX T₀X recordsX
    (hsepX_of_paramCompat_P6JG3 (a := fun n => (aSeed n : ℝ)) hθ recordsX hpc hTn0 hwin hTn hδ
      hRlim)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
