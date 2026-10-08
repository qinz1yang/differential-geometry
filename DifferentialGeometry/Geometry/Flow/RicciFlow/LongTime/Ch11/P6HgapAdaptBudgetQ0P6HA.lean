import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgapAdaptBudgetP6HA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ParamCompatTwoP6SS

/-!
# J8 `hJ7`（budget 形）⇐ 参考 q-records + PARAMCOMPAT θ = 2 + `T₀` late-δ 选择子（J8KAPPA G3b，`_P6HA`）

lead 裁定（2026-10-08 ch12）：J8-a 收窄到 witness 形；J8-b `T₀ ≥ lateDeltaThr_P6JS` 并入 `T₀` 选取；
J8-c 用已有 producer。树内 KNOM witness（`diagonalPack_nom_CXKN` 的 `hnom`）给出的识别是
**static scale 与参考 q-records 相等**（`((recordsK n i hi).static b).neck.scale =
((records (ind n) i).static b).neck.scale`），不显式给 `p.neckRadius = q.neckRadius`；本文件按这个
witness 识别收窄（record 尺度直接读参考 q-record，`p` 的 δ / ρ 不再出现）。
* `window_two_P6HA`：`(L² − L)/R ≥ −1/4` ⇒ `σ − L/R ≥ Tn − 3/4`，`Tn > 2` ⇒ late record 满足 `Tno ≤ 2τ`
  （θ = 2，与 HSCALESEP `paramCompat_q_of_requestCap_P6SS` 的 θ 一致；G3 的 θ = 4 版因此不再需要）；
* `deltaRho_le_window_two_P6HA`：`SurgeryParamCompat_P6PC q 2` ⇒ `δρ(τ) ≤ ρ(Tno)`；
* **`hJ7_loc_of_qRecords_P6HA`**（PROVED 相对 `hpc : SurgeryParamCompat_P6PC q 2` + `hT₀δ` 选择子）：
  hgap 帧数据 + scale 识别 + J7b ⇒ J7 `max (Qs_loc n) 1 ≤ Cb n · scale`。
* `hpc` 的来源： `paramCompat_q_of_requestCap_P6SS`（`hq` + tower request 比值
  `hcap`，HSCALESEP G2 已登记 repair target，`tower_of_blockSteps_ratio_P6SS` 证可满足）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **late record 落在 `Tno` 的 2-窗内（`_P6HA`，PROVED，纯实数）**。 -/
theorem window_two_P6HA {c Tno Tn σ L R τ : ℝ} (hc : 0 < c) (hTn : Tno = c * Tn)
    (h2c : 2 * c < Tno) (hroom : Tn - 1 ^ 2 / 2 ≤ σ - L ^ 2 / R) (hR1 : 1 ≤ R)
    (hτ : c * (σ - L / R) ≤ τ) : Tno ≤ 2 * τ := by
  have hR0 : 0 < R := by linarith
  have hq : -(1 / 4 : ℝ) ≤ (L ^ 2 - L) / R := by
    have h1 : -(1 / 4 : ℝ) ≤ L ^ 2 - L := by nlinarith [sq_nonneg (L - 1 / 2)]
    rcases le_or_gt 0 (L ^ 2 - L) with h | h
    · exact le_trans (by norm_num) (div_nonneg h hR0.le)
    · rw [le_div_iff₀ hR0]
      nlinarith
  have hsplit : σ - L / R = (σ - L ^ 2 / R) + (L ^ 2 - L) / R := by ring
  have hσ : Tn - 3 / 4 ≤ σ - L / R := by
    rw [hsplit]
    have : (1 : ℝ) ^ 2 / 2 = 1 / 2 := by norm_num
    linarith
  have hTn2 : 2 < Tn := by
    have : 2 * c < c * Tn := hTn ▸ h2c
    nlinarith
  have hcσ : c * (Tn - 3 / 4) ≤ c * (σ - L / R) := mul_le_mul_of_nonneg_left hσ hc.le
  nlinarith

/-- **PARAMCOMPAT 2-窗 ⇒ `δρ ≤ ρ(Tno)`（`_P6HA`，PROVED）**。 -/
theorem deltaRho_le_window_two_P6HA {p : CutoffParameters} (hpc : SurgeryParamCompat_P6PC p 2)
    {τ T : ℝ} (hτ0 : 0 ≤ τ) (hT0 : 0 ≤ T) (hw : T ≤ 2 * τ) :
    p.delta τ * p.neckRadius τ ≤ p.neckRadius T := by
  rcases le_or_gt τ T with h | h
  · exact hpc.2 τ T hτ0 h hw
  · have hδ1 := p.delta_lt_one τ hτ0
    have hρ0 := p.neckRadius_pos τ hτ0
    have hanti := hpc.1 (show T ∈ Ici (0 : ℝ) from hT0) (show τ ∈ Ici (0 : ℝ) from hτ0) h.le
    have : p.delta τ * p.neckRadius τ ≤ p.neckRadius τ := by
      have := mul_le_mul_of_nonneg_right hδ1.le hρ0.le
      linarith
    exact this.trans hanti

/-- **J7（budget 形）⇐ 参考 q-records（`_P6HA`，PROVED 相对 `hpc` + `hT₀δ`）**：hgap 帧数据
（`Tno = c·Tn`、`2c < Tno`、`Tn − 1/2 ≤ σ − L²/R`、`n + 1 ≤ R`、`R ≤ c·ρ(Tno)⁻²`、`n + 1 < R`）+
`T₀ ≥ lateDeltaThr_P6JS`（选择子约束）+ `SurgeryParamCompat_P6PC q 2` + witness 识别
`scale(recordsK) = scale(records (ind n) i)` + J7b ⇒ `max (Qs_loc n) 1 ≤ Cb n · scale`。 -/
theorem hJ7_loc_of_qRecords_P6HA {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q) (hδq : Tendsto q.delta atTop (𝓝 0))
    {Cb : ℕ → ℝ} (hCbpos : ∀ n, 0 < Cb n) (hpc : SurgeryParamCompat_P6PC q 2) (ind : ℕ → ℕ)
    {T₀ c σ L R Tn Tno : ℕ → ℝ}
    (hT₀δ : ∀ n, lateDeltaThr_P6JS q hδq hCbpos n ≤ T₀ n)
    (hc : ∀ n, 0 < c n) (hTno : ∀ n, Tno n = c n * Tn n) (hTno0 : ∀ n, 0 ≤ Tno n)
    (h2c : ∀ n, 2 * c n < Tno n) (hroom : ∀ n, Tn n - 1 ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hRr : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n) (hRρ' : ∀ n, R n ≤ c n * (q.neckRadius (Tno n) ^ 2)⁻¹)
    (hlt : ∀ n : ℕ, (n : ℝ) + 1 < R n) {p : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (F.tower.history (ind n)).eventCount),
      max (T₀ n) (c n * (σ n - L n / R n)) ≤ (F.tower.history (ind n)).time i.succ →
        GeometricCutoffRecord (F.tower.history (ind n)).toHistory i (p n))
    (hsc : ∀ n i hi b, ((recordsK n i hi).static b).neck.scale =
      ((records (ind n) i).static b).neck.scale)
    (hJ7b : ∀ n i hi b, max (0 : ℝ) 1 ≤ Cb n * ((recordsK n i hi).static b).neck.scale) :
    ∀ (n : ℕ) i hi b, max (max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹) 1 ≤
      Cb n * ((recordsK n i hi).static b).neck.scale := by
  intro n i hi b
  refine max_le ?_ ((le_max_right (0 : ℝ) 1).trans (hJ7b n i hi b))
  set τ := (F.tower.history (ind n)).time i.succ with hτdef
  have hτ0 : 0 ≤ τ := (F.tower.history (ind n)).toHistory.time_nonneg i.succ
  have hR1 : (1 : ℝ) ≤ R n := by
    have := hRr n
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hw : Tno n ≤ 2 * τ :=
    window_two_P6HA (hc n) (hTno n) (h2c n) (hroom n) hR1 ((le_max_right _ _).trans hi)
  have hlate := lateDelta_of_thr_P6JS q hδq hCbpos
    (n := n) (t := τ) ((hT₀δ n).trans ((le_max_left _ _).trans hi))
  have hρT := q.neckRadius_pos _ (hTno0 n)
  rw [qsLoc_eq_P6HA (hc n) hρT (hRρ' n) (hlt n), hsc n i hi b]
  exact birth_arith_P6JS hρT (q.delta_pos _ hτ0) (q.neckRadius_pos _ hτ0) le_rfl
    (deltaRho_le_window_two_P6HA hpc hτ0 (hTno0 n) hw) hlate.2
    (scale_gt_of_params_P6JS (records (ind n) i) hlate.1 b)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
