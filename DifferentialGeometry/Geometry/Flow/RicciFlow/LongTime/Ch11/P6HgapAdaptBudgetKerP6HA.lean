import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgapAdaptBudgetQ0P6HA

/-!
# J8 `hJ7` ⇐ 参考 q-records，late δ 由 kernel 常数 `δ₀` 付（J8KAPPA G3d，`_P6HA`）

RESID 发现（lead 裁定 J8-b 量词序）：hgapJ / J8 槽的 `∀ Cb` 在最外层、排在 `T₀ = T₀sel` 之前，`T₀sel` 看不到
`Cb` ⇒ G3c 的 `hT₀δ : T₀ ≥ lateDeltaThr_P6JS … Cb …` 不可选。按 lead 优先序：
* **(1) 不行**：`thr` 的另一项 `c(σ − L/R)` 只给 `τ ≥ Tno/2 ≥ (n+1)/2`（`window_two_P6HA`），而 `Cb n` 是
  标准解比较的紧性常数（`cws_uniform_of_diagonal_P6SN` 里 `min (Cbirth(Θₙ)) (1/(n+1)²)`），对 `n` 无下界关系；
  `2δ_q(τ)² ≤ Cb n` 不能由 `τ ≥ (n+1)/2` 推出（`Cb n` 可任意小，`δ_q` 只 `→ 0`）。
* **(3) 采用**：late record 上 `δ_q(τ) ≤ δ₀ n` 已是 hgap 槽前提（`hδW`，KNOM witness 给），所以只需 kernel 常数
  关系 `Λ·δ₀ n ≤ 1/2 ∧ 2·δ₀ n² ≤ Cb n`。kernel 在自身 selection 里选 `δ₀`（`min` 进更小值不破坏 `hcws`：
  `δ₀` 只以上界身份出现），见 `kernelDelta_shrink_P6HA`。`Λ = q.recenterConstant` 要求在 kernel 常数之前已知
  （pB 静态字段，P6M6 `= pB`）。
* `hJ7_loc_of_kernelDelta_P6HA`（PROVED 相对 `hpc`、kernel 关系 `hδ₀K`）：同 G3b，`hlate` 改由 `hδW` + `hδ₀K` 付。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **kernel `δ₀` 收缩（`_P6HA`，PROVED，纯实数）**：`δ₀' n := min (δ₀ n) (min (1/(2Λ)) (√(Cb n/2)))`
保持 `0 < δ₀' ≤ δ₀`，且 `Λ·δ₀' ≤ 1/2 ∧ 2·δ₀'² ≤ Cb n`。 -/
theorem kernelDelta_shrink_P6HA {Λ : ℝ} (hΛ : 0 < Λ) {δ₀ Cb : ℕ → ℝ} (hδ₀ : ∀ n, 0 < δ₀ n)
    (hCb : ∀ n, 0 < Cb n) :
    ∀ n, 0 < min (δ₀ n) (min (1 / (2 * Λ)) (Real.sqrt (Cb n / 2))) ∧
      min (δ₀ n) (min (1 / (2 * Λ)) (Real.sqrt (Cb n / 2))) ≤ δ₀ n ∧
      Λ * min (δ₀ n) (min (1 / (2 * Λ)) (Real.sqrt (Cb n / 2))) ≤ 1 / 2 ∧
      2 * min (δ₀ n) (min (1 / (2 * Λ)) (Real.sqrt (Cb n / 2))) ^ 2 ≤ Cb n := by
  intro n
  set d := min (δ₀ n) (min (1 / (2 * Λ)) (Real.sqrt (Cb n / 2))) with hd
  have hs : 0 < Real.sqrt (Cb n / 2) := Real.sqrt_pos.2 (by linarith [hCb n])
  have hd0 : 0 < d := lt_min (hδ₀ n) (lt_min (by positivity) hs)
  have hd1 : d ≤ 1 / (2 * Λ) := (min_le_right _ _).trans (min_le_left _ _)
  have hd2 : d ≤ Real.sqrt (Cb n / 2) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨hd0, min_le_left _ _, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left hd1 hΛ.le
    rwa [show Λ * (1 / (2 * Λ)) = 1 / 2 by field_simp] at this
  · have h2 : d ^ 2 ≤ Cb n / 2 := by
      have := pow_le_pow_left₀ hd0.le hd2 2
      rwa [Real.sq_sqrt (by linarith [hCb n])] at this
    linarith

/-- **J7 ⇐ 参考 q-records，late δ 由 kernel `δ₀`（`_P6HA`，PROVED 相对 `hpc` + `hδ₀K`）**。 -/
theorem hJ7_loc_of_kernelDelta_P6HA {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    {Cb δ₀ : ℕ → ℝ} (hδ₀K : ∀ n, q.recenterConstant * δ₀ n ≤ 1 / 2 ∧ 2 * δ₀ n ^ 2 ≤ Cb n)
    (hpc : SurgeryParamCompat_P6PC q 2) (ind : ℕ → ℕ)
    {T₀ c σ L R Tn Tno : ℕ → ℝ}
    (hδW : ∀ n (i : Fin (F.tower.history (ind n)).eventCount),
      max (T₀ n) (c n * (σ n - L n / R n)) ≤ (F.tower.history (ind n)).time i.succ →
      q.delta ((F.tower.history (ind n)).time i.succ) ≤ δ₀ n)
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
  have hδτ := hδW n i hi
  have hδ0 := q.delta_pos τ hτ0
  have hΛ : q.recenterConstant * q.delta τ ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hδτ (by linarith [q.recenterConstant_ge_four])).trans (hδ₀K n).1
  have hCb : 2 * q.delta τ ^ 2 ≤ Cb n :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ0.le hδτ 2) (by norm_num)).trans (hδ₀K n).2
  have hρT := q.neckRadius_pos _ (hTno0 n)
  rw [qsLoc_eq_P6HA (hc n) hρT (hRρ' n) (hlt n), hsc n i hi b]
  exact birth_arith_P6JS hρT hδ0 (q.neckRadius_pos _ hτ0) le_rfl
    (deltaRho_le_window_two_P6HA hpc hτ0 (hTno0 n) hw) hCb
    (scale_gt_of_params_P6JS (records (ind n) i) hΛ b)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
