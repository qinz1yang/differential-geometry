import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgapAdaptBudgetKerP6HA

/-!
# J8 `hJ7`：`2δ₀² ≤ Cb` 由 kernel、`Λδ ≤ 1/2` 由 `T₀` 选择子（J8KAPPA G3e，`_P6HA`）

量词序核查（`a12EnhancedFull_of_slots_v10_loc_s14_sel_RS`，`P6A12SlotsV10S14SelRS.lean:58–63`）：hgapJ 槽里
`∀ (Cb Rn ζ δ₀) (m₀)` 在 `∀ {pB}` **之前** ⇒ kernel 常数选取点在 pB 之前，`Λ = pB.recenterConstant` 不可用；
pB 任意（只 `4 ≤ Λ`），也没有全局上界 `Λ̄`。故把 G3d 的 `hδ₀K` 拆开：
* `2·δ₀ C n² ≤ Cb C n`：两者同为 kernel 常数，kernel 自身 selection 内选（`kernelDelta_shrink_P6HA` 取 `Λ := 1`
  的第二分量即可，或直接 `min δ₀ √(Cb/2)`）；
* `Λ_q·δ_q(τ) ≤ 1/2`：`T₀ = T₀sel Γ T F q` 在 `q` 之后、与 `Cb` 无关 ⇒ 选择子约束
  `lateLambdaThr_P6HA q hδq ≤ T₀ n`（只依赖 `q`）。
* `hJ7_loc_of_kernelDeltaT_P6HA`（PROVED 相对 `hpc`、`hδ₀Cb`、`hT₀Λ`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_lateLambda_P6HA (q : CutoffParameters) (hδq : Tendsto q.delta atTop (𝓝 0)) :
    ∃ T : ℝ, ∀ τ : ℝ, T ≤ τ → q.recenterConstant * q.delta τ ≤ 1 / 2 := by
  have hrc : 0 < q.recenterConstant := by linarith [q.recenterConstant_ge_four]
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    (hδq.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / (2 * q.recenterConstant) by positivity)))
  refine ⟨T, fun τ hτ => ?_⟩
  have h := hT τ hτ
  rw [le_div_iff₀ (by positivity)] at h
  nlinarith

/-- `T₀` 选择子约束的阈值（只依赖 `q`，与 kernel 常数无关）。 -/
def lateLambdaThr_P6HA (q : CutoffParameters) (hδq : Tendsto q.delta atTop (𝓝 0)) : ℝ :=
  Classical.choose (exists_lateLambda_P6HA q hδq)

theorem lateLambda_of_thr_P6HA (q : CutoffParameters) (hδq : Tendsto q.delta atTop (𝓝 0))
    {τ : ℝ} (hτ : lateLambdaThr_P6HA q hδq ≤ τ) : q.recenterConstant * q.delta τ ≤ 1 / 2 :=
  Classical.choose_spec (exists_lateLambda_P6HA q hδq) τ hτ

/-- **J7 ⇐ 参考 q-records（`_P6HA`，PROVED 相对 `hpc`、`hδ₀Cb`、`hT₀Λ`）**。 -/
theorem hJ7_loc_of_kernelDeltaT_P6HA {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q) (hδq : Tendsto q.delta atTop (𝓝 0))
    {Cb δ₀ : ℕ → ℝ} (hδ₀Cb : ∀ n, 2 * δ₀ n ^ 2 ≤ Cb n)
    (hpc : SurgeryParamCompat_P6PC q 2) (ind : ℕ → ℕ)
    {T₀ c σ L R Tn Tno : ℕ → ℝ} (hT₀Λ : ∀ n, lateLambdaThr_P6HA q hδq ≤ T₀ n)
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
    lateLambda_of_thr_P6HA q hδq ((hT₀Λ n).trans ((le_max_left _ _).trans hi))
  have hCb : 2 * q.delta τ ^ 2 ≤ Cb n :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ0.le hδτ 2) (by norm_num)).trans (hδ₀Cb n)
  have hρT := q.neckRadius_pos _ (hTno0 n)
  rw [qsLoc_eq_P6HA (hc n) hρT (hRρ' n) (hlt n), hsc n i hi b]
  exact birth_arith_P6JS hρT hδ0 (q.neckRadius_pos _ hτ0) le_rfl
    (deltaRho_le_window_two_P6HA hpc hτ0 (hTno0 n) hw) hCb
    (scale_gt_of_params_P6JS (records (ind n) i) hΛ b)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
