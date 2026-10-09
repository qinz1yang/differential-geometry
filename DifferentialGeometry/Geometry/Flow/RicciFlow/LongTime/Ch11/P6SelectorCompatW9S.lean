import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistLASlotP6DL2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CapBirthSupplyP6JS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongCeilingWireC11SC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Outer.ActivationAdapterC11W4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SpineInterfacesC11SP

/-!
# 选择子相容性（W9-SEL G1，后缀 `_W9S`）

A12′ v10_loc S14 顶层选择子 `εP6 / Csel / T₀sel / Qtsel / Cgsel` 与已登记约束的同一组选择。
* `εSel_W9S`：DISTLA2 `hdistLA_slot_P6DL2` 的全局 `ε₀`（先于 `P g εP6`）；正。
* `Csel := Γf.Ctime`：同槽环境内先验时间导数供给 `hTD_sel_W9S`（KT2c producer 的 `hTD`）。
* `T₀`：阈值 Θ 形（kernel 元组之后、`∀ A / ind` 之前）；多个下界取 `max` 再 `partialSups`。
  J8-b `lateDeltaThr_P6JS` 与原 `hT₀` 阈值同为下界：`lateDelta_of_theta_W9S`。
* `θ₀ := min(1/2, 1/(4·(Ctime+1)·Cg))`：只依赖 `(Ctime, Cg)`；`Cg = 4`。
* 子列（R9）：严格单调复合封闭、阈值细化、指标单调性质与 driver 前提沿复合子列保持。
无新 Prop 合同；全部 PROVED。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open GC.GeneralFlow (ClosedBirthConstants)

/-! ## εP6 -/

/-- 共享精度选择子：DISTLA2 槽的全局 `ε₀`（与 `Γ Γf` 无关）。 -/
def εSel_W9S.{v} : ClosedBirthConstants → ClosedBirthConstants → ℝ :=
  fun _ _ => Classical.choose (hdistLA_slot_P6DL2.{v})

theorem εSel_pos_W9S.{v} : ∀ Γ Γf, 0 < εSel_W9S.{v} Γ Γf :=
  fun _ _ => (Classical.choose_spec (hdistLA_slot_P6DL2.{v})).1

/-- 有限多个正门槛的共同下界（`min` 选择）：各槽对 `εP6` 反单调 ⇒ 同一 `εP6` 相容。 -/
theorem exists_common_eps_W9S {m : ℕ} (e : Fin (m + 1) → ℝ) (he : ∀ i, 0 < e i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ e i := by
  refine ⟨Finset.univ.inf' Finset.univ_nonempty e, ?_,
    fun i => Finset.inf'_le _ (Finset.mem_univ i)⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty e
  rw [hi]
  exact he i

/-! ## Csel := Γf.Ctime -/

/-- 槽环境（`T`、`F.tower = T.toChain.tower`、对角 `hq`）内的先验时间导数供给，常数 `Γf.Ctime`。 -/
theorem hTD_sel_W9S {pB : CutoffParameters} {Γf : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (T : GC.LongTime.Ch11.BlockTower_C11W pB Γf P g Cdist cMax Dstar εReserve)
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (hF : F.tower = T.toChain.tower)
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (GC.LongTime.Ch11.chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (GC.LongTime.Ch11.chainDiagonal_C11A T.toChain).neckRadius t) :
    GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Γf.Ctime :=
  GC.LongTime.Ch11.timeDerivativeSupply_of_blockTower_C11W4 T F hF q
    (GC.LongTime.Ch11.neckRadius_antitone_of_chainDiagonal_C11SP T.toChain q hq)
    (GC.LongTime.Ch11.hpref_of_chainDiagonal_C11SC T.toChain q (fun t ht => (hq t ht).2))

/-! ## T₀：Θ 形阈值 -/

/-- 由阈值族得到的单调 `T₀`（`partialSups` 包络）。 -/
def selT₀_W9S (Θ : ℕ → ℝ) : ℕ → ℝ := ⇑(partialSups Θ)

theorem selT₀_mono_W9S (Θ : ℕ → ℝ) : Monotone (selT₀_W9S Θ) :=
  (partialSups Θ).monotone

theorem le_selT₀_W9S (Θ : ℕ → ℝ) (n : ℕ) : Θ n ≤ selT₀_W9S Θ n :=
  le_partialSups Θ n

/-- 两个下界合成一个：`max` 阈值同时给出两条。 -/
theorem theta_max_W9S {Θ₁ Θ₂ T₀ : ℕ → ℝ} (h : ∀ n, max (Θ₁ n) (Θ₂ n) ≤ T₀ n) :
    (∀ n, Θ₁ n ≤ T₀ n) ∧ (∀ n, Θ₂ n ≤ T₀ n) :=
  ⟨fun n => (le_max_left _ _).trans (h n), fun n => (le_max_right _ _).trans (h n)⟩

/-- 引擎的共同 `T₀`：四个 Θ（J、J8、JF、JF8）同时被 `partialSups` 包络支配，且单调。 -/
theorem common_T₀_W9S (Θ₁ Θ₂ Θ₃ Θ₄ : ℕ → ℝ) :
    let T₀ := selT₀_W9S (fun n => max (max (Θ₁ n) (Θ₂ n)) (max (Θ₃ n) (Θ₄ n)))
    Monotone T₀ ∧ (∀ n, Θ₁ n ≤ T₀ n) ∧ (∀ n, Θ₂ n ≤ T₀ n) ∧ (∀ n, Θ₃ n ≤ T₀ n) ∧
      ∀ n, Θ₄ n ≤ T₀ n := by
  intro T₀
  have h := le_selT₀_W9S (fun n => max (max (Θ₁ n) (Θ₂ n)) (max (Θ₃ n) (Θ₄ n)))
  refine ⟨selT₀_mono_W9S _, fun n => ?_, fun n => ?_, fun n => ?_, fun n => ?_⟩
  · exact (le_max_left _ _).trans ((le_max_left _ _).trans (h n))
  · exact (le_max_right _ _).trans ((le_max_left _ _).trans (h n))
  · exact (le_max_left _ _).trans ((le_max_right _ _).trans (h n))
  · exact (le_max_right _ _).trans ((le_max_right _ _).trans (h n))

/-- **J8-b 的 Θ 形付法**：槽内 kernel 元组 `Cb`（只知正、上界）在 `Ctime₀` 处取值后，
`Θ n := max (Θ₀ n) (lateDeltaThr_P6JS q hδq (Cb Ctime₀) n)`；任意 `T₀ ≥ Θ` 上 late record 时刻满足
`Λδ ≤ 1/2 ∧ 2δ² ≤ Cb Ctime₀ n`，原阈值 `Θ₀`（`lateThrJ8_P6WR2` 等）亦保留。 -/
theorem lateDelta_of_theta_W9S (q : CutoffParameters) (hδq : Tendsto q.delta atTop (𝓝 0))
    (Cb : ℝ≥0 → ℕ → ℝ) (hCb : ∀ (C : ℝ≥0) (n : ℕ), 0 < Cb C n) (Ctime₀ : ℝ≥0)
    (Θ₀ T₀ : ℕ → ℝ)
    (hT : ∀ n, max (Θ₀ n) (lateDeltaThr_P6JS q hδq (Cb := fun n => Cb Ctime₀ n)
      (fun n => hCb Ctime₀ n) n) ≤ T₀ n) :
    (∀ n, Θ₀ n ≤ T₀ n) ∧ ∀ (n : ℕ) (t : ℝ), T₀ n ≤ t →
      q.recenterConstant * q.delta t ≤ 1 / 2 ∧ 2 * q.delta t ^ 2 ≤ Cb Ctime₀ n := by
  obtain ⟨h1, h2⟩ := theta_max_W9S hT
  exact ⟨h1, fun n t ht => lateDelta_of_thr_P6JS q hδq (fun n => hCb Ctime₀ n)
    ((h2 n).trans ht)⟩

/-! ## Cg / θ₀ -/

/-- 共享 `Cg`（lead：`Cgsel := 4`，RESID G2 已付）。 -/
def cgSel_W9S : ℝ := 4

/-- KS2 窗深 `θ₀ := min (1/2) (1/(4·(Ctime+1)·Cg))`，只依赖 `(Ctime, Cg)`，先于 `∀ A`。 -/
def theta0_W9S (Ctime : ℝ≥0) (Cg : ℝ) : ℝ :=
  min (1 / 2) (1 / (4 * ((Ctime : ℝ) + 1) * Cg))

/-- HARNACK A1 续作的全部 θ₀ 约束：`0 < θ₀ ≤ 1/2`、`θ₀ ≤ 1/(4·Ctime·Cg)`（乘法形
`θ₀·Ctime·Cg ≤ 1/4`）、N3 的 `Λ := 2Cg` 下 `Ctime·Λ·θ₀ ≤ 1/2`；`Cg ≥ 4 ≥ 1` 同时付 FOOT5 / HSTAY 门
与 HARNACK N1 `Q_n ≤ R_n ⇒ Q_n ≤ Cg·R_n`。 -/
theorem theta0_spec_W9S (Ctime : ℝ≥0) {Cg : ℝ} (hCg : 4 ≤ Cg) :
    0 < theta0_W9S Ctime Cg ∧ theta0_W9S Ctime Cg ≤ 1 / 2 ∧
      theta0_W9S Ctime Cg * Ctime * Cg ≤ 1 / 4 ∧
      (Ctime : ℝ) * (2 * Cg) * theta0_W9S Ctime Cg ≤ 1 / 2 ∧ 1 ≤ Cg := by
  have hC : (0 : ℝ) ≤ Ctime := Ctime.2
  have hCg0 : 0 < Cg := by linarith
  have hD : 0 < 4 * ((Ctime : ℝ) + 1) * Cg := by positivity
  have hle : theta0_W9S Ctime Cg ≤ 1 / (4 * ((Ctime : ℝ) + 1) * Cg) := min_le_right _ _
  have hpos : 0 < theta0_W9S Ctime Cg := lt_min (by norm_num) (by positivity)
  have hkey : theta0_W9S Ctime Cg * (4 * ((Ctime : ℝ) + 1) * Cg) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hle hD.le
    rwa [one_div, inv_mul_cancel₀ hD.ne'] at this
  have hA : theta0_W9S Ctime Cg * Ctime * Cg ≤ 1 / 4 := by nlinarith
  refine ⟨hpos, min_le_left _ _, hA, by nlinarith, by linarith⟩

theorem theta0_cgSel_W9S (Ctime : ℝ≥0) :
    0 < theta0_W9S Ctime cgSel_W9S ∧ theta0_W9S Ctime cgSel_W9S ≤ 1 / 2 ∧
      theta0_W9S Ctime cgSel_W9S * Ctime * cgSel_W9S ≤ 1 / 4 ∧
      (Ctime : ℝ) * (2 * cgSel_W9S) * theta0_W9S Ctime cgSel_W9S ≤ 1 / 2 ∧ 1 ≤ cgSel_W9S :=
  theta0_spec_W9S Ctime (le_refl 4)

/-- N1 的 `(SEP-ρ⁺)′` 形 `Q_n ≤ Cg·R_n` 由 `Q_n ≤ R_n` 与 `1 ≤ Cg` 给出。 -/
theorem q_le_cg_mul_W9S {Q R Cg : ℝ} (hQ : Q ≤ R) (hR : 0 ≤ R) (hCg : 1 ≤ Cg) : Q ≤ Cg * R := by
  nlinarith

/-! ## 子列（R9） -/

/-- 严格单调子列族在复合下封闭。 -/
theorem strictMono_comp_W9S {φ ψ : ℕ → ℕ} (hφ : StrictMono φ) (hψ : StrictMono ψ) :
    StrictMono (φ ∘ ψ) :=
  hφ.comp hψ

/-- 阈值细化：已在子列 `φ` 上，`Tno → ∞` ⇒ 存在再细化 `ψ` 使 `Θ n ≤ Tno (φ (ψ n))`。 -/
theorem exists_refine_W9S {Tno : ℕ → ℝ} (h : Tendsto Tno atTop atTop) {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (Θ : ℕ → ℝ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ n, Θ n ≤ Tno (φ (ψ n)) := by
  have h' : Tendsto (Tno ∘ φ) atTop atTop := h.comp hφ.tendsto_atTop
  have hev : ∀ n, ∀ᶠ k in atTop, Θ n ≤ (Tno ∘ φ) k := fun n => h'.eventually_ge_atTop (Θ n)
  obtain ⟨ψ, hψ, hψΘ⟩ := Filter.extraction_forall_of_eventually hev
  exact ⟨ψ, hψ, hψΘ⟩

/-- 指标单调（随指标减弱）的性质沿复合子列保持：A4 在 `φ` 上的结论经再细化 `ψ` 仍成立。 -/
theorem index_mono_transfer_W9S (Pr : ℕ → ℕ → Prop)
    (hPr : ∀ m n k, n ≤ m → Pr m k → Pr n k) {φ ψ : ℕ → ℕ} (hφ : ∀ m, Pr m (φ m))
    (hψ : StrictMono ψ) : ∀ n, Pr n (φ (ψ n)) :=
  fun n => hPr (ψ n) n _ (hψ.id_le n) (hφ (ψ n))

/-- **R9 共同子列**：A4 的 `∃ φ` 结论（指标单调性质 `Pr`）与 A1–A3 的阈值 `Θ n ≤ Tno(·)`
由同一严格单调子列同时满足。 -/
theorem exists_common_subseq_W9S {Tno : ℕ → ℝ} (h : Tendsto Tno atTop atTop)
    (Pr : ℕ → ℕ → Prop) (hPr : ∀ m n k, n ≤ m → Pr m k → Pr n k)
    (hA4 : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ m, Pr m (φ m)) (Θ : ℕ → ℝ) :
    ∃ χ : ℕ → ℕ, StrictMono χ ∧ (∀ n, Pr n (χ n)) ∧ ∀ n, Θ n ≤ Tno (χ n) := by
  obtain ⟨φ, hφ, hPφ⟩ := hA4
  obtain ⟨ψ, hψ, hΘ⟩ := exists_refine_W9S h hφ Θ
  exact ⟨φ ∘ ψ, hφ.comp hψ, fun n => index_mono_transfer_W9S Pr hPr hPφ hψ n, hΘ⟩

/-- driver 前提 `k + 1 ≤ T k` 沿严格单调重索引保持（`ind ↦ ind ∘ χ` 时 `Tno ↦ Tno ∘ χ`）。 -/
theorem succ_le_comp_W9S {T : ℕ → ℝ} (hT : ∀ k : ℕ, (k : ℝ) + 1 ≤ T k) {χ : ℕ → ℕ}
    (hχ : StrictMono χ) : ∀ k : ℕ, (k : ℝ) + 1 ≤ T (χ k) := by
  intro k
  have : (k : ℝ) ≤ (χ k : ℝ) := by exact_mod_cast hχ.id_le k
  linarith [hT (χ k)]

/-- 逐点前提（不含指标）沿任意重索引保持；`∀ᶠ` 性质沿严格单调子列保持。 -/
theorem eventually_comp_W9S {Q : ℕ → Prop} (hQ : ∀ᶠ k in atTop, Q k) {χ : ℕ → ℕ}
    (hχ : StrictMono χ) : ∀ᶠ n in atTop, Q (χ n) :=
  hχ.tendsto_atTop.eventually hQ

/-! ## consumer -/

example (Γ Γf : ClosedBirthConstants) :
    ∃ (ε θ₀ : ℝ), 0 < ε ∧ 0 < θ₀ ∧ θ₀ * (1 : ℝ≥0) * cgSel_W9S ≤ 1 / 4 :=
  ⟨εSel_W9S.{0} Γ Γf, theta0_W9S 1 cgSel_W9S, εSel_pos_W9S _ _,
    (theta0_cgSel_W9S 1).1, (theta0_cgSel_W9S 1).2.2.1⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
