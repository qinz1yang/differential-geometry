import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6WindowScaleP6HS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CapBirthP6J7

/-!
# Surgery 参数相容性：HSCALE 与 J7BIRTH 两个合同的共同根（O-CH11-PARAMCOMPAT，后缀 `_P6PC`）

两个 PROVISIONAL 合同都是"晚期 event 的 surgery 尺度 `(δ(τ)⁴ρ(τ)²)⁻¹` 压过一个目标量"：
* HSCALE `WindowNeckScaleBudget_P6HS`：窗口 event 时刻 `R ≤ ρ(τ)⁻²`（目标 = 选点曲率 `R`）；
* J7BIRTH `CapBirthBudget_P6J7`：`Qs n ≤ Cb n · scale`（目标 = `Qs n / Cb n`）。
records 的精细下界 `inv_two_mul_delta_sq_lt_static_scale_C11G`（`Λδ ≤ 1/2` ⇒ `(2δ⁴ρ²)⁻¹ < scale`）把两者都化成
**参数层**不等式；`CutoffParameters` 本身对 `δ`、`ρ` 没有任何时间结构，结构来自 chain。

**树内参数链事实**（`PreparedSpatialChain` / `PreparedSpatialSuccessor`）：`ρ` 是 antitone 阶梯——successor `n` 在
activation `(5/6)·3ⁿ` 之前保持旧 `ρ`、之后取 `(S.state (n+1)).radius`，`radius_le` 给 `r_{n+1} ≤ r_n`；
`δ` 在 `(3^{n-1}, 3ⁿ]` 上取 `accuracy n`。本文件 `neckRadius_diagonal_eq_band_P6PC` 把 diagonal 参数的 `ρ`
在 band `j` 上的值重证为 `(S.state j).radius`（树内同名事实是 `private`）。**树内没有任何相邻比下界**
（`r_{n+1}` 相对 `r_n` 可以任意小）。

**主合同 `SurgeryParamCompat_P6PC p θ`**（θ-局部步比）：`ρ` antitone，且 `0 ≤ x ≤ y ≤ θx ⇒ δ(x)ρ(x) ≤ ρ(y)`。
* 链上来源：`paramCompat_of_steps_P6PC`（抽象阶梯：稀疏步 `θ·s_j ≤ s_{j+1}` + 相邻比 `δ·r_j ≤ r_{j+1}`）与
  `paramCompat_of_chain_P6PC`（树内 chain，`θ ≤ 3`，唯一剩余前提 = 相邻比 `hstep`）。核心是
  `at_most_one_step_in_window_P6PC`：θ-窗内 step 指标至多加一。
* 与 Perelman / Kleiner–Lott 参数构造的对应：`r_j, δ_j` 在二进（这里三进）区间上取常值，`r_{j+1} ≤ r_j`；
  Perelman II Prop 5.1 的量词序是**先** `r_{m+1}`、**后**任意 `δ ≤ δ̄(r_{m+1})`，所以加一条
  `δ_m ≤ r_{m+1}/r_m` 只是把 `δ` 取得更小，**构造上可满足**；但树内 `PreparedSpatialChain` 的 successor
  **没有登记**这条关系（`accuracy_le` 只给 `accuracy n ≤ 1/(n+2)`）⇒ PROVISIONAL，owner = chain / successor 存在性。
* ⇒ HSCALE：合同 + hOpen8 的 Tn 行 `R ≤ ρ(Tn)⁻²` + 窗口比 `Tn ≤ θ·a`（K 单位 `aSeed = Tn − 1 ≥ 1` 给 `θ = 2`）
  ⇒ δ-弱化预算 `R·(δ(τ)ρ(τ))² ≤ 1`（`windowNeckDelta_of_paramCompat_P6PC`）⇒ CXJD `hscale`
  （`hscale_of_paramCompat_P6PC`，只要 `8·Q_b·δ² ≤ 1`）。**HSCALE 合同逐字推不出**：窗内可以恰有一次步，
  证书 `paramCompat_not_windowBudget_P6PC`（合同成立、Tn 行取等，`R ≤ ρ(τ)⁻²` 仍失败）。逐字形只在
  "窗内零步"下成立：`windowNeckScaleBudget_of_noStep_P6PC`（保留为证书 / 特例）。
* 步比是必要的：`not_windowDelta_without_ratio_P6PC`（步比 `d⁻³ > δ⁻¹` 时 δ-弱化预算也失败）。

**J7（`CapBirthParamCompat_P6PC`，PROVISIONAL[单点条件]）**：records 参数 `p n` 的 `δ, ρ` antitone ⇒
`τ ≥ thr n` 的所有 event 化为单点 `t* = max (thr n) 0`：`Λδ(t*) ≤ 1/2 ∧ 2·Qs n·δ(t*)⁴ρ(t*)² ≤ Cb n` ⇒
`CapBirthBudget_P6J7` 逐字（`capBirthBudget_of_paramCompat_P6PC`）。**J7 真缺口的第二种表述**（与 J7BIRTH 的
"KNOM `Tmin` 须依赖 `ind`"并列）：`Qs n = qcanSup_P6WR S (horizon (Ho n))` 取到 state `⌈horizon⌉` 的 `qcan`
（`qcan_state_le_qcanSup_P6PC`），horizon 随 `ind n` 无界、不受 `Tno` 控制，而单点 `t*` 的参数在 `ind` 之前固定
⇒ 单点条件一般不成立（`not_capBirthParamPoint_of_unbounded_P6PC`）；需要 KNOM 侧 `ind`/horizon 受 `Tno` 控制，
或 `qcan` 先验（只依赖常数、可在选 `δ` 之前知道）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-! ## 主合同与 inhabitant -/

/-- **主合同 `SurgeryParamCompat_P6PC`（PROVISIONAL；owner = chain / successor 存在性）**：`ρ` 在 `[0, ∞)` 上
antitone，且 θ-局部步比 `0 ≤ x ≤ y ≤ θx ⇒ δ(x)·ρ(x) ≤ ρ(y)`（`ρ` 在 θ-窗内最多降一个 `δ` 因子）。
链上 ⟸ 稀疏步 + 相邻比 `δ·r_j ≤ r_{j+1}`（`paramCompat_of_steps_P6PC` / `paramCompat_of_chain_P6PC`）；
Perelman 量词序 `r_{m+1}` 先、`δ` 后，构造上可满足，但树内 `PreparedSpatialChain` 的 successor 未登记此关系。 -/
def SurgeryParamCompat_P6PC (p : CutoffParameters) (θ : ℝ) : Prop :=
  AntitoneOn p.neckRadius (Ici 0) ∧
    ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ θ * x → p.delta x * p.neckRadius x ≤ p.neckRadius y

/-- 参数构造器（只换 `δ`、`ρ`，其余字段取自 `p₀`）：给合同 inhabitant 与 ℝ 证书用。 -/
def withRadii_P6PC (p₀ : CutoffParameters) (δ ρ : ℝ → ℝ) (hδ0 : ∀ t, 0 < δ t)
    (hδ1 : ∀ t, δ t < 1) (hρ : ∀ t, 0 < ρ t) : CutoffParameters :=
  { p₀ with
    delta := δ
    neckRadius := ρ
    delta_pos := fun t _ => hδ0 t
    delta_lt_one := fun t _ => hδ1 t
    neckRadius_pos := fun t _ => hρ t }

/-- 合同对常值 `ρ` 成立（任意 `θ`）。 -/
theorem paramCompat_of_const_P6PC (p : CutoffParameters) (θ : ℝ) {r : ℝ}
    (hρ : ∀ t, 0 ≤ t → p.neckRadius t = r) : SurgeryParamCompat_P6PC p θ := by
  refine ⟨fun x hx y hy _ => by rw [hρ x (mem_Ici.mp hx), hρ y (mem_Ici.mp hy)],
    fun x y hx hxy _ => ?_⟩
  have h1 := p.delta_lt_one x hx
  have h2 := p.neckRadius_pos x hx
  rw [hρ y (hx.trans hxy)]
  rw [hρ x hx] at h2 ⊢
  nlinarith

/-- 合同的 inhabitant（编译过的具体参数）：`δ ≡ 1/2`、`ρ ≡ 1`。 -/
theorem exists_paramCompat_P6PC (p₀ : CutoffParameters) (θ : ℝ) :
    ∃ p : CutoffParameters, SurgeryParamCompat_P6PC p θ :=
  ⟨withRadii_P6PC p₀ (fun _ => 1 / 2) (fun _ => 1) (fun _ => by norm_num) (fun _ => by norm_num)
      (fun _ => one_pos),
    paramCompat_of_const_P6PC _ θ (r := 1) (fun _ _ => rfl)⟩

/-- 合同在抛物重标度下不变（`θ` 不变）：K 单位 records 参数 `q.rescale_P6N c` 继承 `q` 的合同。 -/
theorem paramCompat_rescale_P6PC {q : CutoffParameters} {θ : ℝ}
    (hq : SurgeryParamCompat_P6PC q θ) (μ : ℝ) (hμ : 0 < μ) :
    SurgeryParamCompat_P6PC (q.rescale_P6N μ hμ) θ := by
  have hs : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  refine ⟨fun x hx y hy hxy => ?_, fun x y hx hxy hyθ => ?_⟩
  · change q.neckRadius (μ * y) / Real.sqrt μ ≤ q.neckRadius (μ * x) / Real.sqrt μ
    exact div_le_div_of_nonneg_right
      (hq.1 (mem_Ici.mpr (mul_nonneg hμ.le (mem_Ici.mp hx)))
        (mem_Ici.mpr (mul_nonneg hμ.le (mem_Ici.mp hy))) (mul_le_mul_of_nonneg_left hxy hμ.le))
      hs.le
  · change q.delta (μ * x) * (q.neckRadius (μ * x) / Real.sqrt μ) ≤
      q.neckRadius (μ * y) / Real.sqrt μ
    have hθx : μ * y ≤ θ * (μ * x) :=
      (mul_le_mul_of_nonneg_left hyθ hμ.le).trans_eq (by ring)
    have h := hq.2 (μ * x) (μ * y) (mul_nonneg hμ.le hx) (mul_le_mul_of_nonneg_left hxy hμ.le) hθx
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right h hs.le

/-! ## 窗口内至多一次步（抽象阶梯） -/

/-- 阶梯指标：`t` 落在第 `stepIndex_P6PC s hunb t` 个 band（第一个 `j` 使 `t ≤ s j`）。 -/
def stepIndex_P6PC (s : ℕ → ℝ) (hunb : ∀ t : ℝ, ∃ j, t ≤ s j) (t : ℝ) : ℕ :=
  by classical exact Nat.find (hunb t)

theorem stepIndex_spec_P6PC (s : ℕ → ℝ) (hunb : ∀ t : ℝ, ∃ j, t ≤ s j) (t : ℝ) :
    t ≤ s (stepIndex_P6PC s hunb t) ∧ ∀ i < stepIndex_P6PC s hunb t, s i < t := by
  classical
  refine ⟨Nat.find_spec (hunb t), fun i hi => lt_of_not_ge ?_⟩
  exact Nat.find_min (hunb t) hi

theorem stepIndex_le_P6PC (s : ℕ → ℝ) (hunb : ∀ t : ℝ, ∃ j, t ≤ s j) {t : ℝ} {j : ℕ}
    (h : t ≤ s j) : stepIndex_P6PC s hunb t ≤ j := by
  classical
  exact Nat.find_min' (hunb t) h

/-- **`at_most_one_step_in_window_P6PC`（PROVED）**：步时稀疏 `θ·s_j ≤ s_{j+1}`（`θ ≥ 0`）⇒ 任意 θ-窗
`0 ≤ x ≤ y ≤ θx` 内 step 指标至多加一（窗内至多一次参数步）。树内 chain 的步时 `(5/6)·3^j` 对 `θ ≤ 3` 稀疏；
hOpen8 的 K 窗 `[aSeed, Tn]` 在原时间里满足 `Tn ≤ 2·aSeed`（`window_le_two_mul_P6PC`），即 `θ = 2`。 -/
theorem at_most_one_step_in_window_P6PC (s : ℕ → ℝ) (hunb : ∀ t : ℝ, ∃ j, t ≤ s j) {θ : ℝ}
    (hθ : 0 ≤ θ) (hsparse : ∀ j, θ * s j ≤ s (j + 1)) {x y : ℝ} (hxy : x ≤ y) (hyθ : y ≤ θ * x) :
    stepIndex_P6PC s hunb x ≤ stepIndex_P6PC s hunb y ∧
      stepIndex_P6PC s hunb y ≤ stepIndex_P6PC s hunb x + 1 := by
  have hx := stepIndex_spec_P6PC s hunb x
  have hy := stepIndex_spec_P6PC s hunb y
  refine ⟨stepIndex_le_P6PC s hunb (hxy.trans hy.1), stepIndex_le_P6PC s hunb ?_⟩
  exact hyθ.trans ((mul_le_mul_of_nonneg_left hx.1 hθ).trans (hsparse _))

/-- **链上来源（抽象阶梯，PROVED）**：`ρ` 在 band `j`（`s_{j-1} < t ≤ s_j`）上取 `r_j`、`r` antitone、步时稀疏
`θ·s_j ≤ s_{j+1}`、相邻比 `δ(x)·r_j ≤ r_{j+1}`（`x` 在 band `j`）⇒ `SurgeryParamCompat_P6PC p θ`。 -/
theorem paramCompat_of_steps_P6PC {p : CutoffParameters} {θ : ℝ} (hθ : 0 ≤ θ) (s r : ℕ → ℝ)
    (hunb : ∀ t : ℝ, ∃ j, t ≤ s j)
    (hρ : ∀ j t, 0 ≤ t → t ≤ s j → (∀ i < j, s i < t) → p.neckRadius t = r j)
    (hr : Antitone r) (hsparse : ∀ j, θ * s j ≤ s (j + 1))
    (hstep : ∀ j x, 0 ≤ x → x ≤ s j → (∀ i < j, s i < x) → p.delta x * r j ≤ r (j + 1)) :
    SurgeryParamCompat_P6PC p θ := by
  have hval : ∀ t, 0 ≤ t → p.neckRadius t = r (stepIndex_P6PC s hunb t) := fun t ht =>
    hρ _ t ht (stepIndex_spec_P6PC s hunb t).1 (stepIndex_spec_P6PC s hunb t).2
  refine ⟨fun x hx y hy hxy => ?_, fun x y hx hxy hyθ => ?_⟩
  · rw [hval x (mem_Ici.mp hx), hval y (mem_Ici.mp hy)]
    exact hr (stepIndex_le_P6PC s hunb (hxy.trans (stepIndex_spec_P6PC s hunb y).1))
  · have hy0 : 0 ≤ y := hx.trans hxy
    obtain ⟨h1, h2⟩ := at_most_one_step_in_window_P6PC s hunb hθ hsparse hxy hyθ
    have hd := p.delta_lt_one x hx
    have hρx := p.neckRadius_pos x hx
    rw [hval y hy0]
    rcases Nat.eq_or_lt_of_le h2 with h3 | h3
    · rw [h3]
      rw [hval x hx]
      exact hstep _ x hx (stepIndex_spec_P6PC s hunb x).1 (stepIndex_spec_P6PC s hunb x).2
    · have h4 : stepIndex_P6PC s hunb y = stepIndex_P6PC s hunb x := by omega
      rw [h4, ← hval x hx]
      nlinarith

/-- K 窗的原时间比：`aSeed = Tn − 1²`、`1 ≤ aSeed ≤ a` ⇒ `Tn ≤ 2·a`（hOpen8 的 seed clock 行）。 -/
theorem window_le_two_mul_P6PC {aSeed a Tn : ℝ} (hclock : aSeed = Tn - 1 ^ 2) (h1 : 1 ≤ aSeed)
    (has : aSeed ≤ a) : Tn ≤ 2 * a := by
  rw [one_pow] at hclock
  linarith

/-! ## 树内 chain：diagonal `ρ` 的 band 值与合同的链上形 -/

section Chain

variable {pBase : CutoffParameters} {C : GC.GeneralFlow.ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- 树内 chain 的步时（activation）`(5/6)·3^j`。 -/
theorem nat_le_activation_P6PC (n : ℕ) : (n : ℝ) ≤ (5 / 6 : ℝ) * 3 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
    rw [Nat.cast_add, Nat.cast_one, pow_succ]
    nlinarith

theorem activation_mono_P6PC {m n : ℕ} (h : m ≤ n) :
    (5 / 6 : ℝ) * 3 ^ m ≤ (5 / 6 : ℝ) * 3 ^ n :=
  mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) h) (by norm_num)

/-- `(S.state m)` 的 `ρ` 在 band `j`（`j ≤ m`）上等于 `(S.state j).radius`（radius_after_activation /
radius_before_activation 归纳；树内同名事实 `radius_eq_on_activation_band` 是 `private`，此处重证）。 -/
theorem state_neckRadius_eq_band_P6PC (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g)
    (j m : ℕ) (hjm : j ≤ m) {t : ℝ} (ht0 : 0 ≤ t) (hright : t ≤ (5 / 6 : ℝ) * 3 ^ j)
    (hleft : ∀ i < j, (5 / 6 : ℝ) * 3 ^ i < t) :
    (S.state m).parameters.neckRadius t = (S.state j).radius := by
  induction m, hjm using Nat.le_induction with
  | base =>
    cases j with
    | zero => exact (S.state 0).radius_after t ht0
    | succ k => exact (S.successor k).radius_after_activation t (hleft k (Nat.lt_succ_self k))
  | succ m hjm ih =>
    exact ((S.successor m).radius_before_activation t
      (hright.trans (activation_mono_P6PC hjm))).trans ih

/-- **diagonal 参数的 band 值（PROVED）**：`q := diagonal (S.observation ·).parameters` 在 band `j` 上
`q.neckRadius t = (S.state j).radius`。 -/
theorem neckRadius_diagonal_eq_band_P6PC (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g)
    (j : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (hright : t ≤ (5 / 6 : ℝ) * 3 ^ j)
    (hleft : ∀ i < j, (5 / 6 : ℝ) * 3 ^ i < t) :
    (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius t =
      (S.state j).radius := by
  change (S.state (Nat.ceil t + 1)).parameters.neckRadius t = _
  refine state_neckRadius_eq_band_P6PC S j (Nat.ceil t + 1) ?_ ht0 hright hleft
  cases j with
  | zero => exact Nat.zero_le _
  | succ k =>
    have hk : (k : ℝ) < t := (nat_le_activation_P6PC k).trans_lt (hleft k (Nat.lt_succ_self k))
    have hk' : k ≤ Nat.ceil t := by exact_mod_cast hk.le.trans (Nat.le_ceil t)
    omega

/-- **合同的链上形（PROVISIONAL[相邻比 `hstep`]）**：树内 chain 的 diagonal 参数满足
`SurgeryParamCompat_P6PC q θ`（`0 ≤ θ ≤ 3`），唯一前提 = 相邻比：band `j` 内 `q.delta x · r_j ≤ r_{j+1}`
（`r_j = (S.state j).radius`）。antitone、band 值、步时稀疏、窗内至多一次步全部由树内事实给出。
`hstep` 是 Perelman 量词序（`r_{j+1}` 先、`δ ≤ δ̄` 后）下构造可满足的选择约束，树内 successor 未登记。 -/
theorem paramCompat_of_chain_P6PC (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ3 : θ ≤ 3)
    (hstep : ∀ j x, 0 ≤ x → x ≤ (5 / 6 : ℝ) * 3 ^ j → (∀ i < j, (5 / 6 : ℝ) * 3 ^ i < x) →
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta x *
        (S.state j).radius ≤ (S.state (j + 1)).radius) :
    SurgeryParamCompat_P6PC (CutoffParameters.diagonal (fun n => (S.observation n).parameters)) θ :=
  paramCompat_of_steps_P6PC hθ0 (fun j => (5 / 6 : ℝ) * 3 ^ j) (fun j => (S.state j).radius)
    (fun t => ⟨Nat.ceil t, (Nat.le_ceil t).trans (nat_le_activation_P6PC _)⟩)
    (fun j _ ht0 hright hleft => neckRadius_diagonal_eq_band_P6PC S j ht0 hright hleft)
    (antitone_nat_of_succ_le fun n => (S.successor n).radius_le)
    (fun j => by
      have hp : (0 : ℝ) ≤ 3 ^ j := by positivity
      change θ * ((5 / 6 : ℝ) * 3 ^ j) ≤ (5 / 6 : ℝ) * 3 ^ (j + 1)
      rw [pow_succ]
      nlinarith)
    hstep

end Chain

/-! ## ⇒ HSCALE：δ-弱化预算与 CXJD `hscale`（PROVISIONAL[合同]） -/

/-- 单点核：合同 + `Tn ≤ θ·a`、`a < τ` ⇒ `δ(τ)ρ(τ) ≤ ρ(Tn)`（`τ ≤ Tn` 用步比，`τ > Tn` 用 antitone）。 -/
theorem neckDelta_le_of_paramCompat_P6PC {p : CutoffParameters} {θ a Tn τ : ℝ}
    (hpc : SurgeryParamCompat_P6PC p θ) (hθ : 0 ≤ θ) (hTn0 : 0 ≤ Tn) (hwin : Tn ≤ θ * a)
    (haτ : a < τ) (hτ0 : 0 ≤ τ) :
    p.delta τ * p.neckRadius τ ≤ p.neckRadius Tn := by
  rcases le_or_gt τ Tn with hτT | hTτ
  · exact hpc.2 τ Tn hτ0 hτT (hwin.trans (mul_le_mul_of_nonneg_left haτ.le hθ))
  · have h1 := hpc.1 (mem_Ici.mpr hTn0) (mem_Ici.mpr hτ0) hTτ.le
    have h2 := p.delta_lt_one τ hτ0
    have h3 := p.neckRadius_pos τ hτ0
    nlinarith

/-- **δ-弱化窗口预算（PROVISIONAL[合同]）**：合同 + hOpen8 Tn 行 `R ≤ ρ(Tn)⁻²` + `Tn ≤ θ·a` ⇒ 窗口内
（`T₀ ≤ τ`、`a < τ`）每个 event `R·(δ(τ)ρ(τ))² ≤ 1`。比 HSCALE 合同少一个 `δ(τ)²` 因子；HSCALE 逐字形
推不出（`paramCompat_not_windowBudget_P6PC`）。 -/
theorem windowNeckDelta_of_paramCompat_P6PC {H : ObservedHistory.{u}} {p : CutoffParameters}
    {θ T₀ a Tn R : ℝ} (hpc : SurgeryParamCompat_P6PC p θ) (hθ : 0 ≤ θ) (hTn0 : 0 ≤ Tn)
    (hwin : Tn ≤ θ * a) (hTn : R ≤ (p.neckRadius Tn ^ 2)⁻¹) :
    ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → a < H.time e.succ →
      R * (p.delta (H.time e.succ) * p.neckRadius (H.time e.succ)) ^ 2 ≤ 1 := by
  intro e _ hae
  have hτ := H.time_nonneg e.succ
  have hle := neckDelta_le_of_paramCompat_P6PC hpc hθ hTn0 hwin hae hτ
  have hd := p.delta_pos _ hτ
  have hr := p.neckRadius_pos _ hτ
  have hrT := p.neckRadius_pos _ hTn0
  have hsq : (p.delta (H.time e.succ) * p.neckRadius (H.time e.succ)) ^ 2 ≤
      p.neckRadius Tn ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
  have hRρ : R * p.neckRadius Tn ^ 2 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hTn (pow_pos hrT 2).le
    rwa [inv_mul_cancel₀ (pow_pos hrT 2).ne'] at h
  rcases le_or_gt 0 R with hR | hR
  · nlinarith [mul_le_mul_of_nonneg_left hsq hR]
  · nlinarith [sq_nonneg (p.delta (H.time e.succ) * p.neckRadius (H.time e.succ))]

/-- **⇒ CXJD `hscale`（PROVISIONAL[合同]）**：records + 合同 + Tn 行 + `Tn ≤ θ·a` + 窗口 δ 小
（`Λδ ≤ 1/2`、`8·Q_b·δ² ≤ 1`）+ 3/r² 项 ⇒ `exists_crossSlab_ceiling_CXJD` 的 `hscale` 逐字。经
`hscale_of_fineBudget_P6HS`（G1a，PROVED），不经 HSCALE 合同逐字形。 -/
theorem hscale_of_paramCompat_P6PC {H : ObservedHistory.{u}} {p : CutoffParameters}
    {θ T₀ a Tn R r Qb : ℝ}
    (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e p)
    (hpc : SurgeryParamCompat_P6PC p θ) (hθ : 0 ≤ θ) (hTn0 : 0 ≤ Tn) (hwin : Tn ≤ θ * a)
    (hTn : R ≤ (p.neckRadius Tn ^ 2)⁻¹)
    (hδ : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → a < H.time e.succ →
      p.recenterConstant * p.delta (H.time e.succ) ≤ 1 / 2 ∧
        8 * Qb * p.delta (H.time e.succ) ^ 2 ≤ 1)
    (h3 : 3 / r ^ 2 ≤ 2 * (Qb * R)) (hQb : 0 ≤ Qb) :
    ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b, a < H.time e.succ →
      2 * max (3 / r ^ 2) (2 * (Qb * R)) < ((records e he).static b).neck.scale := by
  have hW := windowNeckDelta_of_paramCompat_P6PC (H := H) (T₀ := T₀) hpc hθ hTn0 hwin hTn
  refine hscale_of_fineBudget_P6HS (M := 2 * max (3 / r ^ 2) (2 * (Qb * R))) records
    (fun e he hae => ⟨(hδ e he hae).1, ?_⟩)
  have hτ := H.time_nonneg e.succ
  have hk := hW e he hae
  have hd := (hδ e he hae).2
  have hd0 := p.delta_pos _ hτ
  set d := p.delta (H.time e.succ)
  set ρ := p.neckRadius (H.time e.succ)
  have h8 : 0 ≤ 8 * Qb * d ^ 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hk h8
  have heq : 2 * (2 * (2 * (Qb * R))) * (d ^ 4 * ρ ^ 2) = 8 * Qb * d ^ 2 * (R * (d * ρ) ^ 2) := by
    ring
  rw [max_eq_right h3, heq]
  linarith

/-- **K 单位装配**：hOpen8 的 records 参数是 `q.rescale_P6N c`；`q` 的合同（θ）经
`paramCompat_rescale_P6PC` 下传，K 窗 `aSeed = Tn − 1 ≥ 1`、`aSeed ≤ a` 给 `θ = 2` 的窗口比。 -/
theorem hscale_of_paramCompat_rescale_P6PC {H : ObservedHistory.{u}} {q : CutoffParameters}
    {c : ℝ} (hc : 0 < c) {T₀ aSeed a Tn R r Qb : ℝ}
    (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ →
      GeometricCutoffRecord H e (q.rescale_P6N c hc))
    (hpc : SurgeryParamCompat_P6PC q 2) (hclock : aSeed = Tn - 1 ^ 2) (h1 : 1 ≤ aSeed)
    (has : aSeed ≤ a) (hTn : R ≤ ((q.rescale_P6N c hc).neckRadius Tn ^ 2)⁻¹)
    (hδ : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → a < H.time e.succ →
      (q.rescale_P6N c hc).recenterConstant * (q.rescale_P6N c hc).delta (H.time e.succ) ≤ 1 / 2 ∧
        8 * Qb * (q.rescale_P6N c hc).delta (H.time e.succ) ^ 2 ≤ 1)
    (h3 : 3 / r ^ 2 ≤ 2 * (Qb * R)) (hQb : 0 ≤ Qb) :
    ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b, a < H.time e.succ →
      2 * max (3 / r ^ 2) (2 * (Qb * R)) < ((records e he).static b).neck.scale := by
  have hTn0 : 0 ≤ Tn := by rw [one_pow] at hclock; linarith
  exact hscale_of_paramCompat_P6PC records (paramCompat_rescale_P6PC hpc c hc) (by norm_num) hTn0
    (window_le_two_mul_P6PC hclock h1 has) hTn hδ h3 hQb

/-! ## (a) 零步形 ⇒ HSCALE 合同逐字（证书 / 特例） -/

/-- **(a)（PROVED，特例）**：`ρ` antitone + 窗口 `(a, Tn]` 内 `ρ` 常值（窗内零步）+ Tn 行 ⇒
`WindowNeckScaleBudget_P6HS` **逐字**。零步前提一般不成立（树内步时 `(5/6)·3ⁿ` 只保证窗内至多一次步）。 -/
theorem windowNeckScaleBudget_of_noStep_P6PC {H : ObservedHistory.{u}} {p : CutoffParameters}
    {T₀ a Tn R : ℝ} (hanti : AntitoneOn p.neckRadius (Ici 0)) (hTn0 : 0 ≤ Tn)
    (hflat : ∀ τ, a < τ → τ ≤ Tn → p.neckRadius τ = p.neckRadius Tn)
    (hTn : R ≤ (p.neckRadius Tn ^ 2)⁻¹) : WindowNeckScaleBudget_P6HS H p T₀ a R := by
  intro e _ hae
  have hτ := H.time_nonneg e.succ
  rcases le_or_gt (H.time e.succ) Tn with hle | hlt
  · rw [hflat _ hae hle]
    exact hTn
  · have h1 := hanti (mem_Ici.mpr hTn0) (mem_Ici.mpr hτ) hlt.le
    have h2 := p.neckRadius_pos _ hτ
    have h3 : p.neckRadius (H.time e.succ) ^ 2 ≤ p.neckRadius Tn ^ 2 :=
      pow_le_pow_left₀ h2.le h1 2
    exact hTn.trans (inv_anti₀ (pow_pos h2 2) h3)

/-! ## 证书（HSCALE 侧） -/

/-- **证书 1（`_P6PC`）**：合同推不出 HSCALE 合同逐字。`δ ≡ d`、`ρ = 1_{t<1} + d·1_{t≥1}`（窗内恰一次步，
步比 `d⁻¹`）满足 `SurgeryParamCompat_P6PC p θ`（任意 `θ`），Tn 行取等 `R = ρ(1)⁻²`，但窗内 `τ = 3/4`
处 `R ≤ ρ(τ)⁻²` 失败。 -/
theorem paramCompat_not_windowBudget_P6PC (p₀ : CutoffParameters) {d : ℝ} (hd0 : 0 < d)
    (hd1 : d < 1) (θ : ℝ) :
    ∃ p : CutoffParameters, SurgeryParamCompat_P6PC p θ ∧
      ¬ ((p.neckRadius 1 ^ 2)⁻¹ ≤ (p.neckRadius (3 / 4) ^ 2)⁻¹) := by
  have hρpos : ∀ t : ℝ, 0 < (if t < 1 then (1 : ℝ) else d) := fun t => by
    split_ifs
    · exact one_pos
    · exact hd0
  refine ⟨withRadii_P6PC p₀ (fun _ => d) (fun t => if t < 1 then 1 else d) (fun _ => hd0)
    (fun _ => hd1) hρpos, ⟨?_, ?_⟩, ?_⟩
  · intro x _ y _ hxy
    change (if y < 1 then (1 : ℝ) else d) ≤ (if x < 1 then (1 : ℝ) else d)
    split_ifs <;> first | exact le_rfl | exact hd1.le | (exfalso; linarith)
  · intro x y _ _ _
    change d * (if x < 1 then (1 : ℝ) else d) ≤ (if y < 1 then (1 : ℝ) else d)
    split_ifs <;> nlinarith
  · change ¬ (((if (1 : ℝ) < 1 then (1 : ℝ) else d) ^ 2)⁻¹ ≤
      ((if (3 / 4 : ℝ) < 1 then (1 : ℝ) else d) ^ 2)⁻¹)
    rw [ite_eq_right (lt_irrefl _), ite_eq_left (by norm_num : (3 / 4 : ℝ) < 1), one_pow, inv_one]
    intro h
    have hd2 : d ^ 2 < 1 := by nlinarith
    have := (one_lt_inv₀ (pow_pos hd0 2)).mpr hd2
    linarith

/-- **证书 2（`_P6PC`）**：没有步比时 δ-弱化预算也失败。`δ ≡ d`、`ρ = 1_{t<1} + d³·1_{t≥1}`（步比 `d⁻³ > δ⁻¹`），
Tn 行取等 `R = ρ(1)⁻²`，`τ = 3/4`（`Tn = 1 ≤ 2·(1/2)`）处 `R·(δρ)² = d⁻⁴ > 1`。 -/
theorem not_windowDelta_without_ratio_P6PC (p₀ : CutoffParameters) {d : ℝ} (hd0 : 0 < d)
    (hd1 : d < 1) :
    ∃ p : CutoffParameters, AntitoneOn p.neckRadius (Ici 0) ∧
      ¬ ((p.neckRadius 1 ^ 2)⁻¹ * (p.delta (3 / 4) * p.neckRadius (3 / 4)) ^ 2 ≤ 1) := by
  have hd3 : 0 < d ^ 3 := pow_pos hd0 3
  have hd3' : d ^ 3 < 1 := pow_lt_one₀ hd0.le hd1 (by norm_num)
  have hρpos : ∀ t : ℝ, 0 < (if t < 1 then (1 : ℝ) else d ^ 3) := fun t => by
    split_ifs
    · exact one_pos
    · exact hd3
  refine ⟨withRadii_P6PC p₀ (fun _ => d) (fun t => if t < 1 then 1 else d ^ 3) (fun _ => hd0)
    (fun _ => hd1) hρpos, ?_, ?_⟩
  · intro x _ y _ hxy
    change (if y < 1 then (1 : ℝ) else d ^ 3) ≤ (if x < 1 then (1 : ℝ) else d ^ 3)
    split_ifs <;> first | exact le_rfl | exact hd3'.le | (exfalso; linarith)
  · change ¬ (((if (1 : ℝ) < 1 then (1 : ℝ) else d ^ 3) ^ 2)⁻¹ *
      (d * (if (3 / 4 : ℝ) < 1 then (1 : ℝ) else d ^ 3)) ^ 2 ≤ 1)
    rw [ite_eq_right (lt_irrefl _), ite_eq_left (by norm_num : (3 / 4 : ℝ) < 1), mul_one]
    intro h
    have h6 : (d ^ 3) ^ 2 = d ^ 4 * d ^ 2 := by ring
    have hd4 : d ^ 4 < 1 := pow_lt_one₀ hd0.le hd1 (by norm_num)
    have hd2 : 0 < d ^ 2 := pow_pos hd0 2
    rw [h6, mul_inv, mul_assoc, inv_mul_cancel₀ hd2.ne', mul_one] at h
    have := (one_lt_inv₀ (pow_pos hd0 4)).mpr hd4
    linarith

/-! ## ⇒ J7：单点参数条件（PROVISIONAL[单点条件]） -/

/-- **J7 参数合同 `CapBirthParamCompat_P6PC`（PROVISIONAL；owner = records supplier / KNOM + chain）**：
records 参数 `p n` 的 `δ, ρ` 在 `[0, ∞)` antitone，并在单点 `t* = max (thr n) 0` 上
`Λδ(t*) ≤ 1/2` 且 `2·Qs n·δ(t*)⁴ρ(t*)² ≤ Cb n`。antitone 把 `τ ≥ thr n` 的全部 event 化到 `t*`。
一般不成立：`Qs n = qcanSup_P6WR S (horizon (Ho n))` 取到 state `⌈horizon⌉` 的 `qcan`，horizon 随 `ind n`
无界（J7 真缺口的第二种表述，与 J7BIRTH 的 "KNOM `Tmin` 须依赖 `ind`" 并列）。 -/
def CapBirthParamCompat_P6PC (p : ℕ → CutoffParameters) (thr Qs Cb : ℕ → ℝ) : Prop :=
  ∀ n, AntitoneOn (p n).delta (Ici 0) ∧ AntitoneOn (p n).neckRadius (Ici 0) ∧
    (p n).recenterConstant * (p n).delta (max (thr n) 0) ≤ 1 / 2 ∧
    2 * Qs n * ((p n).delta (max (thr n) 0) ^ 4 * (p n).neckRadius (max (thr n) 0) ^ 2) ≤ Cb n

/-- 合同的 inhabitant：`Qs ≤ 0 ≤ Cb` 时取 `δ ≡ 1/(2Λ)`、`ρ ≡ 1`。 -/
theorem exists_capBirthParamCompat_P6PC (p₀ : CutoffParameters) {thr Qs Cb : ℕ → ℝ}
    (hQs : ∀ n, Qs n ≤ 0) (hCb : ∀ n, 0 ≤ Cb n) :
    ∃ p : ℕ → CutoffParameters, CapBirthParamCompat_P6PC p thr Qs Cb := by
  have hΛ := p₀.recenterConstant_ge_four
  have hpos : ∀ _ : ℝ, 0 < 1 / (2 * p₀.recenterConstant) := fun _ => by positivity
  have hlt : ∀ _ : ℝ, 1 / (2 * p₀.recenterConstant) < 1 := fun _ => by
    rw [div_lt_one (by positivity)]
    linarith
  refine ⟨fun _ => withRadii_P6PC p₀ (fun _ => 1 / (2 * p₀.recenterConstant)) (fun _ => 1) hpos hlt
    (fun _ => one_pos), fun n => ⟨fun _ _ _ _ _ => le_rfl, fun _ _ _ _ _ => le_rfl, ?_, ?_⟩⟩
  · change p₀.recenterConstant * (1 / (2 * p₀.recenterConstant)) ≤ 1 / 2
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  · change 2 * Qs n * ((1 / (2 * p₀.recenterConstant)) ^ 4 * 1 ^ 2) ≤ Cb n
    have h4 : 0 ≤ (1 / (2 * p₀.recenterConstant)) ^ 4 * 1 ^ 2 := by positivity
    nlinarith [hQs n, hCb n]

/-- **单 record 核（PROVED）**：antitone `δ, ρ`、单点 `t ≤ τ` 上 `Λδ(t) ≤ 1/2` 与 `2·Qs·δ(t)⁴ρ(t)² ≤ Cb`、
`0 ≤ Cb·scale` ⇒ `Qs ≤ Cb·scale`。 -/
theorem qs_le_of_paramPoint_P6PC {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {p : CutoffParameters} (Rec : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex) {Qs Cb t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ H.time i.succ)
    (hδa : AntitoneOn p.delta (Ici 0)) (hρa : AntitoneOn p.neckRadius (Ici 0))
    (hΛ : p.recenterConstant * p.delta t ≤ 1 / 2)
    (hpt : 2 * Qs * (p.delta t ^ 4 * p.neckRadius t ^ 2) ≤ Cb)
    (hCs : 0 ≤ Cb * (Rec.static b).neck.scale) :
    Qs ≤ Cb * (Rec.static b).neck.scale := by
  have hτ := H.time_nonneg i.succ
  have hd := hδa (mem_Ici.mpr ht0) (mem_Ici.mpr hτ) ht
  have hr := hρa (mem_Ici.mpr ht0) (mem_Ici.mpr hτ) ht
  have hdτ := p.delta_pos _ hτ
  have hrτ := p.neckRadius_pos _ hτ
  have hΛ4 := p.recenterConstant_ge_four
  have hΛτ : p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hd (by linarith)).trans hΛ
  have hlow := Rec.inv_two_mul_delta_sq_lt_static_scale_C11G hΛτ b
  set sc := (Rec.static b).neck.scale
  set hτv := p.delta (H.time i.succ) ^ 4 * p.neckRadius (H.time i.succ) ^ 2
  have hhpos : 0 < hτv := by positivity
  have hsc : 0 < sc := (inv_pos.mpr (by positivity)).trans hlow
  have h1 : 1 < sc * (2 * hτv) := (inv_lt_iff_one_lt_mul₀ (by positivity)).mp hlow
  have hht : hτv ≤ p.delta t ^ 4 * p.neckRadius t ^ 2 :=
    mul_le_mul (pow_le_pow_left₀ hdτ.le hd 4) (pow_le_pow_left₀ hrτ.le hr 2) (by positivity)
      (pow_nonneg (hdτ.le.trans hd) 4)
  rcases le_or_gt Qs 0 with hQ | hQ
  · linarith
  · have h2 : Qs < Qs * (sc * (2 * hτv)) := lt_mul_of_one_lt_right hQ h1
    have h3 : 2 * Qs * hτv ≤ Cb := (mul_le_mul_of_nonneg_left hht (by linarith)).trans hpt
    have h4 := mul_le_mul_of_nonneg_right h3 hsc.le
    nlinarith

/-- **G2 核（PROVISIONAL[`CapBirthParamCompat_P6PC`]）**：J7 参数合同 + `0 ≤ Cb·scale` ⇒
`CapBirthBudget_P6J7` **逐字**（同一 `recordsK`）。 -/
theorem capBirthBudget_of_paramCompat_P6PC {Ho : ℕ → RetainedCoreHistory.{u}} {thr : ℕ → ℝ}
    {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (Ho n).eventCount), thr n ≤ (Ho n).time i.succ →
      GeometricCutoffRecord (Ho n).toHistory i (p n)}
    {Qs Cb : ℕ → ℝ} (hpc : CapBirthParamCompat_P6PC p thr Qs Cb)
    (hCs : ∀ n i hi b, 0 ≤ Cb n * ((recordsK n i hi).static b).neck.scale) :
    CapBirthBudget_P6J7 Ho thr p recordsK Qs Cb :=
  fun n i hi b => qs_le_of_paramPoint_P6PC (recordsK n i hi) b (le_max_right _ _)
    (max_le hi ((Ho n).toHistory.time_nonneg i.succ)) (hpc n).1 (hpc n).2.1 (hpc n).2.2.1
    (hpc n).2.2.2 (hCs n i hi b)

/-- J7b 形（hOpen8 第二合取实际带的 `max 0 1 ≤ Cb·scale`）给出 `0 ≤ Cb·scale`。 -/
theorem capBirthBudget_of_paramCompat_J7b_P6PC {Ho : ℕ → RetainedCoreHistory.{u}} {thr : ℕ → ℝ}
    {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (Ho n).eventCount), thr n ≤ (Ho n).time i.succ →
      GeometricCutoffRecord (Ho n).toHistory i (p n)}
    {Qs Cb : ℕ → ℝ} (hpc : CapBirthParamCompat_P6PC p thr Qs Cb)
    (hJ7b : ∀ n i hi b, max (0 : ℝ) 1 ≤ Cb n * ((recordsK n i hi).static b).neck.scale) :
    CapBirthBudget_P6J7 Ho thr p recordsK Qs Cb :=
  capBirthBudget_of_paramCompat_P6PC hpc fun n i hi b =>
    zero_le_one.trans ((le_max_right (0 : ℝ) 1).trans (hJ7b n i hi b))

/-! ## 证书（J7 侧） -/

/-- **J7 缺口事实（PROVED）**：`qcanSup_P6WR S v` 取到 state `⌈v⌉₊` 的 `qcan`
（`Qs n` 依赖 horizon 处的未来 state）。 -/
theorem qcan_state_le_qcanSup_P6PC {pBase : CutoffParameters}
    {C : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g) (v : ℝ) :
    (S.state (Nat.ceil v)).prepared.qcan ≤ GC.LongTime.Ch11.qcanSup_P6WR S v :=
  Finset.le_sup' (fun m => (S.state m).prepared.qcan)
    (Finset.mem_range.mpr (Nat.lt_succ_self _))

/-- **J7 证书（`_P6PC`）**：单点数据 `h = δ(t*)⁴ρ(t*)² > 0` 在 `ind` 之前固定，而 `Qs = Q(horizon)` 随 horizon
无界（`Tendsto Q atTop atTop`）⇒ 存在 horizon 使单点条件失败。 -/
theorem not_capBirthParamPoint_of_unbounded_P6PC {Q : ℝ → ℝ} (hQ : Tendsto Q atTop atTop)
    {h : ℝ} (hh : 0 < h) (Cb : ℝ) : ∃ v : ℝ, ¬ (2 * Q v * h ≤ Cb) := by
  obtain ⟨v, hv⟩ := (hQ.eventually_gt_atTop (Cb / (2 * h))).exists
  refine ⟨v, fun hle => ?_⟩
  have h2 : Cb / (2 * h) * (2 * h) = Cb := div_mul_cancel₀ Cb (by positivity)
  have h3 := mul_lt_mul_of_pos_right hv (by positivity : 0 < 2 * h)
  nlinarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
