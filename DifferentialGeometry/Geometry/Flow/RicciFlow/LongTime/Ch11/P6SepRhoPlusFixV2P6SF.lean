import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HscaleKSepRhoP6HN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KdataRescaleP6X3

/-!
# (SEP-ρ⁺)′：天花板统一在 seed 时刻 `T_n`，由已登记 haccuracy 付款（O-CH11-SEPFIX G1，后缀 `_P6SF`）

R-C11-22 F-22-3/4/7（D-22-3/4/7）与 R-C11-21 D-21-3/4 的落实。记 `N = n+1`，`c n = r n²`，
原尺度 seed 时刻 `Tno`，K 帧 `Tn = Tno/c`，`ρ̂ := (q.rescale_P6N c).neckRadius`（`ρ̂(Tn)⁻² = c·ρ(Tno)⁻²`）。

**(SEP-ρ⁺)′（更正形，内联陈述，无 def）**
* 原尺度（J6 形）：`N·max(N/c, (ρ(Tno)²)⁻¹) ≤ S`（records `tᵢ ≥ max T₀ (c·(σ − L/R))`）。
* K 帧（kernel / SLICE 形）：`N·max(N, ρ̂(Tn)⁻²) ≤ Ŝ`，`Ŝ = c·S`；两形由树内 `hscaleK_rescale_P6X3`
  互通（`sepK_iff_orig_P6SF` 为其纯实数等价）。
* 与旧 (SEP-ρ⁺)（HNOT）的差异：(a) 天花板 `ρ̃(t n = σ)` ↦ `ρ(Tno)`（同 KTRUNC `tK := Tn`、`hslabKT`
  阈值、`Qs_loc` 同一 Q）；(b) 原尺度 `max` 的第一支是 `N/c`（旧"两边同缩放"说法错误，R-C11-22 A3②）；
  (c) 删除 "`R n > n+1` ⇒ 原始绝对窗 → 0" 推导（原始窗 = `c·B/R̂`，A3①），改为**相对时间前瞻**
  `late_of_window_P6SF`（消费时刻原尺度 ∈ `(3Tno/4, Tno]`）。新 ⇒ 旧：`sepRhoPlus_old_of_new_P6SF`；
  旧 ⇏ 新（`ρ` 在 `(σ, Tno]` 有跳即反例，A6②）。

**来源（四条）**
* `sepRhoPlus'_of_recent_P6SF`：单 record，`nominal ≤ η·ρ(T)`、`2η²N ≤ 1` ⇒ `N·ρ(T)⁻² ≤ S`
  （recent 路线；`recenter_scale_comparison` + `scale_eq`）。
* **`sepRhoPlus'_of_accuracy_P6SF`（主）**：已登记 haccuracy（`δ(u)²ρ(u) < ρ(2u)/(u+1)`，
  `recentCutoffSupply_of_accuracy_C11RC` 的前提 / A12OfP6ObsC11A 的 `hscale`；δ 由
  `exists_decaying_commonProfile_sq_mul_lt_and_diagonal` 构造）的 c 帧形 + antitone + recenter@tᵢ +
  `T ≤ 2tᵢ` + `N ≤ c·T` ⇒ `N·ρ(T)⁻² ≤ S`。窗口 / 未来 records 一并覆盖（`2tᵢ ≥ T` ⇒ `ρ(2tᵢ) ≤ ρ(T)`）。
* `sepRhoPlus'_of_construction_P6SF`（备用）：C12-7′c (i) `2·(c t)·δ(t′)⁴ρ(t′)² ≤ ρ(t)²`（`t′ ≤ t ≤ 2t′`）。
* `c127c_of_accuracy_P6SF`：haccuracy ⇒ C12-7′c (i)（`2t ≤ 4t′ ≤ (t′+1)²`）。

**adapter**：A1/A3 `hscaleK_of_accuracy_P6SF`（kernel / SLICEDICH `hscaleK` 槽，`T₀ n := Tn − 1/2` 由
`hT₀_seed_P6SF` 付 kernel `hT₀`）；A2 `sepRhoPlusK_branch_of_accuracy_P6SF`（SLICE-BCBD3 G8″ `hsepρ`，
`ρs n := fun _ => ρ̂(Tn)`，窗口支 + 年轻 cap 支）；A4 `hpastJ6_of_accuracy_P6SF` / `j6_of_accuracy_P6SF`
（KTRUNC2c `j6Loc_of_sepRhoPlus_P6KT2c` 的 `hpast` / J6 ∀ n 形，小 n 由 `late_of_Ldomain_P6SF` 覆盖）。
-/

set_option autoImplicit false

/-! CX-WIRE 新文件修订：保留原件声明与证明，修复风格并保留冻结旧源。
原文“已登记 haccuracy”仅指已有条件接口；actual q₀ 的该条件仍待 C12-7′c。
本文件未生产全局 recenter 或 actual haccuracy；late adapter 另交新文件。
不要同时 import/register 原版与 V2，以免同名声明重复。 -/

noncomputable section

open Set Filter Function
open scoped NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-! ### §0 纯实数 -/

/-- `2x ≤ (x/2+1)²`（`_P6SF`）。 -/
theorem two_mul_le_sq_half_add_one_P6SF (x : ℝ) : 2 * x ≤ (x / 2 + 1) ^ 2 := by
  nlinarith [sq_nonneg (x / 2 - 1)]

/-- `N·a ≤ ρT²`（`a > 0`）⇒ `N·(ρT²)⁻¹ ≤ a⁻¹`（`_P6SF`）。 -/
theorem mul_inv_sq_le_inv_P6SF {N a ρT : ℝ} (ha : 0 < a) (hρT : 0 < ρT)
    (h : N * a ≤ ρT ^ 2) : N * (ρT ^ 2)⁻¹ ≤ a⁻¹ := by
  rw [← div_eq_mul_inv, div_le_iff₀ (pow_pos hρT 2), inv_mul_eq_div, le_div_iff₀ ha]
  exact h

/-- **K 帧 ⇔ 原尺度（`_P6SF`）**：`c > 0`、`Ŝ = c·S` 时 `A·max(B, c·X) ≤ c·S ↔ A·max(B/c, X) ≤ S`
（R-C11-22 A3②：`max` 里的 `N` 不随两边同缩放）。 -/
theorem sepK_iff_orig_P6SF {A B X S c : ℝ} (hc : 0 < c) :
    A * max B (c * X) ≤ c * S ↔ A * max (B / c) X ≤ S := by
  have hmax : max B (c * X) = c * max (B / c) X := by
    rw [mul_max_of_nonneg _ _ hc.le, mul_div_cancel₀ B hc.ne']
  rw [hmax, mul_left_comm, mul_le_mul_iff_of_pos_left hc]

/-! ### §1 相对时间前瞻（R-C11-22 A3⑤） -/

/-- **前瞻（`_P6SF`，PROVED）**：`Tn = Tno/c`、`2c < Tno`、K 帧窗口 `Tn − 1/2 ≤ σ − B/R`（hgapJ / hPN
`hwin`）⇒ 窗内消费时刻 `v` 的原尺度 `c·v > 3Tno/4`。 -/
theorem late_of_window_P6SF {c Tno Tn σ R B v : ℝ} (hc : 0 < c) (hTn : Tn = Tno / c)
    (h2 : 2 * c < Tno) (hwin : Tn - 1 ^ 2 / 2 ≤ σ - B / R) (hv : σ - B / R ≤ v) :
    3 * Tno / 4 < c * v := by
  have hcTn : c * (Tn - 1 ^ 2 / 2) = Tno - c / 2 := by
    rw [hTn, mul_sub, mul_div_cancel₀ Tno hc.ne']
    ring
  have h1 : c * (Tn - 1 ^ 2 / 2) ≤ c * v := mul_le_mul_of_nonneg_left (hwin.trans hv) hc.le
  linarith

/-- 前瞻的闭区间形（`_P6SF`）：另有 `v ≤ Tn` 时 `c·v ∈ (3Tno/4, Tno]`。 -/
theorem late_mem_of_window_P6SF {c Tno Tn σ R B v : ℝ} (hc : 0 < c) (hTn : Tn = Tno / c)
    (h2 : 2 * c < Tno) (hwin : Tn - 1 ^ 2 / 2 ≤ σ - B / R) (hv : σ - B / R ≤ v) (hvT : v ≤ Tn) :
    c * v ∈ Ioc (3 * Tno / 4) Tno := by
  refine ⟨late_of_window_P6SF hc hTn h2 hwin hv, ?_⟩
  have h := mul_le_mul_of_nonneg_left hvT hc.le
  rwa [hTn, mul_div_cancel₀ Tno hc.ne'] at h

/-- 前瞻序列形（`_P6SF`）：`hwin : ∀ T > 0, ∀ᶠ k, Tn − 1/2 ≤ σ − T/R`（hgapJ 逐字）。 -/
theorem late_of_window_seq_P6SF {c Tno Tn σ R : ℕ → ℝ} (hc : ∀ k, 0 < c k)
    (hTn : ∀ k, Tn k = Tno k / c k) (h2 : ∀ k, 2 * c k < Tno k)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, Tn k - 1 ^ 2 / 2 ≤ σ k - T / R k) :
    ∀ B : ℝ, 0 < B → ∀ᶠ k in atTop, ∀ v : ℝ, σ k - B / R k ≤ v → 3 * Tno k / 4 < c k * v :=
  fun B hB => (hwin B hB).mono fun k hk _ hv => late_of_window_P6SF (hc k) (hTn k) (h2 k) hk hv

/-- **前瞻 ∀ k 形（J6 域，`_P6SF`，PROVED）**：`∀ k, Tn − 1/2 ≤ σ − L²/R`（hgapJ 逐字）、`1 ≤ R` ⇒
J6 records 下界 `c·(σ − L/R) > Tno/2`（用 `L − L² ≤ 1/4`；对每个 `k` 成立，无 eventually）。 -/
theorem late_of_Ldomain_P6SF {c Tno Tn σ R L t : ℝ} (hc : 0 < c) (hTn : Tn = Tno / c)
    (h2 : 2 * c < Tno) (hR : 1 ≤ R) (hL : Tn - 1 ^ 2 / 2 ≤ σ - L ^ 2 / R)
    (ht : c * (σ - L / R) ≤ t) : Tno / 2 < t := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hq : L / R - L ^ 2 / R ≤ 1 / 4 := by
    have hLL : L - L ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg (L - 1 / 2)]
    have h1 : L / R - L ^ 2 / R = (L - L ^ 2) / R := by ring
    rw [h1]
    calc (L - L ^ 2) / R ≤ (1 / 4) / R := div_le_div_of_nonneg_right hLL hR0.le
      _ ≤ 1 / 4 := div_le_self (by norm_num) hR
  have h3 : Tn - 3 / 4 ≤ σ - L / R := by
    have : Tn - 1 / 2 ≤ σ - L ^ 2 / R := by simpa using hL
    linarith
  have h4 : c * (Tn - 3 / 4) ≤ c * (σ - L / R) := mul_le_mul_of_nonneg_left h3 hc.le
  have h5 : c * (Tn - 3 / 4) = Tno - 3 * c / 4 := by
    rw [hTn, mul_sub, mul_div_cancel₀ Tno hc.ne']
    ring
  linarith

/-! ### §2 core：(SEP-ρ⁺)′ 的四条来源 -/

/-- 重定心 + `scale_eq`（`_P6SF`）：`recenterConstant·δ(tᵢ) ≤ 1/2` ⇒ `neck.scale/2 ≤ static.scale`。 -/
theorem neck_scale_half_le_static_P6SF {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {p : CutoffParameters} (R : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex)
    (hΛδ : p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2) :
    (R.neck b.1.1).scale / 2 ≤ (R.static b).neck.scale := by
  have hnpos := R.nominal_pos ⟨b.1.1⟩
  have hcmp := R.recenter_scale_comparison b
  have hsc := R.scale_eq b.1.1
  have hdα := R.delta_le b.1.1
  have hΛ : (4 : ℝ) ≤ p.recenterConstant := p.recenterConstant_ge_four
  have hNpos : 0 < (R.neck b.1.1).scale := by
    rw [hsc]
    positivity
  have hΛδα : p.recenterConstant * R.delta b.1.1 ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hdα (by linarith)).trans hΛδ
  have hhalf : 1 / 2 ≤ (R.static b).neck.scale / (R.neck b.1.1).scale := by
    have := (abs_le.mp (hcmp.trans hΛδα)).1
    linarith
  rw [le_div_iff₀ hNpos] at hhalf
  linarith

/-- **recent 路线（`_P6SF`，PROVED）**：`nominalRadius ≤ η·ρT`（R-C11-21 D-21-3 的 recent 字段在本 record
上的值）、`2η²N ≤ 1` ⇒ `N·(ρT²)⁻¹ ≤ scale`。 -/
theorem sepRhoPlus'_of_recent_P6SF {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {p : CutoffParameters} (R : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex)
    (hΛδ : p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2)
    {ρT η N : ℝ} (hρT : 0 < ρT)
    (hrec : ∀ h, R.nominalRadius h ≤ η * ρT) (hηN : 2 * η ^ 2 * N ≤ 1) :
    N * (ρT ^ 2)⁻¹ ≤ (R.static b).neck.scale := by
  have hS := neck_scale_half_le_static_P6SF R b hΛδ
  have hsc := R.scale_eq b.1.1
  have hrpos : 0 < R.nominalRadius ⟨b.1.1⟩ := R.nominal_pos _
  have hrle : R.nominalRadius ⟨b.1.1⟩ ≤ η * ρT := hrec _
  set r := R.nominalRadius ⟨b.1.1⟩ with hr
  rw [hsc] at hS
  have hr2 : r ^ 2 ≤ (η * ρT) ^ 2 := pow_le_pow_left₀ hrpos.le hrle 2
  have h1 : N * (2 * r ^ 2) ≤ ρT ^ 2 := by
    rcases le_or_gt 0 N with hN | hN
    · calc N * (2 * r ^ 2) ≤ N * (2 * (η * ρT) ^ 2) :=
            mul_le_mul_of_nonneg_left (by linarith) hN
        _ = (2 * η ^ 2 * N) * ρT ^ 2 := by ring
        _ ≤ 1 * ρT ^ 2 := mul_le_mul_of_nonneg_right hηN (sq_nonneg _)
        _ = ρT ^ 2 := one_mul _
    · have : N * (2 * r ^ 2) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hN.le (by positivity)
      linarith [sq_nonneg ρT]
  have h2 := mul_inv_sq_le_inv_P6SF (by positivity : (0 : ℝ) < 2 * r ^ 2) hρT h1
  have h3 : (2 * r ^ 2)⁻¹ = (r ^ 2)⁻¹ / 2 := by
    rw [mul_inv, div_eq_mul_inv]
    ring
  rw [h3] at h2
  exact h2.trans hS

/-- **主来源：haccuracy（c 帧形）⇒ (SEP-ρ⁺)′（`_P6SF`，PROVED）**。`hacc` 在 `c = 1` 即树内已登记
`δ(u)²ρ(u) < ρ(2u)/(u+1)`（`hacc_one_P6SF`）；K 帧形由 `hacc_rescale_P6SF` 给出。`T ≤ 2tᵢ` 覆盖窗口
records 与未来 records（不分情形）。 -/
theorem sepRhoPlus'_of_accuracy_P6SF {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {p : CutoffParameters} (R : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex) (hanti : AntitoneOn p.neckRadius (Ici 0))
    (hΛδ : p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2)
    {c T N : ℝ} (hc : 0 < c) (hT : 0 ≤ T) (hlate : T ≤ 2 * H.time i.succ) (hN : N ≤ c * T)
    (hacc : ∀ u : ℝ, 0 ≤ u →
      p.delta u ^ 2 * p.neckRadius u < p.neckRadius (2 * u) / (c * u + 1)) :
    N * (p.neckRadius T ^ 2)⁻¹ ≤ (R.static b).neck.scale := by
  set ti := H.time i.succ with hti
  have hti0 : 0 ≤ ti := H.time_nonneg i.succ
  have hρT := p.neckRadius_pos T hT
  have hd : 0 < c * ti + 1 := by positivity
  have h2ti : 0 ≤ 2 * ti := by linarith
  have hρ2 : p.neckRadius (2 * ti) ≤ p.neckRadius T :=
    hanti (mem_Ici.mpr hT) (mem_Ici.mpr h2ti) hlate
  have hrec : ∀ h, R.nominalRadius h ≤ (c * ti + 1)⁻¹ * p.neckRadius T := by
    intro h
    have h1 := R.nominal_small h
    have h2 := hacc ti hti0
    have h3 : p.neckRadius (2 * ti) / (c * ti + 1) ≤ p.neckRadius T / (c * ti + 1) :=
      div_le_div_of_nonneg_right hρ2 hd.le
    rw [inv_mul_eq_div]
    exact (h1.trans (h2.trans_le h3)).le
  have hcT : c * T ≤ 2 * (c * ti) := by nlinarith
  have hsq : (c * T / 2 + 1) ^ 2 ≤ (c * ti + 1) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hd2 : 2 * N ≤ (c * ti + 1) ^ 2 := by
    have := two_mul_le_sq_half_add_one_P6SF (c * T)
    linarith
  have hηN : 2 * ((c * ti + 1)⁻¹) ^ 2 * N ≤ 1 := by
    have hd2pos : 0 < (c * ti + 1) ^ 2 := by positivity
    calc 2 * ((c * ti + 1)⁻¹) ^ 2 * N = (2 * N) * ((c * ti + 1) ^ 2)⁻¹ := by
          rw [inv_pow]
          ring
      _ ≤ (c * ti + 1) ^ 2 * ((c * ti + 1) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hd2 (inv_nonneg.mpr hd2pos.le)
      _ = 1 := mul_inv_cancel₀ hd2pos.ne'
  exact sepRhoPlus'_of_recent_P6SF R b hΛδ hρT hrec hηN

/-- **备用来源：C12-7′c (i) ⇒ (SEP-ρ⁺)′（`_P6SF`，PROVED 相对构造形前提）**。 -/
theorem sepRhoPlus'_of_construction_P6SF {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {p : CutoffParameters} (R : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex) (hanti : AntitoneOn p.neckRadius (Ici 0))
    (hΛδ : p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2)
    {c T N : ℝ} (hc : 0 < c) (hT : 0 < T) (hlate : T < 2 * H.time i.succ) (hN : N ≤ c * T)
    (hPC : ∀ t' t : ℝ, 0 < t' → t' ≤ t → t ≤ 2 * t' →
      2 * (c * t) * p.delta t' ^ 4 * p.neckRadius t' ^ 2 ≤ p.neckRadius t ^ 2) :
    N * (p.neckRadius T ^ 2)⁻¹ ≤ (R.static b).neck.scale := by
  have hS := static_scale_gt_birth_P6HN R b hΛδ
  set ti := H.time i.succ with hti
  have hti0 : 0 < ti := by linarith
  have hρT := p.neckRadius_pos T hT.le
  have hρi := p.neckRadius_pos ti hti0.le
  have hδi := p.delta_pos ti hti0.le
  set a := p.delta ti with ha
  set ρi := p.neckRadius ti with hρidef
  have hkey : (c * T) * (2 * (a ^ 2 * ρi) ^ 2) ≤ p.neckRadius T ^ 2 := by
    rcases le_or_gt ti T with htT | htT
    · have h := hPC ti T hti0 htT hlate.le
      calc (c * T) * (2 * (a ^ 2 * ρi) ^ 2) = 2 * (c * T) * a ^ 4 * ρi ^ 2 := by ring
        _ ≤ _ := h
    · have h := hPC ti ti hti0 le_rfl (by linarith)
      have hρle : ρi ≤ p.neckRadius T :=
        hanti (mem_Ici.mpr hT.le) (mem_Ici.mpr hti0.le) htT.le
      have hsq : ρi ^ 2 ≤ p.neckRadius T ^ 2 := pow_le_pow_left₀ hρi.le hρle 2
      have hcT : c * T ≤ c * ti := mul_le_mul_of_nonneg_left htT.le hc.le
      calc (c * T) * (2 * (a ^ 2 * ρi) ^ 2) ≤ (c * ti) * (2 * (a ^ 2 * ρi) ^ 2) :=
            mul_le_mul_of_nonneg_right hcT (by positivity)
        _ = 2 * (c * ti) * a ^ 4 * ρi ^ 2 := by ring
        _ ≤ ρi ^ 2 := h
        _ ≤ _ := hsq
  have hN' : N * (2 * (a ^ 2 * ρi) ^ 2) ≤ p.neckRadius T ^ 2 := by
    rcases le_or_gt 0 N with hN0 | hN0
    · exact (mul_le_mul_of_nonneg_right hN (by positivity)).trans hkey
    · have : N * (2 * (a ^ 2 * ρi) ^ 2) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hN0.le (by positivity)
      linarith [sq_nonneg (p.neckRadius T)]
  exact (mul_inv_sq_le_inv_P6SF (by positivity) hρT hN').trans hS.le

/-- **haccuracy ⇒ C12-7′c (i)（`_P6SF`，PROVED）**：C12-7′c 不是新 profile 条款。 -/
theorem c127c_of_accuracy_P6SF {p : CutoffParameters} (hanti : AntitoneOn p.neckRadius (Ici 0))
    {c : ℝ} (hc : 0 < c)
    (hacc : ∀ u : ℝ, 0 ≤ u →
      p.delta u ^ 2 * p.neckRadius u < p.neckRadius (2 * u) / (c * u + 1)) :
    ∀ t' t : ℝ, 0 < t' → t' ≤ t → t ≤ 2 * t' →
      2 * (c * t) * p.delta t' ^ 4 * p.neckRadius t' ^ 2 ≤ p.neckRadius t ^ 2 := by
  intro t' t ht' ht't htt'
  have ht0 : 0 ≤ t := ht'.le.trans ht't
  have hd : 0 < c * t' + 1 := by positivity
  have hρ' := p.neckRadius_pos t' ht'.le
  have hδ' := p.delta_pos t' ht'.le
  have hρ2 : p.neckRadius (2 * t') ≤ p.neckRadius t :=
    hanti (mem_Ici.mpr ht0) (mem_Ici.mpr (by linarith)) htt'
  set A := p.delta t' ^ 2 * p.neckRadius t' with hA
  have hApos : 0 < A := by positivity
  have hAd : A * (c * t' + 1) ≤ p.neckRadius t := by
    have h1 := hacc t' ht'.le
    have h2 : A < p.neckRadius t / (c * t' + 1) :=
      h1.trans_le (div_le_div_of_nonneg_right hρ2 hd.le)
    rw [lt_div_iff₀ hd] at h2
    exact h2.le
  have hsq : (A * (c * t' + 1)) ^ 2 ≤ p.neckRadius t ^ 2 :=
    pow_le_pow_left₀ (by positivity) hAd 2
  have hct : 2 * (c * t) ≤ (c * t' + 1) ^ 2 := by
    have h1 : c * t ≤ 2 * (c * t') := by nlinarith
    nlinarith [sq_nonneg (c * t' - 1)]
  calc 2 * (c * t) * p.delta t' ^ 4 * p.neckRadius t' ^ 2 = 2 * (c * t) * A ^ 2 := by
        rw [hA]
        ring
    _ ≤ (c * t' + 1) ^ 2 * A ^ 2 := mul_le_mul_of_nonneg_right hct (sq_nonneg _)
    _ = (A * (c * t' + 1)) ^ 2 := by ring
    _ ≤ _ := hsq

/-- 树内已登记 haccuracy（`c = 1`）⇒ c 帧形（`_P6SF`）。 -/
theorem hacc_one_P6SF {p : CutoffParameters}
    (hacc : ∀ u : ℝ, 0 ≤ u →
      p.delta u ^ 2 * p.neckRadius u < p.neckRadius (2 * u) / (u + 1)) :
    ∀ u : ℝ, 0 ≤ u →
      p.delta u ^ 2 * p.neckRadius u < p.neckRadius (2 * u) / (1 * u + 1) := by
  intro u hu
  rw [one_mul]
  exact hacc u hu

/-- 原尺度 haccuracy ⇒ K 帧（`q.rescale_P6N c`）的 c 帧形（`_P6SF`）。 -/
theorem hacc_rescale_P6SF {q : CutoffParameters} {c : ℝ} (hc : 0 < c)
    (hacc : ∀ u : ℝ, 0 ≤ u →
      q.delta u ^ 2 * q.neckRadius u < q.neckRadius (2 * u) / (u + 1)) :
    ∀ u : ℝ, 0 ≤ u → (q.rescale_P6N c hc).delta u ^ 2 * (q.rescale_P6N c hc).neckRadius u <
      (q.rescale_P6N c hc).neckRadius (2 * u) / (c * u + 1) := by
  intro u hu
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have h := hacc (c * u) (mul_nonneg hc.le hu)
  change q.delta (c * u) ^ 2 * (q.neckRadius (c * u) / Real.sqrt c) <
    q.neckRadius (c * (2 * u)) / Real.sqrt c / (c * u + 1)
  rw [show c * (2 * u) = 2 * (c * u) by ring]
  have h' := div_lt_div_of_pos_right h hs
  calc q.delta (c * u) ^ 2 * (q.neckRadius (c * u) / Real.sqrt c) =
        q.delta (c * u) ^ 2 * q.neckRadius (c * u) / Real.sqrt c := by ring
    _ < q.neckRadius (2 * (c * u)) / (c * u + 1) / Real.sqrt c := h'
    _ = q.neckRadius (2 * (c * u)) / Real.sqrt c / (c * u + 1) := by ring

/-- 原尺度 antitone ⇒ K 帧 antitone（`_P6SF`）。 -/
theorem anti_rescale_P6SF {q : CutoffParameters} {c : ℝ} (hc : 0 < c)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) :
    AntitoneOn (q.rescale_P6N c hc).neckRadius (Ici 0) := by
  intro a ha b hb hab
  change q.neckRadius (c * b) / Real.sqrt c ≤ q.neckRadius (c * a) / Real.sqrt c
  exact div_le_div_of_nonneg_right
    (hanti (mem_Ici.mpr (mul_nonneg hc.le ha)) (mem_Ici.mpr (mul_nonneg hc.le hb))
      (mul_le_mul_of_nonneg_left hab hc.le)) (Real.sqrt_nonneg c)

/-- link（records 参数与 profile `q` 在 `[0,∞)` 上 delta / neckRadius 相同）⇒ haccuracy 与 antitone 搬到
records 参数（`_P6SF`）。 -/
theorem hacc_anti_of_link_P6SF {p q : CutoffParameters}
    (hlink : ∀ t : ℝ, 0 ≤ t → p.delta t = q.delta t ∧ p.neckRadius t = q.neckRadius t)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hacc : ∀ u : ℝ, 0 ≤ u →
      q.delta u ^ 2 * q.neckRadius u < q.neckRadius (2 * u) / (u + 1)) :
    AntitoneOn p.neckRadius (Ici 0) ∧ ∀ u : ℝ, 0 ≤ u →
      p.delta u ^ 2 * p.neckRadius u < p.neckRadius (2 * u) / (u + 1) := by
  refine ⟨fun a ha b hb hab => ?_, fun u hu => ?_⟩
  · rw [(hlink a ha).2, (hlink b hb).2]
    exact hanti ha hb hab
  · rw [(hlink u hu).1, (hlink u hu).2, (hlink (2 * u) (by linarith)).2]
    exact hacc u hu

/-! ### §3 新 ⇒ 旧（R-C11-22 A6②：反方向不成立） -/

/-- **新 ⇒ 旧（`_P6SF`）**：同一 record，`0 ≤ t ≤ T`、`ρ` antitone、`0 ≤ N` 时
`N·max(N, ρ(T)⁻²) ≤ S ⇒ N·max(N, ρ(t)⁻²) ≤ S`（旧 (SEP-ρ⁺)@σ 是新形在 `t := σ ≤ Tn` 的弱化）。 -/
theorem sepRhoPlus_old_of_new_P6SF {q : CutoffParameters}
    (hanti : AntitoneOn q.neckRadius (Ici 0)) {t T N S : ℝ} (ht : 0 ≤ t) (htT : t ≤ T)
    (hN : 0 ≤ N) (h : N * max N (q.neckRadius T ^ 2)⁻¹ ≤ S) :
    N * max N (q.neckRadius t ^ 2)⁻¹ ≤ S :=
  (mul_le_mul_of_nonneg_left
    (max_le_max le_rfl (inv_sq_neckRadius_le_P6HN hanti ht htT)) hN).trans h

/-! ### §4 adapter A1 / A3：kernel / SLICEDICH `hscaleK` 槽 -/

/-- **seed 形 `T₀`（`_P6SF`，PROVED）**：`T₀ n := Tn n − 1/2` 满足 kernel `hT₀`
（`∀ B, ∀ᶠ n, T₀ n ≤ σ n − B/R n`，由 hgapJ `hwin` 逐字；`B ≤ 0` 用 `hwin 1`），且 `Tn/2 ≤ T₀`
（`Tn ≥ 1`）。HNOT G4 的对角抽取不再需要。 -/
theorem hT₀_seed_P6SF {Tn σ R : ℕ → ℝ} (hR : ∀ n, 0 < R n)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, Tn n - 1 ^ 2 / 2 ≤ σ n - T / R n) :
    ∀ B : ℝ, ∀ᶠ n in atTop, Tn n - 1 ^ 2 / 2 ≤ σ n - B / R n := by
  intro B
  rcases lt_or_ge 0 B with hB | hB
  · exact hwin B hB
  · filter_upwards [hwin 1 one_pos] with n hn
    have h1 : B / R n ≤ 1 / R n :=
      div_le_div_of_nonneg_right (by linarith) (hR n).le
    linarith

/-- **A1 / A3：kernel `hscaleK` 槽 ⇐ haccuracy（`_P6SF`，PROVED，∀ n）**。K 帧 records（参数 `p n`，
c 帧形 haccuracy），`T₀ n ≥ Tn n/2`（seed 形），`N = n+1 ≤ c·Tn = Tno`、ceiling 吸收
`n+1 ≤ ρ̂(Tn)⁻²`（selection `n+1 < R ≤ ρ̂(Tn)⁻²`）⇒
`∀ n i hi b, (n+1)·max(n+1, ρ̂(Tn)⁻²) ≤ scale`（= kernel / SLICEDICH `hscaleK`，`Q n := ρ̂(Tn)⁻²`，与
KTRUNC `tK := Tn` / `hslabKT` 同一 Q）。 -/
theorem hscaleK_of_accuracy_P6SF {K : ℕ → RetainedCoreHistory.{u}} {T₀ : ℕ → ℝ}
    {p : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    {c Tn : ℕ → ℝ} (hc : ∀ n, 0 < c n) (hTn0 : ∀ n, 0 ≤ Tn n)
    (hNT : ∀ n : ℕ, (n : ℝ) + 1 ≤ c n * Tn n) (hT₀ : ∀ n, Tn n ≤ 2 * T₀ n)
    (hanti : ∀ n, AntitoneOn (p n).neckRadius (Ici 0))
    (hacc : ∀ n (u : ℝ), 0 ≤ u →
      (p n).delta u ^ 2 * (p n).neckRadius u < (p n).neckRadius (2 * u) / (c n * u + 1))
    (hΛδ : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (p n).recenterConstant * (p n).delta ((K n).time i.succ) ≤ 1 / 2)
    (habs : ∀ n : ℕ, (n : ℝ) + 1 ≤ ((p n).neckRadius (Tn n) ^ 2)⁻¹) :
    ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) ((p n).neckRadius (Tn n) ^ 2)⁻¹ ≤
      ((recordsK n i hi).static b).neck.scale := by
  intro n i hi b
  rw [max_eq_right (habs n)]
  exact sepRhoPlus'_of_accuracy_P6SF (recordsK n i hi) b (hanti n) (hΛδ n i hi) (hc n) (hTn0 n)
    ((hT₀ n).trans (by linarith)) (hNT n) (hacc n)

/-- A1（HNOT G3 路线，`_P6SF`）：旧 `hscaleK_of_sepRhoPlus_P6HN` 在 `σ := Tn` 处调用即新形的 kernel 付款
（`hpast` = (SEP-ρ⁺)′ 窗口支 `tᵢ ≤ Tn`；未来 records 由 `sepRhoPlus_future_P6HN`@Tn）。 -/
example {H : RetainedCoreHistory.{u}} {p : CutoffParameters} {T₀ Tn N : ℝ}
    (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
      GeometricCutoffRecord H.toHistory i p)
    (hanti : AntitoneOn p.neckRadius (Ici 0)) (hTn0 : 0 ≤ Tn) (hN : 1 ≤ N)
    (hpast : ∀ i hi b, H.time i.succ ≤ Tn →
      N * max N (p.neckRadius Tn ^ 2)⁻¹ ≤ ((records i hi).static b).neck.scale)
    (hΛδ : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ → Tn < H.time i.succ →
      p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2)
    (hδ : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ → Tn < H.time i.succ →
      p.delta (H.time i.succ) ^ 4 * (2 * N * max 1 (N * p.neckRadius 0 ^ 2)) ≤ 1) :
    ∀ i hi b, N * max N (max N (p.neckRadius Tn ^ 2)⁻¹) ≤ ((records i hi).static b).neck.scale :=
  hscaleK_of_sepRhoPlus_P6HN records hanti hTn0 hN hpast hΛδ hδ

/-! ### §5 adapter A2：SLICE-BCBD3 G8″ `hsepρ`（窗口支 + 年轻 cap 支） -/

/-- 年轻 cap 支的出生下界（`_P6SF`，PROVED）：`δ < 1`、锐形 birth ⇒ `scale > (2ρ(0)²)⁻¹`，故
`t − tᵢ ≤ θ₀/scale` 时 `t − tᵢ < 2θ₀ρ(0)²`（尺度不变量）。 -/
theorem youngCap_age_lt_P6SF {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {p : CutoffParameters} (R : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex) (hanti : AntitoneOn p.neckRadius (Ici 0))
    (hΛδ : p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2) {θ₀ t : ℝ} (hθ₀ : 0 ≤ θ₀)
    (hage : t - H.time i.succ ≤ θ₀ * ((R.static b).neck.scale)⁻¹) :
    t - H.time i.succ ≤ θ₀ * (2 * p.neckRadius 0 ^ 2) := by
  have hS := static_scale_gt_birth_P6HN R b hΛδ
  have ht0 : 0 ≤ H.time i.succ := H.time_nonneg i.succ
  have hρi := p.neckRadius_pos _ ht0
  have hρ0 := p.neckRadius_pos 0 le_rfl
  have hδi := p.delta_pos _ ht0
  have hδ1 := p.delta_lt_one _ ht0
  have hi0 : p.neckRadius (H.time i.succ) ≤ p.neckRadius 0 :=
    hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht0) ht0
  have hA : p.delta (H.time i.succ) ^ 2 * p.neckRadius (H.time i.succ) ≤ p.neckRadius 0 := by
    have hδ2 : p.delta (H.time i.succ) ^ 2 ≤ 1 := by nlinarith
    calc p.delta (H.time i.succ) ^ 2 * p.neckRadius (H.time i.succ) ≤
          1 * p.neckRadius (H.time i.succ) := mul_le_mul_of_nonneg_right hδ2 hρi.le
      _ ≤ p.neckRadius 0 := by linarith
  have hX : 2 * (p.delta (H.time i.succ) ^ 2 * p.neckRadius (H.time i.succ)) ^ 2 ≤
      2 * p.neckRadius 0 ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hA 2
    linarith
  have hXpos : 0 < 2 * (p.delta (H.time i.succ) ^ 2 * p.neckRadius (H.time i.succ)) ^ 2 := by
    positivity
  have hS' : (2 * p.neckRadius 0 ^ 2)⁻¹ < (R.static b).neck.scale :=
    (inv_anti₀ hXpos hX).trans_lt hS
  have hSpos : 0 < (R.static b).neck.scale := lt_trans (by positivity) hS'
  have hinv : ((R.static b).neck.scale)⁻¹ ≤ 2 * p.neckRadius 0 ^ 2 := by
    have := inv_anti₀ (by positivity) hS'.le
    rwa [inv_inv] at this
  exact hage.trans (mul_le_mul_of_nonneg_left hinv hθ₀)

/-- **A2：SLICE-BCBD3 G8″ `hsepρ` ⇐ haccuracy（`_P6SF`，PROVED）**。K 帧 records（参数 `p n`、c 帧形
haccuracy），观测时刻 `t n ≤ Tn n`，`hwin`（hgapJ 逐字，以 `t n` 为窗心），`Tn = Tno/c`、`2c < Tno`、
`n+1 ≤ Tno`，年轻 cap 余量 `8θ₀ρ̂(0)² ≤ Tn`（= 原尺度 `8θ₀ρ(0)² ≤ Tno`，eventually），ceiling 吸收。
结论 = G8″ `hsepρ` 在 `ρs n := fun _ => (p n).neckRadius (Tn n)` 处逐字（窗口支 ∨ 年轻 cap 支）。 -/
theorem sepRhoPlusK_branch_of_accuracy_P6SF {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    {c Tno Tn R : ℕ → ℝ} {θ₀ : ℝ} (hθ₀ : 0 ≤ θ₀) (hR : ∀ n, 0 < R n)
    (hc : ∀ n, 0 < c n) (hTn : ∀ n, Tn n = Tno n / c n) (h2 : ∀ n, 2 * c n < Tno n)
    (hNT : ∀ n : ℕ, (n : ℝ) + 1 ≤ Tno n)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, Tn n - 1 ^ 2 / 2 ≤ t n - T / R n)
    (hanti : ∀ n, AntitoneOn (p n).neckRadius (Ici 0))
    (hacc : ∀ n (u : ℝ), 0 ≤ u →
      (p n).delta u ^ 2 * (p n).neckRadius u < (p n).neckRadius (2 * u) / (c n * u + 1))
    (hΛδ : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (p n).recenterConstant * (p n).delta ((K n).time i.succ) ≤ 1 / 2)
    (hρ0 : ∀ᶠ n in atTop, 8 * θ₀ * (p n).neckRadius 0 ^ 2 ≤ Tn n)
    (habs : ∀ n : ℕ, (n : ℝ) + 1 ≤ ((p n).neckRadius (Tn n) ^ 2)⁻¹) :
    ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (j n).castSucc →
        (t n - B / R n ≤ (K n).time i.succ ∨
          t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹) →
        ((n : ℝ) + 1) * max ((n : ℝ) + 1) ((p n).neckRadius (Tn n) ^ 2)⁻¹ ≤
          ((recordsK n i hi).static b).neck.scale := by
  intro B hB
  filter_upwards [hwin B hB, hρ0] with n hw hρn
  intro i hi b hij hbr
  have hcn := hc n
  have hTn2 : 2 < Tn n := by
    rw [hTn n, lt_div_iff₀ hcn]
    linarith [h2 n]
  have hBR : 0 ≤ B / R n := div_nonneg hB.le (hR n).le
  have hlate : Tn n ≤ 2 * (K n).time i.succ := by
    rcases hbr with hwb | hyc
    · linarith
    · have hage := youngCap_age_lt_P6SF (recordsK n i hi) b (hanti n) (hΛδ n i hi) hθ₀ hyc
      nlinarith
  have hN : (n : ℝ) + 1 ≤ c n * Tn n := by
    rw [hTn n, mul_div_cancel₀ _ hcn.ne']
    exact hNT n
  rw [max_eq_right (habs n)]
  exact sepRhoPlus'_of_accuracy_P6SF (recordsK n i hi) b (hanti n) (hΛδ n i hi) hcn
    (by linarith) hlate hN (hacc n)

/-! ### §6 adapter A4：KTRUNC2c J6（原尺度 Ho 帧，∀ n） -/

/-- **A4：KTRUNC2c `j6Loc_of_sepRhoPlus_P6KT2c` 的 `hpast` 形 ⇐ haccuracy（`_P6SF`，PROVED，单 history）**。
records 域 `T₀ ≤ tᵢ` 且 `σ ≤ 2T₀`（J6 域：`T₀ := max T₀ (c·(σ − L/R))`、`σ := Tno`，由
`late_of_Ldomain_P6SF` 对**每个** `n` 给出）、`N ≤ σ`、`hρc : ρ(σ)² ≤ c/N`（KTRUNC2c 同名前提）⇒
对**全部** records（含未来）`N·max(N/c, ρ(σ)⁻²) ≤ scale`；`hpast` 取 `fun i hi b _ => …`。 -/
theorem hpastJ6_of_accuracy_P6SF {H : RetainedCoreHistory.{u}} {p : CutoffParameters}
    {T₀ σ N c : ℝ}
    (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
      GeometricCutoffRecord H.toHistory i p)
    (hanti : AntitoneOn p.neckRadius (Ici 0)) (hσ0 : 0 ≤ σ) (hN : 0 < N) (hc : 0 < c)
    (hρc : p.neckRadius σ ^ 2 ≤ c / N) (hlate : σ ≤ 2 * T₀) (hNσ : N ≤ σ)
    (hacc : ∀ u : ℝ, 0 ≤ u →
      p.delta u ^ 2 * p.neckRadius u < p.neckRadius (2 * u) / (u + 1))
    (hΛδ : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
      p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2) :
    ∀ i hi b, N * max (N / c) (p.neckRadius σ ^ 2)⁻¹ ≤ ((records i hi).static b).neck.scale := by
  intro i hi b
  have hρ := p.neckRadius_pos σ hσ0
  have habs : N / c ≤ (p.neckRadius σ ^ 2)⁻¹ := by
    rw [div_le_iff₀ hc, inv_mul_eq_div, le_div_iff₀ (pow_pos hρ 2)]
    have := (le_div_iff₀ hN).mp hρc
    linarith
  rw [max_eq_right habs]
  have hl : σ ≤ 2 * H.time i.succ := hlate.trans (by linarith)
  exact sepRhoPlus'_of_accuracy_P6SF (records i hi) b hanti (hΛδ i hi) one_pos hσ0 hl
    (by linarith) (hacc_one_P6SF hacc)

/-- **A4 序列形：J6 ∀ n ⇐ haccuracy（`_P6SF`，PROVED）**。hgapJ / hOpenJ 的 J6 合取
`(n+1)·max((n+1)/c, Qs_loc) ≤ scale`（`Qs_loc n := max ((n+1)/c n) (ρ(Tno n)²)⁻¹`，与 KTRUNC2 L5 的
J9 截断同一 Q）对**每个** `n` 成立：J6 域 `tᵢ ≥ c·(σ − L/R) > Tno/2`（`late_of_Ldomain_P6SF`）。
records 参数 `p n` 经 link 与 profile `q` 相同。 -/
theorem j6_of_accuracy_P6SF {Ho : ℕ → RetainedCoreHistory.{u}} {p : ℕ → CutoffParameters}
    {q : CutoffParameters} {T₀ c σ L R Tno Tn : ℕ → ℝ}
    (recordsK : ∀ n (i : Fin (Ho n).eventCount),
      max (T₀ n) (c n * (σ n - L n / R n)) ≤ (Ho n).time i.succ →
        GeometricCutoffRecord (Ho n).toHistory i (p n))
    (hc : ∀ n, 0 < c n) (hTn : ∀ n, Tn n = Tno n / c n) (h2 : ∀ n, 2 * c n < Tno n)
    (hNT : ∀ n : ℕ, (n : ℝ) + 1 ≤ Tno n) (hR1 : ∀ n, 1 ≤ R n)
    (hL : ∀ n, Tn n - 1 ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hlink : ∀ n (t : ℝ), 0 ≤ t → (p n).delta t = q.delta t ∧ (p n).neckRadius t = q.neckRadius t)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hacc : ∀ u : ℝ, 0 ≤ u →
      q.delta u ^ 2 * q.neckRadius u < q.neckRadius (2 * u) / (u + 1))
    (hΛδ : ∀ n (i : Fin (Ho n).eventCount),
      max (T₀ n) (c n * (σ n - L n / R n)) ≤ (Ho n).time i.succ →
        (p n).recenterConstant * (p n).delta ((Ho n).time i.succ) ≤ 1 / 2)
    (hρc : ∀ n : ℕ, q.neckRadius (Tno n) ^ 2 ≤ c n / ((n : ℝ) + 1)) :
    ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n)
        (max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹) ≤
      ((recordsK n i hi).static b).neck.scale := by
  intro n i hi b
  rw [← max_assoc, max_self]
  obtain ⟨hantip, haccp⟩ := hacc_anti_of_link_P6SF (hlink n) hanti hacc
  have hTno0 : 0 ≤ Tno n := by linarith [hc n, h2 n]
  have hlate : Tno n ≤ 2 * max (T₀ n) (c n * (σ n - L n / R n)) := by
    have := late_of_Ldomain_P6SF (hc n) (hTn n) (h2 n) (hR1 n) (hL n)
      (le_max_right (T₀ n) (c n * (σ n - L n / R n)))
    linarith
  have hρeq : (p n).neckRadius (Tno n) = q.neckRadius (Tno n) := (hlink n (Tno n) hTno0).2
  have hρc' : (p n).neckRadius (Tno n) ^ 2 ≤ c n / ((n : ℝ) + 1) := hρeq ▸ hρc n
  have h := hpastJ6_of_accuracy_P6SF (recordsK n) hantip hTno0 (Nat.cast_add_one_pos n) (hc n)
    hρc' hlate (hNT n) haccp (hΛδ n) i hi b
  rwa [hρeq] at h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
