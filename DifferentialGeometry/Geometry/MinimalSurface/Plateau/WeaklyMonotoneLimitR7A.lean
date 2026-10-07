import DifferentialGeometry.Topology.LoopSpace.WeaklyMonotone
import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.Basic
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# S-MY-R7A G3：weakly-monotone-once 类在一致极限下封闭（归一化 lift 论证）

外审 D-R-MY3-6：不加 chord-arc；`IsWeaklyMonotoneOnce` 在 `σₙ → σ₀` 一致收敛下封闭，
**不**把"极限严格单调"当中间结论。

证明（纯 `ε`-论证，不用 Helly / Arzelà–Ascoli）：

1. `σ₀` 连续 ⇒ 有连续 lift `Ψ`（`IsCoveringMap.existsUnique_continuousMap_lifts`，ℝ 单连通）。
2. 对每个 `σₙ`（`n` 充分大）有 WMO lift `ψₙ`；`σₙ → σ₀` 一致 ⇒ `ψₙ − Ψ` 连续且处处距整数 `< ε`，
   连通性（IVT）把整数 `mₙ` 定成常数：`|ψₙ t − mₙ − Ψ t| < ε`（"归一化 lift"）。
3. `ε → 0`：`Ψ` 单调（或反单调）、`Ψ (t + 1) = Ψ t ± 1`。符号由 `∃ᶠ` / `∀ᶠ` 二分，
   反单调情形套用 `Ψ ↦ −Ψ`。

主定理 `weaklyMonotoneOnce_closed_under_uniform_limit_R7A`；不含新 Prop / structure。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Function
open DifferentialGeometry.Topology
open scoped Topology

namespace DifferentialGeometry.Geometry

/-- 连续圆周自映射有连续实 lift（覆盖映射 `ℝ → ℝ/ℤ` + ℝ 单连通）。 -/
theorem exists_continuous_lift_R7A (σ : C(loopCircle, loopCircle)) :
    ∃ Ψ : ℝ → ℝ, Continuous Ψ ∧ ∀ t : ℝ, (Ψ t : loopCircle) = σ (t : loopCircle) := by
  let p : ℝ → loopCircle := fun t => (t : loopCircle)
  have hcov : IsCoveringMap p := AddCircle.isCoveringMap_coe (1 : ℝ)
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (σ 0)
  let f : C(ℝ, loopCircle) := ⟨σ ∘ p, σ.continuous.comp hcov.continuous⟩
  obtain ⟨F, ⟨_, hFlift⟩, _⟩ := hcov.existsUnique_continuousMap_lifts f 0 a (by
    change (a : loopCircle) = σ (0 : loopCircle)
    exact ha)
  exact ⟨F, F.continuous, fun t => congrFun hFlift t⟩

/-- 圆周范数 `< ε` ⇒ 距某个整数 `< ε`。 -/
theorem exists_int_abs_lt_of_norm_lt_R7A {x ε : ℝ} (h : ‖(x : loopCircle)‖ < ε) :
    ∃ m : ℤ, |x - m| < ε := by
  refine ⟨round x, ?_⟩
  simpa only [AddCircle.norm_eq, inv_one, one_mul, mul_one] using h

/-- 整数点与半整数点的距离 `≥ 1/2`。 -/
theorem half_le_abs_int_add_half_R7A (m m' : ℤ) : (1 / 2 : ℝ) ≤ |(m : ℝ) + 1 / 2 - m'| := by
  rcases le_or_gt m' m with h | h
  · have : (m' : ℝ) ≤ m := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have : (m : ℝ) + 1 ≤ m' := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- 连续函数处处距整数 `< ε ≤ 1/4` ⇒ 整数可取常数（IVT：不能跨过半整数）。 -/
theorem exists_int_const_R7A {d : ℝ → ℝ} (hd : Continuous d) {ε : ℝ} (hε : ε ≤ 1 / 4)
    (h : ∀ t, ∃ m : ℤ, |d t - m| < ε) : ∃ m : ℤ, ∀ t, |d t - m| < ε := by
  obtain ⟨m, hm⟩ := h 0
  refine ⟨m, fun t => ?_⟩
  obtain ⟨m', hm'⟩ := h t
  rcases lt_trichotomy m' m with hlt | heq | hgt
  · exfalso
    have hlt' : (m' : ℝ) + 1 ≤ m := by exact_mod_cast hlt
    have h1 := abs_lt.mp hm'
    have h2 := abs_lt.mp hm
    obtain ⟨c, hc⟩ := intermediate_value_univ t 0 hd
      (show (m : ℝ) - 1 / 2 ∈ Icc (d t) (d 0) from ⟨by linarith [h1.2], by linarith [h2.1]⟩)
    obtain ⟨m'', hm''⟩ := h c
    have := half_le_abs_int_add_half_R7A (m - 1) m''
    have hcast : ((m - 1 : ℤ) : ℝ) + 1 / 2 = (m : ℝ) - 1 / 2 := by push_cast; ring
    rw [hcast, ← hc] at this
    linarith
  · subst heq
    exact hm'
  · exfalso
    have hgt' : (m : ℝ) + 1 ≤ m' := by exact_mod_cast hgt
    have h1 := abs_lt.mp hm'
    have h2 := abs_lt.mp hm
    obtain ⟨c, hc⟩ := intermediate_value_univ 0 t hd
      (show (m : ℝ) + 1 / 2 ∈ Icc (d 0) (d t) from ⟨by linarith [h2.2], by linarith [h1.1]⟩)
    obtain ⟨m'', hm''⟩ := h c
    have := half_le_abs_int_add_half_R7A m m''
    rw [← hc] at this
    linarith

/-- 若对每个 `ε` 都有单调、`+1` 周期的 `ψ` 与整数 `m` 使 `ψ − m` `ε`-逼近 `Ψ`，则 `Ψ` 单调且 `+1` 周期。 -/
theorem monotone_of_approx_R7A {Ψ : ℝ → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ (ψ : ℝ → ℝ) (m : ℤ), (∀ t, |ψ t - m - Ψ t| < ε) ∧ Monotone ψ ∧
      ∀ t, ψ (t + 1) = ψ t + 1) :
    Monotone Ψ ∧ ∀ t, Ψ (t + 1) = Ψ t + 1 := by
  constructor
  · intro s t hst
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨ψ, m, hψ, hmono, -⟩ := h (ε / 2) (half_pos hε)
    have h1 := (abs_lt.mp (hψ s)).1
    have h2 := (abs_lt.mp (hψ t)).2
    have h3 := hmono hst
    linarith
  · intro t
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨ψ, m, hψ, -, hper⟩ := h (ε / 2) (half_pos hε)
    have h1 := abs_lt.mp (hψ t)
    have h2 := abs_lt.mp (hψ (t + 1))
    have h3 := hper t
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith

/-- **G3**（R7A）：`IsWeaklyMonotoneOnce` 在圆周自映射的一致极限下封闭。
`σᵢ`（`i` 沿 `l` 终将）是 weakly monotone once，`σᵢ → σ₀` 于 `loopCircle` 上一致 ⇒ `σ₀` 也是。
证明用归一化 lift：不把"极限严格单调"当中间结论，不加 chord-arc。 -/
theorem weaklyMonotoneOnce_closed_under_uniform_limit_R7A {ι : Type*} {l : Filter ι} [l.NeBot]
    {σ : ι → C(loopCircle, loopCircle)} {σ₀ : C(loopCircle, loopCircle)}
    (hσ : ∀ᶠ i in l, IsWeaklyMonotoneOnce (σ i))
    (hlim : TendstoUniformly (fun i => (σ i : loopCircle → loopCircle)) σ₀ l) :
    IsWeaklyMonotoneOnce σ₀ := by
  obtain ⟨Ψ, hΨc, hΨ⟩ := exists_continuous_lift_R7A σ₀
  -- 归一化 lift：`n` 充分大时任一 lift `ψ` 与 `Ψ` 相差"整数 + `< ε`"，整数是常数
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → ∀ᶠ i in l, ∀ ψ : ℝ → ℝ, Continuous ψ →
      (∀ t, (ψ t : loopCircle) = σ i (t : loopCircle)) → ∃ m : ℤ, ∀ t, |ψ t - m - Ψ t| < ε := by
    intro ε hε hε4
    filter_upwards [Metric.tendstoUniformly_iff.mp hlim ε hε] with i hi ψ hψc hψ
    have hd : ∀ t, ∃ m : ℤ, |(ψ t - Ψ t) - m| < ε := by
      intro t
      apply exists_int_abs_lt_of_norm_lt_R7A
      have h1 := hi (t : loopCircle)
      rw [dist_comm, dist_eq_norm, ← hΨ t, ← hψ t, ← AddCircle.coe_sub] at h1
      exact h1
    obtain ⟨m, hm⟩ := exists_int_const_R7A (hψc.sub hΨc) hε4 hd
    refine ⟨m, fun t => ?_⟩
    have h2 := hm t
    rwa [show ψ t - m - Ψ t = (ψ t - Ψ t) - m by ring]
  by_cases hfreq : ∃ᶠ i in l, ∃ ψ : ℝ → ℝ, Continuous ψ ∧
      (∀ t, (ψ t : loopCircle) = σ i (t : loopCircle)) ∧ Monotone ψ ∧ ∀ t, ψ (t + 1) = ψ t + 1
  · have happ : ∀ ε : ℝ, 0 < ε → ∃ (ψ : ℝ → ℝ) (m : ℤ), (∀ t, |ψ t - m - Ψ t| < ε) ∧
        Monotone ψ ∧ ∀ t, ψ (t + 1) = ψ t + 1 := by
      intro ε hε
      obtain ⟨i, ⟨ψ, hψc, hψl, hmono, hper⟩, hi⟩ :=
        (hfreq.and_eventually (key (min ε (1 / 4)) (lt_min hε (by norm_num))
          (min_le_right _ _))).exists
      obtain ⟨m, hm⟩ := hi ψ hψc hψl
      exact ⟨ψ, m, fun t => (hm t).trans_le (min_le_left _ _), hmono, hper⟩
    obtain ⟨hmono, hper⟩ := monotone_of_approx_R7A happ
    exact ⟨Ψ, hΨc, hΨ, Or.inl ⟨hmono, hper⟩⟩
  · rw [not_frequently] at hfreq
    have hanti : ∀ᶠ i in l, ∃ ψ : ℝ → ℝ, Continuous ψ ∧
        (∀ t, (ψ t : loopCircle) = σ i (t : loopCircle)) ∧ Antitone ψ ∧
          ∀ t, ψ (t + 1) = ψ t - 1 := by
      filter_upwards [hσ, hfreq] with i hi hn
      obtain ⟨ψ, hc, hl, hs⟩ := hi
      rcases hs with hs | hs
      · exact absurd ⟨ψ, hc, hl, hs⟩ hn
      · exact ⟨ψ, hc, hl, hs⟩
    have happ : ∀ ε : ℝ, 0 < ε → ∃ (ψ : ℝ → ℝ) (m : ℤ),
        (∀ t, |ψ t - m - (fun s => -Ψ s) t| < ε) ∧ Monotone ψ ∧ ∀ t, ψ (t + 1) = ψ t + 1 := by
      intro ε hε
      obtain ⟨i, ⟨ψ, hψc, hψl, hanti, hper⟩, hi⟩ :=
        (hanti.and (key (min ε (1 / 4)) (lt_min hε (by norm_num))
          (min_le_right _ _))).exists
      obtain ⟨m, hm⟩ := hi ψ hψc hψl
      refine ⟨fun t => -ψ t, -m, fun t => ?_, fun s t hst => neg_le_neg (hanti hst), fun t => ?_⟩
      · have h2 := (hm t).trans_le (min_le_left _ _)
        rw [← abs_neg] at h2
        convert h2 using 2
        push_cast
        ring
      · simp only [hper]
        ring
    obtain ⟨hmono, hper⟩ := monotone_of_approx_R7A happ
    refine ⟨Ψ, hΨc, hΨ, Or.inr ⟨fun s t hst => ?_, fun t => ?_⟩⟩
    · exact neg_le_neg_iff.mp (hmono hst)
    · have h : -Ψ (t + 1) = -Ψ t + 1 := hper t
      linarith

end DifferentialGeometry.Geometry

end
