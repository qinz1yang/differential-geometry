import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# 跨 slab first-exit 核（CX-J10DIST G1，后缀 `_CXJD`）

R-C11-16 D-2 的 T0 跨 slab 定位（`hstop`）的抽象 first-exit bootstrap。`f : ℝ → ℝ≥0∞`（窗口 `[a, σ]` 上
`f(v) = d_v(seed(v), A(v))`），预算 `X`、速率 `Λ`：
* `hchain`（**条件**链）：`(s, σ]` 上 `f < X`（= trace 在 Ω 内）⇒ `f(s) ≤ f(σ) + Λ(σ − s)`。
  history 层由"`(s, σ]` 上 ceiling ⇒ 端点曲率 ⇒ I.8.3(b) + (D4)"给出——只用 `(s, σ]` 上的 Good，
  **不**假设整窗 ceiling；
* `husc`（左延拓）：`[s, σ]` 上 `f < X ⇒` `s` 左侧一小段 `[s₁, s]` 上 `f < X`
  （slab 内 USC / crossing 的 terminal 极限；`[s, σ]` 的 Good 供 crossing 处的条件保护）；
* 余量 `f(σ) + Λ(σ − a) < X` ⇒ 首出时刻 `τ* = a`，`∀ s ∈ [a, σ]，f(s) ≤ f(σ) + Λ(σ − s)`。
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

/-- **first-exit 窗口引理（`_CXJD`）**：条件链 `hchain` + 左延拓 `husc` + 余量 ⇒ 整窗距离界。 -/
theorem firstExit_window_CXJD {f : ℝ → ℝ≥0∞} {a σ Λ : ℝ} {X : ℝ≥0∞} (haσ : a ≤ σ)
    (hΛ : 0 ≤ Λ) (hmargin : f σ + ENNReal.ofReal (Λ * (σ - a)) < X)
    (hchain : ∀ s ∈ Icc a σ, (∀ s' ∈ Ioc s σ, f s' < X) →
      f s ≤ f σ + ENNReal.ofReal (Λ * (σ - s)))
    (husc : ∀ s ∈ Ioc a σ, (∀ s' ∈ Icc s σ, f s' < X) →
      ∃ s₁ ∈ Ico a s, ∀ s' ∈ Icc s₁ s, f s' < X) :
    ∀ s ∈ Icc a σ, f s ≤ f σ + ENNReal.ofReal (Λ * (σ - s)) := by
  have hbud : ∀ s ∈ Icc a σ, f σ + ENNReal.ofReal (Λ * (σ - s)) < X := by
    intro s hs
    refine lt_of_le_of_lt (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_)) hmargin
    exact mul_le_mul_of_nonneg_left (by linarith [hs.1]) hΛ
  let S : Set ℝ := {s | a ≤ s ∧ s ≤ σ ∧ ∀ s' ∈ Icc s σ, f s' < X}
  have hσS : σ ∈ S := by
    refine ⟨haσ, le_rfl, fun s' hs' => ?_⟩
    obtain rfl : s' = σ := le_antisymm hs'.2 hs'.1
    exact lt_of_le_of_lt le_self_add hmargin
  have hne : S.Nonempty := ⟨σ, hσS⟩
  have hbdd : BddBelow S := ⟨a, fun s hs => hs.1⟩
  have haS : a ≤ sInf S := le_csInf hne fun s hs => hs.1
  have hSσ : sInf S ≤ σ := csInf_le hbdd hσS
  have hup : ∀ s' ∈ Ioc (sInf S) σ, f s' < X := by
    intro s' hs'
    obtain ⟨s, hsS, hss'⟩ := exists_lt_of_csInf_lt hne hs'.1
    exact hsS.2.2 s' ⟨hss'.le, hs'.2⟩
  have hSlt : f (sInf S) < X :=
    lt_of_le_of_lt (hchain _ ⟨haS, hSσ⟩ hup) (hbud _ ⟨haS, hSσ⟩)
  have hSeq : sInf S = a := by
    by_contra hne'
    have hlt : a < sInf S := lt_of_le_of_ne haS (Ne.symm hne')
    obtain ⟨s₁, hs₁, hnear⟩ := husc _ ⟨hlt, hSσ⟩ fun s' hs' => by
      rcases hs'.1.lt_or_eq with h | h
      · exact hup s' ⟨h, hs'.2⟩
      · rw [← h]
        exact hSlt
    have hs₁S : s₁ ∈ S := by
      refine ⟨hs₁.1, hs₁.2.le.trans hSσ, fun s' hs' => ?_⟩
      rcases le_or_gt s' (sInf S) with h | h
      · exact hnear s' ⟨hs'.1, h⟩
      · exact hup s' ⟨h, hs'.2⟩
    have := csInf_le hbdd hs₁S
    linarith [hs₁.2]
  intro s hs
  refine hchain s hs fun s' hs' => hup s' ⟨?_, hs'.2⟩
  rw [hSeq]
  exact hs.1.trans_lt hs'.1

/-- consumer（`_CXJD` G1）：常值 `f ≡ 0`（链、左延拓平凡）⇒ 结论。 -/
example {a σ : ℝ} (haσ : a ≤ σ) : ∀ s ∈ Icc a σ,
    (fun _ : ℝ => (0 : ℝ≥0∞)) s ≤ (fun _ : ℝ => (0 : ℝ≥0∞)) σ + ENNReal.ofReal (0 * (σ - s)) :=
  firstExit_window_CXJD (X := 1) haσ le_rfl (by simp) (fun _ _ _ => by simp)
    (fun s hs _ => ⟨a, ⟨le_rfl, hs.1⟩, fun _ _ => by simp⟩)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
