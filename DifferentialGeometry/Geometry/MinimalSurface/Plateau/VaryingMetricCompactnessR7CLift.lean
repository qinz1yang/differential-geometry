import DifferentialGeometry.Geometry.MinimalSurface.Plateau.VaryingMetricCompactnessR7CRotation
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CourantLebesgueCircleR7A

/-!
# R7C L5（四）：边界参数化的单调 lift 与一致增量模

边界 cap 引理要求 trace 由**单调**度一 lift `ψ`（`CircleDeg1Lift`）给出，并且 lens 弧上的 lift 增量 `≤ 2/3`。
- `exists_monotone_lift_of_three_fixed_R7C`：weakly monotone once 的 `σ` 若固定三个不同点则保向
  （圆周平移共轭后用树内 `IsWeaklyMonotoneOnce.exists_monotone_lift_of_three_fixed_points`）。
- `lift_increment_lt_of_circle_modulus_R7C`：单调 lift `ψ` 若对应的圆周映射有模
  `dist s t < η ⇒ dist (σ s) (σ t) < ε`（`ε ≤ 1/2`），则 `0 ≤ b − a < η ⇒ ψ b − ψ a < ε`
  （介值定理：增量若越过 `ε`，中途某点圆周距离恰为 `ε`）。与 S-MY-R7A 的
  `courant_lebesgue_equicontinuity_varying_R7A` 合用即得 `uₙ` 一致的 lens 增量条件。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open DifferentialGeometry.Topology
open scoped Topology

namespace DifferentialGeometry.Geometry

/-- 三个不动点 ⇒ 保向单调 lift（R7C）。 -/
theorem exists_monotone_lift_of_three_fixed_R7C {σ : C(loopCircle, loopCircle)}
    (hσ : IsWeaklyMonotoneOnce σ) (θ : Fin 3 → loopCircle) (hθ : Function.Injective θ)
    (hfix : ∀ j, σ (θ j) = θ j) :
    ∃ ψ : ℝ → ℝ, Continuous ψ ∧ (∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle)) ∧
      Monotone ψ ∧ ∀ t, ψ (t + 1) = ψ t + 1 := by
  obtain ⟨t₀, ht₀⟩ := QuotientAddGroup.mk_surjective (θ 0)
  obtain ⟨t₁, ht₁⟩ := QuotientAddGroup.mk_surjective (θ 1)
  obtain ⟨t₂, ht₂⟩ := QuotientAddGroup.mk_surjective (θ 2)
  set σ' : C(loopCircle, loopCircle) := (loopShift_R7C (-t₀)).comp (σ.comp (loopShift_R7C t₀))
    with hσ'
  have hσ'w : IsWeaklyMonotoneOnce σ' :=
    (isWeaklyMonotoneOnce_loopShift_R7C (-t₀)).comp
      (hσ.comp (isWeaklyMonotoneOnce_loopShift_R7C t₀))
  have hσ'apply : ∀ x : ℝ,
      σ' (x : loopCircle) = σ ((x + t₀ : ℝ) : loopCircle) - (t₀ : loopCircle) := by
    intro x
    change σ ((x : loopCircle) + (t₀ : loopCircle)) + ((-t₀ : ℝ) : loopCircle) = _
    rw [AddCircle.coe_add, AddCircle.coe_neg, ← sub_eq_add_neg]
  have hfixr : ∀ (t : ℝ), (t : loopCircle) = θ 0 ∨ (t : loopCircle) = θ 1 ∨
      (t : loopCircle) = θ 2 → σ' ((t - t₀ : ℝ) : loopCircle) = ((t - t₀ : ℝ) : loopCircle) := by
    intro t ht
    rw [hσ'apply, sub_add_cancel]
    have hσt : σ (t : loopCircle) = (t : loopCircle) := by
      rcases ht with h | h | h <;> rw [h] <;> exact hfix _
    rw [hσt, AddCircle.coe_sub]
  set a₁ := Int.fract (t₁ - t₀) with ha₁
  set a₂ := Int.fract (t₂ - t₀) with ha₂
  have hcoe : ∀ x : ℝ, ((Int.fract x : ℝ) : loopCircle) = (x : loopCircle) := by
    intro x
    rw [← Int.self_sub_floor, AddCircle.coe_sub]
    have : ((⌊x⌋ : ℝ) : loopCircle) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr ⟨⌊x⌋, by simp⟩
    rw [this, sub_zero]
  have hne : ∀ {i j : Fin 3}, i ≠ j → ∀ {ti tj : ℝ}, (ti : loopCircle) = θ i →
      (tj : loopCircle) = θ j → Int.fract (ti - t₀) ≠ Int.fract (tj - t₀) := by
    intro i j hij ti tj hi hj heq
    apply hij
    apply hθ
    rw [← hi, ← hj]
    have h1 := hcoe (ti - t₀)
    have h2 := hcoe (tj - t₀)
    rw [heq] at h1
    have h3 : ((ti - t₀ : ℝ) : loopCircle) = ((tj - t₀ : ℝ) : loopCircle) := h1.symm.trans h2
    have h4 := congrArg (fun x => x + (t₀ : loopCircle)) h3
    rw [← AddCircle.coe_add, ← AddCircle.coe_add, sub_add_cancel, sub_add_cancel] at h4
    exact h4
  have hpos : ∀ {j : Fin 3}, j ≠ 0 → ∀ {tj : ℝ}, (tj : loopCircle) = θ j →
      0 < Int.fract (tj - t₀) := by
    intro j hj tj htj
    rcases (Int.fract_nonneg (tj - t₀)).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : Int.fract (t₀ - t₀) = 0 := by rw [sub_self, Int.fract_zero]
      exact hne hj htj ht₀ (by rw [← h, h0])
  have ha₁0 : 0 < a₁ := hpos (by decide) ht₁
  have ha₂0 : 0 < a₂ := hpos (by decide) ht₂
  have ha₁1 : a₁ < 1 := Int.fract_lt_one _
  have ha₂1 : a₂ < 1 := Int.fract_lt_one _
  have ha₁₂ : a₁ ≠ a₂ := hne (by decide) ht₁ ht₂
  have hfa : ∀ {tj : ℝ} {j : Fin 3}, (tj : loopCircle) = θ j →
      σ' ((Int.fract (tj - t₀) : ℝ) : loopCircle) = ((Int.fract (tj - t₀) : ℝ) : loopCircle) := by
    intro tj j htj
    rw [hcoe]
    apply hfixr
    fin_cases j
    · exact Or.inl htj
    · exact Or.inr (Or.inl htj)
    · exact Or.inr (Or.inr htj)
  have h0' : σ' (0 : loopCircle) = 0 := by
    have h := hfixr t₀ (Or.inl ht₀)
    rwa [sub_self, AddCircle.coe_zero] at h
  obtain ⟨ψ', hψ'c, hψ'l, hψ'm, hψ'p, -, -, -⟩ : ∃ ψ' : ℝ → ℝ, Continuous ψ' ∧
      (∀ t : ℝ, (ψ' t : loopCircle) = σ' (t : loopCircle)) ∧ Monotone ψ' ∧
      (∀ t, ψ' (t + 1) = ψ' t + 1) ∧ ψ' 0 = 0 ∧ True ∧ True := by
    rcases lt_or_gt_of_ne ha₁₂ with h | h
    · obtain ⟨ψ', h1, h2, h3, h4, h5, -, -⟩ := hσ'w.exists_monotone_lift_of_three_fixed_points
        ha₁0 h ha₂1 h0' (hfa ht₁) (hfa ht₂)
      exact ⟨ψ', h1, h2, h3, h4, h5, trivial, trivial⟩
    · obtain ⟨ψ', h1, h2, h3, h4, h5, -, -⟩ := hσ'w.exists_monotone_lift_of_three_fixed_points
        ha₂0 h ha₁1 h0' (hfa ht₂) (hfa ht₁)
      exact ⟨ψ', h1, h2, h3, h4, h5, trivial, trivial⟩
  refine ⟨fun t => ψ' (t - t₀) + t₀, (hψ'c.comp (continuous_id.sub continuous_const)).add
    continuous_const, fun t => ?_, fun a b hab => ?_, fun t => ?_⟩
  · change ((ψ' (t - t₀) + t₀ : ℝ) : loopCircle) = σ (t : loopCircle)
    rw [AddCircle.coe_add, hψ'l, hσ'apply, sub_add_cancel, sub_add_cancel]
  · have := hψ'm (sub_le_sub_right hab t₀)
    simp only
    linarith
  · simp only
    rw [show t + 1 - t₀ = (t - t₀) + 1 by ring, hψ'p]
    ring

/-- 圆周模 ⇒ 单调 lift 的一致增量（R7C）：见文件头。 -/
theorem lift_increment_lt_of_circle_modulus_R7C {σ : C(loopCircle, loopCircle)} {ψ : ℝ → ℝ}
    (hψc : Continuous ψ) (hψl : ∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle))
    {η ε : ℝ} (hε : ε ≤ 1 / 2)
    (hmod : ∀ s t : loopCircle, dist s t < η → dist (σ s) (σ t) < ε) :
    ∀ a b : ℝ, a ≤ b → b - a < η → ψ b - ψ a < ε := by
  intro a b hab hba
  by_contra hcon
  push Not at hcon
  have hcont : ContinuousOn (fun t => ψ t - ψ a) (Icc a b) :=
    (hψc.sub continuous_const).continuousOn
  have hmem : ε ∈ Icc ((fun t => ψ t - ψ a) a) ((fun t => ψ t - ψ a) b) := by
    simp only [sub_self]
    have hε0 : 0 ≤ ε := by
      by_contra h
      push Not at h
      have := hmod (a : loopCircle) (a : loopCircle) (by
        rw [dist_self]
        linarith)
      rw [dist_self] at this
      linarith
    exact ⟨hε0, hcon⟩
  obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc hab hcont hmem
  simp only at hteq
  have hdt : dist (t : loopCircle) (a : loopCircle) < η := by
    rw [dist_coe_eq_norm_R7A]
    refine (norm_coe_le_abs_R7A _).trans_lt ?_
    rw [abs_of_nonpos (by linarith [ht.1])]
    linarith [ht.2]
  have hd := hmod _ _ hdt
  rw [← hψl, ← hψl, dist_coe_eq_norm_R7A] at hd
  have hnorm : ‖((ψ a - ψ t : ℝ) : loopCircle)‖ = ε := by
    have hx : ψ a - ψ t = -ε := by linarith
    rw [hx]
    have h0 : 0 ≤ ε := by linarith [hmem.1]
    have habs : |(-ε)| ≤ |(1 : ℝ)| / 2 := by
      rw [abs_neg, abs_of_nonneg h0, abs_one]
      exact hε
    rw [(AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).mpr habs, abs_neg,
      abs_of_nonneg h0]
  rw [hnorm] at hd
  exact lt_irrefl _ hd

end DifferentialGeometry.Geometry
