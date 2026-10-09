import DifferentialGeometry.Analysis.ParameterSelection.AdjustmentBudget
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Fin.VecNotation

/-! GAF01 (master207B, B:5704): one choice, in the retained order
`c₃ ; Γ₃, ε₃, S₃, e₃ ; c₂ ; … ; c₁ ; …`, of all numerical adjustment parameters for the three
stages, with (JA), (JB), `2 e_j < 1/(48 Ω)`, and the hypotheses of the CFS20 budget kernel
`adjustment_errors_lt_of_threshold` (rank margin `μ = 1/2`) at every stage. The smoothing modulus
`Ξ_j` of CFS15, the cutoff constant `b_cut`, `κ`, the derivative bound `L₀` and the graph moduli
`C_j`, `Ω` are data. Index `0, 1, 2` of `Fin 3` is stage `1, 2, 3`. -/

set_option autoImplicit false
open Filter Topology

namespace DifferentialGeometry.Analysis

theorem exists_stage_adjustment_choice (Ξ : ℝ → ℝ) (hΞpos : ∀ Γ, 0 < Γ → 0 < Ξ Γ)
    (hΞ : Tendsto Ξ (𝓝[>] 0) (𝓝 0)) {c bcut L₀ Ω C : ℝ} (hc : 0 < c) (hb : 0 ≤ bcut)
    (hL : 0 ≤ L₀) (hΩ : 1 ≤ Ω) (hC : 0 < C) :
    ∃ Γ S e : ℝ, 0 < Γ ∧ Γ ≤ c / 16 ∧ Ξ Γ < 1 / 10 ∧
      Ξ Γ < min (c / (16 * (1 + bcut) * (1 + L₀))) ((1 / 2) / (8 * (1 + L₀))) ∧
      Ξ Γ < 1 / (1000 * (Ω + 1)) ∧
      0 < S ∧ S < 1 / 2 ∧ S < Ξ Γ / 10000 ∧ S < Γ / 200 ∧ S < Γ ^ 3 / (100 * C) ∧
      0 < e ∧ e < 1 / 100 ∧ e < Γ * S / 100 ∧ e < S / 1000 ∧ 2 * e < 1 / (48 * Ω) := by
  set α := min (c / (16 * (1 + bcut) * (1 + L₀))) ((1 / 2) / (8 * (1 + L₀))) with hα
  have hαpos : 0 < α := lt_min (by positivity) (by positivity)
  set m := min (1 / 10) (min α (1 / (1000 * (Ω + 1)))) with hm
  have hmpos : 0 < m := lt_min (by norm_num) (lt_min hαpos (by positivity))
  have h1 : ∀ᶠ Γ in 𝓝[>] (0 : ℝ), Ξ Γ < m := hΞ (Iio_mem_nhds hmpos)
  have h2 : ∀ᶠ Γ in 𝓝[>] (0 : ℝ), Γ < c / 16 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
  have h3 : ∀ᶠ Γ in 𝓝[>] (0 : ℝ), 0 < Γ := self_mem_nhdsWithin
  obtain ⟨Γ, hΓm, hΓc, hΓ⟩ := (h1.and (h2.and h3)).exists
  have hε := hΞpos Γ hΓ
  have hm1 : m ≤ 1 / 10 := min_le_left _ _
  have hm2 : m ≤ α := (min_le_right _ _).trans (min_le_left _ _)
  have hm3 : m ≤ 1 / (1000 * (Ω + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  set s := min (1 / 2) (min (Ξ Γ / 10000) (min (Γ / 200) (Γ ^ 3 / (100 * C)))) with hs
  have hspos : 0 < s := lt_min (by norm_num) (lt_min (by positivity)
    (lt_min (by positivity) (by positivity)))
  set S := s / 2 with hS
  have hSpos : 0 < S := by positivity
  have hSs : S < s := by linarith
  have hs1 : s ≤ 1 / 2 := min_le_left _ _
  have hs2 : s ≤ Ξ Γ / 10000 := (min_le_right _ _).trans (min_le_left _ _)
  have hs3 : s ≤ Γ / 200 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hs4 : s ≤ Γ ^ 3 / (100 * C) :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  set q := min (1 / 100) (min (Γ * S / 100) (min (S / 1000) (1 / (200 * Ω)))) with hq
  have hqpos : 0 < q := lt_min (by norm_num) (lt_min (by positivity)
    (lt_min (by positivity) (by positivity)))
  have hq1 : q ≤ 1 / 100 := min_le_left _ _
  have hq2 : q ≤ Γ * S / 100 := (min_le_right _ _).trans (min_le_left _ _)
  have hq3 : q ≤ S / 1000 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hq4 : q ≤ 1 / (200 * Ω) :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hΩ' : 1 / (200 * Ω) * 2 < 1 / (48 * Ω) := by
    rw [div_mul_eq_mul_div, one_mul, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  refine ⟨Γ, S, q / 2, hΓ, hΓc.le, by linarith, by linarith, by linarith, hSpos, by linarith,
    by linarith, by linarith, by linarith, by positivity, by linarith, by linarith, by linarith,
    by linarith⟩

/-- GAF01's numerical choice for all three stages, in the retained order, together with the
CFS20 budget conclusions at every stage for any preceding errors at most `t_j`. -/
theorem exists_three_stage_adjustment_choice (Ξ : Fin 3 → ℝ → ℝ)
    (hΞpos : ∀ j Γ, 0 < Γ → 0 < Ξ j Γ) (hΞ : ∀ j, Tendsto (Ξ j) (𝓝[>] 0) (𝓝 0))
    {cadj bcut κ L₀ Ω : ℝ} (C : Fin 3 → ℝ) (hcadj : 0 < cadj) (hb : 0 ≤ bcut) (hκ : 0 < κ)
    (hL : 0 ≤ L₀) (hΩ : 1 ≤ Ω) (hC : ∀ j, 0 < C j) :
    ∃ c Γ S e : Fin 3 → ℝ,
      let α : Fin 3 → ℝ := fun j =>
        min (c j / (16 * (1 + bcut) * (1 + L₀))) ((1 / 2) / (8 * (1 + L₀)))
      let t : Fin 3 → ℝ := fun j => min (3 * S j / 10) (min (α j) 1)
      (c 2 < cadj ∧ c 2 < 1 / 1000 ∧ c 2 < 1 / 512) ∧
      (c 1 ≤ c 2 ∧ c 1 ≤ t 2 ∧ c 1 ≤ 4 * κ / 5 ∧ c 1 ≤ 1 / 1000 ∧ c 1 ≤ 1 / 512) ∧
      (c 0 ≤ c 1 ∧ c 0 ≤ t 1 ∧ c 0 ≤ 4 * κ / 5 ∧ c 0 ≤ 1 / 1000 ∧ c 0 ≤ 1 / 512) ∧
      ∀ j, (0 < c j ∧ c j ≤ 1 ∧ 0 < Γ j ∧ Γ j ≤ c j / 16 ∧ Ξ j (Γ j) < 1 / 10 ∧
        Ξ j (Γ j) < α j ∧ Ξ j (Γ j) < 1 / (1000 * (Ω + 1)) ∧
        0 < S j ∧ S j < 1 / 2 ∧ S j < Ξ j (Γ j) / 10000 ∧ S j < Γ j / 200 ∧
        S j < Γ j ^ 3 / (100 * C j) ∧
        0 < e j ∧ e j < 1 / 100 ∧ e j < Γ j * S j / 100 ∧ e j < S j / 1000 ∧
        2 * e j < 1 / (48 * Ω)) ∧
        ∀ E H ν σ : ℝ, 0 ≤ E → E ≤ t j → 0 ≤ H → H ≤ t j → ν ≤ Γ j → σ ≤ 1 / 2 →
          let a := (5 / 3 : ℝ) * Ξ j (Γ j) * σ + (1 + Ξ j (Γ j)) * E
          E + a < c j ∧ a * bcut * (L₀ + H) + Ξ j (Γ j) * (L₀ + H) + ν + 2 * H < c j ∧
            Ξ j (Γ j) * (L₀ + H) + H < 1 / 2 := by
  -- stage three
  set c₃ := min cadj (min (1 / 1000) (1 / 512)) / 2 with hc₃
  have hc₃pos : 0 < c₃ := by positivity
  have hc₃a : c₃ < cadj := by
    have := min_le_left cadj (min (1 / 1000 : ℝ) (1 / 512)); linarith
  have hc₃b : c₃ < 1 / 1000 := by
    have := (min_le_right cadj (min (1 / 1000 : ℝ) (1 / 512))).trans (min_le_left _ _)
    linarith
  have hc₃c : c₃ < 1 / 512 := by
    have := (min_le_right cadj (min (1 / 1000 : ℝ) (1 / 512))).trans (min_le_right _ _)
    linarith
  obtain ⟨Γ₃, S₃, e₃, h₃⟩ := exists_stage_adjustment_choice (Ξ 2) (hΞpos 2) (hΞ 2) hc₃pos hb hL
    hΩ (hC 2)
  set α₃ := min (c₃ / (16 * (1 + bcut) * (1 + L₀))) ((1 / 2) / (8 * (1 + L₀)))
  have hα₃ : 0 < α₃ := lt_min (by positivity) (by positivity)
  set t₃ := min (3 * S₃ / 10) (min α₃ 1)
  have ht₃ : 0 < t₃ := lt_min (by linarith [h₃.2.2.2.2.2.1]) (lt_min hα₃ one_pos)
  -- stage two
  set c₂ := min c₃ (min t₃ (min (4 * κ / 5) (min (1 / 1000) (1 / 512)))) with hc₂
  have hc₂pos : 0 < c₂ := lt_min hc₃pos (lt_min ht₃ (lt_min (by positivity)
    (lt_min (by norm_num) (by norm_num))))
  obtain ⟨Γ₂, S₂, e₂, h₂⟩ := exists_stage_adjustment_choice (Ξ 1) (hΞpos 1) (hΞ 1) hc₂pos hb hL
    hΩ (hC 1)
  set α₂ := min (c₂ / (16 * (1 + bcut) * (1 + L₀))) ((1 / 2) / (8 * (1 + L₀)))
  have hα₂ : 0 < α₂ := lt_min (by positivity) (by positivity)
  set t₂ := min (3 * S₂ / 10) (min α₂ 1)
  have ht₂ : 0 < t₂ := lt_min (by linarith [h₂.2.2.2.2.2.1]) (lt_min hα₂ one_pos)
  -- stage one
  set c₁ := min c₂ (min t₂ (min (4 * κ / 5) (min (1 / 1000) (1 / 512)))) with hc₁
  have hc₁pos : 0 < c₁ := lt_min hc₂pos (lt_min ht₂ (lt_min (by positivity)
    (lt_min (by norm_num) (by norm_num))))
  obtain ⟨Γ₁, S₁, e₁, h₁⟩ := exists_stage_adjustment_choice (Ξ 0) (hΞpos 0) (hΞ 0) hc₁pos hb hL
    hΩ (hC 0)
  have hc₂le : c₂ ≤ c₃ := min_le_left _ _
  have hc₁le : c₁ ≤ c₂ := min_le_left _ _
  have hc₂t : c₂ ≤ t₃ := (min_le_right _ _).trans (min_le_left _ _)
  have hc₂k : c₂ ≤ 4 * κ / 5 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hc₂m : c₂ ≤ 1 / 1000 := (((min_le_right _ _).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_left _ _)
  have hc₂n : c₂ ≤ 1 / 512 := (((min_le_right _ _).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_right _ _)
  have hc₁t : c₁ ≤ t₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hc₁k : c₁ ≤ 4 * κ / 5 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hc₁m : c₁ ≤ 1 / 1000 := (((min_le_right _ _).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_left _ _)
  have hc₁n : c₁ ≤ 1 / 512 := (((min_le_right _ _).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_right _ _)
  have hstage : ∀ (c Γ S e ε C : ℝ), 0 < c → c ≤ 1 →
      (0 < Γ ∧ Γ ≤ c / 16 ∧ ε < 1 / 10 ∧
        ε < min (c / (16 * (1 + bcut) * (1 + L₀))) ((1 / 2) / (8 * (1 + L₀))) ∧
        ε < 1 / (1000 * (Ω + 1)) ∧
        0 < S ∧ S < 1 / 2 ∧ S < ε / 10000 ∧ S < Γ / 200 ∧ S < Γ ^ 3 / (100 * C) ∧
        0 < e ∧ e < 1 / 100 ∧ e < Γ * S / 100 ∧ e < S / 1000 ∧ 2 * e < 1 / (48 * Ω)) →
      ∀ E H ν σ : ℝ, 0 ≤ E →
        E ≤ min (3 * S / 10) (min (min (c / (16 * (1 + bcut) * (1 + L₀)))
          ((1 / 2) / (8 * (1 + L₀)))) 1) → 0 ≤ H →
        H ≤ min (3 * S / 10) (min (min (c / (16 * (1 + bcut) * (1 + L₀)))
          ((1 / 2) / (8 * (1 + L₀)))) 1) → ν ≤ Γ → σ ≤ 1 / 2 →
        let a := (5 / 3 : ℝ) * ε * σ + (1 + ε) * E
        E + a < c ∧ a * bcut * (L₀ + H) + ε * (L₀ + H) + ν + 2 * H < c ∧
          ε * (L₀ + H) + H < 1 / 2 := by
    intro c Γ S e ε C hc hc1 h E H ν σ hE hEt hH hHt hν hσ
    have hε0 : 0 ≤ ε := by linarith [h.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1]
    have hEα := hEt.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hHα := hHt.trans ((min_le_right _ _).trans (min_le_left _ _))
    exact adjustment_errors_lt_of_threshold hc hc1 (by norm_num) hb hL hε0 hE hH
      h.2.2.1.le hσ (hν.trans h.2.1) h.2.2.2.1.le hEα hHα
  refine ⟨![c₁, c₂, c₃], ![Γ₁, Γ₂, Γ₃], ![S₁, S₂, S₃], ![e₁, e₂, e₃], ?_⟩
  intro α t
  refine ⟨⟨hc₃a, hc₃b, hc₃c⟩, ⟨hc₂le, hc₂t, hc₂k, hc₂m, hc₂n⟩, ⟨hc₁le, hc₁t, hc₁k, hc₁m, hc₁n⟩, ?_⟩
  intro j
  fin_cases j
  · exact ⟨⟨hc₁pos, show c₁ ≤ 1 by linarith, h₁⟩,
      hstage c₁ Γ₁ S₁ e₁ (Ξ 0 Γ₁) (C 0) hc₁pos (by linarith) h₁⟩
  · exact ⟨⟨hc₂pos, show c₂ ≤ 1 by linarith, h₂⟩,
      hstage c₂ Γ₂ S₂ e₂ (Ξ 1 Γ₂) (C 1) hc₂pos (by linarith) h₂⟩
  · exact ⟨⟨hc₃pos, show c₃ ≤ 1 by linarith, h₃⟩,
      hstage c₃ Γ₃ S₃ e₃ (Ξ 2 Γ₃) (C 2) hc₃pos (by linarith) h₃⟩

end DifferentialGeometry.Analysis
