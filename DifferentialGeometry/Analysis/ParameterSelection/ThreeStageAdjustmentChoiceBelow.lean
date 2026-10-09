import DifferentialGeometry.Analysis.ParameterSelection.ThreeStageAdjustmentChoice

/-! GAF01 (master207B, B:5704) with CFS15's validity thresholds: the three-stage choice of
`exists_three_stage_adjustment_choice` when each smoothing modulus `Ξ_j` is only known to be
positive (and to carry CFS15's conclusions) on an interval `(0, θ_j)`. The chosen `Γ_j` then lie
below `θ_j`, so CFS15 applies at every stage. Proof: run the kernel on `Ξ'_j`, equal to `Ξ_j` on
`(0, θ_j)` and to `1` elsewhere; `Ξ'_j(Γ_j) < 1/10` forces `Γ_j < θ_j`. -/

set_option autoImplicit false
open Filter Topology

namespace DifferentialGeometry.Analysis

/-- The modulus truncated at the threshold `θ`: `Ξ` below `θ`, `1` from `θ` on. -/
noncomputable def truncatedModulus (Ξ : ℝ → ℝ) (θ : ℝ) (Γ : ℝ) : ℝ :=
  if Γ < θ then Ξ Γ else 1

theorem truncatedModulus_of_lt {Ξ : ℝ → ℝ} {θ Γ : ℝ} (h : Γ < θ) :
    truncatedModulus Ξ θ Γ = Ξ Γ := by
  simp only [truncatedModulus, h, ↓reduceIte]

theorem lt_of_truncatedModulus_lt_one {Ξ : ℝ → ℝ} {θ Γ : ℝ} (h : truncatedModulus Ξ θ Γ < 1) :
    Γ < θ := by
  by_contra hΓ
  simp only [truncatedModulus, hΓ, ↓reduceIte, lt_self_iff_false] at h

theorem truncatedModulus_pos {Ξ : ℝ → ℝ} {θ : ℝ} (hΞpos : ∀ Γ, 0 < Γ → Γ < θ → 0 < Ξ Γ)
    {Γ : ℝ} (hΓ : 0 < Γ) : 0 < truncatedModulus Ξ θ Γ := by
  by_cases h : Γ < θ
  · rw [truncatedModulus_of_lt h]
    exact hΞpos Γ hΓ h
  · simp only [truncatedModulus, h, ↓reduceIte, zero_lt_one]

theorem tendsto_truncatedModulus {Ξ : ℝ → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hΞ : Tendsto Ξ (𝓝[>] 0) (𝓝 0)) : Tendsto (truncatedModulus Ξ θ) (𝓝[>] 0) (𝓝 0) := by
  refine hΞ.congr' ?_
  have h : ∀ᶠ Γ in 𝓝[>] (0 : ℝ), Γ < θ := nhdsWithin_le_nhds (Iio_mem_nhds hθ)
  filter_upwards [h] with Γ hΓ
  exact (truncatedModulus_of_lt hΓ).symm

/-- **GAF01's numerical choice below CFS15's thresholds**: as
`exists_three_stage_adjustment_choice`, with `Ξ_j` positive only on `(0, θ_j)`, and the extra
conclusion `Γ_j < θ_j` at every stage. -/
theorem exists_three_stage_adjustment_choice_below (Ξ : Fin 3 → ℝ → ℝ) (θ : Fin 3 → ℝ)
    (hθ : ∀ j, 0 < θ j) (hΞpos : ∀ j Γ, 0 < Γ → Γ < θ j → 0 < Ξ j Γ)
    (hΞ : ∀ j, Tendsto (Ξ j) (𝓝[>] 0) (𝓝 0))
    {cadj bcut κ L₀ Ω : ℝ} (C : Fin 3 → ℝ) (hcadj : 0 < cadj) (hb : 0 ≤ bcut) (hκ : 0 < κ)
    (hL : 0 ≤ L₀) (hΩ : 1 ≤ Ω) (hC : ∀ j, 0 < C j) :
    ∃ c Γ S e : Fin 3 → ℝ,
      let α : Fin 3 → ℝ := fun j =>
        min (c j / (16 * (1 + bcut) * (1 + L₀))) ((1 / 2) / (8 * (1 + L₀)))
      let t : Fin 3 → ℝ := fun j => min (3 * S j / 10) (min (α j) 1)
      (c 2 < cadj ∧ c 2 < 1 / 1000 ∧ c 2 < 1 / 512) ∧
      (c 1 ≤ c 2 ∧ c 1 ≤ t 2 ∧ c 1 ≤ 4 * κ / 5 ∧ c 1 ≤ 1 / 1000 ∧ c 1 ≤ 1 / 512) ∧
      (c 0 ≤ c 1 ∧ c 0 ≤ t 1 ∧ c 0 ≤ 4 * κ / 5 ∧ c 0 ≤ 1 / 1000 ∧ c 0 ≤ 1 / 512) ∧
      ∀ j, (Γ j < θ j ∧ 0 < c j ∧ c j ≤ 1 ∧ 0 < Γ j ∧ Γ j ≤ c j / 16 ∧ Ξ j (Γ j) < 1 / 10 ∧
        Ξ j (Γ j) < α j ∧ Ξ j (Γ j) < 1 / (1000 * (Ω + 1)) ∧
        0 < S j ∧ S j < 1 / 2 ∧ S j < Ξ j (Γ j) / 10000 ∧ S j < Γ j / 200 ∧
        S j < Γ j ^ 3 / (100 * C j) ∧
        0 < e j ∧ e j < 1 / 100 ∧ e j < Γ j * S j / 100 ∧ e j < S j / 1000 ∧
        2 * e j < 1 / (48 * Ω)) ∧
        ∀ E H ν σ : ℝ, 0 ≤ E → E ≤ t j → 0 ≤ H → H ≤ t j → ν ≤ Γ j → σ ≤ 1 / 2 →
          let a := (5 / 3 : ℝ) * Ξ j (Γ j) * σ + (1 + Ξ j (Γ j)) * E
          E + a < c j ∧ a * bcut * (L₀ + H) + Ξ j (Γ j) * (L₀ + H) + ν + 2 * H < c j ∧
            Ξ j (Γ j) * (L₀ + H) + H < 1 / 2 := by
  obtain ⟨c, Γ, S, e, h⟩ := exists_three_stage_adjustment_choice
    (fun j => truncatedModulus (Ξ j) (θ j)) (fun j _ hΓ => truncatedModulus_pos (hΞpos j) hΓ)
    (fun j => tendsto_truncatedModulus (hθ j) (hΞ j)) C hcadj hb hκ hL hΩ hC
  obtain ⟨h2, h1, h0, hstage⟩ := h
  refine ⟨c, Γ, S, e, h2, h1, h0, fun j => ?_⟩
  obtain ⟨⟨hc, hc1, hΓ, hΓc, hΞ1, hΞα, hΞΩ, hrest⟩, hbud⟩ := hstage j
  have hlt : Γ j < θ j := lt_of_truncatedModulus_lt_one (hΞ1.trans (by norm_num))
  have heq : truncatedModulus (Ξ j) (θ j) (Γ j) = Ξ j (Γ j) := truncatedModulus_of_lt hlt
  simp only [heq] at hΞ1 hΞα hΞΩ hrest hbud
  exact ⟨⟨hlt, hc, hc1, hΓ, hΓc, hΞ1, hΞα, hΞΩ, hrest⟩, hbud⟩

end DifferentialGeometry.Analysis
