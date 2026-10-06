import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeRimKernel

/-!
# O-WF G6b (part 2): the rim kernel along EDP04's homotopy (`θ ∈ [0, 1]`)

Generalization of `rim_pair_surjective_kernel_BAUGD` (the final time `θ = 1`) to every time of
EDP04's homotopy (closed twin: `Gaf02Chain.edge_homotopy_conorm_EDPE` with
`conorm_homotopy_EDP3`), over an arbitrary real vector space `V` and linear functionals:

* `rim_pert_lt_half_OWF`: under the normalized EDP03 inputs of the rim kernel,
  `|dgq − dη| + |dT − dt| < 1/2` on `Sp`;
* `homotopy_pair_surjective_kernel_OWF`: for `θ ∈ [0, 1]`, the pair
  `((1 − θ)dη + θ dgq, (1 − θ)dt + θ dT)` is onto `ℝ × ℝ` (co-norm `> 9/10` of `(dη, dt)` on `Sp`
  and the perturbation scaled by `θ ≤ 1`).
-/

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.Geometry.Collapse

/-- **The perturbation bound of the rim kernel** (the inputs of
`rim_pair_surjective_kernel_BAUGD` without the co-norm): `|dgq − dη| + |dT − dt| < 1/2` on
`Sp`. -/
theorem rim_pert_lt_half_OWF {V : Type*} [AddCommGroup V] [Module ℝ V] (Sp : Set V)
    (dη dP dρ dA ds dgq dt dT : V →ₗ[ℝ] ℝ) {ρj ρq Pq Aq sq c₃ κ Δ : ℝ} (hρj : 0 < ρj)
    (hq : 99 / 100 < ρq / ρj) (hS : |sq / ρj - ρq / ρj| ≤ κ * (ρq / ρj))
    (hB : |Aq / ρj - Pq / ρj| < c₃ * (ρq / ρj)) (ht0 : 0 ≤ Pq / ρj / (ρq / ρj))
    (ht : Pq / ρj / (ρq / ρj) < 5 * Δ) (hΔ : 1 ≤ Δ) (hκ : 0 ≤ κ) (hϑ : κ * Δ < 1 / 1000000)
    (hc₃ : c₃ < 1 / 100000)
    (hdt : ∀ W, dt W = ρq⁻¹ * dP W - Pq * (ρq ^ 2)⁻¹ * dρ W)
    (hdT : ∀ W, dT W = sq⁻¹ * dA W - Aq * (sq ^ 2)⁻¹ * ds W)
    (hds : ∀ W ∈ Sp, |ds W| ≤ κ * ρj) (hdρ : ∀ W ∈ Sp, |dρ W| ≤ κ * ρj)
    (hdA : ∀ W ∈ Sp, |dA W - dP W| < c₃ * ρj) (hdP : ∀ W ∈ Sp, |dP W| < 2 * ρj)
    (hdg : ∀ W ∈ Sp, |dgq W - dη W| < c₃) :
    ∀ W ∈ Sp, |dgq W - dη W| + |dT W - dt W| < 1 / 2 := by
  obtain ⟨hκ1, hSlow, hS98⟩ := EdgeDisk.edgeHeight_aux hq hS hΔ hκ hϑ
  have hq0 : 0 < ρq / ρj := by linarith
  have hρq : 0 < ρq := by
    have := mul_pos hq0 hρj
    rwa [div_mul_cancel₀ _ hρj.ne'] at this
  have hS0 : 0 < sq / ρj := by linarith
  have hsq : 0 < sq := by
    have := mul_pos hS0 hρj
    rwa [div_mul_cancel₀ _ hρj.ne'] at this
  have hc₃0 : 0 < c₃ := by
    have := abs_nonneg (Aq / ρj - Pq / ρj)
    nlinarith
  have hϑ0 : 0 ≤ κ * Δ := mul_nonneg hκ (by linarith)
  intro W hW
  have hk := EdgeDisk.edgeHeight_quotient_deriv_lt (V := ℝ) (p := Pq / ρj) (q := ρq / ρj)
    (S := sq / ρj) (B := Aq / ρj) (c₃ := c₃) (κ := κ) (Δ := Δ)
    (dp := dP W / ρj) (dq := dρ W / ρj) (dS := ds W / ρj) (dB := dA W / ρj) hq hS hB ht0 ht hΔ hκ
    hϑ hc₃ ?_ ?_ ?_ ?_
  · have heq : (sq / ρj)⁻¹ • (dA W / ρj - dP W / ρj) +
        ((sq / ρj)⁻¹ - (ρq / ρj)⁻¹) • (dP W / ρj) -
        (Aq / ρj / (sq / ρj) / (sq / ρj)) • (ds W / ρj) +
        (Pq / ρj / (ρq / ρj) / (ρq / ρj)) • (dρ W / ρj) = dT W - dt W := by
      rw [hdT, hdt]
      simp only [smul_eq_mul]
      field_simp
      ring
    rw [heq, Real.norm_eq_abs] at hk
    have := hdg W hW
    linarith
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos hρj, div_le_iff₀ hρj]
    exact hds W hW
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos hρj, div_le_iff₀ hρj]
    exact hdρ W hW
  · rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hρj, div_lt_iff₀ hρj]
    exact hdA W hW
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos hρj, div_lt_iff₀ hρj]
    exact hdP W hW

/-- **The rim kernel along the homotopy**: for `θ ∈ [0, 1]`, a co-norm `> 9/10` of `(dη, dt)` on
`Sp` and `|dgq − dη| + |dT − dt| < 1/2` on `Sp` give the time-`θ` pair
`(dh, dTθ) = ((1 − θ)dη + θ dgq, (1 − θ)dt + θ dT)` onto `ℝ × ℝ`. -/
theorem homotopy_pair_surjective_of_conorm_OWF {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Sp : Set V) (dη dt dgq dT dh dTθ : V →ₗ[ℝ] ℝ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hdh : ∀ W, dh W = (1 - θ) * dη W + θ * dgq W)
    (hdTθ : ∀ W, dTθ W = (1 - θ) * dt W + θ * dT W)
    (hco : ∀ ξ : EuclideanSpace ℝ (Fin 2), ‖ξ‖ = 1 →
      ∃ W ∈ Sp, 9 / 10 < dη W * ξ 0 + dt W * ξ 1)
    (hpert : ∀ W ∈ Sp, |dgq W - dη W| + |dT W - dt W| < 1 / 2) :
    Function.Surjective (fun W => (dh W, dTθ W)) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  refine pair_surjective_of_conorm_BAUGD Sp dη dt dh dTθ hco fun W hW => ?_
  have e1 : dh W - dη W = θ * (dgq W - dη W) := by rw [hdh]; ring
  have e2 : dTθ W - dt W = θ * (dT W - dt W) := by rw [hdTθ]; ring
  have h1 : |dh W - dη W| ≤ |dgq W - dη W| := by
    rw [e1, abs_mul, abs_of_nonneg hθ0]
    exact mul_le_of_le_one_left (abs_nonneg _) hθ1
  have h2 : |dTθ W - dt W| ≤ |dT W - dt W| := by
    rw [e2, abs_mul, abs_of_nonneg hθ0]
    exact mul_le_of_le_one_left (abs_nonneg _) hθ1
  have h3 := hpert W hW
  linarith

end DifferentialGeometry.Geometry.Collapse
