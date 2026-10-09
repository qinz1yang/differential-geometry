import DifferentialGeometry.Geometry.Fibration.ActualStageChainRow
import DifferentialGeometry.Analysis.ParameterSelection.ThreeStageAdjustmentChoiceBelow

/-!
# BCG03: GAF01's CHOICE for the boundary chain, with explicit early constants (lane BAUG-D)

Part of target A2-mk (`TargetsBoundary-A-v2.lean.txt`; review 69 D69-5 (2)): the numbers of the
boundary chain are chosen ONCE, from the jet order `Kj` and the explicit early constants only — the
cutoff constant `b_cut`, the derivative constant `L₀` (BCG01's `‖DF_∂‖` bound) and `κ` — with
`c₂ < c_adj` for an adjustment cap `c_adj` fixed at a legal early node (the closed full-CHOICE
pattern; E4 / BASES read `c₂ < c_adj`, never a later shrinking). Nothing here depends on a carrier,
a member or a supply.

* `boundaryChain_choice_BAUGD`: CFS15's shared moduli `Ξ_j(·)` (`cfs15_shared_modulus_GAFS4`), the
  qualities `Γ_j`, radius factors `Σ_j`, normal errors `e_j` and budgets `c_j`
  (`exists_three_stage_adjustment_choice_below` at `(b_cut, κ, L₀)`), with every native-output
  precondition, the planes' size conditions (`Σ_j < Γ_j/200`, `Σ_j < Γ_j³/(100 C_j)`,
  `e_j < Γ_jΣ_j/100`) and, for every choice of weight constants `c_w ≥ 0`, the `numbers` clause of
  `BoundaryGaf02Chain` verbatim.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped ContDiff Topology
open GC.MetricGeometry DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

/-- **GAF01's CHOICE for the boundary chain** with explicit `(b_cut, κ, L₀)` and cap `c_adj`. -/
theorem boundaryChain_choice_BAUGD (Kj : ℕ) {cadj bcut κ L₀ : ℝ} (hcadj : 0 < cadj)
    (hb : 0 ≤ bcut) (hκ : 0 < κ) (hL : 0 ≤ L₀) :
    ∃ (Ξf : Fin 3 → ℝ → ℝ) (Ξ c Γ Sg eg : Fin 3 → ℝ),
      (∀ j, Ξ j = Ξf j (Γ j) ∧ 0 < Γ j ∧ Γ j < 1 ∧ 0 < Ξ j ∧ Ξ j < 1 / 10 ∧
        Cfs15ModulusAtV2 (gafStageDim j) Kj (5 / 3) (Ξf j) (Γ j) ∧
        Γ j * ((80 * (5 / 3) + 31) * (Ξf j (Γ j))⁻¹ + 2) < 1 ∧ 0 < Sg j ∧
        Sg j < Ξ j / 10000 ∧ Sg j < Γ j / 200 ∧ 128 * (Ξ j)⁻¹ * Sg j ≤ 1 / 5 ∧ 0 < eg j ∧
        eg j < 1 / 100 ∧ eg j < Γ j * Sg j / 100 ∧ eg j < Sg j / 1000 ∧ 0 < c j ∧
        c j ≤ 1 / 512) ∧
      Sg 0 < Γ 0 ^ 3 / (100 * tcpGraphConst) ∧ Sg 1 < Γ 1 ^ 3 / (100 * egpGraphConst) ∧
      Sg 2 < Γ 2 ^ 3 / (100 * sgpGraphBound) ∧ c 0 ≤ c 1 ∧ c 1 ≤ c 2 ∧ c 2 < cadj ∧
      ∀ cw : Fin 3 → ℝ, (∀ j, 0 ≤ cw j) →
      ((∀ j, 0 < Ξ j ∧ 0 < Sg j ∧ 128 * (Ξ j)⁻¹ * Sg j ≤ 1 / 5 ∧ 0 ≤ eg j ∧
          Sg j ≤ Ξ j / 10000 ∧ 0 ≤ cw j) ∧
        5 / 3 * Ξ 0 * Sg 0 < c 0 ∧ c 0 ≤ 1 / 512 ∧
        (5 / 3 * Ξ 0 * Sg 0 * bcut * L₀ + Ξ 0 * L₀ + eg 0) < c 0 ∧
        c 0 ≤ 4 * κ / 5 ∧ c 0 ≤ 3 * Sg 1 / 10 ∧
        (c 0 + (5 / 3 * Ξ 1 * Sg 1 + (1 + Ξ 1) * c 0)) < c 1 ∧ c 1 ≤ 1 / 512 ∧
        ((5 / 3 * Ξ 1 * Sg 1 + (1 + Ξ 1) * c 0) * bcut * (L₀ + c 0) +
            Ξ 1 * (L₀ + c 0) + eg 1 + 2 * c 0) < c 1 ∧
        c 1 ≤ 4 * κ / 5 ∧ c 1 ≤ 3 * Sg 2 / 10 ∧
        (c 1 + (5 / 3 * Ξ 2 * Sg 2 + (1 + Ξ 2) * c 1)) < c 2 ∧ c 2 ≤ 1 / 512 ∧
        ((5 / 3 * Ξ 2 * Sg 2 + (1 + Ξ 2) * c 1) * bcut * (L₀ + c 1) +
            Ξ 2 * (L₀ + c 1) + eg 2 + 2 * c 1) < c 2) := by
  choose θ hθ Ξf hΞf using fun st : Fin 3 => cfs15_shared_modulus_GAFS4 (gafStageDim st) Kj
  have hpos : ∀ st Γ, 0 < Γ → Γ < θ st → 0 < Ξf st Γ := fun st Γ hΓ hθΓ => by
    obtain ⟨m, hm⟩ := ((hΞf st).2 Γ hΓ hθΓ).1
    rw [hm]
    positivity
  have hCg : ∀ j, 0 < (![tcpGraphConst, egpGraphConst, sgpGraphBound] : Fin 3 → ℝ) j := by
    intro j
    fin_cases j
    · exact lt_of_lt_of_le one_pos one_le_tcpGraphConst
    · exact egpGraphConst_pos_KC4
    · exact sgpGraphBound_pos_GAF8
  obtain ⟨c, Γ, S, eg, h⟩ := exists_three_stage_adjustment_choice_below Ξf θ hθ hpos
    (fun st => (hΞf st).1) _ hcadj hb hκ hL (le_refl (1 : ℝ)) hCg
  obtain ⟨hA, hB, hC, hj⟩ := h
  have hΞpos : ∀ j, 0 < Ξf j (Γ j) := fun j => hpos j (Γ j) (hj j).1.2.2.2.1 (hj j).1.1
  have hmo : ∀ j, 128 * (Ξf j (Γ j))⁻¹ * S j ≤ 1 / 5 := fun j => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hSΞ, -⟩ := (hj j).1
    have hΞj := hΞpos j
    have h1 : 128 * (Ξf j (Γ j))⁻¹ * S j ≤ 128 * (Ξf j (Γ j))⁻¹ * (Ξf j (Γ j) / 10000) :=
      mul_le_mul_of_nonneg_left hSΞ.le (mul_nonneg (by norm_num) (inv_nonneg.mpr hΞj.le))
    have h2 : 128 * (Ξf j (Γ j))⁻¹ * (Ξf j (Γ j) / 10000) = 128 / 10000 := by
      rw [show 128 * (Ξf j (Γ j))⁻¹ * (Ξf j (Γ j) / 10000) =
        128 / 10000 * ((Ξf j (Γ j))⁻¹ * Ξf j (Γ j)) by ring, inv_mul_cancel₀ hΞj.ne', mul_one]
    linarith only [h1, h2]
  have hν : ∀ j, eg j ≤ Γ j := fun j => by
    obtain ⟨-, -, -, hΓ, -, -, -, -, -, hS2, -, -, -, -, -, heΓ, -, -⟩ := (hj j).1
    have h' : Γ j * S j ≤ Γ j * 100 := mul_le_mul_of_nonneg_left (by linarith only [hS2]) hΓ.le
    linarith only [h', heΓ]
  have hc0 := (hj 0).1.2.1
  have hc1 := (hj 1).1.2.1
  have hb0 : 0 < 16 * (1 + bcut) * (1 + L₀) :=
    mul_pos (mul_pos (by norm_num) (by linarith only [hb])) (by linarith only [hL])
  have hb1 : 0 < 8 * (1 + L₀) := mul_pos (by norm_num) (by linarith only [hL])
  have ht₀ : (0 : ℝ) ≤ min (3 * S 0 / 10) (min (min (c 0 / (16 * (1 + bcut) * (1 + L₀)))
      ((1 / 2) / (8 * (1 + L₀)))) 1) :=
    le_min (by linarith only [(hj 0).1.2.2.2.2.2.2.2.2.1])
      (le_min (le_min (div_nonneg hc0.le hb0.le) (div_nonneg (by norm_num) hb1.le)) zero_le_one)
  have hS2 : ∀ j, S j ≤ 1 / 2 := fun j => (hj j).1.2.2.2.2.2.2.2.2.2.1.le
  have k₀ := (hj 0).2 0 0 (eg 0) (S 0) le_rfl ht₀ le_rfl ht₀ (hν 0) (hS2 0)
  have k₀v := k₀.1
  have k₀d := k₀.2.1
  simp only [mul_zero, add_zero, zero_add] at k₀v k₀d
  have k₁ := (hj 1).2 (c 0) (c 0) (eg 1) (S 1) hc0.le hC.2.1 hc0.le hC.2.1 (hν 1) (hS2 1)
  have k₂ := (hj 2).2 (c 1) (c 1) (eg 2) (S 2) hc1.le hB.2.1 hc1.le hB.2.1 (hν 2) (hS2 2)
  refine ⟨Ξf, fun j => Ξf j (Γ j), c, Γ, S, eg, fun j => ?_, (hj 0).1.2.2.2.2.2.2.2.2.2.2.2.2.1,
    (hj 1).1.2.2.2.2.2.2.2.2.2.2.2.2.1, (hj 2).1.2.2.2.2.2.2.2.2.2.2.2.2.1, hC.1, hB.1, hA.1,
    fun cw hcw => ?_⟩
  · obtain ⟨hθΓ, hcj, hcj1, hΓ, hΓc, hΞ10, -, -, hS, -, hSΞ, hSΓ, -, he, he1, heΓ, heS, -⟩ :=
      (hj j).1
    obtain ⟨-, hat, hint, -⟩ := (hΞf j).2 (Γ j) hΓ hθΓ
    have hc512 : c j ≤ 1 / 512 := by
      fin_cases j
      · exact hC.2.2.2.2
      · exact hB.2.2.2.2
      · exact hA.2.2.le
    exact ⟨rfl, hΓ, by linarith only [hΓc, hcj1], hΞpos j, hΞ10, hat, hint, hS, hSΞ, hSΓ,
      hmo j, he, he1, heΓ, heS, hcj, hc512⟩
  · exact ⟨fun j => ⟨hΞpos j, (hj j).1.2.2.2.2.2.2.2.2.1, hmo j,
        (hj j).1.2.2.2.2.2.2.2.2.2.2.2.2.2.1.le, (hj j).1.2.2.2.2.2.2.2.2.2.2.1.le, hcw j⟩,
      k₀v, hC.2.2.2.2, k₀d, hC.2.2.1, hC.2.1.trans (min_le_left _ _), k₁.1, hB.2.2.2.2, k₁.2.1,
      hB.2.2.1, hB.2.1.trans (min_le_left _ _), k₂.1, hA.2.2.le, k₂.2.1⟩

end DifferentialGeometry.Geometry.Collapse
