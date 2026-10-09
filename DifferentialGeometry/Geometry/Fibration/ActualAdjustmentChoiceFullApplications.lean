import DifferentialGeometry.Geometry.Fibration.ActualAdjustmentChoiceFull

/-!
# Consumer of the GAF01 row: (JA) and (JB) in the blueprint's display form

`gaf01_full_row_ja_RFC` reads off `gaf01_full_row_RFC` (one call) the two displays of GAF01
(B:5709–5711 and B:5757–5765) on the row's single choice:

* (JA) `Σ_j ≤ ε_j/10000` and `c₃ < min{c_adjust, 1/1000, 1/512}`;
* (JB) `0 < Σ_j < min{1/2, ε_j/10000, Γ_j/200, Γ_j³/(100C_j)}` and
  `0 < e_j < min{1/100, Γ_jΣ_j/100, Σ_j/1000, 1/(200Ω)}` with the ACTUAL graph moduli
  `C = (C_TCP, C_EGP, C_SGP)` and `Ω = gafGraphOmega_BAS`;
* `2e_j < 1/(48Ω)` (B:5791, CGP07's (OS)) and `Γ_j ≤ ... < 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter

namespace DifferentialGeometry.Geometry.Collapse

/-- **(JA) and (JB) of GAF01** on the row's single choice, with the actual graph moduli. -/
theorem gaf01_full_row_ja_RFC (Kj : ℕ) {ν cadj : ℝ} (hν : 0 < ν) (hν1 : ν < 1)
    (hcadj : 0 < cadj) :
    ∃ (Ξ : Fin 3 → ℝ → ℝ) (c Γ S eg : Fin 3 → ℝ),
      ((∀ j, S j ≤ Ξ j (Γ j) / 10000) ∧ c 2 < min cadj (min (1 / 1000) (1 / 512))) ∧
      (∀ j, 0 < S j ∧
        S j < min (1 / 2) (min (Ξ j (Γ j) / 10000) (Γ j / 200)) ∧
        0 < eg j ∧
        eg j < min (1 / 100) (min (Γ j * S j / 100) (min (S j / 1000)
          (1 / (200 * gafGraphOmega_BAS)))) ∧
        2 * eg j < 1 / (48 * gafGraphOmega_BAS)) ∧
      S 0 < Γ 0 ^ 3 / (100 * tcpGraphConst) ∧ S 1 < Γ 1 ^ 3 / (100 * egpGraphConst) ∧
      S 2 < Γ 2 ^ 3 / (100 * sgpGraphBound) := by
  obtain ⟨_, Ξ, c, Γ, S, eg, _, hj, h0, h1, h2, -, -, hc, hos, -⟩ :=
    gaf01_full_row_RFC Kj hν hν1 hcadj
  refine ⟨Ξ, c, Γ, S, eg, ⟨fun j => (hj j).2.2.2.2.2.2.2.2.2.1.le, hc⟩, fun j => ?_, h0, h1, h2⟩
  obtain ⟨-, -, -, -, -, -, -, hS, hS2, hSΞ, hSΓ, he, he1, heΓ, heS, heΩ, -, -⟩ := hj j
  exact ⟨hS, lt_min hS2 (lt_min hSΞ hSΓ), he, lt_min he1 (lt_min heΓ (lt_min heS heΩ)),
    (hos j).2.2.1⟩

end DifferentialGeometry.Geometry.Collapse
