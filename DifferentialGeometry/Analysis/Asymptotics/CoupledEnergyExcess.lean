import DifferentialGeometry.Analysis.Asymptotics.PowerDecay

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.Analysis

/-- Coupled scale estimates give common linear energy and cubic excess bounds.
The constants are uniform in the supplied center family. -/
theorem exists_uniform_linear_energy_cubic_excess_bounds
    {C : Type*} (En Ex : C → ℝ → ℝ) {σ η A B D M : ℝ}
    (hσ : 0 < σ) (hη : 0 < η)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hEnmono : ∀ c, MonotoneOn (En c) (Ioc (0 : ℝ) σ))
    (hExmono : ∀ c, MonotoneOn (Ex c) (Ioc (0 : ℝ) σ))
    (hEnσ : ∀ c, 0 ≤ En c σ ∧ En c σ ≤ M)
    (hExσ : ∀ c, 0 ≤ Ex c σ ∧ Ex c σ ≤ M)
    (hEnstep : ∀ c, ∀ r ∈ Ioc (0 : ℝ) σ, ∀ s : ℝ, 0 < s → s ≤ η * r →
      En c s ≤ A * (s / r) ^ 2 * En c r + D * r ^ 2 * En c r)
    (hExstep : ∀ c, ∀ r ∈ Ioc (0 : ℝ) σ, ∀ s : ℝ, 0 < s → s ≤ η * r →
      Ex c s ≤ B * (s / r) ^ 4 * Ex c r + D * r ^ 2 * En c r) :
    ∃ E K : ℝ, 0 ≤ E ∧ 0 ≤ K ∧ ∀ c, ∀ r ∈ Ioc (0 : ℝ) σ,
      En c r ≤ E * r ∧ Ex c r ≤ K * r ^ 3 := by
  have hEnM (c : C) {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) σ) : En c r ≤ M :=
    ((hEnmono c) hr ⟨hσ, le_rfl⟩ hr.2).trans (hEnσ c).2
  have henergyStep (c : C) : ∀ r ∈ Ioc (0 : ℝ) σ,
      ∀ s : ℝ, 0 < s → s ≤ η * r →
        En c s ≤ A * (s / r) ^ (2 : ℝ) * En c r + (D * M * σ) * r ^ (1 : ℝ) := by
    intro r hr s hs hsr
    simp only [Real.rpow_ofNat, Real.rpow_one]
    have hr2 : r ^ 2 ≤ σ * r := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hr.2 hr.1.le
    have herror : D * r ^ 2 * En c r ≤ D * M * σ * r := by
      calc
        D * r ^ 2 * En c r ≤ D * r ^ 2 * M :=
          mul_le_mul_of_nonneg_left (hEnM c hr) (mul_nonneg hD (sq_nonneg r))
        _ = D * M * r ^ 2 := by ring
        _ ≤ D * M * (σ * r) := mul_le_mul_of_nonneg_left hr2 (mul_nonneg hD hM)
        _ = D * M * σ * r := by ring
    exact (hEnstep c r hr s hs hsr).trans (add_le_add_right herror _)
  obtain ⟨E, hE, henergy⟩ := exists_uniform_radius_power_bound_of_decay
    (R := σ) (η := η) (A := A) (B := D * M * σ) (M := M) (p := 2) (q := 1)
    hσ hη hA (mul_nonneg (mul_nonneg hD hM) hσ.le) hM (by norm_num) (by norm_num)
  have hEnlinear (c : C) {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) σ) : En c r ≤ E * r := by
    simpa only [Real.rpow_one] using
      henergy (En c) (hEnmono c) (hEnσ c).1 (hEnσ c).2 (henergyStep c) r hr
  have hexcessStep (c : C) : ∀ r ∈ Ioc (0 : ℝ) σ,
      ∀ s : ℝ, 0 < s → s ≤ η * r →
        Ex c s ≤ B * (s / r) ^ (4 : ℝ) * Ex c r + (D * E) * r ^ (3 : ℝ) := by
    intro r hr s hs hsr
    simp only [Real.rpow_ofNat]
    have herror : D * r ^ 2 * En c r ≤ D * E * r ^ 3 := by
      calc
        D * r ^ 2 * En c r ≤ D * r ^ 2 * (E * r) :=
          mul_le_mul_of_nonneg_left (hEnlinear c hr) (mul_nonneg hD (sq_nonneg r))
        _ = D * E * r ^ 3 := by ring
    exact (hExstep c r hr s hs hsr).trans (add_le_add_right herror _)
  obtain ⟨K, hK, hexcess⟩ := exists_uniform_radius_power_bound_of_decay
    (R := σ) (η := η) (A := B) (B := D * E) (M := M) (p := 4) (q := 3)
    hσ hη hB (mul_nonneg hD hE) hM (by norm_num) (by norm_num)
  refine ⟨E, K, hE, hK, ?_⟩
  intro c r hr
  refine ⟨hEnlinear c hr, ?_⟩
  simpa only [Real.rpow_ofNat] using
    hexcess (Ex c) (hExmono c) (hExσ c).1 (hExσ c).2 (hexcessStep c) r hr

end DifferentialGeometry.Analysis
