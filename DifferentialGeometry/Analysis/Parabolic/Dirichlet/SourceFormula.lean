import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory
open scoped BigOperators ENNReal

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

theorem ae_source_formula_of_expansions
    {P ι : Type*} [MeasurableSpace P] [Fintype ι]
    {μ : Measure P} (k : ι)
    {F Fdiv Flower U R Dρ DDρ C₀ DC₀ : P → ℝ}
    {V C DC : ι → P → ℝ} {H DA DDA : ι → ι → P → ℝ}
    (hF : F =ᵐ[μ] fun p => Fdiv p + Flower p - (Dρ p * R p + DDρ p * U p))
    (hFdiv : Fdiv =ᵐ[μ] fun p => ∑ i : ι, ∑ j : ι,
      (DA i j p * H i j p + DDA i j p * V i p))
    (hFlower : Flower =ᵐ[μ] fun p =>
      (∑ i : ι, (C i p * H i k p + DC i p * V i p)) +
        (C₀ p * V k p + DC₀ p * U p)) :
    F =ᵐ[μ] fun p =>
      (∑ i : ι, ∑ j : ι,
        (DA i j p * H i j p + DDA i j p * V i p)) +
        (∑ i : ι, (DC i p * V i p + C i p * H i k p)) +
          (DC₀ p - DDρ p) * U p + C₀ p * V k p - Dρ p * R p := by
  filter_upwards [hF, hFdiv, hFlower] with p hp hd hl
  rw [hp, hd, hl]
  have hlower : (∑ i : ι, (C i p * H i k p + DC i p * V i p)) =
      ∑ i : ι, (DC i p * V i p + C i p * H i k p) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hlower]
  ring

theorem ae_source_formula_toLp
    {P ι : Type*} [MeasurableSpace P] [Fintype ι]
    {μ : Measure P} (k : ι)
    (Fdiv Flower : Lp ℝ 2 μ) {U R Dρ DDρ C₀ DC₀ : P → ℝ}
    {V C DC : ι → P → ℝ} {H DA DDA : ι → ι → P → ℝ}
    (hf : MemLp (fun p => Fdiv p + Flower p -
      (Dρ p * R p + DDρ p * U p)) 2 μ)
    (hFdiv : Fdiv =ᵐ[μ] fun p => ∑ i : ι, ∑ j : ι,
      (DA i j p * H i j p + DDA i j p * V i p))
    (hFlower : Flower =ᵐ[μ] fun p =>
      (∑ i : ι, (C i p * H i k p + DC i p * V i p)) +
        (C₀ p * V k p + DC₀ p * U p)) :
    hf.toLp _ =ᵐ[μ] fun p =>
      (∑ i : ι, ∑ j : ι,
        (DA i j p * H i j p + DDA i j p * V i p)) +
        (∑ i : ι, (DC i p * V i p + C i p * H i k p)) +
          (DC₀ p - DDρ p) * U p + C₀ p * V k p - Dρ p * R p := by
  exact ae_source_formula_of_expansions k hf.coeFn_toLp hFdiv hFlower

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
