import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open Set Filter
open scoped Topology

namespace MeasureTheory

theorem locallyIntegrableOn_of_integrable_mul_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    {q : E → ℝ} {U : Set E} {n : ℕ∞} (hU : IsOpen U)
    (hint : ∀ φ : E → ℝ, ContDiff ℝ n φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∀ x, 0 ≤ φ x) → Integrable (fun x => q x * φ x) μ) :
    LocallyIntegrableOn q U μ := by
  intro x hx
  obtain ⟨φ, hφU, hφsupp, hφ, hφrange, hφx⟩ :=
    exists_contDiff_tsupport_subset (n := n) (hU.mem_nhds hx)
  have hφnonneg : ∀ y, 0 ≤ φ y := fun y => (hφrange (mem_range_self y)).1
  have hprod := hint φ hφ hφsupp hφU hφnonneg
  let V : Set E := {y | 1 / 2 < φ y}
  have hV : IsOpen V := isOpen_lt continuous_const hφ.continuous
  have hxV : x ∈ V := by
    change 1 / 2 < φ x
    rw [hφx]
    norm_num
  refine ⟨V, nhdsWithin_le_nhds (hV.mem_nhds hxV), ?_⟩
  have hbound : Integrable (fun y => 2 * ‖q y * φ y‖) (μ.restrict V) :=
    (hprod.norm.const_mul 2).restrict
  have hqV : AEStronglyMeasurable q (μ.restrict V) := by
    apply ((hprod.aestronglyMeasurable.div₀
      hφ.continuous.aestronglyMeasurable).restrict).congr
    filter_upwards [ae_restrict_mem hV.measurableSet] with y hy
    have hyφ : φ y ≠ 0 := ne_of_gt (lt_trans (by norm_num) hy)
    exact mul_div_cancel_right₀ (q y) hyφ
  refine hbound.mono' hqV ?_
  filter_upwards [ae_restrict_mem hV.measurableSet] with y hy
  have hyφ : 1 / 2 < φ y := hy
  rw [norm_mul, Real.norm_of_nonneg (hφnonneg y)]
  calc
    ‖q y‖ = ‖q y‖ * 1 := (mul_one _).symm
    _ ≤ ‖q y‖ * (2 * φ y) :=
      mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    _ = 2 * (‖q y‖ * φ y) := by ring

end MeasureTheory
