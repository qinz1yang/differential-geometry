import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.MetricSpace.Snowflaking

open Set (EqOn MapsTo Icc eq_empty_or_nonempty eqOn_empty)
open scoped NNReal

theorem HolderOnWith.extend_real
    {X : Type*} [PseudoMetricSpace X] {f : X → ℝ} {s : Set X} {K α : ℝ≥0}
    (hf : HolderOnWith K α f s) (hα₁ : α ≤ 1) :
    ∃ g : X → ℝ, HolderWith K α g ∧ EqOn g f s := by
  classical
  by_cases hα₀ : α = 0
  · subst α
    rcases eq_empty_or_nonempty s with rfl | ⟨z, hz⟩
    · refine ⟨fun _ => 0, ?_, eqOn_empty _ _⟩
      intro x y
      simp
    · refine ⟨fun x => if x ∈ s then f x else f z, ?_, ?_⟩
      · intro x y
        by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
        · simpa only [if_pos hx, if_pos hy] using hf x hx y hy
        · simpa only [if_pos hx, if_neg hy, NNReal.coe_zero, ENNReal.rpow_zero,
            mul_one] using hf x hx z hz
        · simpa only [if_neg hx, if_pos hy, NNReal.coe_zero, ENNReal.rpow_zero,
            mul_one] using hf z hz y hy
        · simp only [if_neg hx, if_neg hy, edist_self, zero_le]
      · intro x hx
        exact if_pos hx
  have hαpos : 0 < (α : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hα₀)
  let Y := Metric.Snowflaking X (α : ℝ) hαpos hα₁
  let : PseudoMetricSpace Y := Metric.Snowflaking.instPseudoMetricSpace
  let e : X ≃ Y := Metric.Snowflaking.toSnowflaking
  have hfl : LipschitzOnWith K (fun x : Y => f (e.symm x)) (e.symm ⁻¹' s) := by
    intro x hx y hy
    exact hf (e.symm x) hx (e.symm y) hy
  obtain ⟨g, hg, he⟩ := hfl.extend_real
  refine ⟨fun x => g (e x), ?_, ?_⟩
  · intro x y
    exact hg (e x) (e y)
  · intro x hx
    exact (he (x := e x) hx).symm

theorem HolderOnWith.extend_real_Icc
    {X : Type*} [PseudoMetricSpace X] {f : X → ℝ} {s : Set X} {K α : ℝ≥0}
    (hf : HolderOnWith K α f s) (hα : α ≤ 1) {a b : ℝ} (hab : a ≤ b)
    (hbound : MapsTo f s (Icc a b)) :
    ∃ g : X → ℝ, HolderWith K α g ∧ EqOn g f s ∧ ∀ x, g x ∈ Icc a b := by
  obtain ⟨g, hg, he⟩ := hf.extend_real hα
  let c : ℝ → ℝ := fun y => max a (min b y)
  have hc : LipschitzWith 1 c := (LipschitzWith.id.const_min b).const_max a
  refine ⟨c ∘ g, ?_, ?_, ?_⟩
  · simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul] using hc.holderWith.comp hg
  · intro x hx
    change max a (min b (g x)) = f x
    rw [he hx, min_eq_right (hbound hx).2, max_eq_right (hbound hx).1]
  · intro x
    exact ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
