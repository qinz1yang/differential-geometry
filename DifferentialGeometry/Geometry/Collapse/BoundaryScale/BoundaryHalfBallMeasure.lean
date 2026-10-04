import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Exact Haar measure of a ball cut by a linear half-space

A nonzero linear functional divides a centred ball into two sets of equal measure.
Its zero hyperplane is null, so the open and closed half-spaces have the same measure.
This applies to the metric-normalized half-space in an actual boundary chart.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem measure_ball_inter_positive_halfspace (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (ell : E →L[ℝ] ℝ) (hell : ell ≠ 0) (r : ℝ) :
    μ (ball (0 : E) r ∩ {x | 0 < ell x}) = μ (ball (0 : E) r) / 2 := by
  have hker : μ {x | ell x = 0} = 0 := by
    apply Measure.addHaar_submodule μ (LinearMap.ker ell.toLinearMap)
    intro ht
    apply hell
    ext x
    have hx : x ∈ LinearMap.ker ell.toLinearMap := ht.symm ▸ Submodule.mem_top
    exact hx
  let A := ball (0 : E) r ∩ {x | 0 < ell x}
  let B := ball (0 : E) r ∩ {x | ell x < 0}
  have hB : MeasurableSet B := measurableSet_ball.inter
    (isOpen_lt ell.continuous continuous_const).measurableSet
  have hneg : Neg.neg ⁻¹' B = A := by
    ext x
    simp only [B, A, mem_preimage, mem_inter_iff, mem_ball, dist_zero_right,
      norm_neg, mem_ofPred_eq, map_neg, neg_lt_zero]
  have heq : μ A = μ B := by
    rw [← hneg]
    have h := μ.addHaar_preimage_linearEquiv (LinearEquiv.neg ℝ) B
    change μ (Neg.neg ⁻¹' B) =
      ENNReal.ofReal |LinearMap.det (-LinearMap.id : E →ₗ[ℝ] E)| * μ B at h
    have hdet : LinearMap.det (-LinearMap.id : E →ₗ[ℝ] E) =
        (-1 : ℝ) ^ Module.finrank ℝ E := by
      rw [show (-LinearMap.id : E →ₗ[ℝ] E) = (-1 : ℝ) • LinearMap.id by simp,
        LinearMap.det_smul, LinearMap.det_id, mul_one]
    simpa only [hdet, abs_pow, abs_neg,
      abs_one, one_pow, ENNReal.ofReal_one, one_mul] using h
  have hd : Disjoint A B := by
    apply disjoint_left.mpr
    intro x hx hy
    exact (show 0 < ell x from hx.2).not_gt (show ell x < 0 from hy.2)
  have hu : A ∪ B = ball (0 : E) r \ {x | ell x = 0} := by
    ext x
    simp only [A, B, mem_union, mem_inter_iff, mem_sdiff, mem_ofPred_eq]
    constructor
    · rintro (⟨hx, hh⟩ | ⟨hx, hh⟩)
      · exact ⟨hx, hh.ne'⟩
      · exact ⟨hx, hh.ne⟩
    · rintro ⟨hx, hh⟩
      rcases lt_or_gt_of_ne hh with hh | hh
      · exact Or.inr ⟨hx, hh⟩
      · exact Or.inl ⟨hx, hh⟩
  have hsum : μ A + μ A = μ (ball (0 : E) r) := by
    calc
      μ A + μ A = μ A + μ B := congrArg (fun b : ℝ≥0∞ => μ A + b) heq
      _ = μ (A ∪ B) := (measure_union hd hB).symm
      _ = μ (ball (0 : E) r) := by rw [hu, measure_sdiff_null hker]
  calc
    μ A = (μ A + μ A) / 2 := by simp [ENNReal.add_div, ENNReal.add_halves]
    _ = μ (ball (0 : E) r) / 2 := congrArg (fun a : ℝ≥0∞ => a / 2) hsum

theorem measure_ball_inter_nonnegative_halfspace (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (ell : E →L[ℝ] ℝ) (hell : ell ≠ 0) (r : ℝ) :
    μ (ball (0 : E) r ∩ {x | 0 ≤ ell x}) = μ (ball (0 : E) r) / 2 := by
  have hker : μ {x | ell x = 0} = 0 := by
    apply Measure.addHaar_submodule μ (LinearMap.ker ell.toLinearMap)
    intro ht
    apply hell
    ext x
    have hx : x ∈ LinearMap.ker ell.toLinearMap := ht.symm ▸ Submodule.mem_top
    exact hx
  have hd : (ball (0 : E) r ∩ {x | 0 ≤ ell x}) \ {x | ell x = 0} =
      ball (0 : E) r ∩ {x | 0 < ell x} := by
    ext x
    simp only [mem_sdiff, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hx, hh⟩, hn⟩
      exact ⟨hx, lt_of_le_of_ne hh (Ne.symm hn)⟩
    · rintro ⟨hx, hh⟩
      exact ⟨⟨hx, hh.le⟩, hh.ne'⟩
  rw [← measure_sdiff_null (s := ball (0 : E) r ∩ {x | 0 ≤ ell x}) hker,
    hd, measure_ball_inter_positive_halfspace μ ell hell r]

end DifferentialGeometry.Geometry.Measure
