import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.L2
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X]

theorem exists_pos_integral_norm_sq_lt {τ : ℝ} (hτ : 0 < τ) (f : timeL2 X τ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ ∈ Set.Ioc 0 τ, ∀ T ∈ Set.Icc (0 : ℝ) δ,
      (∫ t in Set.Icc (0 : ℝ) T, ‖f t‖ ^ 2) < ε := by
  have hf : IntegrableOn (fun t => ‖f t‖ ^ 2) (Set.Icc (0 : ℝ) τ) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp
      (Lp.memLp f)
  have hcont : ContinuousOn
      (fun T : ℝ => ∫ t in Set.Icc (0 : ℝ) T, ‖f t‖ ^ 2)
      (Set.Icc (0 : ℝ) τ) :=
    intervalIntegral.continuousOn_primitive_Icc hf
  obtain ⟨r, hr, hrbound⟩ :=
    Metric.continuousWithinAt_iff.1 (hcont 0 ⟨le_rfl, hτ.le⟩) ε hε
  let δ := min τ (r / 2)
  have hδpos : 0 < δ := lt_min hτ (by linarith)
  have hδle : δ ≤ τ := min_le_left _ _
  refine ⟨δ, ⟨hδpos, hδle⟩, ?_⟩
  intro T hT
  have hTτ : T ∈ Set.Icc (0 : ℝ) τ := ⟨hT.1, hT.2.trans hδle⟩
  have hTr : dist T 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hT.1]
    have hδr : δ ≤ r / 2 := min_le_right _ _
    linarith [hT.2]
  have hbound := hrbound hTτ hTr
  have hnonneg : 0 ≤ ∫ t in Set.Icc (0 : ℝ) T, ‖f t‖ ^ 2 :=
    integral_nonneg (fun t => sq_nonneg ‖f t‖)
  have hzero : (∫ t in Set.Icc (0 : ℝ) (0 : ℝ), ‖f t‖ ^ 2) = 0 := by
    simp
  rw [hzero] at hbound
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using hbound

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
