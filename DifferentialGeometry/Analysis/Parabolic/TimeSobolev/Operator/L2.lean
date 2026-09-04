import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Operator.Basic

noncomputable section

open MeasureTheory

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
variable {T : ℝ}

omit [CompleteSpace Y] in
theorem memLp_timeOpL2
    (A : ℝ → X →L[ℝ] Y)
    (hA : MemLp A 2 (timeMeasure T))
    (u : ℝ → X)
    (hu : AEStronglyMeasurable u (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖u t‖ ≤ (C : ℝ)) :
    MemLp (fun t => A t (u t)) 2 (timeMeasure T) := by
  have hmeas : AEStronglyMeasurable (fun t => A t (u t))
      (timeMeasure T) := by
    have h :=
      (ContinuousLinearMap.apply ℝ Y).aestronglyMeasurable_comp₂ hu hA.1
    simpa only [ContinuousLinearMap.apply_apply] using h
  refine MemLp.of_le_mul (c := (C : ℝ)) hA hmeas ?_
  filter_upwards [hC] with t ht
  calc
    ‖A t (u t)‖ ≤ ‖A t‖ * ‖u t‖ := (A t).le_opNorm (u t)
    _ ≤ ‖A t‖ * (C : ℝ) :=
      mul_le_mul_of_nonneg_left ht (norm_nonneg _)
    _ = (C : ℝ) * ‖A t‖ := mul_comm _ _

def timeOpL2
    (A : ℝ → X →L[ℝ] Y)
    (hA : MemLp A 2 (timeMeasure T))
    (u : ℝ → X)
    (hu : AEStronglyMeasurable u (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖u t‖ ≤ (C : ℝ)) :
    timeL2 Y T :=
  (memLp_timeOpL2 A hA u hu C hC).toLp (fun t => A t (u t))

omit [CompleteSpace Y] in
theorem timeOpL2_apply_ae
    (A : ℝ → X →L[ℝ] Y)
    (hA : MemLp A 2 (timeMeasure T))
    (u : ℝ → X)
    (hu : AEStronglyMeasurable u (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖u t‖ ≤ (C : ℝ)) :
    timeOpL2 A hA u hu C hC =ᵐ[timeMeasure T]
      fun t => A t (u t) :=
  (memLp_timeOpL2 A hA u hu C hC).coeFn_toLp

omit [CompleteSpace Y] in
theorem timeOpL2_sub
    (A : ℝ → X →L[ℝ] Y)
    (hA : MemLp A 2 (timeMeasure T))
    (u v : ℝ → X)
    (hu : AEStronglyMeasurable u (timeMeasure T))
    (hv : AEStronglyMeasurable v (timeMeasure T))
    (huv : AEStronglyMeasurable (fun t => u t - v t) (timeMeasure T))
    (Cu Cv Cuv : NNReal)
    (hCu : ∀ᵐ t ∂timeMeasure T, ‖u t‖ ≤ (Cu : ℝ))
    (hCv : ∀ᵐ t ∂timeMeasure T, ‖v t‖ ≤ (Cv : ℝ))
    (hCuv : ∀ᵐ t ∂timeMeasure T, ‖u t - v t‖ ≤ (Cuv : ℝ)) :
    timeOpL2 A hA u hu Cu hCu - timeOpL2 A hA v hv Cv hCv =
      timeOpL2 A hA (fun t => u t - v t) huv Cuv hCuv := by
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_sub (timeOpL2 A hA u hu Cu hCu) (timeOpL2 A hA v hv Cv hCv),
    timeOpL2_apply_ae A hA u hu Cu hCu,
    timeOpL2_apply_ae A hA v hv Cv hCv,
    timeOpL2_apply_ae A hA (fun t => u t - v t) huv Cuv hCuv]
    with t hout hu' hv' huv'
  rw [hout, Pi.sub_apply, hu', hv', huv', map_sub]

omit [CompleteSpace Y] in
theorem timeOpL2_congr
    (A : ℝ → X →L[ℝ] Y)
    (hA : MemLp A 2 (timeMeasure T))
    (u v : ℝ → X)
    (hu : AEStronglyMeasurable u (timeMeasure T))
    (hv : AEStronglyMeasurable v (timeMeasure T))
    (Cu Cv : NNReal)
    (hCu : ∀ᵐ t ∂timeMeasure T, ‖u t‖ ≤ (Cu : ℝ))
    (hCv : ∀ᵐ t ∂timeMeasure T, ‖v t‖ ≤ (Cv : ℝ))
    (huv : u =ᵐ[timeMeasure T] v) :
    timeOpL2 A hA u hu Cu hCu = timeOpL2 A hA v hv Cv hCv := by
  apply Lp.ext
  filter_upwards [
    timeOpL2_apply_ae A hA u hu Cu hCu,
    timeOpL2_apply_ae A hA v hv Cv hCv, huv]
    with t hu' hv' huv'
  rw [hu', hv', huv']

omit [CompleteSpace Y] in
theorem timeOpL2_norm_le
    (A : ℝ → X →L[ℝ] Y)
    (hA : MemLp A 2 (timeMeasure T))
    (u : ℝ → X)
    (hu : AEStronglyMeasurable u (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖u t‖ ≤ (C : ℝ)) :
    ‖timeOpL2 A hA u hu C hC‖ ≤
      (C : ℝ) * ‖hA.toLp A‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [timeOpL2_apply_ae A hA u hu C hC,
    hA.coeFn_toLp, hC] with t hout hcoeff ht
  rw [hout, hcoeff]
  calc
    ‖A t (u t)‖ ≤ ‖A t‖ * ‖u t‖ := (A t).le_opNorm (u t)
    _ ≤ ‖A t‖ * (C : ℝ) :=
      mul_le_mul_of_nonneg_left ht (norm_nonneg _)
    _ = (C : ℝ) * ‖A t‖ := mul_comm _ _

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
