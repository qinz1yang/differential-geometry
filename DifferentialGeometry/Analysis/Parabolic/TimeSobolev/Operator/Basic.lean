import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.L2
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {T : ℝ}

omit [CompleteSpace X] in
theorem memLp_timeOp
    (A : ℝ → X →L[ℝ] Y)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (f : timeL2 X T) :
    MemLp (fun t => A t (f t)) 2 (timeMeasure T) := by
  have hf : AEStronglyMeasurable (fun t => f t) (timeMeasure T) :=
    Lp.aestronglyMeasurable f
  have hmeas : AEStronglyMeasurable (fun t => A t (f t)) (timeMeasure T) := by
    have h :=
      (ContinuousLinearMap.apply ℝ Y).aestronglyMeasurable_comp₂ hf hA
    simpa only [ContinuousLinearMap.apply_apply] using h
  refine MemLp.of_le_mul (c := (C : ℝ)) (Lp.memLp f) hmeas ?_
  filter_upwards [hC] with t ht
  calc
    ‖A t (f t)‖ ≤ ‖A t‖ * ‖f t‖ := (A t).le_opNorm (f t)
    _ ≤ (C : ℝ) * ‖f t‖ :=
      mul_le_mul_of_nonneg_right ht (norm_nonneg _)

variable [CompleteSpace Y]

private noncomputable def timeOpFun
    (A : ℝ → X →L[ℝ] Y)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (f : timeL2 X T) : timeL2 Y T :=
  (memLp_timeOp A hA C hC f).toLp (fun t => A t (f t))

omit [CompleteSpace X] [CompleteSpace Y] in
private theorem timeOpFun_apply_ae
    (A : ℝ → X →L[ℝ] Y)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (f : timeL2 X T) :
    timeOpFun A hA C hC f =ᵐ[timeMeasure T] fun t => A t (f t) :=
  (memLp_timeOp A hA C hC f).coeFn_toLp

omit [CompleteSpace X] [CompleteSpace Y] in
private theorem timeOpFun_add
    (A : ℝ → X →L[ℝ] Y)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (f g : timeL2 X T) :
    timeOpFun A hA C hC (f + g) =
      timeOpFun A hA C hC f + timeOpFun A hA C hC g := by
  apply Lp.ext
  filter_upwards [timeOpFun_apply_ae A hA C hC (f + g),
    timeOpFun_apply_ae A hA C hC f, timeOpFun_apply_ae A hA C hC g,
    Lp.coeFn_add f g,
    Lp.coeFn_add (timeOpFun A hA C hC f) (timeOpFun A hA C hC g)]
    with t hfg hf hg hfg_in hfg_out
  rw [hfg, hfg_out, hfg_in]
  simp only [Pi.add_apply]
  rw [hf, hg, map_add]

omit [CompleteSpace X] [CompleteSpace Y] in
private theorem timeOpFun_smul
    (A : ℝ → X →L[ℝ] Y)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (c : ℝ) (f : timeL2 X T) :
    timeOpFun A hA C hC (c • f) = c • timeOpFun A hA C hC f := by
  apply Lp.ext
  filter_upwards [timeOpFun_apply_ae A hA C hC (c • f),
    timeOpFun_apply_ae A hA C hC f, Lp.coeFn_smul c f,
    Lp.coeFn_smul c (timeOpFun A hA C hC f)]
    with t hcf hf hcf_in hcf_out
  rw [hcf, hcf_out, hcf_in]
  simp only [Pi.smul_apply]
  rw [hf, map_smul]

omit [CompleteSpace X] [CompleteSpace Y] in
private theorem timeOpFun_norm_le
    (A : ℝ → X →L[ℝ] Y)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (f : timeL2 X T) :
    ‖timeOpFun A hA C hC f‖ ≤ (C : ℝ) * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [timeOpFun_apply_ae A hA C hC f, hC] with t htf ht
  rw [htf]
  calc
    ‖A t (f t)‖ ≤ ‖A t‖ * ‖f t‖ := (A t).le_opNorm (f t)
    _ ≤ (C : ℝ) * ‖f t‖ :=
      mul_le_mul_of_nonneg_right ht (norm_nonneg _)

private noncomputable def timeOpLin
    (A : ℝ → X →L[ℝ] Y)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ)) :
    timeL2 X T →ₗ[ℝ] timeL2 Y T where
  toFun := timeOpFun A hA C hC
  map_add' := timeOpFun_add A hA C hC
  map_smul' := timeOpFun_smul A hA C hC

noncomputable def timeOp
    (A : ℝ → X →L[ℝ] Y)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ)) :
    timeL2 X T →L[ℝ] timeL2 Y T :=
  (timeOpLin A hA C hC).mkContinuous (C : ℝ)
    (timeOpFun_norm_le A hA C hC)

omit [CompleteSpace X] [CompleteSpace Y] in
theorem timeOp_apply_ae
    (A : ℝ → X →L[ℝ] Y)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (f : timeL2 X T) :
    timeOp A hA C hC f =ᵐ[timeMeasure T] fun t => A t (f t) :=
  timeOpFun_apply_ae A hA C hC f

omit [CompleteSpace X] [CompleteSpace Y] in
theorem timeOp_norm_le
    (A : ℝ → X →L[ℝ] Y)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ)) :
    ‖timeOp A hA C hC‖ ≤ (C : ℝ) := by
  exact LinearMap.mkContinuous_norm_le (timeOpLin A hA C hC) C.coe_nonneg
    (timeOpFun_norm_le A hA C hC)

omit [CompleteSpace X] [CompleteSpace Y] in
theorem timeOp_sub
    (A B : ℝ → X →L[ℝ] Y)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (hB : AEStronglyMeasurable B (timeMeasure T))
    (CA CB C : NNReal)
    (hCA : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (CA : ℝ))
    (hCB : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ (CB : ℝ))
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t - B t‖ ≤ (C : ℝ)) :
    timeOp A hA CA hCA - timeOp B hB CB hCB =
      timeOp (fun t ↦ A t - B t) (hA.sub hB) C hC := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (timeOp A hA CA hCA f) (timeOp B hB CB hCB f),
    timeOp_apply_ae A hA CA hCA f, timeOp_apply_ae B hB CB hCB f,
    timeOp_apply_ae (fun t ↦ A t - B t) (hA.sub hB) C hC f]
    with t hsub hAf hBf hDf
  change ((timeOp A hA CA hCA f - timeOp B hB CB hCB f : timeL2 Y T) : ℝ → Y) t = _
  rw [hsub, Pi.sub_apply, hAf, hBf, hDf, sub_apply]

omit [CompleteSpace X] [CompleteSpace Y] in
theorem timeOp_sub_norm_le
    (A B : ℝ → X →L[ℝ] Y)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (hB : AEStronglyMeasurable B (timeMeasure T))
    (CA CB C : NNReal)
    (hCA : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (CA : ℝ))
    (hCB : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ (CB : ℝ))
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t - B t‖ ≤ (C : ℝ)) :
    ‖timeOp A hA CA hCA - timeOp B hB CB hCB‖ ≤ (C : ℝ) := by
  rw [timeOp_sub A B hA hB CA CB C hCA hCB hC]
  exact timeOp_norm_le _ _ C hC


end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
