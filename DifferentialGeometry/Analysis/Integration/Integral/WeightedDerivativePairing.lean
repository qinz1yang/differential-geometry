import DifferentialGeometry.Analysis.Integration.Lp.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] [SecondCountableTopology F]

theorem integrableOn_bilinear_fderiv_of_lipschitz
    {f : ℂ → F} {L : ℝ≥0} (hf : LipschitzWith L f)
    {D : Set ℂ} (hD : MeasurableSet D) (hDfinite : volume D ≠ ∞)
    {K : Set F} (hK : IsCompact K) (hfK : MapsTo f D K)
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (hA : ContinuousOn A K) (v w : ℂ) :
    IntegrableOn (fun z => A (f z) (fderiv ℝ f z v) (fderiv ℝ f z w)) D := by
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.mpr hDfinite
  have hder (d : ℂ) : MemLp (fun z => fderiv ℝ f z d) 2 (volume.restrict D) := by
    apply MemLp.of_bound (measurable_fderiv_apply_const ℝ f d).aestronglyMeasurable
      ((L : ℝ) * ‖d‖)
    exact Eventually.of_forall fun z => ((fderiv ℝ f z).le_opNorm d).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg d))
  have hAf : ContinuousOn (fun z => A (f z)) D :=
    hA.comp hf.continuous.continuousOn hfK
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hA
  apply integrable_bilinear_of_apply_aestronglyMeasurable (fun z => A (f z))
    (fun a b => ((hAf.clm_apply continuousOn_const).clm_apply
      continuousOn_const).aestronglyMeasurable hD) (C := C) _ (hder v) (hder w)
  filter_upwards [ae_restrict_mem hD] with z hz
  exact hC (f z) (hfK hz)

theorem integrableOn_weighted_bilinear_fderiv_of_lipschitz
    {f : ℂ → F} {L : ℝ≥0} (hf : LipschitzWith L f)
    {D : Set ℂ} (hD : MeasurableSet D) (hDfinite : volume D ≠ ∞)
    {K : Set F} (hK : IsCompact K) (hfK : MapsTo f D K)
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (hA : ContinuousOn A K)
    {weight : ℂ → ℝ} (hweight : AEStronglyMeasurable weight (volume.restrict D))
    {C : ℝ} (hbound : ∀ᵐ z ∂volume.restrict D, ‖weight z‖ ≤ C) (v w : ℂ) :
    IntegrableOn (fun z => weight z *
      A (f z) (fderiv ℝ f z v) (fderiv ℝ f z w)) D := by
  exact (integrableOn_bilinear_fderiv_of_lipschitz hf hD hDfinite hK hfK A hA v w).bdd_mul
    hweight hbound

end DifferentialGeometry.Analysis

end
