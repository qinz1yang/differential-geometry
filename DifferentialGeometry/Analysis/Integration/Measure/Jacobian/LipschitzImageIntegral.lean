import DifferentialGeometry.Analysis.Calculus.Rademacher
import DifferentialGeometry.Analysis.Integration.Measure.Jacobian.ImageIntegralBound
import DifferentialGeometry.Analysis.Integration.Measure.LipschitzChangeOfVariables

/-! A weighted image-volume bound for maps which are locally Lipschitz on an open set. -/

open Filter Set
open scoped ENNReal

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The Jacobian bounds the weighted measure of an image without an injectivity assumption.
Local Lipschitz regularity is needed only on the given open neighborhood of the source set. -/
theorem image_lintegral_le_of_locallyLipschitzOn
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → E} {U S : Set E}
    (hU : IsOpen U) (hS : MeasurableSet S) (hSU : S ⊆ U)
    (hf : Measurable f) (hLip : LocallyLipschitzOn U f)
    {w : E → ℝ≥0∞} (hw : Measurable w) :
    ∫⁻ y in f '' S, w y ∂μ ≤
      ∫⁻ x in S, w (f x) * ENNReal.ofReal |(fderiv ℝ f x).det| ∂μ := by
  have hd : ∀ᵐ x ∂μ, x ∈ U → DifferentiableAt ℝ f x := by
    filter_upwards [hLip.ae_differentiableWithinAt_of_mem (μ := μ)] with x hx
    intro hxU
    exact (hx hxU).differentiableAt (hU.mem_nhds hxU)
  let T : Set E := S ∩ {x | DifferentiableAt ℝ f x}
  have hT : MeasurableSet T := hS.inter (measurableSet_of_differentiableAt ℝ f)
  have hTS : T =ᵐ[μ] S := by
    filter_upwards [hd] with x hx
    apply propext
    exact ⟨fun hxT => hxT.1, fun hxS => ⟨hxS, hx (hSU hxS)⟩⟩
  have hnull : μ (S \ T) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hd] with x hx
    intro hxST
    exact hxST.2 ⟨hxST.1, hx (hSU hxST.1)⟩
  have hnullImage : μ (f '' (S \ T)) = 0 :=
    (hLip.mono (show S \ T ⊆ U from fun _ hx => hSU hx.1)).addHaar_image_eq_zero rfl hnull
  have himage : f '' T =ᵐ[μ] f '' S := by
    have he : μ (f '' S \ f '' T) = 0 := measure_mono_null
      (by
        rintro x ⟨⟨y, hy, rfl⟩, hxT⟩
        exact ⟨y, ⟨hy, fun hyT => hxT ⟨y, hyT, rfl⟩⟩, rfl⟩) hnullImage
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp he] with x hx
    apply propext
    exact ⟨fun ⟨y, hy, hxy⟩ => ⟨y, hy.1, hxy⟩,
      fun hxS => not_not.mp (fun hxT => hx ⟨hxS, hxT⟩)⟩
  rw [← setLIntegral_congr himage, ← setLIntegral_congr hTS]
  exact image_lintegral_le μ hT hf
    (fun _ hx => hx.2.hasFDerivAt.hasFDerivWithinAt) hw

end MeasureTheory
