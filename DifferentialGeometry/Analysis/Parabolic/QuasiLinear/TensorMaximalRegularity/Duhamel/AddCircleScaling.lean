import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleLaplacianScaling
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.FiniteProduct

noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

theorem maximalRegularityDuhamelVectorMap_timeDeriv_eq_scaled_parameterSecondDerivative
    {ι : Type*} [Fintype ι] (c : ℝ) (hc : 0 < c) (n : ℕ) {T : ℝ} (hT : 0 < T)
    (u₀ : PiLp 2 (fun _ : ι =>
      TensorHs (scaleMetric c⁻¹ (inv_pos.mpr hc) AddCircle.flatMetric) 0 0 ((n : ℝ) + 2)))
    (F : timeL2 (PiLp 2 (fun _ : ι =>
      TensorHs (scaleMetric c⁻¹ (inv_pos.mpr hc) AddCircle.flatMetric) 0 0 (n : ℝ))) T) :
    timeH1.timeDeriv _ T (maximalRegularityDuhamelVectorMap hT u₀ F) =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        c • AddCircle.parameterSecondDerivativeHs
          (scaleMetric c⁻¹ (inv_pos.mpr hc) AddCircle.flatMetric) n)).compLpL 2
        (timeMeasure T) (maximalRegularityDuhamelVectorField hT u₀ F) + F := by
  have heq := maximalRegularityDuhamelVectorMap_timeDeriv_eq hT
    (tensorResolventL2_isCompactOperator
      (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
      (scaleMetric c⁻¹ (inv_pos.mpr hc) AddCircle.flatMetric) 0 0) u₀ F
  rw [AddCircle.piLpMap_tensorScaleLaplacian_scaleMetric_flatMetric, inv_inv] at heq
  exact heq

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
