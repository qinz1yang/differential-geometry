import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleLaplacian
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.FiniteProduct

noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

theorem maximalRegularityDuhamelVectorMap_timeDeriv_eq_principal_add_drift
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (n : ℕ) {T : ℝ} (hT : 0 < T)
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 2)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ))) T) :
    timeH1.timeDeriv _ T (maximalRegularityDuhamelVectorMap hT u₀ F) =
      ((ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        appHs g 0 0 n (scalarCc g (AddCircle.laplacianPrincipalCoefficient g)))).comp
        (AddCircle.parameterSecondDerivativeHsPi g n) +
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        appHs g 0 0 n (scalarCc g (AddCircle.laplacianDriftCoefficient g)))).comp
        ((AddCircle.parameterDerivativeHsPi g n).comp
          (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
            tensorHsInclusion (g := g) (r := 0) (s := 0)
              (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith))))).compLpL 2
        (timeMeasure T) (maximalRegularityDuhamelVectorField hT u₀ F) + F := by
  rw [← AddCircle.piLpMap_tensorScaleLaplacian_eq_principal_add_drift]
  exact maximalRegularityDuhamelVectorMap_timeDeriv_eq hT
    (tensorResolventL2_isCompactOperator
      (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0) u₀ F

theorem maximalRegularityDuhamelVectorMap_timeDeriv_eq_parameterSecondDerivative
    {ι : Type*} [Fintype ι] (n : ℕ) {T : ℝ} (hT : 0 < T)
    (u₀ : PiLp 2 (fun _ : ι => TensorHs AddCircle.flatMetric 0 0 ((n : ℝ) + 2)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs AddCircle.flatMetric 0 0 (n : ℝ))) T) :
    timeH1.timeDeriv _ T (maximalRegularityDuhamelVectorMap hT u₀ F) =
      (AddCircle.parameterSecondDerivativeHsPi AddCircle.flatMetric n).compLpL 2
        (timeMeasure T) (maximalRegularityDuhamelVectorField hT u₀ F) + F := by
  rw [AddCircle.parameterSecondDerivativeHsPi_flatMetric]
  exact maximalRegularityDuhamelVectorMap_timeDeriv_eq hT
    (DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator
      (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) AddCircle.flatMetric 0 0) u₀ F

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
