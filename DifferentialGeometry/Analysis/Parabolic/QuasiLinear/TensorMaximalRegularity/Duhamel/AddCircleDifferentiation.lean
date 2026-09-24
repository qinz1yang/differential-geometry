import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.LinearTransport
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleDerivative

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

variable {ι : Type*} [Fintype ι]

def parameterDerivativeDuhamelForcing
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 1 : ℕ) : ℝ))) T) :
    timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ))) T :=
    let D := (AddCircle.parameterDerivativeHsPi (ι := ι) g n).comp
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by push_cast; rfl : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ))))
    let Dh := (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ)))).comp
      ((AddCircle.parameterDerivativeHsPi (ι := ι) g (n + 2)).comp
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := 0) (s := 0)
            (by push_cast; linarith : ((n + 2 : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 2))))
    let U := maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0)
      (a := ((n + 1 : ℕ) : ℝ)) hT 0 F
    let L₁ := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((n + 1 : ℕ) : ℝ))
    let L₀ := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ))
    D.compLpL 2 (timeMeasure T) F +
      (D.comp L₁ - L₀.comp Dh).compLpL 2 (timeMeasure T) U

theorem parameterDerivative_duhamel_vector_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 1 : ℕ) : ℝ))) T) :
    let D := (AddCircle.parameterDerivativeHsPi (ι := ι) g n).comp
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by push_cast; rfl : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ))))
    let Dh := (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ)))).comp
      ((AddCircle.parameterDerivativeHsPi (ι := ι) g (n + 2)).comp
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := 0) (s := 0)
            (by push_cast; linarith : ((n + 2 : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 2))))
    let U := maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0)
      (a := ((n + 1 : ℕ) : ℝ)) hT 0 F
    let G := parameterDerivativeDuhamelForcing g n hT F
    Dh.compLpL 2 (timeMeasure T) U =
        maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0) (a := n) hT 0 G ∧
      (maximalRegularityDuhamelVectorMap (g := g) (r := 0) (s := 0) (a := n) hT 0 G).initial = 0 ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        (maximalRegularityDuhamelVectorMap (g := g) (r := 0) (s := 0) (a := n) hT 0 G).toFun t =
          D ((maximalRegularityDuhamelVectorMap (g := g) (r := 0) (s := 0)
            (a := ((n + 1 : ℕ) : ℝ)) hT 0 F).toFun t) := by
  intro D Dh U G
  have hc := DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator
    (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0
  exact duhamel_vector_comp_zero_eq (ι := ι) (E := ℝ) (H := ℝ)
    (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0)
    (a := n) (b := ((n + 1 : ℕ) : ℝ)) hT hc D Dh (by
      apply ContinuousLinearMap.ext
      intro f
      apply PiLp.ext
      intro i
      simp only [D, Dh, ContinuousLinearMap.comp_apply, ContinuousLinearMap.piLpMap_apply,
        AddCircle.parameterDerivativeHsPi_apply]
      rw [← tensorHsInclusion_trans_apply, ← tensorHsInclusion_trans_apply]
      have hi := AddCircle.parameterDerivativeHs_tensorHsInclusion g
        (show n ≤ n + 2 by omega)
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by push_cast; linarith : ((n + 2 : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 2) (f i))
      rw [← tensorHsInclusion_trans_apply] at hi
      exact hi.symm) F


section
open DifferentialGeometry.Analysis.Spectral

def parameterSecondDerivativeDuhamelForcing
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 2 : ℕ) : ℝ))) T) :
    timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ))) T :=
  let D := (AddCircle.parameterSecondDerivativeHsPi (ι := ι) g n).comp
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0)
        (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ))))
  let Dh := (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := 0) (s := 0)
      (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ)))).comp
    (AddCircle.parameterSecondDerivativeHsPi (ι := ι) g (n + 2))
  let U := maximalRegularityDuhamelVectorField hT 0 F
  let Lh := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((n + 2 : ℕ) : ℝ))
  let Ll := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ))
  D.compLpL 2 (timeMeasure T) F + (D.comp Lh - Ll.comp Dh).compLpL 2 (timeMeasure T) U

theorem parameterSecondDerivative_duhamel_vector_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 2 : ℕ) : ℝ))) T) :
    let D := (AddCircle.parameterSecondDerivativeHsPi (ι := ι) g n).comp
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ))))
    let Dh := (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0)
        (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ)))).comp
      (AddCircle.parameterSecondDerivativeHsPi (ι := ι) g (n + 2))
    let U := maximalRegularityDuhamelVectorField hT 0 F
    let G := parameterSecondDerivativeDuhamelForcing g n hT F
    Dh.compLpL 2 (timeMeasure T) U = maximalRegularityDuhamelVectorField hT 0 G ∧
      (maximalRegularityDuhamelVectorMap hT 0 G).initial = 0 ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        (maximalRegularityDuhamelVectorMap hT 0 G).toFun t =
          D ((maximalRegularityDuhamelVectorMap hT 0 F).toFun t) := by
  intro D Dh U G
  apply duhamel_vector_comp_zero_eq hT (tensorResolventL2_isCompactOperator g 0 0) D Dh
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro i
  simp only [D, Dh, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.piLpMap_apply, AddCircle.parameterSecondDerivativeHsPi_apply]
  rw [← tensorHsInclusion_trans_apply]
  have hi := AddCircle.parameterSecondDerivativeHs_tensorHsInclusion g
    (show n ≤ n + 2 by omega) (u i)
  rw [← tensorHsInclusion_trans_apply]
  exact hi.symm

end

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
