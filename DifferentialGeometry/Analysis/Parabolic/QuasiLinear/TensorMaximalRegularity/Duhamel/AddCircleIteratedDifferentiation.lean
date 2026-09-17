import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.LinearTransport
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleIteratedDerivative

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity
open DifferentialGeometry.Analysis.Spectral

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

variable {ι : Type*} [Fintype ι]

def iteratedParameterDerivativeDuhamelForcing
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m + n : ℕ) : ℝ))) T) :
    timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ))) T :=
  let D := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    (AddCircle.iteratedParameterDerivativeHs g n m).comp
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith :
          ((n + m : ℕ) : ℝ) ≤ ((m + n : ℕ) : ℝ))))
  let Dh := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ))).comp
        ((AddCircle.iteratedParameterDerivativeHs g (n + 2) m).comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by push_cast; linarith :
              ((n + 2 + m : ℕ) : ℝ) ≤ ((m + n : ℕ) : ℝ) + 2))))
  let U := maximalRegularityDuhamelVectorField
    (g := g) (r := 0) (s := 0) (a := ((m + n : ℕ) : ℝ)) hT 0 F
  let Lh := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((m + n : ℕ) : ℝ))
  let Ll := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ))
  D.compLpL 2 (timeMeasure T) F +
    (D.comp Lh - Ll.comp Dh).compLpL 2 (timeMeasure T) U

theorem iteratedParameterDerivative_duhamel_vector_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m + n : ℕ) : ℝ))) T) :
    let D := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      (AddCircle.iteratedParameterDerivativeHs g n m).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by push_cast; linarith :
            ((n + m : ℕ) : ℝ) ≤ ((m + n : ℕ) : ℝ))))
    let Dh := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ))).comp
          ((AddCircle.iteratedParameterDerivativeHs g (n + 2) m).comp
            (tensorHsInclusion (g := g) (r := 0) (s := 0)
              (by push_cast; linarith :
                ((n + 2 + m : ℕ) : ℝ) ≤ ((m + n : ℕ) : ℝ) + 2))))
    let U := maximalRegularityDuhamelVectorField
      (g := g) (r := 0) (s := 0) (a := ((m + n : ℕ) : ℝ)) hT 0 F
    let G := iteratedParameterDerivativeDuhamelForcing g n m hT F
    Dh.compLpL 2 (timeMeasure T) U =
        maximalRegularityDuhamelVectorField
          (g := g) (r := 0) (s := 0) (a := n) hT 0 G ∧
      (maximalRegularityDuhamelVectorMap
        (g := g) (r := 0) (s := 0) (a := n) hT 0 G).initial = 0 ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        (maximalRegularityDuhamelVectorMap
          (g := g) (r := 0) (s := 0) (a := n) hT 0 G).toFun t =
          D ((maximalRegularityDuhamelVectorMap
            (g := g) (r := 0) (s := 0)
            (a := ((m + n : ℕ) : ℝ)) hT 0 F).toFun t) := by
  intro D Dh U G
  have hc := tensorResolventL2_isCompactOperator
    (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0
  exact duhamel_vector_comp_zero_eq (ι := ι) (E := ℝ) (H := ℝ)
    (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0)
    (a := n) (b := ((m + n : ℕ) : ℝ)) hT hc D Dh (by
      apply ContinuousLinearMap.ext
      intro f
      apply PiLp.ext
      intro i
      simp only [D, Dh, ContinuousLinearMap.comp_apply, ContinuousLinearMap.piLpMap_apply]
      have hi := AddCircle.iteratedParameterDerivativeHs_tensorHsInclusion g
        (show n ≤ n + 2 by omega) m
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by push_cast; linarith :
            ((n + 2 + m : ℕ) : ℝ) ≤ ((m + n : ℕ) : ℝ) + 2) (f i))
      simpa only [← tensorHsInclusion_trans_apply] using hi.symm) F

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
