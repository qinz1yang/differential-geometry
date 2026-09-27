import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleClassicalDerivative
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.ContinuousRepresentative

open MeasureTheory Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open TensorHeatEquation TensorSpectral TimeSobolev
open DifferentialGeometry.Analysis.Spectral

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

variable {ι : Type*} [Fintype ι]

theorem ae_contDiff_two_parameterDerivative_representative
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) T)
    (v : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℝ) + 2))) T)
    (hlink : ∀ᵐ t ∂timeMeasure T,
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show (1 : ℝ) ≤ (1 : ℝ) + 2 by norm_num)) (v t) = u.toFun t) :
    ∀ᵐ t ∂timeMeasure T,
      ContDiff ℝ 2 (fun x : ℝ => scalarH1PiToContinuous g (u.toFun t)
        (x : AddCircle (1 : ℝ))) ∧
      ∀ x : ℝ, HasDerivAt
        (deriv (fun y : ℝ => scalarH1PiToContinuous g (u.toFun t)
          (y : AddCircle (1 : ℝ))))
        (scalarH1PiToContinuous g
          (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
            tensorHsInclusion (g := g) (r := 0) (s := 0)
              (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
            (AddCircle.parameterDerivativeHsPi g 1
              (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
                tensorHsInclusion (g := g) (r := 0) (s := 0)
                  (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ)))
                (AddCircle.parameterDerivativeHsPi g 2
                  (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
                    tensorHsInclusion (g := g) (r := 0) (s := 0)
                      (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ (1 : ℝ) + 2)) (v t))))))
          (x : AddCircle (1 : ℝ))) x := by
  filter_upwards [hlink] with t ht
  let V := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ (1 : ℝ) + 2)) (v t)
  have hlo : ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((2 : ℕ) : ℝ) + 1)) V = u.toFun t := by
    rw [← ht]
    apply PiLp.ext
    intro i
    exact (tensorHsInclusion_trans_apply (by norm_num) (by norm_num) (v t i)).symm
  constructor
  · have h := AddCircle.contDiff_two_scalarH1PiToContinuous g V
    rw [hlo] at h
    exact h
  · intro x
    have h := AddCircle.hasDerivAt_deriv_scalarH1PiToContinuous g V x
    rw [hlo] at h
    exact h

theorem maximalRegularityDuhamelVectorMap_ae_contDiff_two_parameterDerivative
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} (hT : 0 < T)
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℝ) + 2)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) T) :
    let u := maximalRegularityDuhamelVectorMap hT u₀ F
    let v := maximalRegularityDuhamelVectorField hT u₀ F
    ∀ᵐ t ∂timeMeasure T,
      ContDiff ℝ 2 (fun x : ℝ => scalarH1PiToContinuous g (u.toFun t)
        (x : AddCircle (1 : ℝ))) ∧
      ∀ x : ℝ, HasDerivAt
        (deriv (fun y : ℝ => scalarH1PiToContinuous g (u.toFun t)
          (y : AddCircle (1 : ℝ))))
        (scalarH1PiToContinuous g
          (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
            tensorHsInclusion (g := g) (r := 0) (s := 0)
              (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
            (AddCircle.parameterDerivativeHsPi g 1
              (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
                tensorHsInclusion (g := g) (r := 0) (s := 0)
                  (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ)))
                (AddCircle.parameterDerivativeHsPi g 2
                  (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
                    tensorHsInclusion (g := g) (r := 0) (s := 0)
                      (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ (1 : ℝ) + 2)) (v t))))))
          (x : AddCircle (1 : ℝ))) x := by
  dsimp only
  apply ae_contDiff_two_parameterDerivative_representative g
    (maximalRegularityDuhamelVectorMap hT u₀ F)
    (maximalRegularityDuhamelVectorField hT u₀ F)
  obtain ⟨w, _, hwlo, hwhi⟩ :=
    maximalRegularityDuhamelVectorMap_exists_continuousOn_representative hT
      (tensorResolventL2_isCompactOperator
        (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0) u₀ F
  filter_upwards [hwhi, ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht hmem
  rw [← hwlo t hmem, ht]
  apply PiLp.ext
  intro i
  exact tensorHsInclusion_trans_apply (by norm_num) (by norm_num)
    (maximalRegularityDuhamelVectorField hT u₀ F t i)

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
