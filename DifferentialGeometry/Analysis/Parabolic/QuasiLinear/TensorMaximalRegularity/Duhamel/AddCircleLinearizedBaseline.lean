import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleForcing
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.H0MultiplicationInclusion

noncomputable section

open scoped Manifold ContDiff ENNReal

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

variable {ι : Type*}

def parameterDerivativeBaselineForcingHsPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2))) :
    (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1) ×
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) →L[ℝ]
        PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)) :=
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))
    let D := parameterDerivativeHs g 1
    let Q := K.comp (parameterSecondDerivativeHs g 2)
    let m := scalarHsMul g 1 (by norm_num)
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i : ι =>
        (((m.flip (D (Q (f₀ i)))).comp J +
          (m.flip (J (Q (f₀ i)))).comp D).comp (ContinuousLinearMap.fst ℝ _ _)) +
          (D.comp (PiLp.proj 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) i)).comp
            (ContinuousLinearMap.snd ℝ _ _))

private theorem parameterDerivativeHs_project_one
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let D := (parameterDerivativeHs g 0).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    Z (D (J u)) = P (parameterDerivativeHs g 1 u) := by
  intro J D Z P
  simp only [D, J, ContinuousLinearMap.comp_apply]
  rw [← tensorHsInclusion_trans_apply,
    parameterDerivativeHs_tensorHsInclusion g (by omega : 0 ≤ 1)]
  exact (tensorHsInclusion_trans_apply _ _ _).symm

private theorem parameterSecondDerivativeHs_project_two
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u : TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    parameterSecondDerivativeHs g 1 (P u) = J (K (parameterSecondDerivativeHs g 2 u)) := by
  intro J K P
  rw [parameterSecondDerivativeHs_tensorHsInclusion g (by omega : 1 ≤ 2)]
  exact tensorHsInclusion_trans_apply _ _ _

theorem tensorHsInclusion_parameterDerivativeBaselineForcingHsPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)))
    (a₂ : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))
    (b₂ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let P := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    (ContinuousLinearMap.piLpMap 2 fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ)))
      (parameterDerivativeBaselineForcingHsPi g f₀ (a₂, b₂)) =
    WithLp.toLp 2 (fun i => parameterDerivativeParabolicForcing g (J a₂) (J (b₂ i)) (P (f₀ i)) 0) := by
  intro J P
  let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))
  let Q := K.comp (parameterSecondDerivativeHs g 2)
  let D := (parameterDerivativeHs g 0).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ)))
  let Dh := (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ))).comp
      ((parameterDerivativeHs g 2).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)))
  let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
  let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
  let J₀ := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
  have hD (u : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) :
      Z (D (J u)) = J₀ (parameterDerivativeHs g 1 u) :=
    parameterDerivativeHs_project_one g u
  have hQ (i : ι) : parameterSecondDerivativeHs g 1 (P (f₀ i)) = J (Q (f₀ i)) :=
    parameterSecondDerivativeHs_project_two g (f₀ i)
  have hthird (i : ι) :
      J₀ (parameterDerivativeHs g 1 (Q (f₀ i))) =
        Z (parameterSecondDerivativeHs g 0 (Dh (P (f₀ i)))) := by
    rw [← hD, ← hQ]
    exact congrArg Z (parameterDerivativeHs_parameterSecondDerivativeHs g 0 (P (f₀ i)))
  apply PiLp.ext
  intro i
  change J₀ (scalarHsMul g 1 (by norm_num) (J a₂)
      (parameterDerivativeHs g 1 (Q (f₀ i))) +
    scalarHsMul g 1 (by norm_num) (parameterDerivativeHs g 1 a₂) (J (Q (f₀ i))) +
      parameterDerivativeHs g 1 (b₂ i)) = _
  rw [J₀.map_add, J₀.map_add, tensorHsInclusion_scalarHsMul_zero,
    tensorHsInclusion_scalarHsMul_zero, hthird]
  change scalarH0ContinuousMul g (C (J a₂))
      (Z (parameterSecondDerivativeHs g 0 (Dh (P (f₀ i))))) +
    scalarH0ContinuousMul g (C (parameterDerivativeHs g 1 a₂)) (J₀ (J (Q (f₀ i)))) +
      J₀ (parameterDerivativeHs g 1 (b₂ i)) = _
  rw [scalarH0ContinuousMul_scalarH1ToContinuous_comm]
  simp only [parameterDerivativeParabolicForcing, map_zero, zero_apply,
    zero_add, add_zero, sub_zero]
  change _ = scalarH0ContinuousMul g (C (J a₂))
      (Z (parameterSecondDerivativeHs g 0 (Dh (P (f₀ i))))) +
    scalarH0ContinuousMul g (C (parameterSecondDerivativeHs g 1 (P (f₀ i))))
      (Z (D (J a₂))) + Z (D (J (b₂ i)))
  rw [hQ, hD, hD]

end AddCircle
