import DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ScalarEvaluation
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Application.IteratedCovariantDerivative
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.Application
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothInclusion
import DifferentialGeometry.Analysis.FunctionalAnalysis.PiLpMap

section

noncomputable section
open scoped Manifold ContDiff

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral

def parameterTangentSection :
    ContMDiffSection 𝓘(ℝ, ℝ) ℝ ∞ (TangentSpace 𝓘(ℝ, ℝ) : AddCircle (1 : ℝ) → Type _) where
  toFun := parameterTangent
  contMDiff_toFun := contMDiff_parameterTangent

theorem parameterTangentSection_apply (z : AddCircle (1 : ℝ)) :
    parameterTangentSection z = parameterTangent z := rfl

def parameterTangentCcTensor (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    SmoothCcTensor g 1 0 :=
  covectorEvaluationCcTensor g parameterTangentSection

theorem parameterTangentCcTensor_apply
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (z : AddCircle (1 : ℝ)) (α : Tensor0SSpace 1 𝓘(ℝ, ℝ) z)
    (w : Fin 0 → TangentSpace 𝓘(ℝ, ℝ) z) :
    (parameterTangentCcTensor g).toSection z α w = α (fun _ => parameterTangent z) := by
  change interiorProduct 0 z (parameterTangent z) α w = _
  rw [interior_product_apply]
  congr 1
  funext i
  fin_cases i
  rfl


end AddCircle

end

end

section

noncomputable section
open scoped Manifold ContDiff

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

def parameterDerivativeCcTensor
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (S : SmoothCcTensor g 0 0) : SmoothCcTensor g 0 0 :=
  operatorFieldApply g 1 0 (parameterTangentCcTensor g) (covGrad g 0 0 S)

theorem scalar0_parameterDerivativeCcTensor
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (S : SmoothCcTensor g 0 0) (z : AddCircle (1 : ℝ)) :
    TensorRSField.scalar0 (parameterDerivativeCcTensor g S).toSection z =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (TensorRSField.scalar0 S.toSection) z (parameterTangent z) := by
  exact scalar0_covectorEvaluationCcTensor_covGrad g parameterTangentSection S z

theorem scalar0_parameterDerivativeCcTensor_coe
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (S : SmoothCcTensor g 0 0) (x : ℝ) :
    TensorRSField.scalar0 (parameterDerivativeCcTensor g S).toSection (x : AddCircle (1 : ℝ)) =
      deriv (fun t : ℝ => TensorRSField.scalar0 S.toSection (t : AddCircle (1 : ℝ))) x := by
  rw [scalar0_parameterDerivativeCcTensor]
  exact (deriv_comp_coe (TensorRSField.scalar0_smooth S.toSection |>.mdifferentiableAt (by decide))).symm

end AddCircle

end

end

section

noncomputable section
open scoped Manifold ContDiff

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2

theorem scalar0_parameterDerivativeCcTensor_twice_coe
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (S : SmoothCcTensor g 0 0) (x : ℝ) :
    TensorRSField.scalar0
        (parameterDerivativeCcTensor g (parameterDerivativeCcTensor g S)).toSection
        (x : AddCircle (1 : ℝ)) =
      deriv (deriv (fun t : ℝ => TensorRSField.scalar0 S.toSection (t : AddCircle (1 : ℝ)))) x := by
  rw [scalar0_parameterDerivativeCcTensor_coe]
  congr 1
  funext t
  exact scalar0_parameterDerivativeCcTensor_coe g S t

end AddCircle

end

end

section

noncomputable section
open scoped Manifold ContDiff

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation (TensorHs)

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

def parameterDerivativeHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    TensorHs g 0 0 ((n : ℝ) + 1) →L[ℝ] TensorHs g 0 0 (n : ℝ) :=
  (appHs g 1 0 n (parameterTangentCcTensor g)).comp
    ((iterCovGradHs g 0 1 n).comp
      (TensorHs.castEquiv (g := g) (r := 0) (s := 0)
        (by norm_num : (n : ℝ) + 1 = (n : ℝ) + ((1 : ℕ) : ℝ))).toContinuousLinearEquiv.toContinuousLinearMap)

theorem parameterDerivativeHs_apply_ccTensorToHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (W : SmoothCcTensor g 0 0) :
    parameterDerivativeHs g n (ccTensorToHs g 0 ((n : ℝ) + 1) W) =
      ccTensorToHs g 0 (n : ℝ)
        (parameterDerivativeCcTensor g W) := by
  have hcast :
      (TensorHs.castEquiv (g := g) (r := 0) (s := 0)
        (by norm_num : (n : ℝ) + 1 = (n : ℝ) + ((1 : ℕ) : ℝ)))
        (ccTensorToHs g 0 ((n : ℝ) + 1) W) =
      ccTensorToHs g 0 ((n : ℝ) + ((1 : ℕ) : ℝ)) W := by
    apply TensorHs.ext
    funext i
    simp only [TensorHs.castEquiv_coeff, ccTensorToHs_coeff]
  change (appHs g 1 0 n (parameterTangentCcTensor g))
    ((iterCovGradHs g 0 1 n)
      ((TensorHs.castEquiv (g := g) (r := 0) (s := 0)
        (by norm_num : (n : ℝ) + 1 = (n : ℝ) + ((1 : ℕ) : ℝ)))
        (ccTensorToHs g 0 ((n : ℝ) + 1) W))) = _
  rw [hcast, iterCovGradHs_apply_ccTensorToHs, appHs_apply_ccTensorToHs]
  rfl

end AddCircle

end

end

section

open scoped Manifold ContDiff

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

theorem parameterDerivativeHs_comp_tensorHsInclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n m : ℕ} (h : n ≤ m) :
    (parameterDerivativeHs g n).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show (n : ℝ) + 1 ≤ (m : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right h 1)) =
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast h)).comp
          (parameterDerivativeHs g m) := by
  let L := (parameterDerivativeHs g n).comp
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (n : ℝ) + 1 ≤ (m : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right h 1))
  let R := (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast h)).comp (parameterDerivativeHs g m)
  have heq : (L : _ → _) = R := (ccToHsLin_dense g 0 (by positivity :
      (0 : ℝ) ≤ (m : ℝ) + 1)).equalizer L.continuous R.continuous (by
    funext S
    simp only [Function.comp_apply, L, R, ContinuousLinearMap.comp_apply, ccToHsLin_apply]
    rw [tensorHsInclusion_ccTensorToHs, parameterDerivativeHs_apply_ccTensorToHs,
      parameterDerivativeHs_apply_ccTensorToHs, tensorHsInclusion_ccTensorToHs])
  exact DFunLike.coe_injective heq

theorem parameterDerivativeHs_tensorHsInclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n m : ℕ} (h : n ≤ m) (u : TensorHs g 0 0 ((m : ℝ) + 1)) :
    parameterDerivativeHs g n
        (tensorHsInclusion (show (n : ℝ) + 1 ≤ (m : ℝ) + 1 by
          exact_mod_cast Nat.add_le_add_right h 1) u) =
      tensorHsInclusion (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast h)
        (parameterDerivativeHs g m u) :=
  DFunLike.congr_fun (parameterDerivativeHs_comp_tensorHsInclusion g h) u

end AddCircle

end

section

noncomputable section

open scoped Manifold ContDiff

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

variable {ι : Type*}

def parameterDerivativeHsPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ)) :=
  ContinuousLinearMap.piLpMap 2 (fun _ => parameterDerivativeHs g n)

@[simp] theorem parameterDerivativeHsPi_apply
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (u : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1))) (i : ι) :
    parameterDerivativeHsPi g n u i = parameterDerivativeHs g n (u i) := rfl

theorem parameterDerivativeHsPi_apply_ccTensorToHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (W : ι → SmoothCcTensor g 0 0) :
    parameterDerivativeHsPi g n
        (WithLp.toLp 2 (fun i => ccTensorToHs g 0 ((n : ℝ) + 1) (W i))) =
      WithLp.toLp 2 (fun i => ccTensorToHs g 0 (n : ℝ)
        (parameterDerivativeCcTensor g (W i))) := by
  apply PiLp.ext
  intro i
  exact parameterDerivativeHs_apply_ccTensorToHs g n (W i)

theorem norm_parameterDerivativeHsPi_le [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    ‖parameterDerivativeHsPi (ι := ι) g n‖ ≤ ‖parameterDerivativeHs g n‖ := by
  exact ContinuousLinearMap.norm_piLpMap_le (fun _ : ι => parameterDerivativeHs g n)
    (norm_nonneg _) (fun _ => le_rfl)

def parameterSecondDerivativeHsPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ)) :=
  (parameterDerivativeHsPi g n).comp
    ((ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (show (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) by norm_num))).comp
      ((parameterDerivativeHsPi g (n + 1)).comp
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (show ((n + 1 : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 2 by push_cast; linarith)))))

theorem parameterSecondDerivativeHsPi_apply_ccTensorToHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (W : ι → SmoothCcTensor g 0 0) :
    parameterSecondDerivativeHsPi g n
        (WithLp.toLp 2 (fun i => ccTensorToHs g 0 ((n : ℝ) + 2) (W i))) =
      WithLp.toLp 2 (fun i => ccTensorToHs g 0 (n : ℝ)
        (parameterDerivativeCcTensor g (parameterDerivativeCcTensor g (W i)))) := by
  apply PiLp.ext
  intro i
  simp only [parameterSecondDerivativeHsPi, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.piLpMap_apply, parameterDerivativeHsPi_apply]
  rw [tensorHsInclusion_ccTensorToHs, parameterDerivativeHs_apply_ccTensorToHs,
    tensorHsInclusion_ccTensorToHs, parameterDerivativeHs_apply_ccTensorToHs]

theorem parameterDerivativeHsPi_comp_tensorHsInclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n m : ℕ} (h : n ≤ m) :
    (parameterDerivativeHsPi (ι := ι) g n).comp
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (show (n : ℝ) + 1 ≤ (m : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right h 1))) =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast h))).comp
            (parameterDerivativeHsPi g m) := by
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro i
  exact parameterDerivativeHs_tensorHsInclusion g h (u i)

end AddCircle

end

end


noncomputable section

open scoped Manifold ContDiff

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

def parameterSecondDerivativeHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    TensorHs g 0 0 ((n : ℝ) + 2) →L[ℝ] TensorHs g 0 0 (n : ℝ) :=
  (parameterDerivativeHs g n).comp
    ((tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) by norm_num)).comp
      ((parameterDerivativeHs g (n + 1)).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show ((n + 1 : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 2 by push_cast; linarith))))

theorem parameterSecondDerivativeHs_apply_ccTensorToHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (W : SmoothCcTensor g 0 0) :
    parameterSecondDerivativeHs g n (ccTensorToHs g 0 ((n : ℝ) + 2) W) =
      ccTensorToHs g 0 (n : ℝ)
        (parameterDerivativeCcTensor g (parameterDerivativeCcTensor g W)) := by
  simp only [parameterSecondDerivativeHs, ContinuousLinearMap.comp_apply]
  rw [tensorHsInclusion_ccTensorToHs, parameterDerivativeHs_apply_ccTensorToHs,
    tensorHsInclusion_ccTensorToHs, parameterDerivativeHs_apply_ccTensorToHs]

@[simp] theorem parameterSecondDerivativeHsPi_apply {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (u : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 2))) (i : ι) :
    parameterSecondDerivativeHsPi g n u i = parameterSecondDerivativeHs g n (u i) := rfl

theorem parameterSecondDerivativeHs_comp_tensorHsInclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n m : ℕ} (h : n ≤ m) :
    (parameterSecondDerivativeHs g n).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show (n : ℝ) + 2 ≤ (m : ℝ) + 2 by exact_mod_cast Nat.add_le_add_right h 2)) =
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast h)).comp
          (parameterSecondDerivativeHs g m) := by
  let L := (parameterSecondDerivativeHs g n).comp
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (n : ℝ) + 2 ≤ (m : ℝ) + 2 by exact_mod_cast Nat.add_le_add_right h 2))
  let R := (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast h)).comp (parameterSecondDerivativeHs g m)
  have heq : (L : _ → _) = R := (ccToHsLin_dense g 0 (by positivity :
      (0 : ℝ) ≤ (m : ℝ) + 2)).equalizer L.continuous R.continuous (by
    funext S
    simp only [Function.comp_apply, L, R, ContinuousLinearMap.comp_apply, ccToHsLin_apply]
    rw [tensorHsInclusion_ccTensorToHs, parameterSecondDerivativeHs_apply_ccTensorToHs,
      parameterSecondDerivativeHs_apply_ccTensorToHs, tensorHsInclusion_ccTensorToHs])
  exact DFunLike.coe_injective heq

theorem parameterSecondDerivativeHs_tensorHsInclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n m : ℕ} (h : n ≤ m) (u : TensorHs g 0 0 ((m : ℝ) + 2)) :
    parameterSecondDerivativeHs g n
        (tensorHsInclusion (show (n : ℝ) + 2 ≤ (m : ℝ) + 2 by
          exact_mod_cast Nat.add_le_add_right h 2) u) =
      tensorHsInclusion (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast h)
        (parameterSecondDerivativeHs g m u) :=
  DFunLike.congr_fun (parameterSecondDerivativeHs_comp_tensorHsInclusion g h) u

theorem parameterSecondDerivativeHsPi_comp_tensorHsInclusion
    {ι : Type*} (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n m : ℕ} (h : n ≤ m) :
    (parameterSecondDerivativeHsPi (ι := ι) g n).comp
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (show (n : ℝ) + 2 ≤ (m : ℝ) + 2 by exact_mod_cast Nat.add_le_add_right h 2))) =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast h))).comp
            (parameterSecondDerivativeHsPi g m) := by
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro i
  exact parameterSecondDerivativeHs_tensorHsInclusion g h (u i)

end AddCircle
