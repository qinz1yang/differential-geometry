import DifferentialGeometry.Geometry.Operator.Laplacian.AddCircle
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleDerivative
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Scalar.RankZeroRealization
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.Parametric.ScalarSmulJet

section

open scoped Manifold ContDiff

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem scalar0_rawTensorConnLapSmooth_flatMetric
    (S : SmoothCcTensor flatMetric 0 0) (x : ℝ) :
    TensorRSField.scalar0 (rawTensorConnLapSmooth flatMetric 0 0 S).toSection
        (x : AddCircle (1 : ℝ)) =
      TensorRSField.scalar0
        (parameterDerivativeCcTensor flatMetric
          (parameterDerivativeCcTensor flatMetric S)).toSection
        (x : AddCircle (1 : ℝ)) := by
  rw [rawLap_cc_scalar, scalar0_parameterDerivativeCcTensor_twice_coe]
  rw [← laplacian_levi_eq flatMetric (TensorRSField.scalar0_smooth S.toSection)]
  exact laplacian_flatMetric_coe
    ((TensorRSField.scalar0_smooth S.toSection).of_le (by decide : (2 : ℕ∞ω) ≤ ∞)) x

theorem rawTensorConnLapSmooth_flatMetric
    (S : SmoothCcTensor flatMetric 0 0) :
    rawTensorConnLapSmooth flatMetric 0 0 S =
      parameterDerivativeCcTensor flatMetric (parameterDerivativeCcTensor flatMetric S) := by
  apply SmoothCcTensor.ext
  have h : TensorRSField.scalar0 (rawTensorConnLapSmooth flatMetric 0 0 S).toSection =
      TensorRSField.scalar0
        (parameterDerivativeCcTensor flatMetric
          (parameterDerivativeCcTensor flatMetric S)).toSection := by
    funext z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact scalar0_rawTensorConnLapSmooth_flatMetric S x
  rw [← TensorRSField.lift_scalar0 (rawTensorConnLapSmooth flatMetric 0 0 S).toSection,
    ← TensorRSField.lift_scalar0
      (parameterDerivativeCcTensor flatMetric
        (parameterDerivativeCcTensor flatMetric S)).toSection]
  congr 2

end AddCircle

end

section

noncomputable section
open scoped Manifold ContDiff

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem parameterSecondDerivativeHsPi_eq_of_core
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (hcore : ∀ S : SmoothCcTensor g 0 0,
      parameterDerivativeCcTensor g (parameterDerivativeCcTensor g S) =
        rawTensorConnLapSmooth g 0 0 S) :
    parameterSecondDerivativeHsPi (ι := ι) g n =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
          (g := g) (r := 0) (s := 0) (n : ℝ)) := by
  let L := (parameterDerivativeHs g n).comp
    ((tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) by norm_num)).comp
      ((parameterDerivativeHs g (n + 1)).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show ((n + 1 : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 2 by push_cast; linarith))))
  let R := tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
    (g := g) (r := 0) (s := 0) (n : ℝ)
  have heq : (L : _ → _) = R := (ccToHsLin_dense g 0 (by positivity :
      (0 : ℝ) ≤ (n : ℝ) + 2)).equalizer L.continuous R.continuous (by
    funext S
    simp only [Function.comp_apply, L, R, ContinuousLinearMap.comp_apply, ccToHsLin_apply]
    rw [tensorHsInclusion_ccTensorToHs, parameterDerivativeHs_apply_ccTensorToHs,
      tensorHsInclusion_ccTensorToHs, parameterDerivativeHs_apply_ccTensorToHs,
      hcore, tensorScaleLaplacian_apply_ccTensorToHs])
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro i
  exact congrFun heq (u i)

theorem parameterSecondDerivativeHsPi_flatMetric {ι : Type*} (n : ℕ) :
    parameterSecondDerivativeHsPi (ι := ι) flatMetric n =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
          (g := flatMetric) (r := 0) (s := 0) (n : ℝ)) :=
  parameterSecondDerivativeHsPi_eq_of_core flatMetric n
    (fun S => (rawTensorConnLapSmooth_flatMetric S).symm)

end AddCircle

end

end

open scoped Manifold ContDiff

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

theorem rawTensorConnLapSmooth_eq_principal_add_drift
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (S : SmoothCcTensor g 0 0) :
    rawTensorConnLapSmooth g 0 0 S =
      scalarSmul g 0 0 (laplacianPrincipalCoefficient g)
        (parameterDerivativeCcTensor g (parameterDerivativeCcTensor g S)) +
      scalarSmul g 0 0 (laplacianDriftCoefficient g)
        (parameterDerivativeCcTensor g S) := by
  apply SmoothCcTensor.ext
  have h : TensorRSField.scalar0 (rawTensorConnLapSmooth g 0 0 S).toSection =
      TensorRSField.scalar0
        (scalarSmul g 0 0 (laplacianPrincipalCoefficient g)
          (parameterDerivativeCcTensor g (parameterDerivativeCcTensor g S)) +
        scalarSmul g 0 0 (laplacianDriftCoefficient g)
          (parameterDerivativeCcTensor g S)).toSection := by
    funext z
    rw [SmoothCcTensor.toSection_add, TensorRSField.scalar0_add, Pi.add_apply,
      scalar0_smul_cc, scalar0_smul_cc]
    rw [rawLap_cc_scalar,
      ← laplacian_levi_eq g (TensorRSField.scalar0_smooth S.toSection)]
    rw [laplacian_eq_principal_add_drift g
      ((TensorRSField.scalar0_smooth S.toSection).contMDiffAt.of_le (by decide : (2 : ℕ∞ω) ≤ ∞))]
    rw [scalar0_parameterDerivativeCcTensor, scalar0_parameterDerivativeCcTensor]
    have hD : TensorRSField.scalar0 (parameterDerivativeCcTensor g S).toSection =
        fun y => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (TensorRSField.scalar0 S.toSection) y
          (parameterTangent y) := funext (scalar0_parameterDerivativeCcTensor g S)
    rw [hD]
    rfl
  rw [← TensorRSField.lift_scalar0 (rawTensorConnLapSmooth g 0 0 S).toSection,
    ← TensorRSField.lift_scalar0
      (scalarSmul g 0 0 (laplacianPrincipalCoefficient g)
        (parameterDerivativeCcTensor g (parameterDerivativeCcTensor g S)) +
      scalarSmul g 0 0 (laplacianDriftCoefficient g)
        (parameterDerivativeCcTensor g S)).toSection]
  congr 2

end AddCircle

noncomputable section
open scoped Manifold ContDiff

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem tensorScaleLaplacian_eq_of_scalar_core
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (a b : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯)
    (hcore : ∀ S : SmoothCcTensor g 0 0,
      rawTensorConnLapSmooth g 0 0 S =
        scalarSmul g 0 0 a (parameterDerivativeCcTensor g (parameterDerivativeCcTensor g S)) +
          scalarSmul g 0 0 b (parameterDerivativeCcTensor g S)) :
    tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ) =
      (appHs g 0 0 n (scalarCc g a)).comp
        (parameterSecondDerivativeHs g n) +
      (appHs g 0 0 n (scalarCc g b)).comp
        ((parameterDerivativeHs g n).comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith))) := by
  let L := tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ)
  let R := (appHs g 0 0 n (scalarCc g a)).comp (parameterSecondDerivativeHs g n) +
    (appHs g 0 0 n (scalarCc g b)).comp
      ((parameterDerivativeHs g n).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith)))
  have heq : (L : _ → _) = R :=
    (ccToHsLin_dense g 0 (by positivity : (0 : ℝ) ≤ (n : ℝ) + 2)).equalizer
      L.continuous R.continuous (by
        funext S
        simp only [Function.comp_apply, L, R, add_apply,
          ContinuousLinearMap.comp_apply, ccToHsLin_apply]
        rw [tensorScaleLaplacian_apply_ccTensorToHs,
          parameterSecondDerivativeHs_apply_ccTensorToHs,
          tensorHsInclusion_ccTensorToHs, parameterDerivativeHs_apply_ccTensorToHs,
          appHs_apply_ccTensorToHs, appHs_apply_ccTensorToHs,
          app_scalarCc, app_scalarCc, hcore, ccTensorToHs_add])
  exact ContinuousLinearMap.coeFn_injective heq

private local instance piLp_continuousAdd {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    ContinuousAdd (PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ))) where
  continuous_add := by
    change Continuous (fun z : PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ)) ×
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ)) =>
        WithLp.toLp 2 (fun i => z.1 i + z.2 i))
    apply (PiLp.continuous_toLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ))).comp
    apply continuous_pi
    intro i
    exact ((PiLp.continuous_apply 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ)) i).comp
      continuous_fst).add
      ((PiLp.continuous_apply 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ)) i).comp continuous_snd)


private theorem piLpMap_tensorScaleLaplacian_eq_of_scalar_core
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (a b : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯)
    (hcore : ∀ S : SmoothCcTensor g 0 0,
      rawTensorConnLapSmooth g 0 0 S =
        scalarSmul g 0 0 a (parameterDerivativeCcTensor g (parameterDerivativeCcTensor g S)) +
          scalarSmul g 0 0 b (parameterDerivativeCcTensor g S)) :
    ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ)) =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => appHs g 0 0 n (scalarCc g a))).comp
        (parameterSecondDerivativeHsPi g n) +
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => appHs g 0 0 n (scalarCc g b))).comp
        ((parameterDerivativeHsPi g n).comp
          (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
            tensorHsInclusion (g := g) (r := 0) (s := 0)
              (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith)))) := by
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro i
  have h := congrArg (fun L => L (u i)) (tensorScaleLaplacian_eq_of_scalar_core g n a b hcore)
  exact h

theorem tensorScaleLaplacian_eq_principal_add_drift
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ) =
      (appHs g 0 0 n (scalarCc g (laplacianPrincipalCoefficient g))).comp
        (parameterSecondDerivativeHs g n) +
      (appHs g 0 0 n (scalarCc g (laplacianDriftCoefficient g))).comp
        ((parameterDerivativeHs g n).comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith))) :=
  tensorScaleLaplacian_eq_of_scalar_core g n _ _
    (rawTensorConnLapSmooth_eq_principal_add_drift g)

theorem piLpMap_tensorScaleLaplacian_eq_principal_add_drift
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ)) =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        appHs g 0 0 n (scalarCc g (laplacianPrincipalCoefficient g)))).comp
        (parameterSecondDerivativeHsPi g n) +
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        appHs g 0 0 n (scalarCc g (laplacianDriftCoefficient g)))).comp
        ((parameterDerivativeHsPi g n).comp
          (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
            tensorHsInclusion (g := g) (r := 0) (s := 0)
              (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith)))) :=
  piLpMap_tensorScaleLaplacian_eq_of_scalar_core g n _ _
    (rawTensorConnLapSmooth_eq_principal_add_drift g)

end AddCircle
