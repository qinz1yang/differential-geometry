import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleDerivative
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.ScalarContinuous
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothInclusion
import DifferentialGeometry.Analysis.Calculus.Derivative.UniformLimit
import Mathlib.Topology.Sequences

open scoped Manifold ContDiff Topology

namespace AddCircle

open Filter
open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

theorem hasDerivAt_scalarHsToContinuous
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) (x : ℝ) :
    HasDerivAt
      (fun t : ℝ => scalarHsToContinuous g
        (tensorHsInclusion (by norm_num :
          ((Module.finrank ℝ ℝ / 2 + 1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) u)
        (t : AddCircle (1 : ℝ)))
      (scalarHsToContinuous g
        (tensorHsInclusion (by norm_num :
          ((Module.finrank ℝ ℝ / 2 + 1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))
          (parameterDerivativeHs g 1 u)) (x : AddCircle (1 : ℝ))) x := by
  let L := (scalarHsToContinuous g).comp (tensorHsInclusion (by norm_num :
    ((Module.finrank ℝ ℝ / 2 + 1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1))
  let D := ((scalarHsToContinuous g).comp (tensorHsInclusion (by norm_num :
    ((Module.finrank ℝ ℝ / 2 + 1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))).comp (parameterDerivativeHs g 1)
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.mp
    (ccToHsLin_dense (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) u)
  choose S hS using hv
  have hcore (i : ℕ) : v i = ccTensorToHs g 0 (((1 : ℕ) : ℝ) + 1) (S i) := (hS i).symm
  apply ContinuousMap.hasDerivAt_comp_of_tendsto
    (f := fun i => L (v i)) (g := fun i => D (v i))
    ((L.continuous.tendsto u).comp hvlim) ((D.continuous.tendsto u).comp hvlim)
    (Filter.Eventually.of_forall ?_) x
  intro i t
  have hval (z : AddCircle (1 : ℝ)) :
      L (v i) z = TensorRSField.scalar0 (S i).toSection z := by
    simp only [L, ContinuousLinearMap.comp_apply]
    rw [hcore, tensorHsInclusion_ccTensorToHs, scalarHsToContinuous_apply_ccTensorToHs]
  have hder (z : AddCircle (1 : ℝ)) :
      D (v i) z = TensorRSField.scalar0 (parameterDerivativeCcTensor g (S i)).toSection z := by
    simp only [D, ContinuousLinearMap.comp_apply]
    rw [hcore, parameterDerivativeHs_apply_ccTensorToHs,
      tensorHsInclusion_ccTensorToHs, scalarHsToContinuous_apply_ccTensorToHs]
  have hsmooth : ContDiff ℝ ∞ (fun r : ℝ =>
      TensorRSField.scalar0 (S i).toSection (r : AddCircle (1 : ℝ))) := by
    exact contMDiff_iff_contDiff.mp
      ((TensorRSField.scalar0_smooth (S i).toSection).comp contMDiff_coe)
  have h := (hsmooth.differentiable (by decide) t).hasDerivAt
  simpa only [hval, hder, scalar0_parameterDerivativeCcTensor_coe] using h

end AddCircle

open scoped Manifold ContDiff Topology

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem scalarH1ToContinuous_tensorHsInclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {σ : ℝ} (hσ : 1 ≤ σ) (u : TensorHs g 0 0 σ) :
    scalarH1ToContinuous g (tensorHsInclusion hσ u) =
      scalarHsToContinuous g
        (tensorHsInclusion (by simpa using hσ :
          ((Module.finrank ℝ ℝ / 2 + 1 : ℕ) : ℝ) ≤ σ) u) := by
  unfold scalarH1ToContinuous
  rw [ContinuousLinearMap.comp_apply]
  congr 1
  have hcongr {a b : ℝ} (h : a = b) (v : TensorHs g 0 0 a) :
      (tensorHsCongrL g 0 0 h v).coeff = v.coeff := by
    cases h
    rfl
  apply TensorHs.ext
  rw [hcongr]
  rfl

theorem hasDerivAt_scalarH1ToContinuous
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) (x : ℝ) :
    HasDerivAt
      (fun t : ℝ => scalarH1ToContinuous g
        (tensorHsInclusion (by norm_num : 1 ≤ ((1 : ℕ) : ℝ) + 1) u)
          (t : AddCircle (1 : ℝ)))
      (scalarH1ToContinuous g
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
          (parameterDerivativeHs g 1 u)) (x : AddCircle (1 : ℝ))) x := by
  rw [scalarH1ToContinuous_tensorHsInclusion]
  rw [scalarH1ToContinuous_tensorHsInclusion]
  exact hasDerivAt_scalarHsToContinuous g u x

theorem hasDerivAt_scalarH1PiToContinuous {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) (x : ℝ) :
    HasDerivAt
      (fun t : ℝ => scalarH1PiToContinuous g
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)) u)
          (t : AddCircle (1 : ℝ)))
      (scalarH1PiToContinuous g
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
          (parameterDerivativeHsPi g 1 u)) (x : AddCircle (1 : ℝ))) x := by
  apply hasDerivAt_pi.mpr
  intro i
  exact hasDerivAt_scalarH1ToContinuous g (u i) x


private theorem deriv_scalarH1ToContinuous_three
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u : TensorHs g 0 0 (((2 : ℕ) : ℝ) + 1)) :
    deriv (fun t : ℝ => scalarH1ToContinuous g
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((2 : ℕ) : ℝ) + 1) u)
        (t : AddCircle (1 : ℝ))) =
      fun t : ℝ => scalarH1ToContinuous g
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((2 : ℕ) : ℝ))
          (parameterDerivativeHs g 2 u)) (t : AddCircle (1 : ℝ)) := by
  funext x
  have h := hasDerivAt_scalarH1ToContinuous g
    (tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ) + 1) u) x
  have hder := parameterDerivativeHs_tensorHsInclusion g (n := 1) (m := 2)
    (by norm_num : 1 ≤ 2) u
  rw [hder, ← tensorHsInclusion_trans_apply] at h
  simpa only [← tensorHsInclusion_trans_apply] using h.deriv

theorem hasDerivAt_deriv_scalarH1ToContinuous
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u : TensorHs g 0 0 (((2 : ℕ) : ℝ) + 1)) (x : ℝ) :
    HasDerivAt
      (deriv (fun t : ℝ => scalarH1ToContinuous g
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((2 : ℕ) : ℝ) + 1) u)
        (t : AddCircle (1 : ℝ))))
      (scalarH1ToContinuous g
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
          (parameterDerivativeHs g 1
            (tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))
              (parameterDerivativeHs g 2 u))))
        (x : AddCircle (1 : ℝ))) x := by
  rw [deriv_scalarH1ToContinuous_three]
  have h := hasDerivAt_scalarH1ToContinuous g
    (tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))
      (parameterDerivativeHs g 2 u)) x
  simpa only [← tensorHsInclusion_trans_apply] using h

theorem contDiff_two_scalarH1ToContinuous
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u : TensorHs g 0 0 (((2 : ℕ) : ℝ) + 1)) :
    ContDiff ℝ 2 (fun t : ℝ => scalarH1ToContinuous g
      (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((2 : ℕ) : ℝ) + 1) u)
      (t : AddCircle (1 : ℝ))) := by
  rw [show (2 : ℕ∞ω) = (1 : ℕ∞ω) + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨?_, ?_, contDiff_one_iff_deriv.mpr ⟨?_, ?_⟩⟩
  · intro x
    have h := hasDerivAt_scalarH1ToContinuous g
      (tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ) + 1) u) x
    simpa only [← tensorHsInclusion_trans_apply] using h.differentiableAt
  · intro h
    norm_num at h
  · intro x
    exact (hasDerivAt_deriv_scalarH1ToContinuous g u x).differentiableAt
  · have heq := funext (fun x => (hasDerivAt_deriv_scalarH1ToContinuous g u x).deriv)
    rw [heq]
    exact (scalarH1ToContinuous g
      (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
        (parameterDerivativeHs g 1
          (tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ))
            (parameterDerivativeHs g 2 u))))).continuous.comp (AddCircle.continuous_mk' 1)

theorem contDiff_two_scalarH1PiToContinuous {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 1))) :
    ContDiff ℝ 2 (fun t : ℝ => scalarH1PiToContinuous g
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ ((2 : ℕ) : ℝ) + 1)) u)
      (t : AddCircle (1 : ℝ))) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_two_scalarH1ToContinuous g (u i)

theorem hasDerivAt_deriv_scalarH1PiToContinuous {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 1))) (x : ℝ) :
    HasDerivAt
      (deriv (fun t : ℝ => scalarH1PiToContinuous g
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by norm_num : (1 : ℝ) ≤ ((2 : ℕ) : ℝ) + 1)) u)
        (t : AddCircle (1 : ℝ))))
      (scalarH1PiToContinuous g
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
          (parameterDerivativeHsPi g 1
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
              tensorHsInclusion (g := g) (r := 0) (s := 0)
                (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ)))
              (parameterDerivativeHsPi g 2 u))))
        (x : AddCircle (1 : ℝ))) x := by
  have heq : deriv (fun t : ℝ => scalarH1PiToContinuous g
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ ((2 : ℕ) : ℝ) + 1)) u)
      (t : AddCircle (1 : ℝ))) = fun t i => deriv (fun y : ℝ =>
        scalarH1ToContinuous g
          (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((2 : ℕ) : ℝ) + 1) (u i))
            (y : AddCircle (1 : ℝ))) t := by
    funext t
    apply deriv_pi
    intro i
    exact ((contDiff_two_scalarH1ToContinuous g (u i)).differentiable (by norm_num)) t
  rw [heq]
  apply hasDerivAt_pi.mpr
  intro i
  exact hasDerivAt_deriv_scalarH1ToContinuous g (u i) x

end AddCircle
