import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleClassicalDerivative

noncomputable section
open scoped Manifold ContDiff

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Integral.L2

variable {ι : Type*}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

def firstJetHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1)) →L[ℝ]
      PiLp 2 (fun _ : ι ⊕ ι => TensorHs g 0 0 (n : ℝ)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ⊕ ι => TensorHs g 0 0 (n : ℝ))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => match j with
      | .inl i =>
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)).comp
              (PiLp.proj 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1)) i)
      | .inr i =>
          (parameterDerivativeHs g n).comp
            (PiLp.proj 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1)) i))

@[simp] theorem firstJetHs_inl
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (u : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1))) (i : ι) :
    firstJetHs g n u (.inl i) =
      tensorHsInclusion (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith) (u i) := rfl

@[simp] theorem firstJetHs_inr
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (u : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1))) (i : ι) :
    firstJetHs g n u (.inr i) = parameterDerivativeHs g n (u i) := rfl

theorem firstJetHs_apply_ccTensorToHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (S : ι → SmoothCcTensor g 0 0) :
    firstJetHs g n (WithLp.toLp 2 (fun i => ccTensorToHs g 0 ((n : ℝ) + 1) (S i))) =
      WithLp.toLp 2 (fun j => ccTensorToHs g 0 (n : ℝ)
        (Sum.elim S (fun i => parameterDerivativeCcTensor g (S i)) j)) := by
  apply PiLp.ext
  intro j
  cases j with
  | inl i =>
    change tensorHsInclusion (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith)
      (ccTensorToHs g 0 ((n : ℝ) + 1) (S i)) = ccTensorToHs g 0 (n : ℝ) (S i)
    rw [tensorHsInclusion_ccTensorToHs]
  | inr i => exact parameterDerivativeHs_apply_ccTensorToHs g n (S i)

theorem firstJetHs_comp_tensorHsInclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {n m : ℕ} (h : n ≤ m) :
    (firstJetHs (ι := ι) g n).comp
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (show (n : ℝ) + 1 ≤ (m : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right h 1))) =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι ⊕ ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast h))).comp
            (firstJetHs g m) := by
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro j
  cases j with
  | inl i =>
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.piLpMap_apply,
      firstJetHs_inl]
    apply TensorHs.ext
    rfl
  | inr i => exact parameterDerivativeHs_tensorHsInclusion g h (u i)

end AddCircle
