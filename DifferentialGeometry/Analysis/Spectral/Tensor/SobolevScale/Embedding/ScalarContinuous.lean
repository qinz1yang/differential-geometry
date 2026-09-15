import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.Embedding.H2Pointwise
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothCompactSupportDense
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Lp.PiLp
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Basic.ExponentCongruence

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]

private noncomputable def scalarCcContinuousLinear
    (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 0 0 →ₗ[ℝ] C(M, ℝ) where
  toFun T := ⟨TensorRSField.scalar0 T.toSection, (TensorRSField.scalar0_smooth T.toSection).continuous⟩
  map_add' T S := by
    ext x
    change TensorRSField.scalar0 (T + S).toSection x = _
    rw [SmoothCcTensor.toSection_add, TensorRSField.scalar0_add]
    rfl
  map_smul' c T := by
    ext x
    change TensorRSField.scalar0 (c • T).toSection x = _
    rw [SmoothCcTensor.toSection_smul, TensorRSField.scalar0_smul]
    rfl

noncomputable def scalarHsToContinuous
    (g : SmoothRiemannianMetric I M) :
    TensorHs (I := I) (M := M) g 0 0
      ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ) →L[ℝ] C(M, ℝ) :=
  (scalarCcContinuousLinear (I := I) (M := M) g).extendOfNorm
    (ccToHsLin (I := I) (M := M) g 0 ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ))

theorem scalarHsToContinuous_apply_ccTensorToHs
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 0) (x : M) :
    scalarHsToContinuous (I := I) (M := M) g
        (ccTensorToHs (I := I) (M := M) g 0
          ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ) T) x =
      TensorRSField.scalar0 T.toSection x := by
  obtain ⟨C, hC, hbound⟩ := scalar0_abs_le_hs (I := I) (M := M) g
  have heq := LinearMap.extendOfNorm_eq
    (f := scalarCcContinuousLinear (I := I) (M := M) g)
    (ccToHsLin_dense (I := I) (M := M) g 0 (by positivity :
      (0 : ℝ) ≤ ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ)))
    (show ∃ C : ℝ, ∀ S : SmoothCcTensor g 0 0,
      ‖scalarCcContinuousLinear (I := I) (M := M) g S‖ ≤
        C * ‖ccToHsLin (I := I) (M := M) g 0
          ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ) S‖ from ?_) T
  · exact congrArg (fun f : C(M, ℝ) => f x) heq
  refine ⟨C, fun S => ?_⟩
  apply (ContinuousMap.norm_le (f := scalarCcContinuousLinear (I := I) (M := M) g S) (mul_nonneg hC (norm_nonneg _))).2
  intro y
  exact hbound S y

end DifferentialGeometry.Analysis.Spectral

noncomputable section
namespace DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold 𝓘(ℝ, ℝ) ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M]

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem tensorHsCongrL_core
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M) {a b : ℝ} (h : a = b)
    (T : SmoothCcTensor g 0 0) :
    tensorHsCongrL g 0 0 h (ccTensorToHs g 0 a T) = ccTensorToHs g 0 b T := by
  cases h
  rfl

def scalarH1ToContinuous
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M) : TensorHs g 0 0 1 →L[ℝ] C(M, ℝ) :=
  (scalarHsToContinuous g).comp (tensorHsCongrL g 0 0 (by norm_num))

@[simp] theorem scalarH1ToContinuous_apply_ccTensorToHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M) (T : SmoothCcTensor g 0 0) (x : M) :
    scalarH1ToContinuous g (ccTensorToHs g 0 1 T) x =
      TensorRSField.scalar0 T.toSection x := by
  simp only [scalarH1ToContinuous, ContinuousLinearMap.comp_apply, tensorHsCongrL_core,
    scalarHsToContinuous_apply_ccTensorToHs]

end DifferentialGeometry.Analysis.Spectral

noncomputable section
open Manifold Set
open scoped BigOperators NNReal ENNReal
namespace DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {ι : Type*} [Fintype ι]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold 𝓘(ℝ, ℝ) ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private local instance hsNorm (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M) :
    NormedAddCommGroup (TensorHs g 0 0 1) := TensorHs.instNormedAddCommGroup
private local instance hsSpace (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M) :
    NormedSpace ℝ (TensorHs g 0 0 1) :=
  (TensorHs.instInnerProductSpace (g := g) (r := 0) (s := 0) (σ := 1)).toNormedSpace
private local instance hsComplete (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M) :
    CompleteSpace (TensorHs g 0 0 1) := TensorHs.instCompleteSpace

def scalarH1PiToContinuous
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 1) →L[ℝ] C(M, ι → ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨fun x i => scalarH1ToContinuous g (u i) x,
        continuous_pi fun i => (scalarH1ToContinuous g (u i)).continuous⟩
      map_add' := fun u v => by
        ext x i
        exact congrArg (fun f : C(M, ℝ) => f x) ((scalarH1ToContinuous g).map_add (u i) (v i))
      map_smul' := fun c u => by
        ext x i
        exact congrArg (fun f : C(M, ℝ) => f x) ((scalarH1ToContinuous g).map_smul c (u i)) }
    ‖scalarH1ToContinuous g‖ (fun u => by
      apply (ContinuousMap.norm_le _ (by positivity)).2
      intro x
      apply (pi_norm_le_iff_of_nonneg (by positivity)).2
      intro i
      exact ((ContinuousMap.norm_coe_le_norm _ x).trans
        ((scalarH1ToContinuous g).le_opNorm (u i))).trans
        (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le u i) (norm_nonneg _)))

@[simp] theorem scalarH1PiToContinuous_apply
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M)
    (u : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) (x : M) (i : ι) :
    scalarH1PiToContinuous g u x i = scalarH1ToContinuous g (u i) x := rfl

@[simp] theorem scalarH1PiToContinuous_apply_ccTensorToHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M) (S : ι → SmoothCcTensor g 0 0) (x : M) :
    scalarH1PiToContinuous g (WithLp.toLp 2 (fun i => ccTensorToHs g 0 1 (S i))) x =
      fun i => TensorRSField.scalar0 (S i).toSection x := by
  funext i
  exact scalarH1ToContinuous_apply_ccTensorToHs g (S i) x

end DifferentialGeometry.Analysis.Spectral
