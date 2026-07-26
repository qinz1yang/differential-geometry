import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.ParametricScalarSmulJet
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.ParametricAppHsTime
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs

/-!
# Smooth tensor paths in the spectral Sobolev scale

The completed tensor-action API already contains the required time
regularity: regard a covariant tensor as a `(0,c)` operator and apply it to the
constant rank-zero unit section.  This file exports that argument for `(0,2)`
tensors on an open time set.
-/

noncomputable section

open Bundle Manifold Set Filter MeasureTheory Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem rankZero_one (x : M) (A : Tensor0SSpace 0 I x) :
    tensor0SSpace_evalScalar x A •
        Tensor0SField.one0 (𝕜 := ℝ) (E := E) (H := H)
          (I := I) (M := M) ∞ x = A := by
  apply (tensor0SSpace_continuousLinearEquiv 0 x).injective
  apply ContinuousMultilinearMap.ext
  intro v
  change Tensor0SSpace.toModel
      (tensor0SSpace_evalScalar x A •
        Tensor0SField.one0 (𝕜 := ℝ) (E := E) (H := H)
          (I := I) (M := M) ∞ x) v = Tensor0SSpace.toModel A v
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    Tensor0SField.one0_apply, smul_eq_mul, mul_one,
    Tensor0SSpace.evalScalar_apply]
  exact congrArg (Tensor0SSpace.toModel A) (Subsingleton.elim Fin.elim0 v)

private noncomputable def oneCc (g : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 0 0 :=
  scalarCc (I := I) (M := M) g
    ⟨(fun _ : M => (1 : ℝ)), contMDiff_const⟩

private theorem oneCc_apply (g : SmoothRiemannianMetric I M)
    (x : M) (A : Tensor0SSpace 0 I x) :
    (oneCc (I := I) (M := M) g).toSection x A = A := by
  simp only [oneCc, scalarCc, tensorRSField_smulByFun_apply]
  rw [ContinuousLinearMap.smul_apply, one_smul,
    Tensor0SField.toRS0_apply, rankZero_one (I := I) (M := M)]

private theorem appCc_one (g : SmoothRiemannianMetric I M) (c : ℕ)
    (Phi : SmoothCcTensor g 0 c) :
    appCc (I := I) (M := M) g 0 c Phi (oneCc (I := I) (M := M) g) = Phi := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCc_toSection]
  apply ContinuousLinearMap.ext
  intro A
  rw [ContinuousLinearMap.comp_apply, oneCc_apply (I := I) (M := M)]

/-- The generic covariant smooth embedding and the Ricci--DeTurck `(0,2)`
embedding are the same spectral element. -/
theorem ccHs_eq_smoothHs (g : SmoothRiemannianMetric I M) (sigma : ℝ)
    (Phi : SmoothCcTensor g 0 2) :
    ccTensorToHs (I := I) (M := M) g 2 sigma Phi =
      smoothCcToTensorHs (I := I) (M := M) g sigma Phi := by
  refine tensorHs.ext ?_
  funext i
  rfl

/-- A jointly smooth compactly supported `(0,2)`-tensor family is a smooth
path in every integer spectral Sobolev space. -/
theorem smoothHs_path_cd
    (g : SmoothRiemannianMetric I M) (n : ℕ)
    (Phi : ℝ → SmoothCcTensor g 0 2) {S : Set ℝ} (hS : IsOpen S)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun x : M => TensorRSSpace 0 2 I x) p.1
        ((Phi p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContDiffOn ℝ ∞
      (fun t => smoothCcToTensorHs (I := I) (M := M) g (n : ℝ) (Phi t)) S := by
  let U : tensorHs (I := I) (M := M) g 0 0 (n : ℝ) :=
    ccTensorToHs (I := I) (M := M) g 0 (n : ℝ)
      (oneCc (I := I) (M := M) g)
  have h := appHs_path_cd (I := I) (M := M) g 0 2 n Phi hS hPhi U
  have hpath :
      (fun t => appHs g 0 2 n (Phi t) U) =
        fun t => smoothCcToTensorHs (I := I) (M := M) g (n : ℝ) (Phi t) := by
    funext t
    rw [appHs_core, appCc_one (I := I) (M := M), ccHs_eq_smoothHs]
  rwa [hpath] at h

/-- A jointly smooth `(0,2)`-tensor family has one jointly smooth tensor time
derivative whose spectral embedding is the strong derivative at every integer
Sobolev order. -/
theorem smoothHs_deriv
    (g : SmoothRiemannianMetric I M)
    (Phi : ℝ → SmoothCcTensor g 0 2) {S : Set ℝ} (hS : IsOpen S)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun x : M => TensorRSSpace 0 2 I x) p.1
        ((Phi p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ∃ dPhi : ℝ → SmoothCcTensor g 0 2,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
          (E := fun x : M => TensorRSSpace 0 2 I x) p.1
          ((dPhi p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ S) ∧
      (∀ t ∈ S, ∀ x : M, ∀ A : Tensor0SSpace 0 I x,
        ∀ slots : Fin 2 → E,
          HasDerivAt
            (fun tau => Tensor0SSpace.toModel (((Phi tau).toSection x) A) slots)
            (Tensor0SSpace.toModel (((dPhi t).toSection x) A) slots) t) ∧
      ∀ n : ℕ, ∀ t ∈ S,
        HasDerivAt
          (fun tau => smoothCcToTensorHs (I := I) (M := M) g (n : ℝ) (Phi tau))
          (smoothCcToTensorHs (I := I) (M := M) g (n : ℝ) (dPhi t)) t := by
  obtain ⟨dPhi, hdPhi, hcomp, hderiv⟩ :=
    exists_appHsFull (I := I) (M := M) g 0 2 Phi hS hPhi
  refine ⟨dPhi, hdPhi, hcomp, ?_⟩
  intro n t ht
  let U : tensorHs (I := I) (M := M) g 0 0 (n : ℝ) :=
    ccTensorToHs (I := I) (M := M) g 0 (n : ℝ)
      (oneCc (I := I) (M := M) g)
  have happ := hderiv n t ht U
  have hpath :
      (fun tau => appHs g 0 2 n (Phi tau) U) =
        fun tau => smoothCcToTensorHs (I := I) (M := M) g (n : ℝ) (Phi tau) := by
    funext tau
    rw [appHs_core, appCc_one (I := I) (M := M), ccHs_eq_smoothHs]
  have hdval : appHs g 0 2 n (dPhi t) U =
      smoothCcToTensorHs (I := I) (M := M) g (n : ℝ) (dPhi t) := by
    rw [appHs_core, appCc_one (I := I) (M := M), ccHs_eq_smoothHs]
  rwa [hpath, hdval] at happ

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
