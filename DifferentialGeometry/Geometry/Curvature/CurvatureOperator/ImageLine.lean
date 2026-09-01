import DifferentialGeometry.Geometry.Connection.ParallelTransport.Kernel
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.EndomorphismNaturality
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Smoothness

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

def curvatureOperatorImageAnnihilatorAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    Submodule Real (TangentSpace I x) :=
  ContinuousAlternatingMap.contractionAnnihilator
    (curvatureOperatorImageAt (I := I) g x A)

omit [CompleteSpace E] [T2Space M] in
theorem curvatureOperatorImageAnnihilatorAt_finrank
    (hE : Module.finrank Real E = 3)
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hrank : Module.finrank Real
      (curvatureOperatorImageAt (I := I) g x A) = 1) :
    Module.finrank Real
      (curvatureOperatorImageAnnihilatorAt (I := I) g x A) = 1 := by
  apply ContinuousAlternatingMap.finrank_contractionAnnihilator_eq_one
  · exact hE
  · exact hrank

omit [CompleteSpace E] [T2Space M] in
theorem curvatureOperatorImage_isParallel_of_kernel_isParallel
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) (∞ : WithTop ℕ∞) 4)
    (hA : ∀ x, A x ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hkernel : IsParallelContinuousAlternatingSubmoduleFamily g
      (fun x => curvatureOperatorKernelAt (I := I) g x ⟨A x, hA x⟩)) :
    IsParallelContinuousAlternatingSubmoduleFamily g
      (fun x => curvatureOperatorImageAt (I := I) g x ⟨A x, hA x⟩) := by
  dsimp only [IsParallelContinuousAlternatingSubmoduleFamily]
  intro gamma hgamma a b hab
  let e := Riemannian.Variation.parallelTransportLinearEquivBetween
    (I := I) g gamma hgamma hab
  let F := e.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
    (ι := Fin 2) (F := Real)
  let basisA := Module.finBasis Real (TangentSpace I (gamma a))
  let _ : FiniteDimensional Real
      (TangentSpace I (gamma a) [⋀^Fin 2]→L[Real] Real) :=
    (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2) basisA)
      |>.finiteDimensional_of_finite
  let basisB := Module.finBasis Real (TangentSpace I (gamma b))
  let _ : FiniteDimensional Real
      (TangentSpace I (gamma b) [⋀^Fin 2]→L[Real] Real) :=
    (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2) basisB)
      |>.finiteDimensional_of_finite
  change Submodule.map F.toLinearMap
      (curvatureOperatorImageAt (I := I) g (gamma a)
        ⟨A (gamma a), hA (gamma a)⟩) =
    curvatureOperatorImageAt (I := I) g (gamma b)
      ⟨A (gamma b), hA (gamma b)⟩
  rw [curvatureOperatorImageAt_eq_orthogonal_kernel,
    curvatureOperatorImageAt_eq_orthogonal_kernel]
  calc
    Submodule.map F.toLinearMap
        ((twoFormMetricData (I := I) g (gamma a)).orthogonal
          (curvatureOperatorKernelAt (I := I) g (gamma a)
            ⟨A (gamma a), hA (gamma a)⟩)) =
      (twoFormMetricData (I := I) g (gamma b)).orthogonal
        (Submodule.map F.toLinearMap
          (curvatureOperatorKernelAt (I := I) g (gamma a)
            ⟨A (gamma a), hA (gamma a)⟩)) := by
      apply MetricFiberData.map_orthogonal_of_inner_eq
      intro u v
      apply twoFormMetricData_inner_congrLeft
      intro X Y
      exact Riemannian.Variation.parallelTransportLinearEquivBetween_inner
        (I := I) g gamma hgamma hab X Y
    _ = (twoFormMetricData (I := I) g (gamma b)).orthogonal
        (curvatureOperatorKernelAt (I := I) g (gamma b)
          ⟨A (gamma b), hA (gamma b)⟩) := by
      rw [hkernel gamma hgamma hab]

omit [CompleteSpace E] in
theorem exists_smooth_parallel_curvatureOperatorImageLine
    [I.Boundaryless]
    (hE : Module.finrank Real E = 3)
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) (∞ : WithTop ℕ∞) 4)
    (hA : ∀ x, A x ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hrank : ∀ x, Module.finrank Real
      (curvatureOperatorImageAt (I := I) g x ⟨A x, hA x⟩) = 1)
    (hkernel : IsParallelContinuousAlternatingSubmoduleFamily g
      (fun x => curvatureOperatorKernelAt (I := I) g x ⟨A x, hA x⟩)) :
    ∃ S : ContMDiffVectorSubbundle
        (I := I) (F := E) (V := TangentSpace I) (n := (∞ : WithTop ℕ∞)),
      S.rank = 1 ∧
      (∀ x, S.fiber x =
        curvatureOperatorImageAnnihilatorAt (I := I) g x ⟨A x, hA x⟩) ∧
      IsParallelSubmoduleFamily g S.fiber := by
  let K := curvatureOperatorImageSubbundle (I := I) g A hA 1 hrank
  apply exists_smooth_parallel_contractionAnnihilator hE g K rfl
  intro gamma hgamma a b hab
  change Submodule.map
      (((Riemannian.Variation.parallelTransportLinearEquivBetween
        (I := I) g gamma hgamma hab).toContinuousLinearEquiv
          |>.continuousAlternatingMapCongrLeft (ι := Fin 2)).toLinearMap)
      (curvatureOperatorImageAt (I := I) g (gamma a)
        ⟨A (gamma a), hA (gamma a)⟩) =
    curvatureOperatorImageAt (I := I) g (gamma b)
      ⟨A (gamma b), hA (gamma b)⟩
  exact curvatureOperatorImage_isParallel_of_kernel_isParallel
    (I := I) g A hA hkernel gamma hgamma hab

end DifferentialGeometry.Geometry.Curvature
