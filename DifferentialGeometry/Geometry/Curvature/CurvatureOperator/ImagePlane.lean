import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ImageLine
import DifferentialGeometry.Geometry.Metric.SmoothSubbundle

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

theorem exists_smooth_parallel_curvatureOperatorImagePlane
    [I.Boundaryless]
    (hE : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) (∞ : WithTop ℕ∞) 4)
    (hA : ∀ x, A x ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hrank : ∀ x, Module.finrank ℝ
      (curvatureOperatorImageAt (I := I) g x ⟨A x, hA x⟩) = 1)
    (hkernel : IsParallelContinuousAlternatingSubmoduleFamily g
      (fun x => curvatureOperatorKernelAt (I := I) g x ⟨A x, hA x⟩)) :
    ∃ P : ContMDiffVectorSubbundle
        (I := I) (F := E) (V := TangentSpace I) (n := (∞ : WithTop ℕ∞)),
      P.rank = 2 ∧
      (∀ x, P.fiber x = (tangentMetricData (I := I) g x).metric.orthogonal
        (curvatureOperatorImageAnnihilatorAt (I := I) g x ⟨A x, hA x⟩)) ∧
      IsParallelSubmoduleFamily g P.fiber := by
  obtain ⟨L, hLrank, hLfiber, hLparallel⟩ :=
    exists_smooth_parallel_curvatureOperatorImageLine hE g A hA hrank hkernel
  obtain ⟨P, hPrank, hPmem⟩ := L.exists_orthogonal g
  have hPfiber (x : M) : P.fiber x =
      (tangentMetricData (I := I) g x).metric.orthogonal (L.fiber x) := by
    ext v
    rw [hPmem, MetricFiberData.mem_orthogonal]
    rfl
  refine ⟨P, ?_, ?_, ?_⟩
  · simpa only [hE, hLrank] using hPrank
  · intro x
    rw [hPfiber, hLfiber]
  · have heq : P.fiber = fun x =>
        (tangentMetricData (I := I) g x).metric.orthogonal (L.fiber x) :=
      funext hPfiber
    rw [heq]
    exact hLparallel.orthogonal

end DifferentialGeometry.Geometry.Curvature
