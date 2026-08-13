import DifferentialGeometry.Geometry.Curvature.AlgebraicTensor
import DifferentialGeometry.Geometry.Curvature.Metric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle Tensor0SBundle
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
theorem metricRm04At_mem_algebraicCurvatureTensorSubmodule
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricRm04At (I := I) (M := M) g x ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
  let K := metricCurvData (I := I) (M := M) g
  apply mem_algebraicCurvatureTensorSubmodule_iff_symmetries.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro X Y Z W
    simpa [metricRm04StdAt_apply, metricRm04_apply] using
      (rm04InputSkewAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g) K.h_rm04 Y X Z W)
  · intro X Y Z W
    simpa [metricRm04StdAt_apply, metricRm04_apply] using
      (rm04OutputSkewAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g) K.h_rm04 X Y Z W)
  · intro X Y Z W
    simpa [metricRm04StdAt_apply, metricRm04_apply] using
      (firstBianchiAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g) K.h_rm04 X Y Z W)

omit [SigmaCompactSpace M] in
noncomputable def metricAlgebraicCurvatureTensorAt
    (g : SmoothRiemannianMetric I M) (x : M) :
    algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
  ⟨metricRm04At (I := I) (M := M) g x,
    metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (M := M) g x⟩

omit [SigmaCompactSpace M] in
@[simp]
theorem metricAlgebraicCurvatureTensorAt_coe
    (g : SmoothRiemannianMetric I M) (x : M) :
    (metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x :
      Tensor04At (I := I) (M := M) x) =
        metricRm04At (I := I) (M := M) g x :=
  rfl

end DifferentialGeometry.Geometry.Curvature
