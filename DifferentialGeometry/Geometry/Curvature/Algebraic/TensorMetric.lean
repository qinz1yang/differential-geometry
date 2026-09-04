import DifferentialGeometry.Geometry.Curvature.Algebraic.Tensor
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M]

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
noncomputable def algebraicCurvatureTensorProjection
    (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor04At (I := I) (M := M) x →ₗ[Real]
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
  MetricFiberData.submoduleProjection
    (tensor0SMetricData (I := I) g x 4)
    (algebraicCurvatureTensorSubmodule (I := I) (M := M) x)

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem algebraicCurvatureTensorProjection_inner
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor04At (I := I) (M := M) x)
    (B : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    inner0S (I := I) g x 4
        (algebraicCurvatureTensorProjection (I := I) g x A :
          Tensor04At (I := I) (M := M) x) B =
      inner0S (I := I) g x 4 A B :=
  MetricFiberData.submoduleProjection_inner
    (tensor0SMetricData (I := I) g x 4)
    (algebraicCurvatureTensorSubmodule (I := I) (M := M) x) A B

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem algebraicCurvatureTensorProjection_coe
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    algebraicCurvatureTensorProjection (I := I) g x
        (A : Tensor04At (I := I) (M := M) x) = A :=
  MetricFiberData.submoduleProjection_eq_self
    (tensor0SMetricData (I := I) g x 4)
    (algebraicCurvatureTensorSubmodule (I := I) (M := M) x) A A.2

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem algebraicCurvatureTensorProjection_eq_self
    (g : SmoothRiemannianMetric I M) (x : M)
    {A : Tensor04At (I := I) (M := M) x}
    (hA : A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    (algebraicCurvatureTensorProjection (I := I) g x A :
      Tensor04At (I := I) (M := M) x) = A :=
  congrArg Subtype.val
    (MetricFiberData.submoduleProjection_eq_self
      (tensor0SMetricData (I := I) g x 4)
      (algebraicCurvatureTensorSubmodule (I := I) (M := M) x) A hA)

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem algebraicCurvatureTensorProjection_norm_le
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor04At (I := I) (M := M) x) :
    tensor04FiberNorm (I := I) g x
        (algebraicCurvatureTensorProjection (I := I) g x A :
          Tensor04At (I := I) (M := M) x) ≤
      tensor04FiberNorm (I := I) g x A := by
  unfold tensor04FiberNorm tensor0SFiberNorm normSq0S
  exact Real.sqrt_le_sqrt
    (MetricFiberData.submoduleProjection_inner_self_le
      (tensor0SMetricData (I := I) g x 4)
      (algebraicCurvatureTensorSubmodule (I := I) (M := M) x) A)

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
        (I := I) g (metricRm04 (I := I) (M := M) g) K.rm04Realizes Y X Z W)
  · intro X Y Z W
    simpa [metricRm04StdAt_apply, metricRm04_apply] using
      (rm04OutputSkewAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g) K.rm04Realizes X Y Z W)
  · intro X Y Z W
    simpa [metricRm04StdAt_apply, metricRm04_apply] using
      (firstBianchiAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g) K.rm04Realizes X Y Z W)

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
