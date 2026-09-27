import Batteries.Tactic.Alias
import DifferentialGeometry.Geometry.Curvature.Metric.SectionalCone
import DifferentialGeometry.Geometry.Curvature.Coordinates.RiemannTensorBridge

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M]

def hasNonnegativeSectionalCurvature
    (g : SmoothRiemannianMetric I M) : Prop :=
  ∀ x : M, metricRm04At (I := I) (M := M) g x ∈
    tensor04SectionalNonnegativeCone (I := I) (M := M)

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
theorem hasNonnegativeSectionalCurvature_iff
    (g : SmoothRiemannianMetric I M) :
    hasNonnegativeSectionalCurvature (I := I) g ↔
      ∀ x : M, ∀ W T : TangentSpace I x,
        0 ≤ metricRm04StandardAt (I := I) (M := M) g x W T T W := by
  constructor
  · intro h x
    exact (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff
      (I := I) (M := M) g x).mp (h x)
  · intro h x
    exact (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff
      (I := I) (M := M) g x).mpr (h x)

omit [SigmaCompactSpace M] in
theorem riemann_contraction_nonneg
    {g : SmoothRiemannianMetric I M}
    (hsec : hasNonnegativeSectionalCurvature (I := I) g)
    (x : M) (W T : TangentSpace I x) :
    0 ≤ g.inner x W
      (riemannOp (cov := LeviCivita (I := I) g) x W T T) := by
  have hRm : 0 ≤ metricRm04StandardAt (I := I) (M := M) g x W T T W :=
    (hasNonnegativeSectionalCurvature_iff (I := I) g).mp hsec x W T
  rwa [rm04_eq_inner_riem (I := I) (M := M) g x W T T W] at hRm

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

@[reducible] alias HasNonnegativeSectionalCurvature := DifferentialGeometry.Geometry.hasNonnegativeSectionalCurvature

end DifferentialGeometry.Geometry
