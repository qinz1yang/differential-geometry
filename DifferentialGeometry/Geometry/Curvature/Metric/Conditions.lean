import DifferentialGeometry.Geometry.Curvature.Sections.Connection
import DifferentialGeometry.Geometry.Curvature.Metric.Sectional

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

def positiveRicciMetric (g : SmoothRiemannianMetric I M) : Prop :=
  ∀ x : M, ∀ v : TangentSpace I x, v ≠ 0 →
    0 < metricRicciAt (I := I) (M := M) g x (vec2 (I := I) v v)

def admitsPositiveRicci : Prop :=
  ∃ g : SmoothRiemannianMetric I M, positiveRicciMetric (I := I) (M := M) g

def constantPositiveSectionalCurvatureMetric
    (g : SmoothRiemannianMetric I M) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ x : M, ∀ X Y : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y)

def admitsConstantPositiveSectionalCurvature : Prop :=
  ∃ g : SmoothRiemannianMetric I M,
    constantPositiveSectionalCurvatureMetric (I := I) (M := M) g

end DifferentialGeometry.Geometry.Curvature
