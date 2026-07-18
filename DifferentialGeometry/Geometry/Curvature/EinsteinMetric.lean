import DifferentialGeometry.Geometry.Curvature.Metric

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

def IsEinsteinMetric (g : SmoothRiemannianMetric I M) (κ : Real) : Prop :=
  forall (x : M) (v w : TangentSpace I x),
    metricRicciAt (I := I) (M := M) g x (vec2 (I := I) v w) = κ * g.inner x v w

theorem IsEinsteinMetric.ricci_apply
    {g : SmoothRiemannianMetric I M} {κ : Real}
    (hg : IsEinsteinMetric (I := I) g κ) (x : M) (v w : TangentSpace I x) :
    metricRicciAt (I := I) (M := M) g x (vec2 (I := I) v w) = κ * g.inner x v w :=
  hg x v w

end DifferentialGeometry.Integral.Connection
