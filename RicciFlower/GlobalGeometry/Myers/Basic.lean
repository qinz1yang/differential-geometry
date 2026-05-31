import RicciFlower.Curvature.Tensor
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Basic Myers compactness interfaces

This file contains the theorem-independent definitions shared by the parent
`Myers.lean` endpoint and the lower Hopf-Rinow wiring file.  Keeping these
definitions below `HopfRinow.lean` avoids an import cycle when the parent module
imports the Hopf-Rinow producer.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry

open Bundle Bornology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

/-- The model-space dimension-three assumption used by the Hamilton endpoint. -/
def DimensionThree (E : Type*) [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] : Prop :=
  Module.finrank Real E = 3

section TopologicalCurvature

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Pointwise tensor inequality `Ric >= c * g`, evaluated on diagonal tangent
vectors.  This is the Ricci lower-bound object that future Myers interfaces
should consume from RicciFlower curvature data. -/
def RicciLowerBound
    (g : SmoothRiemannianMetric I M)
    (Ric : Curvature.Tensor02Section (I := I) (M := M))
    (c : Real) : Prop :=
  forall x : M, forall v : TangentSpace I x,
    c * g.inner x v v <= Ric x (Curvature.vec2 (I := I) v v)

/-- Einstein condition in the RicciFlower static tensor conventions. -/
def EinsteinMetric
    (g : SmoothRiemannianMetric I M)
    (Ric : Curvature.Tensor02Section (I := I) (M := M))
    (lambda : Real) : Prop :=
  forall x : M, forall v w : TangentSpace I x,
    Ric x (Curvature.vec2 (I := I) v w) = lambda * g.inner x v w

/-- The scalar curvature is positive at some point. -/
def ScalarPositiveSomewhere (scalar : M -> Real) : Prop :=
  exists x : M, 0 < scalar x

/-- Trace normalization for an Einstein metric: in dimension `n`, scalar
curvature is `n * lambda`.  This is stated separately because RicciFlower's
scalar-trace realization currently lives in frame-dependent curvature data. -/
def EinsteinScalarTrace (scalar : M -> Real) (lambda : Real) : Prop :=
  forall x : M, scalar x = (Module.finrank Real E : Real) * lambda

end TopologicalCurvature

section MetricCompactness

variable {X : Type*}

/-- Metric-space compactness endpoint available from mathlib: in a proper
metric space, bounded diameter of the whole space implies compactness. -/
theorem compactSpace_of_proper_of_forall_dist_le
    [PseudoMetricSpace X] [ProperSpace X]
    {C : Real} (hdiam : forall x y : X, dist x y <= C) :
    CompactSpace X := by
  have hbounded : IsBounded (Set.univ : Set X) := by
    rw [Metric.isBounded_iff]
    exact ⟨C, by intro x _hx y _hy; exact hdiam x y⟩
  exact (Metric.compactSpace_iff_isBounded_univ).2 hbounded

end MetricCompactness

end GlobalGeometry
end RicciFlower
