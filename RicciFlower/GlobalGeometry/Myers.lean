import RicciFlower.Curvature.Tensor
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Global-geometry Myers compactness interfaces

This file records a RicciFlower-facing global-geometry side project around the
Myers compactness interface eventually needed by the Hamilton positive-Ricci
blueprint.  It is intentionally a thin interface layer: the Jacobi field, index
form, minimizing geodesic, exponential-map, and Hopf-Rinow developments are not
attempted here.

The metric-space endpoint is already available in mathlib for proper metric
spaces: a bounded universe in a `ProperSpace` is compact.  The missing future
work is the Riemannian-geometric theorem turning a positive Ricci lower bound
and metric completeness into a uniform diameter bound or properness.
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

section RiemannianInterfaces

variable {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]
variable [IsRiemannianManifold I M]

/-- Black-box Bonnet-Myers/Myers compactness interface in dimension `n`.

Intended reading:
* the active `EMetricSpace`/`IsRiemannianManifold` structure is the
  Riemannian distance associated to `g`;
* `CompleteSpace M` is completeness for that distance;
* `Ric` is the Ricci tensor of the Levi-Civita connection of `g`;
* `RicciLowerBound g Ric (((n - 1 : Nat) : Real) * k)` is
  `Ric >= (n - 1) k g`.

The proof frontier is the global Riemannian analysis package: minimizing
geodesics, second variation or index form, conjugate-point comparison, and
Hopf-Rinow/properness. -/
theorem myers_compactSpace_of_ricci_lower_bound
    [CompleteSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (Ric : Curvature.Tensor02Section (I := I) (M := M))
    {n : Nat} {k : Real}
    (_hdim : Module.finrank Real E = n)
    (_hk : 0 < k)
    (_hRic : RicciLowerBound (I := I) (M := M) g Ric (((n - 1 : Nat) : Real) * k)) :
    CompactSpace M := by
  sorry

/-- Three-dimensional Myers interface for Hamilton's positive-Ricci route:
`Ric >= 2 k g`, `k > 0`, completeness, and connectedness imply compactness. -/
theorem myers_compactSpace_three_of_ricci_lower_bound
    [CompleteSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (Ric : Curvature.Tensor02Section (I := I) (M := M))
    {k : Real}
    (_hdim : DimensionThree E)
    (_hk : 0 < k)
    (_hRic : RicciLowerBound (I := I) (M := M) g Ric (2 * k)) :
    CompactSpace M := by
  sorry

/-- Hamilton-tailored compactness interface: a complete connected 3D Einstein
limit with positive scalar curvature is compact.

The explicit `EinsteinScalarTrace` hypothesis is the future bridge from the
existing frame-based scalar trace realization to the positive Einstein
constant needed to feed Myers with `k = lambda / 2`. -/
theorem compactSpace_of_three_einstein_scalar_positive
    [CompleteSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (Ric : Curvature.Tensor02Section (I := I) (M := M))
    (scalar : M -> Real)
    {lambda : Real}
    (_hdim : DimensionThree E)
    (_hEinstein : EinsteinMetric (I := I) (M := M) g Ric lambda)
    (_hScalarTrace : EinsteinScalarTrace (E := E) scalar lambda)
    (_hScalarPos : ScalarPositiveSomewhere scalar) :
    CompactSpace M := by
  sorry

/-!
Optional future diameter-bound shape, once the geodesic comparison statement is
available:

```
theorem myers_diam_univ_le
    [PseudoMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [CompleteSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (Ric : Curvature.Tensor02Section (I := I) (M := M))
    {k : Real} (hk : 0 < k)
    (hRic : RicciLowerBound (I := I) (M := M) g Ric (2 * k)) :
    Metric.diam (Set.univ : Set M) <= Real.pi / Real.sqrt k := by
  ...
```

Combined with `compactSpace_of_proper_of_forall_dist_le`, this would give the
metric-space compactness endpoint as soon as the Riemannian Hopf-Rinow/proper
bridge supplies `ProperSpace M`.
-/

end RiemannianInterfaces

end GlobalGeometry
end RicciFlower
