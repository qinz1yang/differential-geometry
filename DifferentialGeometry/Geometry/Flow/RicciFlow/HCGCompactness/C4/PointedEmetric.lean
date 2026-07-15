import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedRiemannian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The Riemannian emetric of a pointed Riemannian manifold

`PointedRiemannianManifold.emetricSpace` packages the `EMetricSpace` induced by the
stored smooth Riemannian metric, the same construction used inside
`PointedRiemannian.MetricComplete`.  It is factored out here, in a context WITHOUT
`[InnerProductSpace ℝ E]`, on purpose: when the model space `E` is itself an inner
product space, the model fiber inner product on `TangentSpace I x` does not coincide
definitionally with the Riemannian one (see Mathlib's
`normedAddCommGroupTangentSpaceVectorSpace`), so the per-fibre `InnerProductSpace`
synthesis needed to build the emetric must run where only the Riemannian fiber
structure is in scope.  Downstream files (e.g. the Step A good-covering net) consume
this already-elaborated `EMetricSpace` and never re-synthesize the fiber instance.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff Bundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]

/-- The `EMetricSpace` on a pointed Riemannian manifold induced by its stored smooth
Riemannian metric (Mathlib's `EMetricSpace.ofRiemannianMetric`).  This is the same
emetric whose completeness `MetricComplete` asserts. -/
@[reducible] def PointedRiemannianManifold.emetricSpace
    {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) : EMetricSpace Y.M := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M :=
    IsManifold.of_le (I := I) (M := Y.M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : TopologicalSpace.MetrizableSpace Y.M := Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  letI : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : Y.M => TangentSpace I x) :=
    ⟨⟨Y.metric.inner, Y.metric.contMDiff.continuous, by intro x v w; rfl⟩⟩
  exact EMetricSpace.ofRiemannianMetric I Y.M

/-- The `RiemannianBundle` instance on the tangent bundle determined by the stored
smooth Riemannian metric.  This is separated from `emetricSpace` so downstream
Hopf--Rinow consumers can reuse the same instance package. -/
@[reducible] def PointedRiemannianManifold.riemBundle
    {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  exact ⟨Y.metric.toRiemannianMetric⟩

/-- The per-fiber inner-product instances induced by the stored metric's
`RiemannianBundle`. -/
@[reducible] def PointedRiemannianManifold.riemInner
    {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
      Y.riemBundle (I := I)
    (x : Y.M) → InnerProductSpace Real (TangentSpace I x) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    Y.riemBundle (I := I)
  exact fun _ => inferInstance

/-- Continuity of the tangent-bundle Riemannian structure determined by the
stored metric. -/
@[reducible] def PointedRiemannianManifold.riemBundle_cont
    {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
      Y.riemBundle (I := I)
    IsContinuousRiemannianBundle E (fun x : Y.M => TangentSpace I x) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    Y.riemBundle (I := I)
  exact ⟨⟨Y.metric.inner, Y.metric.contMDiff.continuous, by intro x v w; rfl⟩⟩

end HCGCompactness
end DifferentialGeometry
