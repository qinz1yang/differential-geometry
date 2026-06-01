import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Existence
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Uniqueness
import Mathlib.Analysis.ODE.PicardLindelof

set_option linter.unusedSectionVars false

/-!
# Regularity of geodesics

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, the local existence /
uniqueness theorems already produce a curve `γ : ℝ → M` with a velocity
lift `f : ℝ → TangentBundle I M` that is an integral curve of the
chart-fixed geodesic vector field `geodesicVectorFieldChart g α`. The
present file packages the regularity statements that follow at no cost
from the integral-curve property.

## Main results

* `IsGeodesicAt.continuousAt`: a local spray geodesic at `t₀` is continuous
  at `t₀`. The proof is a direct projection of the lift's continuity,
  inherited from Mathlib's `IsMIntegralCurveAt.continuousAt`.

* `chartPushLift`, `chartPushVF`: the analytic shape of the lifted
  curve and the chart-pushed geodesic vector field in `E × E` (the
  model space of `I.tangent`), i.e. phase-space coordinates
  (position, velocity).

* `chartPushLift_eventually_hasDerivAt`: the chart-pushed lift admits
  a `HasDerivAt`-formula on a neighbourhood of `t₀`, with the
  chart-pushed vector field as right-hand side. This is the
  geodesic specialisation of `IsMIntegralCurveAt.eventually_hasDerivAt`
  (`Mathlib/Geometry/Manifold/IntegralCurve/Basic.lean`).

## Mathlib status (recorded for transparency)

Mathlib provides flow-existence theorems for `C^1`-vector fields
(`ContDiffAt.exists_eventually_eq_hasDerivAt` in
`Mathlib/Analysis/ODE/PicardLindelof.lean`) but only with continuous /
Lipschitz dependence on the initial condition, NOT `C^k`-dependence in
initial data for any `k ≥ 1`. The classical proof of `C^k`-dependence on
initial data via the variational equation is not in Mathlib, and is
deferred to a follow-up substep. The present file therefore focuses on
the regularity statements that the integral-curve property delivers
unconditionally: continuity and the chart-pushed `HasDerivAt`-formula.

Higher-order `C^k`-smoothness in time of a fixed integral curve is a
purely analytic consequence of `contDiffOn_enat_Icc_of_hasDerivWithinAt`
(`Mathlib/Analysis/ODE/PicardLindelof.lean`, line 572), but requires a
chart-pushed `ContDiffOn` form of the geodesic vector field which is
substantive; the deliverable here is the chart-pushed `HasDerivAt`-form
that downstream analytic bootstraps can plug directly into Mathlib's
ODE regularity theorems.
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

section LiftContinuity

/-- A local integral curve of the chart-fixed geodesic vector field at
`t₀` is continuous at `t₀`. Direct restatement of
`IsMIntegralCurveAt.continuousAt`. -/
lemma IsMIntegralCurveAt.continuousAt_lift
    {g : SmoothRiemannianMetric I M} {α : M} {t₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t₀) :
    ContinuousAt f t₀ :=
  hf.continuousAt

/-- A global integral curve of the chart-fixed geodesic vector field is
globally continuous. Direct restatement of `IsMIntegralCurve.continuous`. -/
lemma IsMIntegralCurve.continuous_lift
    {g : SmoothRiemannianMetric I M} {α : M}
    {f : ℝ → TangentBundle I M}
    (hf : IsMIntegralCurve f (geodesicVectorFieldChart (I := I) g α)) :
    Continuous f :=
  hf.continuous

end LiftContinuity

section BaseContinuity

/-- Continuity of the bundle projection on the tangent bundle, restated
for use below. -/
lemma continuous_tangentBundle_proj :
    Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
  FiberBundle.continuous_proj E (TangentSpace I)

/-- **Continuity of a local geodesic.** A local geodesic at `t₀` is
continuous at `t₀`. -/
theorem IsGeodesicAt.continuousAt
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t₀) :
    ContinuousAt γ t₀ := by
  obtain ⟨α, f, hproj, _hα_src, hf⟩ := hγ
  have hf_cont : ContinuousAt f t₀ := hf.continuousAt
  have hπ_cont : ContinuousAt
      (Bundle.TotalSpace.proj : TangentBundle I M → M) (f t₀) :=
    continuous_tangentBundle_proj.continuousAt
  have hcomp : ContinuousAt (fun t => (f t).proj) t₀ := hπ_cont.comp hf_cont
  have heq : (fun t => (f t).proj) = γ := funext hproj
  rw [heq] at hcomp
  exact hcomp

end BaseContinuity

section ChartPushedDerivative

variable [I.Boundaryless]

/-- The chart-pushed lift: the lift `f : ℝ → TangentBundle I M`
post-composed with the chart on the tangent bundle of `M` at `f t₀`.
This is the analytic curve in `E × E` (the model space of `I.tangent`)
that solves the chart-local geodesic ODE in phase-space (position,
velocity) coordinates. -/
def chartPushLift (f : ℝ → TangentBundle I M) (t₀ : ℝ) :
    ℝ → E × E := fun t => extChartAt I.tangent (f t₀) (f t)

@[simp] lemma chartPushLift_apply (f : ℝ → TangentBundle I M) (t₀ t : ℝ) :
    chartPushLift (I := I) f t₀ t = extChartAt I.tangent (f t₀) (f t) := rfl

/-- The chart-pushed geodesic vector field at `(f t₀, f t)`: the value of
`geodesicVectorFieldChart g α` at `f t`, transported through the
tangent-chart change `f t → f t₀` and read off as a vector in `E × E`.
This is the RHS of the chart-pushed geodesic ODE. -/
def chartPushVF (g : SmoothRiemannianMetric I M) (α : M)
    (f : ℝ → TangentBundle I M) (t₀ t : ℝ) : E × E :=
  tangentCoordChange I.tangent (f t) (f t₀) (f t)
    (geodesicVectorFieldChart (I := I) g α (f t))

@[simp] lemma chartPushVF_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (f : ℝ → TangentBundle I M) (t₀ t : ℝ) :
    chartPushVF (I := I) g α f t₀ t =
      tangentCoordChange I.tangent (f t) (f t₀) (f t)
        (geodesicVectorFieldChart (I := I) g α (f t)) := rfl

/-- **Chart-pushed derivative formula.** On a neighbourhood of `t₀`,
the chart-pushed lift `chartPushLift f t₀` has derivative
`chartPushVF g α f t₀ t` at `t`. This is the geodesic specialisation of
`IsMIntegralCurveAt.eventually_hasDerivAt`, providing the analytic
(Banach-space-valued) form of the geodesic ODE in chart coordinates.

This is the precise hypothesis required by Mathlib's ODE regularity
theorem `contDiffOn_enat_Icc_of_hasDerivWithinAt` to bootstrap to
higher-order time smoothness; the latter bootstrap requires
chart-pushed `ContDiffOn` of the RHS, which is a separate
analytic/manifold task. -/
theorem chartPushLift_eventually_hasDerivAt
    {g : SmoothRiemannianMetric I M} {α : M} {t₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t₀) :
    ∀ᶠ t in 𝓝 t₀, HasDerivAt (chartPushLift (I := I) f t₀)
      (chartPushVF (I := I) g α f t₀ t) t := by
  have h := hf.eventually_hasDerivAt
  filter_upwards [h] with t ht
  exact ht

/-- **Chart-pushed first-order regularity.** On a neighbourhood of `t₀`,
the chart-pushed lift has a derivative — in particular, it is
differentiable (and hence continuous) there. -/
lemma chartPushLift_eventually_differentiableAt
    {g : SmoothRiemannianMetric I M} {α : M} {t₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t₀) :
    ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ (chartPushLift (I := I) f t₀) t := by
  filter_upwards [chartPushLift_eventually_hasDerivAt (I := I)
    (g := g) (α := α) (t₀ := t₀) hf] with t ht
  exact ht.differentiableAt

/-- The chart-pushed lift is continuous at `t₀`. (Combines `f` continuous
at `t₀` with chart continuity at `f t₀`.) -/
lemma chartPushLift_continuousAt
    {f : ℝ → TangentBundle I M} {t₀ : ℝ}
    (hf_cont : ContinuousAt f t₀) :
    ContinuousAt (chartPushLift (I := I) f t₀) t₀ := by
  have hchart_cont : ContinuousAt (extChartAt I.tangent (f t₀)) (f t₀) :=
    continuousAt_extChartAt (I := I.tangent) (f t₀)
  exact hchart_cont.comp hf_cont

/-- The chart-pushed lift evaluated at the base time `t₀` is the chart
image of `f t₀`. -/
@[simp] lemma chartPushLift_self
    (f : ℝ → TangentBundle I M) (t₀ : ℝ) :
    chartPushLift (I := I) f t₀ t₀ = extChartAt I.tangent (f t₀) (f t₀) := rfl

end ChartPushedDerivative

section IsGeodesicAtChartPush

variable [I.Boundaryless] [CompleteSpace E]

/-- **`IsGeodesicAt` chart-pushed derivative formula.** A local geodesic
at `t₀` admits a lift `f` and a chart basepoint `α` such that the
chart-pushed lift satisfies the chart-local geodesic ODE in `E × E`
phase space on a neighbourhood of `t₀`. -/
theorem IsGeodesicAt.exists_chartPushLift_hasDerivAt
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t₀) :
    ∃ (α : M) (f : ℝ → TangentBundle I M),
      (∀ t, (f t).proj = γ t) ∧
      IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t₀ ∧
      ∀ᶠ t in 𝓝 t₀, HasDerivAt (chartPushLift (I := I) f t₀)
        (chartPushVF (I := I) g α f t₀ t) t := by
  obtain ⟨α, f, hproj, _hα_src, hf⟩ := hγ
  exact ⟨α, f, hproj, hf,
    chartPushLift_eventually_hasDerivAt (I := I) (g := g) (α := α)
      (t₀ := t₀) (f := f) hf⟩

end IsGeodesicAtChartPush

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
