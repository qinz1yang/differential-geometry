import Mathlib.Analysis.Calculus.ContDiff.Operations
import RicciFlower.RicciFlow.Basic
import RicciFlower.Connection.MetricCompatibility
import RicciFlower.Coordinates.Christoffel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-!
# Ricci-Flow Metric Evolution in a Fixed Frame

This file translates the first Section 6.2 metric calculation into the realized
interval API.  The core geometric input is the Ricci-flow equation
`partial_t g = -2 Ric`; the inverse-metric result is obtained by differentiating
the frame identity `g^{-1} g = I`.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open Bundle
open RicciFlower.Coordinates
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Components

variable {Idx : Type*} [Fintype Idx]
variable {u : Set M}

/-- Metric component in a fixed local frame. -/
def metricCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  (S.family.metric t).inner x (frame i x) (frame j x)

@[simp] theorem metricCompInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    metricCompInFrame (I := I) S frame t x i j =
      (S.family.metric t).inner x (frame i x) (frame j x) := by
  rfl

/-- Fixed-frame metric evolution, directly extracted from `IsSolutionOn`. -/
theorem metricCompInFrame_hasDerivWithinAt
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => metricCompInFrame (I := I) S frame s x i j)
      ((-2 : Real) * ricciCompInFrame (I := I) S frame (t : Real) x i j)
      D.carrier
      (t : Real) := by
  simpa [metricCompInFrame, ricciCompInFrame] using
    metric_derivWithin_eq_neg_two_ricci (I := I) S hS t x
      (frame i x) (frame j x)

/-- Coordinate-frame metric components are jointly smooth in spacetime, by the
metric-family spacetime smoothness assumed in `IsSolutionOn`. -/
theorem coordMetricSmooth
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M) (i j : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ⊤
      (fun p : Real × M =>
        metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀)
          p.1 p.2 i j)
      (D.carrier ×ˢ coordinateFrameSet (I := I) x₀) := by
  simpa [metricCompInFrame] using
    hS.smoothMetric.frameCompSmooth
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) i j

/-- Pointwise spacetime smoothness of coordinate-frame metric components at
regular times and points in the coordinate-frame domain. -/
theorem coordMetricSmoothAt
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M) (t : Realized.RealTimeInterval.RegularTime D) (x : M)
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ⊤
      (fun p : Real × M =>
        metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀)
          p.1 p.2 i j)
      ((t : Real), x) := by
  exact
    (coordMetricSmooth (I := I) S hS x₀ i j).contMDiffAt
      (prod_mem_nhds (D.regular_mem_nhds t.2)
        ((coordinateFrameSet_open (I := I) x₀).mem_nhds hx))

/-- Deprecated global inverse-metric components in a fixed frame.

Prefer `InvMetricLocal` on the actual local frame domain.  A general manifold
does not carry this kind of global frame data. -/
@[deprecated "use InvMetricLocal on the actual local frame domain" (since := "2026-05-22")]
def InverseMetricComponentsInFrameOn [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall t x i j,
    (∑ k : Idx,
        gInv t x i k * metricCompInFrame (I := I) S frame t x k j) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx,
        metricCompInFrame (I := I) S frame t x i k * gInv t x k j) =
        (if i = j then 1 else 0)

/-- Local two-sided inverse-metric components in a frame domain. -/
def InvMetricLocal [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M) : Prop :=
  forall t x, x ∈ u -> forall i j,
    (∑ k : Idx,
        gInv t x i k * metricCompInFrame (I := I) S frame t x k j) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx,
        metricCompInFrame (I := I) S frame t x i k * gInv t x k j) =
        (if i = j then 1 else 0)

/-- Deprecated global symmetry predicate for supplied inverse metric
components.

Prefer a pointwise symmetry hypothesis or derive symmetry from
`MetricInverseInBasis` at the point where it is needed. -/
@[deprecated "use pointwise inverse symmetry or derive it from MetricInverseInBasis" (since := "2026-05-22")]
def SymmetricInverseMetricComponentsInFrameOn
    (gInv : Real -> Realized.InverseMetricComponents M Idx) : Prop :=
  forall t x i j, gInv t x i j = gInv t x j i

/-- Deprecated global-frame symmetry projection.

Prefer deriving pointwise symmetry from `MetricInverseInBasis`, or from
`InvMetricLocal` plus a local-frame membership proof. -/
@[deprecated "derive pointwise symmetry from MetricInverseInBasis or InvMetricLocal" (since := "2026-05-22")]
theorem gInv_symm [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame) :
    SymmetricInverseMetricComponentsInFrameOn gInv := by
  intro t x i j
  exact Curvature.invComp_symm
    (I := I) (g := S.family.metric t)
    (gInv := fun x i j => gInv t x i j) frame
    (by
      intro y a b
      simpa [metricCompInFrame] using hinv t y a b)
    x i j

/-- Componentwise regularity of a supplied inverse-metric component family. -/
def InverseMetricDerivativeComponentsOn
    {D : Realized.RealTimeInterval}
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    HasDerivWithinAt
      (fun s : Real => gInv s x i j)
      (gInvDt (t : Real) x i j)
      D.carrier
      (t : Real)

/-- Metric-side regularity in a fixed local frame.

This package is deliberately metric-side: it records smooth time dependence of
the frame Gram matrix, nondegeneracy through a chosen two-sided inverse frame
matrix, time differentiability of that inverse matrix, and uniqueness of time
derivatives on the interval.  The inverse evolution formula itself is still
proved by differentiating the inverse identity in
`inverseMetricEvolutionEquationInFrame_of_inverse_components`; it is not assumed
here. -/
structure MetricFrameTimeRegularityInFrameOnLocal
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M) : Prop where
  metricSmooth :
    forall x : M, x ∈ u -> forall i j : Idx,
      ContDiffOn Real ⊤
        (fun t : Real => metricCompInFrame (I := I) S frame t x i j)
        D.carrier
  /-- Nondegeneracy is represented by an explicit two-sided inverse of the
  frame Gram matrix. -/
  nondegenerateGram :
    InvMetricLocal (I := I) S gInv frame u
  inverseMetricDerivative :
    InverseMetricDerivativeComponentsOn (D := D) gInv gInvDt
  uniqueTimeDerivatives :
    forall t : Realized.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real)

/-- Spacetime metric regularity in a fixed local frame.

The extra mixed-derivative field is the fixed-base statement
`∂s d_x(g_s) = d_x(∂s g_s)` specialized to the Ricci-flow metric variation
`∂s g_s = -2 Ric_s`.  This is weaker than, and does not assert, commutation of
`∂t` with the evolving covariant derivative. -/
structure MetricFrameSpacetimeRegularityInFrameOnLocal
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M) : Prop extends
      MetricFrameTimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u where
  frameMetricSpacetimeSmooth :
    forall i j : Idx,
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ⊤
        (fun p : Real × M => metricCompInFrame (I := I) S frame p.1 p.2 i j)
        (D.carrier ×ˢ u)
  frameMetricExtDerivTimeDerivative :
    forall (t : Realized.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
      forall d a b : Idx,
        HasDerivWithinAt
          (fun s : Real =>
            extDerivFun (I := I)
              (fun y : M => metricCompInFrame (I := I) S frame s y a b)
              x (frame d x))
          ((-2 : Real) *
            extDerivFun (I := I)
              (fun y : M => ricciCompInFrame (I := I) S frame (t : Real) y a b)
              x (frame d x))
          D.carrier
          (t : Real)


end Components

end RicciFlow
end RicciFlower
