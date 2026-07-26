import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Covariant

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-!
# Metric covariant-derivative-in-frame components (HCG port)

The definitions `metricCovDeriv{,2,3}ForMetricCompInFrame` exist in the source
RicciFlower development under `Coordinates/MetricCompatibility/Covariant.lean`
but are absent from this repository's
`Geometry/Coordinates/MetricCompatibility/Covariant.lean` (which only carries the
`inverse...` variants).  They are reproduced here verbatim, in the same
`DifferentialGeometry.Tensor.Coordinates` namespace, so the
Hamilton--Cheeger--Gromov `AllTimesBounds` file can cite them.
-/

namespace DifferentialGeometry.Tensor.Coordinates

noncomputable section

open Bundle
open DifferentialGeometry.Integral.Connection
open Tensor0SBundle
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Components

variable {Idx : Type*} [Fintype Idx]
variable {u : Set M}

/-- Covariant derivative components of a metric with respect to an arbitrary
connection in a local frame. -/
def metricCovDerivForMetricCompInFrame
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (d a b : Idx) : Real :=
  extDerivFun (I := I)
      (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
      x (frame d x) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x d a p *
        metricCompForMetricInFrame (I := I) g frame x p b) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x d b p *
        metricCompForMetricInFrame (I := I) g frame x a p)

/-- Second covariant derivative components of a metric with respect to an
arbitrary connection in a local frame.

The slot order is the derivative direction `d`, followed by the three slots
`a b c` of `nabla g`.  This is the coordinate object needed for the
differentiated Christoffel-difference formula used in MSM135 Chapter 4 F3. -/
def metricCovDeriv2ForMetricCompInFrame
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (d a b c : Idx) : Real :=
  extDerivFun (I := I)
      (fun y : M =>
        metricCovDerivForMetricCompInFrame
          (I := I) g cov frame hframe y a b c)
      x (frame d x) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x d a p *
        metricCovDerivForMetricCompInFrame
          (I := I) g cov frame hframe x p b c) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x d b p *
        metricCovDerivForMetricCompInFrame
          (I := I) g cov frame hframe x a p c) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x d c p *
        metricCovDerivForMetricCompInFrame
          (I := I) g cov frame hframe x a b p)

/-- Third covariant derivative components of a metric with respect to an
arbitrary connection in a local frame.

The slot order is the new derivative direction `m`, followed by the four slots
`d a b c` of `nabla^2 g`.  This is the coordinate object needed for the first
higher-order connection-difference estimate in MSM135 Chapter 4 F3. -/
def metricCovDeriv3ForMetricCompInFrame
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (m d a b c : Idx) : Real :=
  extDerivFun (I := I)
      (fun y : M =>
        metricCovDeriv2ForMetricCompInFrame
          (I := I) g cov frame hframe y d a b c)
      x (frame m x) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x m d p *
        metricCovDeriv2ForMetricCompInFrame
          (I := I) g cov frame hframe x p a b c) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x m a p *
        metricCovDeriv2ForMetricCompInFrame
          (I := I) g cov frame hframe x d p b c) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x m b p *
        metricCovDeriv2ForMetricCompInFrame
          (I := I) g cov frame hframe x d a p c) -
    (∑ p : Idx,
      christoffelSymbolInFrame cov frame hframe x m c p *
        metricCovDeriv2ForMetricCompInFrame
          (I := I) g cov frame hframe x d a b p)

end Components

end

end DifferentialGeometry.Tensor.Coordinates
