import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.LeviCivita
import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.Realized

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Local-frame Hessian trace experiment

This file is an experiment for the local-frame route behind the `canHessAt`
proof.  The invariant input is still `DifferentialGeometry.Integral.Connection.canScalHess`; this file packages
its component form for an arbitrary realized `LocalChartAt.Frame`.

The supplied-component theorem remains available for consumers that already
realize inverse-metric arrays.  The canonical specialization below uses the
pointwise metric-sharp inverse in the frame basis; it still does not identify
any separately supplied chart/Ricci-flow component arrays with canonical
`∇² Ric` components.
-/

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates
open scoped BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E] [Module.Finite Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M]

/-- Canonical scalar-Hessian trace written in a realized local-chart frame.

The frame enters only through the pointwise basis `F.basisAt hx`.  This is the
frame-general version of the contraction used by the centered coordinate proof
of `canHessAt`. -/
def scalHessFrame
    (g : SmoothRiemannianMetric I M)
    {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {x : M} (hx : x ∈ F.domain)
    (gInv :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  let cov := leviCivitaConnectionOfMetric (I := I) g
  let hcov :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g
  let Ric : Tensor02Section (I := I) (M := M) :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
  let nablaRic :=
    totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov Ric (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
        2 cov hcov Ric)
  let nabla2Ric :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 cov nablaRic x
  ∑ k : CoordinateIdx (𝕜 := Real) E,
    ∑ l : CoordinateIdx (𝕜 := Real) E,
      gInv k l *
        nabla2Ric (vec4 (I := I) (F.basisAt hx i) (F.basisAt hx j)
          (F.basisAt hx k) (F.basisAt hx l))

/-- The canonical scalar-Hessian trace is symmetric in any realized
local-chart frame.

This is the experimental general-coordinate consumer: all chart/frame-specific
work is reduced to the pointwise inverse-metric realization `hinv`, while the
geometric proof is `DifferentialGeometry.Integral.Connection.canScalHess`. -/
theorem scalHessFrameSymm
    (g : SmoothRiemannianMetric I M)
    {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {x : M} (hx : x ∈ F.domain)
    (gInv :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (hinv :
      MetricInverseInBasis_gen (I := I) (M := M) g x (F.basisAt hx) gInv)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    scalHessFrame (I := I) (M := M) g F hx gInv i j =
      scalHessFrame (I := I) (M := M) g F hx gInv j i := by
  simpa [scalHessFrame] using
    DifferentialGeometry.Integral.Connection.canScalHess (I := I) (M := M) (g := g)
      (basis := F.basisAt hx) gInv hinv i j

/-- Canonical inverse-metric components in a realized local-chart frame.

These are pointwise components in `F.basisAt hx`, obtained from the metric
sharp map.  This is a producer for the inverse-metric basis predicate, not a
claim about any externally supplied coordinate array. -/
def frameInvMetric
    (g : SmoothRiemannianMetric I M)
    {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {x : M} (hx : x ∈ F.domain)
    (i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  basisInvMetric (I := I) (M := M) g x (F.basisAt hx) i j

/-- The canonical frame inverse components realize the inverse metric in the
pointwise frame basis. -/
theorem frameInvMetric_real
    (g : SmoothRiemannianMetric I M)
    {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {x : M} (hx : x ∈ F.domain) :
    MetricInverseInBasis_gen (I := I) (M := M) g x (F.basisAt hx)
      (frameInvMetric (I := I) (M := M) g F hx) := by
  simpa [frameInvMetric] using
    basisInvMetric_real (I := I) (M := M) (g := g) (x := x)
      (basis := F.basisAt hx)

/-- Canonical scalar-Hessian trace in a realized local-chart frame. -/
def frameScalHess
    (g : SmoothRiemannianMetric I M)
    {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {x : M} (hx : x ∈ F.domain)
    (i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  scalHessFrame (I := I) (M := M) g F hx
    (frameInvMetric (I := I) (M := M) g F hx) i j

/-- Canonical frame scalar-Hessian trace symmetry, with no supplied inverse
array argument. -/
theorem frameScalHess_symm
    (g : SmoothRiemannianMetric I M)
    {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {x : M} (hx : x ∈ F.domain)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    frameScalHess (I := I) (M := M) g F hx i j =
      frameScalHess (I := I) (M := M) g F hx j i := by
  simpa [frameScalHess] using
    scalHessFrameSymm (I := I) (M := M) g F hx
      (frameInvMetric (I := I) (M := M) g F hx)
      (frameInvMetric_real (I := I) (M := M) g F hx) i j

end DifferentialGeometry.Integral.Connection
