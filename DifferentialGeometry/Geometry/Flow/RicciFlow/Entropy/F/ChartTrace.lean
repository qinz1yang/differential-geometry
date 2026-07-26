import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.F.TraceAlgebra
import DifferentialGeometry.Geometry.Connection.LeviCivita.DivergenceFrameInvariance


set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open Filter MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Coordinates
open Tensor0SBundle
open scoped Manifold ContDiff

variable {M : Type*}

/-!
# Perelman F connection-trace chart bridge

Split-out component of the Perelman `F`-functional layer
(`DifferentialGeometry.PDE.RicciFlow.Entropy.F`).

This file connects the basis-invariant Voss–Weyl divergence of the constructed
metric-trace field `tr_g A` (computed through the proven
`divergence_g_eq_coordinateFrame_covariant_divergence` bridge) to the
`coordinateFrameAt`-frame product-rule expansion that feeds the finite trace
algebra `rawDivTraceAlg`.  Both sides live in the point-centered
`coordinateFrameAt` (`Module.finBasis`) frame, so the product-rule expansion is
genuinely the same frame as the bridge — no chart-coefficient identity is used.
-/

section GeometryFormula510

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

/-- At any base-set point, the `∞`-regularity and `1`-regularity coordinate-frame
local frames give the same coordinate coefficient (they share the same pointwise
basis `toBasisAt`). -/
private theorem coordinateFrameAt_coeff_one_eq
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (v : TangentSpace I x) (p : CoordinateIdx (𝕜 := Real) E) :
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff p x v =
      (coordinateFrameAt_isLocalFrame (I := I) x₀).coeff p x v := by
  classical
  have hbasis :
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀).toBasisAt hx =
        (coordinateFrameAt_isLocalFrame (I := I) x₀).toBasisAt hx := by
    unfold IsLocalFrameOn.toBasisAt
    congr 1
  unfold IsLocalFrameOn.coeff
  rw [dif_pos hx, dif_pos hx, hbasis]

/-- The intrinsic inverse-metric chart component function. -/
def gInvFun
    (g : SmoothRiemannianMetric I M)
    (x : M) (i j : CoordinateIdx (𝕜 := Real) E) : M -> Real :=
  fun y : M =>
    inverseMetricFlatModelInChart_component (I := I) g x i j (extChartAt I x y)

/-- The intrinsic upper-component function `A^p_{ij}` of the connection-variation
tensor, evaluated against the point-centered coordinate basis tensors. -/
def compFun
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (x : M) (p i j : CoordinateIdx (𝕜 := Real) E) : M -> Real :=
  fun y : M =>
    (A y
      (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 1 x
        ((continuousMultilinearMap_basis
          (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
          (fun _ : Fin 1 => p)) y))
      (fun q : Fin 2 =>
        coordinateFrameAt (I := I) x (if q = 0 then i else j) y)

/-- The coefficient field `coeff_p (tr_g A)` equals, near the chart centre, the
explicit inverse-metric contraction of the `(1,2)` tensor components in the
`coordinateFrameAt` frame.  This is the bridge-frame replacement for the friend's
false chart-coefficient identity. -/
theorem connTraceCoeff_one_eventually
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (x₀ : M) (p : CoordinateIdx (𝕜 := Real) E) :
    (fun y : M =>
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff p y
          ((DifferentialGeometry.Integral.Connection.connTraceField (I := I) g A).toFun y))
      =ᶠ[nhds x₀]
      fun y : M =>
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            gInvFun (I := I) g x₀ i j y * compFun (I := I) A x₀ p i j y := by
  classical
  have hcoeff :=
    DifferentialGeometry.Integral.Connection.connTraceCoeff_eventually (I := I) g A x₀ p
  filter_upwards
    [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀), hcoeff] with y hy hcoeff_y
  rw [coordinateFrameAt_coeff_one_eq (I := I) x₀ hy _ p]
  rw [show ((DifferentialGeometry.Integral.Connection.connTraceField (I := I) g A).toFun y) =
        DifferentialGeometry.Integral.Connection.connTraceAt (I := I) g (A y) from rfl]
  exact hcoeff_y

end GeometryFormula510

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
