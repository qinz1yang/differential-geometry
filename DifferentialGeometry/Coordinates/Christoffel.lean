import DifferentialGeometry.Analysis.Time
import DifferentialGeometry.Coordinates.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# DifferentialGeometry Christoffel Symbols in a Local Frame

Mathlib's bundled covariant derivative has argument order
`cov sigma x v = (nabla_v sigma)(x)`. Given a local frame `frame i`, the
Christoffel coefficient is the `k`-th frame coefficient of
`nabla_{frame i} frame j`.
-/

namespace DifferentialGeometry
namespace Coordinates

noncomputable section

open Bundle Module
open scoped BigOperators Manifold ContDiff

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {Idx : Type*}
  {u : Set M}

/-- Christoffel coefficients in a local frame:
`Gamma^k_ij(x) = coeff_k(nabla_{frame_i} frame_j)`. -/
def christoffelSymbolInFrame
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i j k : Idx) : Real :=
  hframe.coeff k x ((cov (frame j) x) (frame i x))

/-- Christoffel coefficient with an arbitrary tangent direction in the first slot. -/
def christoffelAlongInFrame
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (X : TangentSpace I x) (j k : Idx) : Real :=
  hframe.coeff k x ((cov (frame j) x) X)

@[simp] theorem christoffelSymbolInFrame_eval
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i j k : Idx) :
    christoffelSymbolInFrame cov frame hframe x i j k =
      hframe.coeff k x ((cov (frame j) x) (frame i x)) := by
  rfl

@[simp] theorem christoffelAlongInFrame_eval
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (X : TangentSpace I x) (j k : Idx) :
    christoffelAlongInFrame cov frame hframe x X j k =
      hframe.coeff k x ((cov (frame j) x) X) := by
  rfl

/-- `christoffelAlongInFrame` recovers ordinary Christoffel symbols when the
direction is a frame vector. -/
theorem christoffelAlongInFrame_frame
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i j k : Idx) :
    christoffelAlongInFrame cov frame hframe x (frame i x) j k =
      christoffelSymbolInFrame cov frame hframe x i j k := by
  rfl

/-- Expansion of `nabla_{frame i} frame j` in the local frame. -/
theorem covariantDerivative_eq_sum_christoffel
    [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u) (i j : Idx) :
    (cov (frame j) x) (frame i x) =
      ∑ k, christoffelSymbolInFrame cov frame hframe x i j k • frame k x := by
  exact hframe.coeff_sum_eq (fun y => (cov (frame j) y) (frame i y)) hx

/-- Predicate saying a chosen local frame is normal for `cov` at `x`.

This is not a theorem asserting existence or automatic vanishing; it is the
named condition `Gamma^k_ij(x) = 0` for later normal-frame arguments. -/
def IsNormalFrameForConnectionAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) : Prop :=
  forall i j k : Idx, christoffelSymbolInFrame cov frame hframe x i j k = 0

section Difference

variable [FiniteDimensional Real E]
  [VectorBundle Real E (TangentSpace I : M -> Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]

/-- Components of the tensorial connection difference `cov - cov'` in a local frame. -/
def christoffelSymbolDifferenceInFrame
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i j k : Idx) : Real :=
  hframe.coeff k x (((CovariantDerivative.difference cov cov' x) (frame j x)) (frame i x))

/-- Expansion of the connection-difference tensor in the local frame. -/
theorem christoffelSymbolDifference_expansion
    [Fintype Idx]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u) (i j : Idx) :
    ((CovariantDerivative.difference cov cov' x) (frame j x)) (frame i x) =
      ∑ k, christoffelSymbolDifferenceInFrame cov cov' frame hframe x i j k • frame k x := by
  exact hframe.coeff_sum_eq
    (fun y => ((CovariantDerivative.difference cov cov' y) (frame j y)) (frame i y)) hx

/-- If the frame vector `frame j` is differentiable at `x`, the tensorial
connection-difference coefficient is the pointwise subtraction of Christoffel
coefficients. -/
theorem christoffelSymbolDifferenceInFrame_eq_sub
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (i j k : Idx)
    (hframe_j : MDiffAt (T% (frame j)) x) :
    christoffelSymbolDifferenceInFrame cov cov' frame hframe x i j k =
      christoffelSymbolInFrame cov frame hframe x i j k -
        christoffelSymbolInFrame cov' frame hframe x i j k := by
  unfold christoffelSymbolDifferenceInFrame christoffelSymbolInFrame
  change hframe.coeff k x
      (((cov.isCovariantDerivativeOnUniv.difference cov'.isCovariantDerivativeOnUniv x)
        (frame j x)) (frame i x)) =
    hframe.coeff k x ((cov (frame j) x) (frame i x)) -
      hframe.coeff k x ((cov' (frame j) x) (frame i x))
  rw [IsCovariantDerivativeOn.difference_apply
    (hcov := cov.isCovariantDerivativeOnUniv)
    (hcov' := cov'.isCovariantDerivativeOnUniv)
    (σ := frame j) (x := x) (hx := by trivial) hframe_j]
  simp

end Difference

section TimeDerivative

variable {A Time : Type*} [CommRing A] [Algebra Real A]

/-- The coordinate-facing time derivative `partial_t Gamma^k_ij` in a fixed local frame. -/
def christoffelSymbolTimeDerivativeInFrame
    (td : TimeDerivativeData Real A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (t : Time) (x : M) (i j k : Idx) : Real :=
  td.dt_apply (fun s => christoffelSymbolInFrame (covFam s) frame hframe x i j k) t

@[simp] theorem christoffelSymbolTimeDerivativeInFrame_eval
    (td : TimeDerivativeData Real A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (t : Time) (x : M) (i j k : Idx) :
    christoffelSymbolTimeDerivativeInFrame td covFam frame hframe t x i j k =
      td.dt_apply (fun s => christoffelSymbolInFrame (covFam s) frame hframe x i j k) t := by
  rfl

/-- A named coordinate evolution equation for Christoffel coefficients. -/
def ChristoffelSymbolEvolutionEquationInFrame
    (td : TimeDerivativeData Real A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (rhs : Time -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall t x i j k,
    christoffelSymbolTimeDerivativeInFrame td covFam frame hframe t x i j k =
      rhs t x i j k

theorem christoffelSymbolEvolution_from_equation
    (td : TimeDerivativeData Real A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (rhs : Time -> M -> Idx -> Idx -> Idx -> Real)
    (h_evol : ChristoffelSymbolEvolutionEquationInFrame td covFam frame hframe rhs)
    (t : Time) (x : M) (i j k : Idx) :
    christoffelSymbolTimeDerivativeInFrame td covFam frame hframe t x i j k =
      rhs t x i j k :=
  h_evol t x i j k

/-- Ricci-flow right hand side for Christoffel evolution in a local frame.

`nablaRicLastRaised t x i j k` represents `g^{kl} (nabla_i Ric)_{jl}`.
`nablaRicDirectionRaised t x i j k` represents `g^{kl} (nabla_l Ric)_{ij}`. -/
def ricciFlowChristoffelEvolutionRHSInFrame
    (nablaRicLastRaised nablaRicDirectionRaised : Time -> M -> Idx -> Idx -> Idx -> Real)
    (t : Time) (x : M) (i j k : Idx) : Real :=
  - nablaRicLastRaised t x i j k -
    nablaRicLastRaised t x j i k +
    nablaRicDirectionRaised t x i j k

/-- Coordinate statement of the Ricci-flow Christoffel evolution equation,
parameterized by the raised Ricci-derivative components. -/
def RicciFlowChristoffelSymbolEvolutionEquationInFrame
    (td : TimeDerivativeData Real A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRicLastRaised nablaRicDirectionRaised :
      Time -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  ChristoffelSymbolEvolutionEquationInFrame td covFam frame hframe
    (ricciFlowChristoffelEvolutionRHSInFrame nablaRicLastRaised nablaRicDirectionRaised)

theorem ricciFlow_christoffelSymbolEvolution_from_equation
    (td : TimeDerivativeData Real A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRicLastRaised nablaRicDirectionRaised :
      Time -> M -> Idx -> Idx -> Idx -> Real)
    (h_evol : RicciFlowChristoffelSymbolEvolutionEquationInFrame
      td covFam frame hframe nablaRicLastRaised nablaRicDirectionRaised)
    (t : Time) (x : M) (i j k : Idx) :
    christoffelSymbolTimeDerivativeInFrame td covFam frame hframe t x i j k =
      - nablaRicLastRaised t x i j k -
        nablaRicLastRaised t x j i k +
        nablaRicDirectionRaised t x i j k := by
  simpa [RicciFlowChristoffelSymbolEvolutionEquationInFrame,
    ChristoffelSymbolEvolutionEquationInFrame, ricciFlowChristoffelEvolutionRHSInFrame]
    using h_evol t x i j k

end TimeDerivative

end

end Coordinates
end DifferentialGeometry
