import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Sqrt
import RicciFlower.Realized.TimeInterval

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Reduction to the Associated ODE System

MSM110 Chapter 6.4, component-level statement interfaces.

LaTeX labels covered here:
`ODEsystemFor3Manifolds`, `Lie-algebra-square`, `identify-Rm-M`, `dM/DT`,
`Rm-ev-eqn-3d`, `Ricci-matrix`, and `trace-free-Rm-Rc`.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open scoped BigOperators

variable {M : Type*}
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- Lie-algebra square in a chosen basis, local to the ODE-reduction scaffold. -/
def odeLieSquareInBasis
    (C : Idx -> Idx -> Idx -> Real) (L : Idx -> Idx -> Real)
    (i j : Idx) : Real :=
  ∑ g : Idx, ∑ d : Idx, ∑ e : Idx, ∑ z : Idx,
    C i g d * C j e z * L g e * L d z

/-- Matrix square plus Lie square in a fixed basis. -/
def curvatureOperatorReactionInBasis
    (C : Idx -> Idx -> Idx -> Real)
    (Mtx : Idx -> Idx -> Real) (i j : Idx) : Real :=
  (∑ k : Idx, Mtx i k * Mtx k j) + odeLieSquareInBasis C Mtx i j

/-- ODE `dM/dt = M^2 + M#` in a fixed basis of two-forms. -/
def CurvatureOperatorODEInFrameOn
    {D : Realized.RealTimeInterval}
    (C : Idx -> Idx -> Idx -> Real)
    (Mtx : Real -> M -> Idx -> Idx -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    HasDerivWithinAt
      (fun s : Real => Mtx s x i j)
      (curvatureOperatorReactionInBasis C (Mtx (t : Real) x) i j)
      D.carrier
      (t : Real)

/-- In dimension three, the Lie-square matrix displayed in
`eq:lie_minus_algebra_minus_square`. -/
def lieSquareThreeMatrix
    (a b c d e f : Real) : Fin 3 -> Fin 3 -> Real
  | ⟨0, _⟩, ⟨0, _⟩ => d * f - e ^ 2
  | ⟨0, _⟩, ⟨1, _⟩ => c * e - b * f
  | ⟨0, _⟩, ⟨2, _⟩ => b * e - c * d
  | ⟨1, _⟩, ⟨0, _⟩ => c * e - b * f
  | ⟨1, _⟩, ⟨1, _⟩ => a * f - c ^ 2
  | ⟨1, _⟩, ⟨2, _⟩ => b * c - a * e
  | ⟨2, _⟩, ⟨0, _⟩ => b * e - c * d
  | ⟨2, _⟩, ⟨1, _⟩ => b * c - a * e
  | ⟨2, _⟩, ⟨2, _⟩ => a * d - b ^ 2

/-- Book display `eq:lie_minus_algebra_minus_square`, as a predicate so later
work can identify the structure constants of the Hodge-star basis. -/
def LieSquareThreeMatrixFormula
    (C : Fin 3 -> Fin 3 -> Fin 3 -> Real) : Prop :=
  ∀ a b c d e f : Real,
    odeLieSquareInBasis C
      (fun
        | ⟨0, _⟩, ⟨0, _⟩ => a
        | ⟨0, _⟩, ⟨1, _⟩ => b
        | ⟨0, _⟩, ⟨2, _⟩ => c
        | ⟨1, _⟩, ⟨0, _⟩ => b
        | ⟨1, _⟩, ⟨1, _⟩ => d
        | ⟨1, _⟩, ⟨2, _⟩ => e
        | ⟨2, _⟩, ⟨0, _⟩ => c
        | ⟨2, _⟩, ⟨1, _⟩ => e
        | ⟨2, _⟩, ⟨2, _⟩ => f) =
    lieSquareThreeMatrix a b c d e f

/-- The curvature operator is represented by the matrix `Mtx` in the chosen
orthonormal basis of two-forms:
`<R(e_i,e_j)e_k,e_l> = M_pq theta^p_ij theta^q_lk`. -/
def RiemannIdentifiedWithCurvatureMatrix
    (theta : Idx -> Idx -> Idx -> Real)
    (Rm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (Mtx : Real -> M -> Idx -> Idx -> Real) : Prop :=
  ∀ (t : Real) (x : M) (i j k l : Idx),
    Rm04 t x i j k l =
      ∑ p : Idx, ∑ q : Idx, Mtx t x p q * theta p i j * theta q l k

/-- The three-dimensional diagonal eigenvalue ODE
`lambda' = lambda^2 + mu nu`, etc. -/
def CurvatureEigenvalueTripleODEOn
    {D : Realized.RealTimeInterval}
    (lambda mu nu : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt (fun s : Real => lambda s x)
        (lambda (t : Real) x ^ 2 + mu (t : Real) x * nu (t : Real) x)
        D.carrier (t : Real) ∧
    HasDerivWithinAt (fun s : Real => mu s x)
        (mu (t : Real) x ^ 2 + lambda (t : Real) x * nu (t : Real) x)
        D.carrier (t : Real) ∧
    HasDerivWithinAt (fun s : Real => nu s x)
        (nu (t : Real) x ^ 2 + lambda (t : Real) x * mu (t : Real) x)
        D.carrier (t : Real)

/-- Ricci matrix in terms of curvature-operator eigenvalues. -/
def RicciMatrixFromCurvatureEigenvalues
    (lambda mu nu : Real) : Fin 3 -> Fin 3 -> Real
  | ⟨0, _⟩, ⟨0, _⟩ => (mu + nu) / 2
  | ⟨1, _⟩, ⟨1, _⟩ => (lambda + nu) / 2
  | ⟨2, _⟩, ⟨2, _⟩ => (lambda + mu) / 2
  | _, _ => 0

/-- Trace-free relation `Rm^0 = -2 Rc^0` in dimension three, recorded in
component form for the chosen diagonal basis. -/
def TracefreeRmRicciRelationThree
    (tracefreeRm tracefreeRic : Fin 3 -> Fin 3 -> Real) : Prop :=
  ∀ i j : Fin 3, tracefreeRm i j = -2 * tracefreeRic i j

/-- The slick Uhlenbeck curvature-operator PDE from Section 6.3, kept as a
local assumption interface for the Section 6.4 reduction. -/
def CurvatureOperatorSlickEvolutionInFrameOn
    {D : Realized.RealTimeInterval}
    (pulledRm roughLapD reaction :
      Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M)
    (a b c d : Idx),
    HasDerivWithinAt
      (fun s : Real => pulledRm s x a b c d)
      (roughLapD (t : Real) x a b c d +
        reaction (t : Real) x a b c d)
      D.carrier
      (t : Real)

/-- MSM110 Section 6.4: the curvature-operator PDE yields the associated ODE
system in each fiber after the Uhlenbeck-frame reduction. -/
theorem curvatureOperatorPDE_reduces_to_ode_system
    {D : Realized.RealTimeInterval}
    (C : Idx -> Idx -> Idx -> Real)
    (pulledRm roughLapD reaction :
      Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (Mtx : Real -> M -> Idx -> Idx -> Real)
    (_hevol : CurvatureOperatorSlickEvolutionInFrameOn
      (D := D) pulledRm roughLapD reaction)
    (_hidentify :
      RiemannIdentifiedWithCurvatureMatrix
        (fun p i j => if p = i then (if j = i then 0 else 1) else 0)
        pulledRm Mtx) :
    CurvatureOperatorODEInFrameOn (D := D) C Mtx := by
  sorry

/-- MSM110 equation `eq:rm_evolution_equation_three_d`, as an eigenvalue ODE
producer from the matrix ODE and diagonalization assumptions. -/
theorem curvatureEigenvalueTripleODE_of_diagonal_matrix_ode
    {D : Realized.RealTimeInterval}
    (C : Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (Mtx : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (lambda mu nu : Real -> M -> Real)
    (_hformula : LieSquareThreeMatrixFormula C)
    (_hdiag : ∀ (t : Real) (x : M),
      Mtx t x =
        fun
          | ⟨0, _⟩, ⟨0, _⟩ => lambda t x
          | ⟨1, _⟩, ⟨1, _⟩ => mu t x
          | ⟨2, _⟩, ⟨2, _⟩ => nu t x
          | _, _ => 0)
    (_hode : CurvatureOperatorODEInFrameOn (D := D) C Mtx) :
    CurvatureEigenvalueTripleODEOn (D := D) lambda mu nu := by
  sorry

end RicciFlow
end RicciFlower
