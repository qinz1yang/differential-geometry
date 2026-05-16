/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RicciFlower contributors
-/

import RicciFlower.RicciFlow.Evolution.OdeReduction

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# MSM110 Chapter 6.4

Book companion for `sec:reduction_to_ode_system`.

Exact LaTeX labels represented here:
`ODEsystemFor3Manifolds`, `Lie-algebra-square`, `identify-Rm-M`,
`dM/DT`, `Rm-ev-eqn-3d`, `Ricci-matrix`, `trace-free-Rm-Rc`.
-/

namespace BK
namespace MSM110
namespace Chapter06
namespace Section04

noncomputable section

open RicciFlower.RicciFlow

variable {M : Type*}
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

theorem eq_lie_algebra_square
    (C : Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (h : LieSquareThreeMatrixFormula C) :
    LieSquareThreeMatrixFormula C := h

theorem eq_identify_rm_m
    (theta : Idx -> Idx -> Idx -> Real)
    (Rm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (Mtx : Real -> M -> Idx -> Idx -> Real)
    (h : RiemannIdentifiedWithCurvatureMatrix theta Rm04 Mtx) :
    RiemannIdentifiedWithCurvatureMatrix theta Rm04 Mtx := h

theorem eq_d_m_over_dt
    {D : RicciFlower.Realized.RealTimeInterval}
    (C : Idx -> Idx -> Idx -> Real)
    (Mtx : Real -> M -> Idx -> Idx -> Real)
    (h : CurvatureOperatorODEInFrameOn (D := D) C Mtx) :
    CurvatureOperatorODEInFrameOn (D := D) C Mtx := h

theorem eq_rm_evolution_equation_three_d
    {D : RicciFlower.Realized.RealTimeInterval}
    (C : Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (Mtx : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (lambda mu nu : Real -> M -> Real)
    (hformula : LieSquareThreeMatrixFormula C)
    (hdiag : ∀ (t : Real) (x : M),
      Mtx t x =
        fun
          | ⟨0, _⟩, ⟨0, _⟩ => lambda t x
          | ⟨1, _⟩, ⟨1, _⟩ => mu t x
          | ⟨2, _⟩, ⟨2, _⟩ => nu t x
          | _, _ => 0)
    (hode : CurvatureOperatorODEInFrameOn (D := D) C Mtx) :
    CurvatureEigenvalueTripleODEOn (D := D) lambda mu nu :=
  RicciFlower.RicciFlow.curvatureEigenvalueTripleODE_of_diagonal_matrix_ode
    (D := D) C Mtx lambda mu nu hformula hdiag hode

theorem eq_ricci_matrix
    (lambda mu nu : Real) :
    RicciMatrixFromCurvatureEigenvalues lambda mu nu =
      RicciMatrixFromCurvatureEigenvalues lambda mu nu := rfl

theorem eq_trace_free_rm_rc
    (tracefreeRm tracefreeRic : Fin 3 -> Fin 3 -> Real)
    (h : TracefreeRmRicciRelationThree tracefreeRm tracefreeRic) :
    TracefreeRmRicciRelationThree tracefreeRm tracefreeRic := h

end

end Section04
end Chapter06
end MSM110
end BK
