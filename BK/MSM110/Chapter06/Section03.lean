/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RicciFlower contributors
-/

import RicciFlower.RicciFlow.Evolution.CurvatureOperator

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# MSM110 Chapter 6.3

Book companion for "The structure of the curvature evolution equation."  The
mathematical statement interfaces live in
`RicciFlower.RicciFlow.Evolution.CurvatureOperator`; this module preserves the
book labels and names.
-/

namespace BK
namespace MSM110
namespace Chapter06
namespace Section03

noncomputable section

open RicciFlower.RicciFlow
open scoped BigOperators

variable {M : Type*}
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- MSM110 Chapter 6.3, equation `eq:inner_product_for_wedge_two`. -/
theorem eq_inner_product_for_wedge_two
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (U V : Idx -> Idx -> Real) (t : Real) (x : M) :
    twoFormInnerProductInFrame hInv U V t x =
      ∑ i : Idx, ∑ k : Idx, ∑ j : Idx, ∑ l : Idx,
        hInv t x i k * hInv t x j l * U i j * V k l := by
  rfl

/-- MSM110 Chapter 6.3, curvature operator self-adjointness assertion. -/
theorem curvature_operator_self_adjoint
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (Rm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hsymm : Riemann04AlgebraicSymmetriesInFrame Rm04) :
    CurvatureOperatorSelfAdjointInFrame hInv Rm04 :=
  RicciFlower.RicciFlow.curvatureOperator_selfAdjoint_of_riemann_symmetries
    hInv Rm04 hsymm

/-- MSM110 Chapter 6.3, equation `eq:define_square_of_riemann`. -/
theorem eq_define_square_of_riemann
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (Rm04 RmSq : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (h : RiemannSquareComponents hInv Rm04 RmSq) :
    RiemannSquareComponents hInv Rm04 RmSq :=
  h

/-- MSM110 Chapter 6.3, equation `eq:define_lie_square`. -/
theorem eq_define_lie_square
    {A : Type*} [Fintype A]
    (C : A -> A -> A -> Real) (L LSharp : A -> A -> Real)
    (h : LieSquareComponents C L LSharp) :
    LieSquareComponents C L LSharp :=
  h

/-- MSM110 Chapter 6.3, algebraic lemma that `L >= 0` implies `L# >= 0`. -/
theorem lem_lie_square_nonnegative
    {A : Type*} [Fintype A] [DecidableEq A]
    (C : A -> A -> A -> Real) (L : A -> A -> Real)
    (hsymm : ComponentBilinearSymmetric L)
    (hnonneg : ComponentBilinearNonnegative L) :
    ComponentBilinearNonnegative (lieSquareInBasis C L) :=
  RicciFlower.RicciFlow.lieSquare_nonnegative C L hsymm hnonneg

/-- MSM110 Chapter 6.3, equation `eq:lie_bracket_for_wedge_two`. -/
theorem eq_lie_bracket_for_wedge_two
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (U V : Idx -> Idx -> Real) (i j : Idx) :
    twoFormLieBracketInFrame hInv t x U V i j =
      ∑ k : Idx, ∑ l : Idx,
        hInv t x k l * (U i k * V l j - V i k * U l j) := by
  rfl

/-- MSM110 Chapter 6.3, equation `item:lie_square_of_riemann`. -/
theorem item_lie_square_of_riemann
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (Rm04 RmSharp : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (h : RiemannLieSquareComponents hInv Rm04 RmSharp) :
    RiemannLieSquareComponents hInv Rm04 RmSharp :=
  h

/-- MSM110 Chapter 6.3, Theorem
`thm:uhlenbeck_curvature_evolution_two`. -/
theorem thm_uhlenbeck_curvature_evolution_two
    {D : RicciFlower.Realized.RealTimeInterval}
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (pulledRm roughLapD B :
      Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hsquare : RiemannSquareBTensorIdentityInFrame hInv pulledRm B)
    (hsharp : RiemannLieSquareBTensorIdentityInFrame hInv pulledRm B)
    (hevol : UhlenbeckCurvatureEvolutionInFrameOn
      (D := D) pulledRm roughLapD B) :
    CurvatureOperatorEvolutionInFrameOn
      (D := D) hInv pulledRm roughLapD :=
  RicciFlower.RicciFlow.uhlenbeckCurvatureEvolution_slick_of_btensor_identities
    (D := D) hInv pulledRm roughLapD B hsquare hsharp hevol

/-- MSM110 Chapter 6.3, Corollary `cor:pc_opreserved`, positive half. -/
theorem cor_pc_opreserved_positive
    {D : RicciFlower.Realized.RealTimeInterval}
    [TopologicalSpace M] [CompactSpace M]
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (pulledRm roughLapD :
      Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hevol : CurvatureOperatorEvolutionInFrameOn
      (D := D) hInv pulledRm roughLapD)
    (hinit : ∀ x : M,
      CurvatureOperatorPositiveInFrame hInv pulledRm 0 x) :
    ∀ (t : RicciFlower.Realized.RealTimeInterval.RegularTime D) (x : M),
      CurvatureOperatorPositiveInFrame hInv pulledRm (t : Real) x :=
  RicciFlower.RicciFlow.positiveCurvatureOperator_preserved_of_slick_evolution
    (D := D) hInv pulledRm roughLapD hevol hinit

/-- MSM110 Chapter 6.3, Corollary `cor:pc_opreserved`, negative half. -/
theorem cor_pc_opreserved_negative
    {D : RicciFlower.Realized.RealTimeInterval}
    [TopologicalSpace M] [CompactSpace M]
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (pulledRm roughLapD :
      Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hevol : CurvatureOperatorEvolutionInFrameOn
      (D := D) hInv pulledRm roughLapD)
    (hinit : ∀ x : M,
      CurvatureOperatorNegativeInFrame hInv pulledRm 0 x) :
    ∀ (t : RicciFlower.Realized.RealTimeInterval.RegularTime D) (x : M),
      CurvatureOperatorNegativeInFrame hInv pulledRm (t : Real) x :=
  RicciFlower.RicciFlow.negativeCurvatureOperator_preserved_of_slick_evolution
    (D := D) hInv pulledRm roughLapD hevol hinit

end

end Section03
end Chapter06
end MSM110
end BK
