import RicciFlower.RicciFlow.Evolution.Uhlenbeck

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Curvature Operator Evolution, Component Interfaces

This file records MSM110 Chapter 6.3 in the RicciFlower proof layer.  The
statements are algebraic component interfaces for the curvature operator on
two-forms, its ordinary square, its Lie-algebra square, and the resulting
Uhlenbeck-form evolution equation.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open scoped BigOperators

variable {M : Type*}
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- Inner product on component two-forms:
`<U,V> = g^{ik} g^{jl} U_ij V_kl`. -/
def twoFormInnerProductInFrame
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (U V : Idx -> Idx -> Real)
    (t : Real) (x : M) : Real :=
  ∑ i : Idx, ∑ k : Idx, ∑ j : Idx, ∑ l : Idx,
    hInv t x i k * hInv t x j l * U i j * V k l

/-- Curvature operator on two-form components:
`(Rm(U))_ij = - g^{kp} g^{lq} R_ijkl U_pq`. -/
def curvatureOperatorTwoFormInFrame
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (Rm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (U : Idx -> Idx -> Real) (i j : Idx) :
    Real :=
  -∑ k : Idx, ∑ p : Idx, ∑ l : Idx, ∑ q : Idx,
    hInv t x k p * hInv t x l q * Rm04 t x i j k l * U p q

/-- The book's self-adjointness assertion for the curvature operator. -/
def CurvatureOperatorSelfAdjointInFrame
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (Rm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ (t : Real) (x : M) (U V : Idx -> Idx -> Real),
    twoFormInnerProductInFrame hInv
        (curvatureOperatorTwoFormInFrame hInv Rm04 t x U) V t x =
      twoFormInnerProductInFrame hInv U
        (curvatureOperatorTwoFormInFrame hInv Rm04 t x V) t x

/-- Algebraic curvature symmetries needed to make the curvature operator
self-adjoint in the book convention. -/
def Riemann04AlgebraicSymmetriesInFrame
    (Rm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ (t : Real) (x : M) (i j k l : Idx),
    Rm04 t x i j k l = -Rm04 t x j i k l ∧
    Rm04 t x i j k l = -Rm04 t x i j l k ∧
    Rm04 t x i j k l = Rm04 t x k l i j

/-- Self-adjointness of the curvature operator, left as the algebraic
symmetry calculation for a later pass. -/
theorem curvatureOperator_selfAdjoint_of_riemann_symmetries
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (Rm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (_hsymm : Riemann04AlgebraicSymmetriesInFrame Rm04) :
    CurvatureOperatorSelfAdjointInFrame hInv Rm04 := by
  sorry

/-- Components of `Rm^2 = Rm ∘ Rm`:
`(Rm^2)_ijkl = g^{pq} g^{rs} R_ijps R_rqkl`. -/
def riemannSquareInFrame
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (Rm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k l : Idx) : Real :=
  ∑ p : Idx, ∑ q : Idx, ∑ r : Idx, ∑ s : Idx,
    hInv t x p q * hInv t x r s *
      Rm04 t x i j p s * Rm04 t x r q k l

/-- Component assertion for the book formula defining `Rm^2`. -/
def RiemannSquareComponents
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (Rm04 RmSq : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ (t : Real) (x : M) (i j k l : Idx),
    RmSq t x i j k l = riemannSquareInFrame hInv Rm04 t x i j k l

/-- Symmetry of a component bilinear form. -/
def ComponentBilinearSymmetric
    {A : Type*} (L : A -> A -> Real) : Prop :=
  ∀ a b : A, L a b = L b a

/-- Nonnegativity of a component bilinear form. -/
def ComponentBilinearNonnegative
    {A : Type*} [Fintype A] (L : A -> A -> Real) : Prop :=
  ∀ v : A -> Real, 0 ≤ ∑ a : A, ∑ b : A, v a * L a b * v b

/-- Lie-algebra square in a chosen basis:
`(L#)_ab = C_a^{gd} C_b^{ez} L_ge L_dz`. -/
def lieSquareInBasis
    {A : Type*} [Fintype A]
    (C : A -> A -> A -> Real) (L : A -> A -> Real) (a b : A) :
    Real :=
  ∑ g : A, ∑ d : A, ∑ e : A, ∑ z : A,
    C a g d * C b e z * L g e * L d z

/-- Components of the Lie square `L#`. -/
def LieSquareComponents
    {A : Type*} [Fintype A]
    (C : A -> A -> A -> Real) (L LSharp : A -> A -> Real) : Prop :=
  ∀ a b : A, LSharp a b = lieSquareInBasis C L a b

/-- MSM110's algebraic lemma: the Lie square of a nonnegative symmetric
bilinear form is nonnegative. -/
theorem lieSquare_nonnegative
    {A : Type*} [Fintype A] [DecidableEq A]
    (C : A -> A -> A -> Real) (L : A -> A -> Real)
    (_hsymm : ComponentBilinearSymmetric L)
    (_hnonneg : ComponentBilinearNonnegative L) :
    ComponentBilinearNonnegative (lieSquareInBasis C L) := by
  sorry

/-- Lie bracket on two-forms:
`[U,V]_ij = g^{kl}(U_ik V_lj - V_ik U_lj)`. -/
def twoFormLieBracketInFrame
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M)
    (U V : Idx -> Idx -> Real) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    hInv t x k l * (U i k * V l j - V i k * U l j)

/-- Components of the elementary two-form `dx^p wedge dx^q` in the convention
`dx^p wedge dx^q = 1/2 (dx^p tensor dx^q - dx^q tensor dx^p)`. -/
def wedgeTwoBasisComponent (p q i j : Idx) : Real :=
  (1 / 2 : Real) *
    (((if i = p then (1 : Real) else 0) *
        (if j = q then (1 : Real) else 0)) -
      ((if i = q then (1 : Real) else 0) *
        (if j = p then (1 : Real) else 0)))

/-- Structure constants for the two-form Lie algebra in the ordered-pair
coordinate basis.  The book restricts to `i < j`; this component interface keeps
ordered pairs and records the same bracket calculation without choosing an
ordering on `Idx`. -/
def twoFormStructureConstInFrame
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M)
    (ij pq rs : Idx × Idx) : Real :=
  twoFormLieBracketInFrame hInv t x
    (wedgeTwoBasisComponent pq.1 pq.2)
    (wedgeTwoBasisComponent rs.1 rs.2)
    ij.1 ij.2

/-- Components of the curvature-operator Lie square `Rm#`. -/
def riemannLieSquareInFrame
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (Rm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k l : Idx) : Real :=
  ∑ p : Idx, ∑ q : Idx, ∑ u : Idx, ∑ v : Idx,
  ∑ r : Idx, ∑ s : Idx, ∑ w : Idx, ∑ z : Idx,
    Rm04 t x p q u v * Rm04 t x r s w z *
      twoFormStructureConstInFrame hInv t x (i, j) (p, q) (r, s) *
      twoFormStructureConstInFrame hInv t x (l, k) (u, v) (w, z)

/-- Component assertion for equation `item:lie_square_of_riemann`. -/
def RiemannLieSquareComponents
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (Rm04 RmSharp : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ (t : Real) (x : M) (i j k l : Idx),
    RmSharp t x i j k l = riemannLieSquareInFrame hInv Rm04 t x i j k l

/-- Algebraic identity used in MSM110:
`(Rm^2)_abcd = 2 (B_abcd - B_abdc)`. -/
def RiemannSquareBTensorIdentityInFrame
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (pulledRm B : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ (t : Real) (x : M) (a b c d : Idx),
    riemannSquareInFrame hInv pulledRm t x a b c d =
      2 * (B t x a b c d - B t x a b d c)

/-- Algebraic identity used in MSM110:
`(Rm#)_abcd = 2 (B_acbd - B_adbc)`. -/
def RiemannLieSquareBTensorIdentityInFrame
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (pulledRm B : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ (t : Real) (x : M) (a b c d : Idx),
    riemannLieSquareInFrame hInv pulledRm t x a b c d =
      2 * (B t x a c b d - B t x a d b c)

/-- RHS of the slick Uhlenbeck curvature evolution equation:
`Delta_D Rm + Rm^2 + Rm#`. -/
def curvatureOperatorEvolutionRHSInFrame
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (pulledRm roughLapD :
      Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (a b c d : Idx) : Real :=
  roughLapD t x a b c d +
    riemannSquareInFrame hInv pulledRm t x a b c d +
    riemannLieSquareInFrame hInv pulledRm t x a b c d

/-- MSM110 equation `eq:evolution_of_riemann_minus_slick`, component form:
`partial_t Rm = Delta_D Rm + Rm^2 + Rm#`. -/
def CurvatureOperatorEvolutionInFrameOn
    {D : Realized.RealTimeInterval}
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (pulledRm roughLapD :
      Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M)
    (a b c d : Idx),
    HasDerivWithinAt
      (fun s : Real => pulledRm s x a b c d)
      (curvatureOperatorEvolutionRHSInFrame hInv pulledRm roughLapD
        (t : Real) x a b c d)
      D.carrier
      (t : Real)

/-- MSM110 Theorem `thm:uhlenbeck_curvature_evolution_two`, component form.

The remaining proof is algebraic: rewrite the `B`-tensor RHS from Section 6.2
as `Rm^2 + Rm#` using the first Bianchi identity and the two-form Lie bracket
structure constants. -/
theorem uhlenbeckCurvatureEvolution_slick_of_btensor_identities
    {D : Realized.RealTimeInterval}
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (pulledRm roughLapD B :
      Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (_hsquare : RiemannSquareBTensorIdentityInFrame hInv pulledRm B)
    (_hsharp : RiemannLieSquareBTensorIdentityInFrame hInv pulledRm B)
    (_hevol : UhlenbeckCurvatureEvolutionInFrameOn
      (D := D) pulledRm roughLapD B) :
    CurvatureOperatorEvolutionInFrameOn
      (D := D) hInv pulledRm roughLapD := by
  sorry

/-- Positivity of the curvature operator at a spacetime point. -/
def CurvatureOperatorPositiveInFrame
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (Rm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) : Prop :=
  ∀ U : Idx -> Idx -> Real, U ≠ 0 ->
    0 <
      twoFormInnerProductInFrame hInv U
        (curvatureOperatorTwoFormInFrame hInv Rm04 t x U) t x

/-- Negativity of the curvature operator at a spacetime point. -/
def CurvatureOperatorNegativeInFrame
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (Rm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) : Prop :=
  ∀ U : Idx -> Idx -> Real, U ≠ 0 ->
    twoFormInnerProductInFrame hInv U
        (curvatureOperatorTwoFormInFrame hInv Rm04 t x U) t x < 0

/-- MSM110 Corollary `cor:pc_opreserved`, positive-curvature-operator half.

The proof belongs to the tensor maximum-principle layer after the Section 6.3
algebra has been connected to the Chapter 4 system maximum principle. -/
theorem positiveCurvatureOperator_preserved_of_slick_evolution
    {D : Realized.RealTimeInterval}
    [TopologicalSpace M] [CompactSpace M]
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (pulledRm roughLapD :
      Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (_hevol : CurvatureOperatorEvolutionInFrameOn
      (D := D) hInv pulledRm roughLapD)
    (_hinit : ∀ x : M,
      CurvatureOperatorPositiveInFrame hInv pulledRm 0 x) :
    ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      CurvatureOperatorPositiveInFrame hInv pulledRm (t : Real) x := by
  sorry

/-- MSM110 Corollary `cor:pc_opreserved`, negative-curvature-operator half. -/
theorem negativeCurvatureOperator_preserved_of_slick_evolution
    {D : Realized.RealTimeInterval}
    [TopologicalSpace M] [CompactSpace M]
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (pulledRm roughLapD :
      Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (_hevol : CurvatureOperatorEvolutionInFrameOn
      (D := D) hInv pulledRm roughLapD)
    (_hinit : ∀ x : M,
      CurvatureOperatorNegativeInFrame hInv pulledRm 0 x) :
    ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      CurvatureOperatorNegativeInFrame hInv pulledRm (t : Real) x := by
  sorry

end RicciFlow
end RicciFlower
