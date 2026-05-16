import RicciFlower.RicciFlow.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Uhlenbeck's Trick, Component Interfaces

This file records MSM110 Chapter 6.2 in the RicciFlower proof layer.  The
statements are component-level on a fixed finite frame so later work can plug in
the actual vector-bundle isomorphism, pulled-back connection, and Riemann
curvature producers without changing the book-facing shape.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open scoped BigOperators

variable {M : Type*}
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- Ricci-flow metric component equation in a fixed frame:
`partial_t g_ij = -2 Ric_ij`. -/
def MetricCompRicciFlowInFrameOn
    {D : Realized.RealTimeInterval}
    (metricComp Ric : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    HasDerivWithinAt
      (fun s : Real => metricComp s x i j)
      (-2 * Ric (t : Real) x i j)
      D.carrier
      (t : Real)

/-- Frame-component ODE from `d e_a / dt = Rc(e_a)`.

Here `ricciOneUp t x l k` denotes the component `R_l^k`. -/
def FrameRicciODEInFrameOn
    {D : Realized.RealTimeInterval}
    (frameComp ricciOneUp : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (a k : Idx),
    HasDerivWithinAt
      (fun s : Real => frameComp s x a k)
      (∑ l : Idx, ricciOneUp (t : Real) x l k * frameComp (t : Real) x a l)
      D.carrier
      (t : Real)

/-- Compatibility saying that the one-up Ricci tensor represents the metric
endomorphism associated to `Ric`.  This is the algebraic input behind
`g(Rc v,w) = Ric(v,w) = g(v,Rc w)`. -/
def RicciEndomorphismCompatibleInFrame
    (metricComp Ric ricciOneUp : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall (t : Real) (x : M) (v w : Idx -> Real),
    (∑ l : Idx, ∑ k : Idx, ∑ j : Idx,
        v l * ricciOneUp t x l k * w j * metricComp t x k j) =
      (∑ i : Idx, ∑ j : Idx, v i * w j * Ric t x i j) /\
    (∑ i : Idx, ∑ l : Idx, ∑ k : Idx,
        v i * w l * ricciOneUp t x l k * metricComp t x i k) =
      (∑ i : Idx, ∑ j : Idx, v i * w j * Ric t x i j)

/-- Gram component of a moving frame with respect to a time-dependent metric. -/
def movingFrameGramInFrame
    (metricComp frameComp : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (a b : Idx) : Real :=
  ∑ i : Idx, ∑ j : Idx,
    frameComp t x a i * frameComp t x b j * metricComp t x i j

/-- The moving-frame Gram matrix has zero time derivative. -/
def MovingFrameGramConstantOn
    {D : Realized.RealTimeInterval}
    (metricComp frameComp : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (a b : Idx),
    HasDerivWithinAt
      (fun s : Real => movingFrameGramInFrame metricComp frameComp s x a b)
      0
      D.carrier
      (t : Real)

/-- MSM110 Lemma `lem:evolving_frame_calculation`, component form. -/
theorem evolvingFrameGram_constant_of_ricciFlow
    {D : Realized.RealTimeInterval}
    (metricComp Ric frameComp ricciOneUp :
      Real -> M -> Idx -> Idx -> Real)
    (_hmetric : MetricCompRicciFlowInFrameOn (D := D) metricComp Ric)
    (_hframe : FrameRicciODEInFrameOn (D := D) frameComp ricciOneUp)
    (_hcompat : RicciEndomorphismCompatibleInFrame
      metricComp Ric ricciOneUp) :
    MovingFrameGramConstantOn (D := D) metricComp frameComp := by
  sorry

/-- Orthonormality of a moving frame in component form. -/
def MovingFrameOrthonormalInFrame
    (metricComp frameComp : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) : Prop :=
  forall a b : Idx,
    movingFrameGramInFrame metricComp frameComp t x a b =
      if a = b then 1 else 0

/-- MSM110 corollary after `lem:evolving_frame_calculation`: an initially
orthonormal evolving frame remains orthonormal. -/
theorem evolvingFrame_orthonormal_of_initial
    {D : Realized.RealTimeInterval}
    (metricComp frameComp : Real -> M -> Idx -> Idx -> Real)
    (_hconst : MovingFrameGramConstantOn (D := D) metricComp frameComp)
    (_hinit : forall x : M,
      MovingFrameOrthonormalInFrame metricComp frameComp 0 x) :
    forall (t : Realized.RealTimeInterval.RegularTime D) (x : M),
      MovingFrameOrthonormalInFrame metricComp frameComp (t : Real) x := by
  sorry

/-- Components of Uhlenbeck's bundle isomorphism ODE
`partial_t iota_a^k = R_l^k iota_a^l`. -/
def BundleIsomorphismODEInFrameOn
    {D : Realized.RealTimeInterval}
    (iota ricciOneUp : Real -> M -> Idx -> Idx -> Real) : Prop :=
  FrameRicciODEInFrameOn (D := D) iota ricciOneUp

/-- Pullback metric components `h_ab = g(iota e_a, iota e_b)`. -/
def uhlenbeckPullbackMetricCompInFrame
    (metricComp iota : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (a b : Idx) : Real :=
  movingFrameGramInFrame metricComp iota t x a b

/-- Components of the pullback metric `h = iota^* g`. -/
def UhlenbeckPullbackMetricComponents
    (metricComp iota hComp : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall (t : Real) (x : M) (a b : Idx),
    hComp t x a b =
      uhlenbeckPullbackMetricCompInFrame metricComp iota t x a b

/-- Uhlenbeck isometry claim, in the useful component form that the pulled-back
metric is time-constant under Ricci flow and the isomorphism ODE. -/
theorem uhlenbeck_pullbackMetric_constant_of_ricciFlow
    {D : Realized.RealTimeInterval}
    (metricComp Ric iota ricciOneUp :
      Real -> M -> Idx -> Idx -> Real)
    (hmetric : MetricCompRicciFlowInFrameOn (D := D) metricComp Ric)
    (hiota : BundleIsomorphismODEInFrameOn (D := D) iota ricciOneUp)
    (hcompat : RicciEndomorphismCompatibleInFrame
      metricComp Ric ricciOneUp) :
    MovingFrameGramConstantOn (D := D) metricComp iota :=
  evolvingFrameGram_constant_of_ricciFlow
    (D := D) metricComp Ric iota ricciOneUp hmetric hiota hcompat

/-- Pullback of the lowered Riemann tensor:
`(iota^* Rm)_{abcd} = iota_a^i iota_b^j iota_c^k iota_d^l R_{ijkl}`. -/
def uhlenbeckPullbackRmInFrame
    (iota : Real -> M -> Idx -> Idx -> Real)
    (Rm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (a b c d : Idx) : Real :=
  ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
    iota t x a i * iota t x b j * iota t x c k * iota t x d l *
      Rm04 t x i j k l

/-- Component assertion for equation `eq:uhlenbeck_pullback_of_riemann`. -/
def UhlenbeckPullbackRmComponents
    (iota : Real -> M -> Idx -> Idx -> Real)
    (Rm04 pulledRm : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Real) (x : M) (a b c d : Idx),
    pulledRm t x a b c d =
      uhlenbeckPullbackRmInFrame iota Rm04 t x a b c d

/-- Uhlenbeck's quadratic `B_abcd = h^eg h^fh R_aebf R_cgdh`. -/
def uhlenbeckBTensorInFrame
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (pulledRm : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (a b c d : Idx) : Real :=
  ∑ e : Idx, ∑ g : Idx, ∑ f : Idx, ∑ r : Idx,
    hInv t x e g * hInv t x f r *
      pulledRm t x a e b f * pulledRm t x c g d r

/-- Component assertion for the Uhlenbeck `B` tensor. -/
def UhlenbeckBTensorComponents
    (hInv : Real -> M -> Idx -> Idx -> Real)
    (pulledRm B : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Real) (x : M) (a b c d : Idx),
    B t x a b c d = uhlenbeckBTensorInFrame hInv pulledRm t x a b c d

/-- Pullback of a rough Riemann Laplacian through `iota`.  This records the
book step `nabla_D iota = 0`, hence `iota^*(Delta Rm) = Delta_D(iota^* Rm)`. -/
def UhlenbeckLaplacianPullbackComponents
    (iota : Real -> M -> Idx -> Idx -> Real)
    (roughLapRm04 roughLapD :
      Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Real) (x : M) (a b c d : Idx),
    roughLapD t x a b c d =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        iota t x a i * iota t x b j * iota t x c k * iota t x d l *
          roughLapRm04 t x i j k l

/-- Ricci-drift term in the pre-Uhlenbeck lowered Riemann evolution equation. -/
def riemann04RicciDriftInFrame
    (ricciOneUp : Real -> M -> Idx -> Idx -> Real)
    (Rm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k l : Idx) : Real :=
  (∑ p : Idx, ricciOneUp t x i p * Rm04 t x p j k l) +
    (∑ p : Idx, ricciOneUp t x j p * Rm04 t x i p k l) +
    (∑ p : Idx, ricciOneUp t x k p * Rm04 t x i j p l) +
    (∑ p : Idx, ricciOneUp t x l p * Rm04 t x i j k p)

/-- Riemann evolution before Uhlenbeck's cancellation of Ricci-drift terms. -/
def Riemann04BTensorWithRicciDriftEvolutionInFrameOn
    {D : Realized.RealTimeInterval}
    (Rm04 roughLapRm04 B :
      Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (ricciOneUp : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M)
    (i j k l : Idx),
    HasDerivWithinAt
      (fun s : Real => Rm04 s x i j k l)
      (roughLapRm04 (t : Real) x i j k l +
        2 * (B (t : Real) x i j k l - B (t : Real) x i j l k +
          B (t : Real) x i k j l - B (t : Real) x i l j k) -
        riemann04RicciDriftInFrame ricciOneUp Rm04 (t : Real) x i j k l)
      D.carrier
      (t : Real)

/-- RHS of Uhlenbeck's pulled-back curvature evolution equation. -/
def uhlenbeckCurvatureEvolutionRHSInFrame
    (roughLapD B : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (a b c d : Idx) : Real :=
  roughLapD t x a b c d +
    2 * (B t x a b c d - B t x a b d c +
      B t x a c b d - B t x a d b c)

/-- Uhlenbeck curvature evolution equation:
`partial_t R_abcd = Delta_D R_abcd + 2(B_abcd - B_abdc + B_acbd - B_adbc)`. -/
def UhlenbeckCurvatureEvolutionInFrameOn
    {D : Realized.RealTimeInterval}
    (pulledRm roughLapD B :
      Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M)
    (a b c d : Idx),
    HasDerivWithinAt
      (fun s : Real => pulledRm s x a b c d)
      (uhlenbeckCurvatureEvolutionRHSInFrame roughLapD B
        (t : Real) x a b c d)
      D.carrier
      (t : Real)

/-- MSM110 Lemma `lem:uhlenbeck_curvature_evolution_one`, component form. -/
theorem uhlenbeckCurvatureEvolutionInFrameOn_of_ricciFlow
    {D : Realized.RealTimeInterval}
    (iota : Real -> M -> Idx -> Idx -> Real)
    (Rm04 pulledRm roughLapRm04 roughLapD B :
      Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (ricciOneUp : Real -> M -> Idx -> Idx -> Real)
    (_hiota : BundleIsomorphismODEInFrameOn (D := D) iota ricciOneUp)
    (_hpull : UhlenbeckPullbackRmComponents iota Rm04 pulledRm)
    (_hlap : UhlenbeckLaplacianPullbackComponents iota roughLapRm04 roughLapD)
    (_hrm : Riemann04BTensorWithRicciDriftEvolutionInFrameOn
      (D := D) Rm04 roughLapRm04 B ricciOneUp) :
    UhlenbeckCurvatureEvolutionInFrameOn
      (D := D) pulledRm roughLapD B := by
  sorry

end RicciFlow
end RicciFlower
