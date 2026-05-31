import RicciFlower.RicciFlow.Evolution.Connection.Components

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Lowered connection-pairing evolution

Koszul and Ricci-flow lowered pairing identities for connection variation.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Components

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {u : Set M}

/-- The Koszul/Levi-Civita variation identity specialized to Ricci flow:
the lowered connection derivative is
`-∇_i Ric_jl - ∇_j Ric_il + ∇_l Ric_ij`. -/
def KoszulConnectionVariationInFrame
    (pairDt nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall t x i j l,
    pairDt t x i j l =
      christoffelVariationLoweredRHSInFrame nablaRic t x i j l

/-- The lowered pairing variation formula for the connection along Ricci flow.

The metric is frozen at the differentiating time `t`; only the connection
family varies in the scalar function. -/
def ConnectionVariationPairingEquationInFrameOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j l : Idx),
    HasDerivWithinAt
      (fun s : Real =>
        (S.family.metric (t : Real)).inner x (frame l x)
          ((S.family.connection s (frame j) x) (frame i x)))
      (christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l)
      D.carrier
      (t : Real)

/-- Local lowered pairing variation equation. -/
def ConnectionVariationPairingEquationInFrameOnLocal
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall i j l : Idx,
      HasDerivWithinAt
        (fun s : Real =>
          (S.family.metric (t : Real)).inner x (frame l x)
            ((S.family.connection s (frame j) x) (frame i x)))
        (christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l)
        D.carrier
        (t : Real)

/-- Component identity behind the general first variation formula, obtained
by differentiating the finite-difference Koszul identity in time. -/
theorem connectionPairDt_eq_metricVariationRHS
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (pairDt metricCovDerivDt : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hvarDiff :
      VariableMetricConnectionDiffDerivativeInFrameOnLocal
        (I := I) S frame u pairDt)
    (hmetric :
      MetricCovDerivDerivativeComponentsInFrameOnLocal
        (I := I) S frame u metricCovDerivDt)
    (hunique : forall t : Realized.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real))
    (t : Realized.RealTimeInterval.RegularTime D) (x : M) (hx : x ∈ u)
    (i j l : Idx) :
    pairDt (t : Real) x i j l =
      connectionVariationLoweredRHSFromMetricVariationInFrame
        metricCovDerivDt (t : Real) x i j l := by
  have htcarrier : (t : Real) ∈ D.carrier := D.regular_subset t.2
  have hL :
      HasDerivWithinAt
        (fun s : Real =>
          2 * connectionDiffLoweredInFrame (I := I) S frame s (t : Real) s x i j l)
        (2 * pairDt (t : Real) x i j l)
        D.carrier
        (t : Real) := by
    simpa using
      HasDerivWithinAt.const_mul (2 : Real) (hvarDiff t x hx i j l)
  have hL_as_R :
      HasDerivWithinAt
        (fun s : Real =>
          finiteDifferenceKoszulRHSInFrame (I := I) S frame (t : Real) s x i j l)
        (2 * pairDt (t : Real) x i j l)
        D.carrier
        (t : Real) := by
    refine hL.congr ?_ ?_
    · intro s hs
      exact (finiteDifferenceKoszulInFrame
        (I := I) S hS frame hframe hu hx htcarrier hs i j l
        ).symm
    · exact (finiteDifferenceKoszulInFrame
        (I := I) S hS frame hframe hu hx htcarrier htcarrier i j l).symm
  have hR :
      HasDerivWithinAt
        (fun s : Real =>
          finiteDifferenceKoszulRHSInFrame (I := I) S frame (t : Real) s x i j l)
        (metricCovDerivDt (t : Real) x i j l +
          metricCovDerivDt (t : Real) x j i l -
            metricCovDerivDt (t : Real) x l i j)
        D.carrier
        (t : Real) := by
    unfold finiteDifferenceKoszulRHSInFrame
    exact ((hmetric t x hx i j l).add (hmetric t x hx j i l)).sub
      (hmetric t x hx l i j)
  have hderiv :
      2 * pairDt (t : Real) x i j l =
        metricCovDerivDt (t : Real) x i j l +
          metricCovDerivDt (t : Real) x j i l -
            metricCovDerivDt (t : Real) x l i j := by
    exact (hL_as_R.derivWithin (hunique t)).symm.trans
      (hR.derivWithin (hunique t))
  unfold connectionVariationLoweredRHSFromMetricVariationInFrame
  linarith

/-- General first variation of Christoffel symbols in lowered-pairing form:
`pairDt = 1/2 (nabla_i h_jl + nabla_j h_il - nabla_l h_ij)`. -/
theorem connectionVariationPairing_of_metricVariation
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (pairDt metricCovDerivDt : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hpair :
      ConnectionPairingDerivativeInFrameOnLocal
        (I := I) S frame u pairDt)
    (hvarDiff :
      VariableMetricConnectionDiffDerivativeInFrameOnLocal
        (I := I) S frame u pairDt)
    (hmetric :
      MetricCovDerivDerivativeComponentsInFrameOnLocal
        (I := I) S frame u metricCovDerivDt)
    (hunique : forall t : Realized.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real)) :
    forall (t : Realized.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
      forall i j l : Idx,
        HasDerivWithinAt
          (fun s : Real =>
            (S.family.metric (t : Real)).inner x (frame l x)
              ((S.family.connection s (frame j) x) (frame i x)))
          (connectionVariationLoweredRHSFromMetricVariationInFrame
            metricCovDerivDt (t : Real) x i j l)
          D.carrier
          (t : Real) := by
  intro t x hx i j l
  exact (hpair t x hx i j l).congr_deriv
    (connectionPairDt_eq_metricVariationRHS
      (I := I) S hS frame hframe hu pairDt metricCovDerivDt
      hvarDiff hmetric hunique t x hx i j l)

/-- Ricci-flow specialization of the general Christoffel first variation,
using `partial_t g = -2 Ric`. -/
theorem connectionVariationPairing_of_ricciFlow
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (pairDt metricCovDerivDt nablaRic :
      Real -> M -> Idx -> Idx -> Idx -> Real)
    (hpair :
      ConnectionPairingDerivativeInFrameOnLocal
        (I := I) S frame u pairDt)
    (hvarDiff :
      VariableMetricConnectionDiffDerivativeInFrameOnLocal
        (I := I) S frame u pairDt)
    (hmetric :
      MetricCovDerivDerivativeComponentsInFrameOnLocal
        (I := I) S frame u metricCovDerivDt)
    (hmetricRicci :
      MetricCovDerivDerivativeIsRicciFlowInFrame metricCovDerivDt nablaRic)
    (hunique : forall t : Realized.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real)) :
    ConnectionVariationPairingEquationInFrameOnLocal
      (I := I) S frame u nablaRic := by
  intro t x hx i j l
  have hmetricVar :=
    connectionVariationPairing_of_metricVariation
      (I := I) S hS frame hframe hu pairDt metricCovDerivDt
      hpair hvarDiff hmetric hunique t x hx i j l
  refine hmetricVar.congr_deriv ?_
  unfold connectionVariationLoweredRHSFromMetricVariationInFrame
    christoffelVariationLoweredRHSInFrame
  rw [hmetricRicci (t : Real) x i j l,
    hmetricRicci (t : Real) x j i l,
    hmetricRicci (t : Real) x l i j]
  ring

/-- Lemma 6.2, lowered-pairing form, from the connection derivative and the
Ricci-flow Koszul variation identity. -/
theorem connectionVariationPairing_of_koszul
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (pairDt nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hdt : ConnectionPairingDerivativeInFrameOn (I := I) S frame pairDt)
    (hkoszul : KoszulConnectionVariationInFrame (M := M) pairDt nablaRic) :
    ConnectionVariationPairingEquationInFrameOn
      (I := I) S frame nablaRic := by
  intro t x i j l
  exact (hdt t x i j l).congr_deriv (hkoszul (t : Real) x i j l)

end Components

end RicciFlow
end RicciFlower
