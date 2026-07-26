import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Christoffel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Connection evolution producers

Book-facing producers for Christoffel evolution from metric variation, smoothness, inverse-metric data, Ricci flow, and Koszul inputs.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

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

/-- General metric-variation Christoffel formula in raised component form. -/
theorem christoffelMetricVariationEquationInFrameOn_of_metricVariation
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (pairDt metricCovDerivDt : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (hpair :
      ConnectionPairingDerivativeInFrameOnLocal
        (I := I) S frame u pairDt)
    (hvarDiff :
      VariableMetricConnectionDiffDerivativeInFrameOnLocal
        (I := I) S frame u pairDt)
    (hmetric :
      MetricCovDerivDerivativeComponentsInFrameOnLocal
        (I := I) S frame u metricCovDerivDt)
    (hunique : forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real)) :
    ChristoffelMetricVariationEquationInFrameOn
      (I := I) S gInv frame hframe metricCovDerivDt :=
  christoffelVariationEquationInFrameOn_of_pairing_local
    (I := I) S gInv frame hframe
    (connectionVariationLoweredRHSFromMetricVariationInFrame metricCovDerivDt)
    hinv
    (connectionVariationPairing_of_metricVariation
      (I := I) S hS frame hframe hu pairDt metricCovDerivDt
      hpair hvarDiff hmetric hunique)

/-- Lemma 6.2 from metric-frame regularity plus the fixed-base metric
covariant-derivative frontier.

This proof differentiates
`Gamma(s) - Gamma(t) = gInv(s) * g_s((nabla^s - nabla^t)e_i e_j, e_l)`.
The product-rule term containing `dt gInv` vanishes because the connection
difference is zero at `s = t`; the remaining derivative is supplied by the
finite-difference Koszul computation and the Ricci-flow metric variation. -/
theorem christoffelEvolution_of_metricFrameTimeRegularity
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (metricCovDerivDt nablaRic :
      Real -> M -> Idx -> Idx -> Idx -> Real)
    (hmetricFrame :
      MetricFrameTimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u)
    (hmetric :
      MetricCovDerivDerivativeComponentsInFrameOnLocal
        (I := I) S frame u metricCovDerivDt)
    (hmetricRicci :
      MetricCovDerivDerivativeIsRicciFlowInFrame metricCovDerivDt nablaRic) :
    ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv frame hframe nablaRic := by
  intro t x hx i j k
  let gamma : Real -> Real := fun s =>
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
      (S.family.connection s) frame hframe x i j k
  let gamma0 : Real := gamma (t : Real)
  let rhs : Real -> Real := fun s =>
    ∑ l : Idx, gInv s x k l *
      connectionDiffLoweredInFrame (I := I) S frame s (t : Real) s x i j l
  let target : Real :=
    ∑ l : Idx, gInv (t : Real) x k l *
      christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l
  have hDiff :
      VariableMetricConnectionDiffDerivativeInFrameOnLocal
        (I := I) S frame u (christoffelVariationLoweredRHSInFrame nablaRic) :=
    variableMetricConnectionDiffDerivative_of_metricCovDeriv
      (I := I) S hS frame hframe hu metricCovDerivDt nablaRic
      hmetric hmetricRicci
  have hRhs :
      HasDerivWithinAt rhs target D.carrier (t : Real) := by
    dsimp [rhs, target]
    simpa [Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun l s =>
          gInv s x k l *
            connectionDiffLoweredInFrame (I := I) S frame s (t : Real) s x i j l)
        (A' := fun l =>
          gInv (t : Real) x k l *
            christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l)
        (s := D.carrier) (x := (t : Real))
        (fun l _hl =>
          by
            have hprod :=
              (hmetricFrame.inverseMetricDerivative t x k l).mul
                (hDiff t x hx i j l)
            refine hprod.congr_deriv ?_
            simp))
  have hSub :
      HasDerivWithinAt
        (fun s : Real => gamma s - gamma0)
        target
        D.carrier
        (t : Real) := by
    refine hRhs.congr ?_ ?_
    · intro s _hs
      exact gammaSubLocal
        (I := I) S gInv frame hframe hmetricFrame.nondegenerateGram
        (t : Real) s hx i j k
    · exact gammaSubLocal
        (I := I) S gInv frame hframe hmetricFrame.nondegenerateGram
        (t : Real) (t : Real) hx i j k
  have hGammaPlus :
      HasDerivWithinAt
        (fun s : Real => (gamma s - gamma0) + gamma0)
        target
        D.carrier
        (t : Real) := by
    simpa using hSub.add_const gamma0
  have hGamma :
      HasDerivWithinAt gamma target D.carrier (t : Real) := by
    refine hGammaPlus.congr ?_ ?_
    · intro s _hs
      ring
    · ring
  simpa [gamma, target, christoffelEvolutionRHSInFrame] using hGamma

/-- Lemma 6.2 from inverse-metric evolution and fixed-base metric variation.

This theorem-level producer avoids the legacy metric-frame package: the inverse
metric derivative is supplied by the actual inverse evolution equation, and the
metric covariant-derivative variation is supplied separately. -/
theorem gammaEvolOfInv
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (metricCovDerivDt nablaRic :
      Real -> M -> Idx -> Idx -> Idx -> Real)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (hinvEvol : InverseMetricEvolutionEquationInFrame
      (I := I) S gInv frame u)
    (hmetric :
      MetricCovDerivDerivativeComponentsInFrameOnLocal
        (I := I) S frame u metricCovDerivDt)
    (hmetricRicci :
      MetricCovDerivDerivativeIsRicciFlowInFrame metricCovDerivDt nablaRic) :
    ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv frame hframe nablaRic := by
  intro t x hx i j k
  let gamma : Real -> Real := fun s =>
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
      (S.family.connection s) frame hframe x i j k
  let gamma0 : Real := gamma (t : Real)
  let rhs : Real -> Real := fun s =>
    ∑ l : Idx, gInv s x k l *
      connectionDiffLoweredInFrame (I := I) S frame s (t : Real) s x i j l
  let target : Real :=
    ∑ l : Idx, gInv (t : Real) x k l *
      christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l
  have hDiff :
      VariableMetricConnectionDiffDerivativeInFrameOnLocal
        (I := I) S frame u (christoffelVariationLoweredRHSInFrame nablaRic) :=
    variableMetricConnectionDiffDerivative_of_metricCovDeriv
      (I := I) S hS frame hframe hu metricCovDerivDt nablaRic
      hmetric hmetricRicci
  have hRhs :
      HasDerivWithinAt rhs target D.carrier (t : Real) := by
    dsimp [rhs, target]
    simpa [Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun l s =>
          gInv s x k l *
            connectionDiffLoweredInFrame (I := I) S frame s (t : Real) s x i j l)
        (A' := fun l =>
          gInv (t : Real) x k l *
            christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l)
        (s := D.carrier) (x := (t : Real))
        (fun l _hl =>
          by
            have hprod :=
              (hinvEvol t x hx k l).mul (hDiff t x hx i j l)
            refine hprod.congr_deriv ?_
            simp))
  have hSub :
      HasDerivWithinAt
        (fun s : Real => gamma s - gamma0)
        target
        D.carrier
        (t : Real) := by
    refine hRhs.congr ?_ ?_
    · intro s _hs
      exact gammaSubLocal
        (I := I) S gInv frame hframe hinv
        (t : Real) s hx i j k
    · exact gammaSubLocal
        (I := I) S gInv frame hframe hinv
        (t : Real) (t : Real) hx i j k
  have hGammaPlus :
      HasDerivWithinAt
        (fun s : Real => (gamma s - gamma0) + gamma0)
        target
        D.carrier
        (t : Real) := by
    simpa using hSub.add_const gamma0
  have hGamma :
      HasDerivWithinAt gamma target D.carrier (t : Real) := by
    refine hGammaPlus.congr ?_ ?_
    · intro s _hs
      ring
    · ring
  simpa [gamma, target, christoffelEvolutionRHSInFrame] using hGamma

/-- Lemma 6.2 from local inverse-metric evolution and fixed-base metric
variation. -/
theorem gammaEvolLocal
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (metricCovDerivDt nablaRic :
      Real -> M -> Idx -> Idx -> Idx -> Real)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (hinvEvol : InverseMetricEvolutionEquationInFrame
      (I := I) S gInv frame u)
    (hmetric :
      MetricCovDerivDerivativeComponentsInFrameOnLocal
        (I := I) S frame u metricCovDerivDt)
    (hmetricRicci :
      MetricCovDerivDerivativeIsRicciFlowInFrame metricCovDerivDt nablaRic) :
    ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv frame hframe nablaRic := by
  intro t x hx i j k
  let gamma : Real -> Real := fun s =>
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
      (S.family.connection s) frame hframe x i j k
  let gamma0 : Real := gamma (t : Real)
  let rhs : Real -> Real := fun s =>
    ∑ l : Idx, gInv s x k l *
      connectionDiffLoweredInFrame (I := I) S frame s (t : Real) s x i j l
  let target : Real :=
    ∑ l : Idx, gInv (t : Real) x k l *
      christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l
  have hDiff :
      VariableMetricConnectionDiffDerivativeInFrameOnLocal
        (I := I) S frame u (christoffelVariationLoweredRHSInFrame nablaRic) :=
    variableMetricConnectionDiffDerivative_of_metricCovDeriv
      (I := I) S hS frame hframe hu metricCovDerivDt nablaRic
      hmetric hmetricRicci
  have hRhs :
      HasDerivWithinAt rhs target D.carrier (t : Real) := by
    dsimp [rhs, target]
    simpa [Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun l s =>
          gInv s x k l *
            connectionDiffLoweredInFrame (I := I) S frame s (t : Real) s x i j l)
        (A' := fun l =>
          gInv (t : Real) x k l *
            christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l)
        (s := D.carrier) (x := (t : Real))
        (fun l _hl =>
          by
            have hprod :=
              (hinvEvol t x hx k l).mul (hDiff t x hx i j l)
            refine hprod.congr_deriv ?_
            simp))
  have hSub :
      HasDerivWithinAt
        (fun s : Real => gamma s - gamma0)
        target
        D.carrier
        (t : Real) := by
    refine hRhs.congr ?_ ?_
    · intro s _hs
      exact gammaSubLocal
        (I := I) S gInv frame hframe hinv
        (t : Real) s hx i j k
    · exact gammaSubLocal
        (I := I) S gInv frame hframe hinv
        (t : Real) (t : Real) hx i j k
  have hGammaPlus :
      HasDerivWithinAt
        (fun s : Real => (gamma s - gamma0) + gamma0)
        target
        D.carrier
        (t : Real) := by
    simpa using hSub.add_const gamma0
  have hGamma :
      HasDerivWithinAt gamma target D.carrier (t : Real) := by
    refine hGammaPlus.congr ?_ ?_
    · intro s _hs
      ring
    · ring
  simpa [gamma, target, christoffelEvolutionRHSInFrame] using hGamma

/-- Lemma 6.2 from spacetime-smooth Ricci-flow metric components.

This constructor eliminates the broad connection-regularity black box: the only
time/spatial input is the fixed-base mixed derivative of the metric components,
recorded in `MetricFrameSpacetimeRegularityInFrameOnLocal`. -/
theorem christoffelEvolution_of_spacetimeSmoothMetric
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hreg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u)
    (hnabla :
      NablaRicciComponentsByConnectionInFrameOn
        (I := I) S frame u nablaRic) :
    ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv frame hframe nablaRic :=
  christoffelEvolution_of_metricFrameTimeRegularity
    (I := I) S hS gInv gInvDt frame hframe hu
    (fun t x d a b => (-2 : Real) * nablaRic t x d a b)
    nablaRic
    hreg.toMetricFrameTimeRegularityInFrameOnLocal
    (metricCovDerivDerivativeComponents_of_ricciFlow
      (I := I) S hS gInv gInvDt frame hreg nablaRic hnabla)
    (metricCovDerivDerivativeIsRicciFlowInFrame_neg_two
      (M := M) (Idx := Idx) nablaRic)

/-- LaTeX Lemma 6.2, `lem:evol-christoffel`, in fixed-frame component form:
along Ricci flow,
`partial_t Gamma^k_ij =
  -g^{kl} nabla_i Ric_jl - g^{kl} nabla_j Ric_il
    + g^{kl} nabla_l Ric_ij`. -/
theorem evol_christoffel_inFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hreg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u)
    (hnabla :
      NablaRicciComponentsByConnectionInFrameOn
        (I := I) S frame u nablaRic)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (hx : x ∈ u)
    (i j k : Idx) :
    HasDerivWithinAt
      (fun s : Real =>
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
          (S.family.connection s) frame hframe x i j k)
      (DifferentialGeometry.Tensor.Coordinates.ricciFlowChristoffelEvolutionRHSInFrame
        (nablaRicLastRaisedInFrame (M := M) gInv nablaRic)
        (nablaRicDirectionRaisedInFrame (M := M) gInv nablaRic)
        (t : Real) x i j k)
      D.carrier
      (t : Real) := by
  have hEvol :
      ChristoffelEvolutionEquationInFrameOn
        (I := I) S gInv frame hframe nablaRic :=
    christoffelEvolution_of_spacetimeSmoothMetric
      (I := I) S hS gInv gInvDt frame hframe hu nablaRic hreg hnabla
  exact (hEvol t x hx i j k).congr_deriv
    (christoffelEvolutionRHSInFrame_eq_coordinates_rhs
      (M := M) gInv nablaRic (t : Real) x i j k)

/-- Lemma 6.2 in raised Christoffel-component form, from the proved
finite-difference Koszul computation plus the remaining time-regularity
frontiers. -/
theorem christoffelEvolution_of_ricciFlowMetricVariation
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (pairDt metricCovDerivDt nablaRic :
      Real -> M -> Idx -> Idx -> Idx -> Real)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
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
    (hunique : forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real)) :
    ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv frame hframe nablaRic :=
  christoffelEvolutionEquationInFrameOn_of_pairing_local
    (I := I) S gInv frame hframe nablaRic hinv
    (connectionVariationPairing_of_ricciFlow
      (I := I) S hS frame hframe hu pairDt metricCovDerivDt nablaRic
      hpair hvarDiff hmetric hmetricRicci hunique)

/-- Lemma 6.2 in raised Christoffel-component form, from the connection
pairing derivative and the Ricci-flow Koszul variation identity. -/
theorem christoffelEvolution_of_koszul
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (pairDt nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (hdt : ConnectionPairingDerivativeInFrameOn (I := I) S frame pairDt)
    (hkoszul : KoszulConnectionVariationInFrame (M := M) pairDt nablaRic) :
    ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv frame hframe nablaRic :=
  christoffelEvolutionEquationInFrameOn_of_pairing
    (I := I) S gInv frame hframe nablaRic hinv
    (connectionVariationPairing_of_koszul
      (I := I) S frame pairDt nablaRic hdt hkoszul)


end Components

end DifferentialGeometry.PDE.RicciFlow
