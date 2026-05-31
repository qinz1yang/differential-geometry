import RicciFlower.RicciFlow.Perelman.F.ConnectionTrace


set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RicciFlower
namespace RicciFlow
namespace Perelman

noncomputable section

open Filter MeasureTheory
open RicciFlower.Analysis.Volume
open RicciFlower.Analysis.VolumeVariation
open RicciFlower.Coordinates
open Tensor0SBundle
open scoped Manifold ContDiff

variable {M : Type*}

/-!
# Perelman F Producer

Split-out component of `RicciFlow.Perelman.F`.
-/

section GeometryFormula510

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Formula 5.10 using the intrinsic metric trace field `tr_g A` of a smooth
connection-variation tensor.  This specializes `formula510_of_connTrace` with
the smooth section constructed in `Tensor.RSTensor.MetricTrace`. -/
theorem formula510_of_connTraceField
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    {firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace rawTrace actionTrace q : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hfirst :
      firstVariation =
        ∫ x,
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
          ∂(expNegPotentialWeightedMeasure
              (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hfinal_int :
      Integrable
        (fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess)
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hdiv_int :
      Integrable weightedDivergenceTrace
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hshift_int :
      Integrable shiftedTrace
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hcorr_int :
      Integrable
        (fun x : M =>
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x))
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hdivTrace :
      ∀ x : M,
        RicciFlower.Analysis.DivergenceTheorem.divergence_g
            (I := I) g (RicciFlower.Realized.connTraceField (I := I) g A) x =
          rawTrace x)
    (hactionTrace :
      ∀ x : M,
        RicciFlower.Analysis.DivergenceTheorem.tangentSectionAction
            (I := I) (RicciFlower.Realized.connTraceField (I := I) g A) potential x =
          actionTrace x)
    (hweighted :
      ∀ x : M,
        weightedDivergenceTrace x = rawTrace x - actionTrace x)
    (hlap :
      ∀ x : M,
        lapPotential x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hpotential x)
    (hgradSq :
      ∀ x : M,
        gradPotentialNormSq x =
          g.inner x
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x)
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x))
    (hshift :
      ∀ x : M,
        shiftedTrace x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hq x)
    (hqeq :
      ∀ x : M,
        q x = potentialVariation x - metricVariationTrace x / 2) :
    FFunctionalFormula510
      (expNegPotentialWeightedMeasure
        (riemannianVolumeMeasure (I := I) (M := M) g) potential)
      firstVariation scalarCurvature lapPotential gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess :=
  formula510_of_connTrace (I := I) g hpotential hq
    (RicciFlower.Realized.connTraceField (I := I) g A)
    hmeas hfirst hfinal_int hdiv_int hshift_int hcorr_int
    hdivTrace hactionTrace hweighted hlap hgradSq hshift hqeq

/-- Formula 5.10 assembly with the raw divergence and action trace supplied by
the constructed field `tr_g A` itself.  The remaining geometric bridge is the
single pointwise identity saying the weighted-divergence component produced by
the `δ(Ric + Hess f)` calculation is `div(tr_g A) - (tr_g A)(f)`. -/
theorem formula510_of_trace
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    {firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace q : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hfirst :
      firstVariation =
        ∫ x,
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
          ∂(expNegPotentialWeightedMeasure
              (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hfinal_int :
      Integrable
        (fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess)
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hdiv_int :
      Integrable weightedDivergenceTrace
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hshift_int :
      Integrable shiftedTrace
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hcorr_int :
      Integrable
        (fun x : M =>
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x))
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hweighted :
      ∀ x : M,
        weightedDivergenceTrace x =
          connTraceRawDiv (I := I) g A x -
            connTraceAction (I := I) g A potential x)
    (hlap :
      ∀ x : M,
        lapPotential x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hpotential x)
    (hgradSq :
      ∀ x : M,
        gradPotentialNormSq x =
          g.inner x
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x)
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x))
    (hshift :
      ∀ x : M,
        shiftedTrace x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hq x)
    (hqeq :
      ∀ x : M,
        q x = potentialVariation x - metricVariationTrace x / 2) :
    FFunctionalFormula510
      (expNegPotentialWeightedMeasure
        (riemannianVolumeMeasure (I := I) (M := M) g) potential)
      firstVariation scalarCurvature lapPotential gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess := by
  exact formula510_of_connTraceField (I := I) g A hpotential hq hmeas
    hfirst hfinal_int hdiv_int hshift_int hcorr_int
    (rawTrace := connTraceRawDiv (I := I) g A)
    (actionTrace := connTraceAction (I := I) g A potential)
    (fun x => rfl)
    (connTraceAction_eq (I := I) g A potential)
    hweighted hlap hgradSq hshift hqeq

/-- Formula 5.10 with the weighted-divergence trace supplied by the coordinate
components of a global connection-variation tensor `A`.

This is the formula-5.10-facing assembly point after the raw divergence bridge:
the fixed-chart product rule, `nabla g^{-1}=0`, and the coordinate formula for
`nabla A` are consumed here to provide the weighted-divergence cancellation. -/
theorem formula510_of_components
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (g : SmoothRiemannianMetric I M)
    (hLC : RicciFlower.LeviCivita.IsLeviCivita (I := I) cov g)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (nablaChristoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (christoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (gradPotential : M -> CoordinateIdx (𝕜 := Real) E -> Real)
    (gInvDeriv :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (componentDeriv :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    {firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      shiftedTrace q : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hfirst :
      firstVariation =
        ∫ x,
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess
            (christoffelWeightedDivergenceTrace (I := I) g
              nablaChristoffelVariation christoffelVariation gradPotential)
            shiftedTrace x
          ∂(expNegPotentialWeightedMeasure
              (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hfinal_int :
      Integrable
        (fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess)
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hdiv_int :
      Integrable
        (christoffelWeightedDivergenceTrace (I := I) g
          nablaChristoffelVariation christoffelVariation gradPotential)
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hshift_int :
      Integrable shiftedTrace
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hcorr_int :
      Integrable
        (fun x : M =>
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x))
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hA :
      ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
        componentRS (I := I)
            (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
            (A x) (fun _ : Fin 1 => p)
            (fun q : Fin 2 => if q = 0 then i else j) =
          christoffelVariation x p i j)
    (hgrad :
      ∀ x : M, ∀ p : CoordinateIdx (𝕜 := Real) E,
        extDerivFun (I := I) potential x (coordinateFrameAt (I := I) x p x) =
          gradPotential x p)
    (hgInvDiff : ∀ x : M, ∀ i j : CoordinateIdx (𝕜 := Real) E,
      DifferentiableAt Real
        (fun y : E =>
          inverseMetricFlatModelInChart_component (I := I) g x i j y)
        (extChartAt I x x))
    (hADiff : ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      DifferentiableAt Real
        (fun y : E =>
          (A ((extChartAt I x).symm y)
            (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x
              ((continuousMultilinearMap_basis
                (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                (fun _ : Fin 1 => p)) ((extChartAt I x).symm y)))
            (fun q : Fin 2 =>
              coordinateFrameAt (I := I) x (if q = 0 then i else j)
                ((extChartAt I x).symm y)))
        (extChartAt I x x))
    (hgInvDeriv : ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (fun y : E =>
          inverseMetricFlatModelInChart_component (I := I) g x i j y)
        (extChartAt I x x) = gInvDeriv x p i j)
    (hADeriv : ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (fun y : E =>
          (A ((extChartAt I x).symm y)
            (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x
              ((continuousMultilinearMap_basis
                (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                (fun _ : Fin 1 => p)) ((extChartAt I x).symm y)))
            (fun q : Fin 2 =>
              coordinateFrameAt (I := I) x (if q = 0 then i else j)
                ((extChartAt I x).symm y)))
        (extChartAt I x x) = componentDeriv x p p i j)
    (hginvExt : ∀ x : M, ∀ d i j : CoordinateIdx (𝕜 := Real) E,
      gInvDeriv x d i j =
        extDerivFun (I := I)
          (fun y : M =>
            inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x y))
          x (coordinateFrameAt (I := I) x d x))
    (hzero : ∀ x : M, ∀ d i j : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Coordinates.inverseMetricCovDerivForMetricCompInFrame
        (I := I)
        (fun y : M => fun a b : CoordinateIdx (𝕜 := Real) E =>
          inverseMetricFlatModelInChart_component (I := I) g x a b
            (extChartAt I x y))
        cov (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x)
        x d i j = 0)
    (hNabla : ∀ x : M, ∀ d k i j : CoordinateIdx (𝕜 := Real) E,
      nablaChristoffelVariation x d k i j =
        componentDeriv x d k i j +
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => a)
                (fun q : Fin 2 => if q = 0 then i else j)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => k)
                (fun q : Fin 2 => if q = 0 then a else j)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => k)
                (fun q : Fin 2 => if q = 0 then i else a)))
    (hGamma : ∀ x : M, ∀ d a k : CoordinateIdx (𝕜 := Real) E,
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k =
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x a d k)
    (hlap :
      ∀ x : M,
        lapPotential x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hpotential x)
    (hgradSq :
      ∀ x : M,
        gradPotentialNormSq x =
          g.inner x
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x)
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x))
    (hshift :
      ∀ x : M,
        shiftedTrace x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) g hq x)
    (hqeq :
      ∀ x : M,
        q x = potentialVariation x - metricVariationTrace x / 2) :
    FFunctionalFormula510
      (expNegPotentialWeightedMeasure
        (riemannianVolumeMeasure (I := I) (M := M) g) potential)
      firstVariation scalarCurvature lapPotential gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess := by
  have hraw :
      ∀ x : M,
        connTraceRawDiv (I := I) g A x =
          gammaRawDivergenceTrace (I := I) g nablaChristoffelVariation x :=
    connTraceRaw_of_components (I := I) (cov := cov) g hLC A
      nablaChristoffelVariation gInvDeriv componentDeriv
      hgInvDiff hADiff hgInvDeriv hADeriv hginvExt hzero hNabla hGamma
  have hweighted :
      ∀ x : M,
        christoffelWeightedDivergenceTrace (I := I) g
            nablaChristoffelVariation christoffelVariation gradPotential x =
          connTraceRawDiv (I := I) g A x -
            connTraceAction (I := I) g A potential x :=
    weightedTrace_of_raw (I := I) g A potential nablaChristoffelVariation
      christoffelVariation gradPotential hraw hA hgrad
  exact formula510_of_trace (I := I) g A
    (weightedDivergenceTrace :=
      christoffelWeightedDivergenceTrace (I := I) g
        nablaChristoffelVariation christoffelVariation gradPotential)
    hpotential hq hmeas hfirst hfinal_int hdiv_int hshift_int hcorr_int
    hweighted hlap hgradSq hshift hqeq

/-- Formula 5.10 endpoint producer.

This is the book-facing assembly theorem for the current component route: the
input first variation is the moving-volume derivative of the original
`R + |grad f|^2` bracket, and the theorem uses the per-time weighted IBP
comparison with the closed `R + Delta f` bracket plus the connection-trace
component geometry to produce `FFunctionalFormula510`. -/
theorem formula510_producer
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    {s0 : Real}
    (hLC : RicciFlower.LeviCivita.IsLeviCivita (I := I) cov (G.metric s0))
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (nablaChristoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (christoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (gradPotential : M -> CoordinateIdx (𝕜 := Real) E -> Real)
    (gInvDeriv :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (componentDeriv :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    {scalarCurvaturePath lapPotentialPath gradPotentialNormSqPath
      potentialPath : Real -> M -> Real}
    {firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      shiftedTrace q scalarCurvatureVariation lapPotentialVariation
      gradPotentialNormSqVariation : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)))
    (hfirstVariation :
      firstVariation =
        ∫ x,
          expWeightedIntegralVariationIntegrand
            (potentialPath s0) potentialVariation metricVariationTrace
            (fFunctionalBracket (scalarCurvaturePath s0)
              (gradPotentialNormSqPath s0))
            (fFunctionalBracketVariation scalarCurvatureVariation
              gradPotentialNormSqVariation) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s0))
    (hmeas_near :
      ∀ᶠ s in nhds s0,
        AEMeasurable
          (fun x : M =>
            ENNReal.ofReal (expNegPotentialDensity (potentialPath s) x))
          (volumeMeasureFamily (I := I) (M := M) G s))
    (hibp_near :
      ∀ᶠ s in nhds s0,
        (∫ x,
          fFunctionalBracket (scalarCurvaturePath s)
            (gradPotentialNormSqPath s) x
          ∂(expNegPotentialWeightedMeasure
              (volumeMeasureFamily (I := I) (M := M) G s)
              (potentialPath s))) =
        ∫ x,
          fFunctionalClosedBracket (scalarCurvaturePath s)
            (lapPotentialPath s) x
          ∂(expNegPotentialWeightedMeasure
              (volumeMeasureFamily (I := I) (M := M) G s)
              (potentialPath s)))
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hgrad_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => gradPotentialNormSqPath s x)
          (gradPotentialNormSqVariation x) s0)
    (hlap_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => lapPotentialPath s x)
          (lapPotentialVariation x) s0)
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_reg :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (horig_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x)
        s0)
    (hclosed_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalClosedBracket (scalarCurvaturePath s)
              (lapPotentialPath s) x)
        s0)
    (hpotential0 : potentialPath s0 = potential)
    (hscalar0 : scalarCurvaturePath s0 = scalarCurvature)
    (hlap0 : lapPotentialPath s0 = lapPotential)
    (hclosed_variation :
      ∀ x : M,
        fFunctionalClosedBracketVariation scalarCurvatureVariation
            lapPotentialVariation x =
          -metricVariationRicciHess x +
            christoffelWeightedDivergenceTrace (I := I) (G.metric s0)
              nablaChristoffelVariation christoffelVariation gradPotential x +
            shiftedTrace x)
    (hfinal_int :
      Integrable
        (fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess)
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)) potential))
    (hdiv_int :
      Integrable
        (christoffelWeightedDivergenceTrace (I := I) (G.metric s0)
          nablaChristoffelVariation christoffelVariation gradPotential)
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)) potential))
    (hshift_int :
      Integrable shiftedTrace
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)) potential))
    (hcorr_int :
      Integrable
        (fun x : M =>
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x))
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)) potential))
    (hA :
      ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
        componentRS (I := I)
            (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
            (A x) (fun _ : Fin 1 => p)
            (fun q : Fin 2 => if q = 0 then i else j) =
          christoffelVariation x p i j)
    (hgrad :
      ∀ x : M, ∀ p : CoordinateIdx (𝕜 := Real) E,
        extDerivFun (I := I) potential x (coordinateFrameAt (I := I) x p x) =
          gradPotential x p)
    (hgInvDiff : ∀ x : M, ∀ i j : CoordinateIdx (𝕜 := Real) E,
      DifferentiableAt Real
        (fun y : E =>
          inverseMetricFlatModelInChart_component (I := I) (G.metric s0) x i j y)
        (extChartAt I x x))
    (hADiff : ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      DifferentiableAt Real
        (fun y : E =>
          (A ((extChartAt I x).symm y)
            (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x
              ((continuousMultilinearMap_basis
                (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                (fun _ : Fin 1 => p)) ((extChartAt I x).symm y)))
            (fun q : Fin 2 =>
              coordinateFrameAt (I := I) x (if q = 0 then i else j)
                ((extChartAt I x).symm y)))
        (extChartAt I x x))
    (hgInvDeriv : ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (fun y : E =>
          inverseMetricFlatModelInChart_component (I := I) (G.metric s0) x i j y)
        (extChartAt I x x) = gInvDeriv x p i j)
    (hADeriv : ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (fun y : E =>
          (A ((extChartAt I x).symm y)
            (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x
              ((continuousMultilinearMap_basis
                (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                (fun _ : Fin 1 => p)) ((extChartAt I x).symm y)))
            (fun q : Fin 2 =>
              coordinateFrameAt (I := I) x (if q = 0 then i else j)
                ((extChartAt I x).symm y)))
        (extChartAt I x x) = componentDeriv x p p i j)
    (hginvExt : ∀ x : M, ∀ d i j : CoordinateIdx (𝕜 := Real) E,
      gInvDeriv x d i j =
        extDerivFun (I := I)
          (fun y : M =>
            inverseMetricFlatModelInChart_component (I := I) (G.metric s0) x i j
              (extChartAt I x y))
          x (coordinateFrameAt (I := I) x d x))
    (hzero : ∀ x : M, ∀ d i j : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Coordinates.inverseMetricCovDerivForMetricCompInFrame
        (I := I)
        (fun y : M => fun a b : CoordinateIdx (𝕜 := Real) E =>
          inverseMetricFlatModelInChart_component (I := I) (G.metric s0) x a b
            (extChartAt I x y))
        cov (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x)
        x d i j = 0)
    (hNabla : ∀ x : M, ∀ d k i j : CoordinateIdx (𝕜 := Real) E,
      nablaChristoffelVariation x d k i j =
        componentDeriv x d k i j +
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => a)
                (fun q : Fin 2 => if q = 0 then i else j)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => k)
                (fun q : Fin 2 => if q = 0 then a else j)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => k)
                (fun q : Fin 2 => if q = 0 then i else a)))
    (hGamma : ∀ x : M, ∀ d a k : CoordinateIdx (𝕜 := Real) E,
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k =
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x a d k)
    (hlap :
      ∀ x : M,
        lapPotential x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) (G.metric s0) hpotential x)
    (hgradSq :
      ∀ x : M,
        gradPotentialNormSq x =
          (G.metric s0).inner x
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) (G.metric s0) hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x)
            ((RicciFlower.Analysis.DivergenceTheorem.grad_g
              (I := I) (G.metric s0) hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x))
    (hshift :
      ∀ x : M,
        shiftedTrace x =
          RicciFlower.Analysis.DivergenceTheorem.Δ_g
            (I := I) (G.metric s0) hq x)
    (hqeq :
      ∀ x : M,
        q x = potentialVariation x - metricVariationTrace x / 2) :
    FFunctionalFormula510
      (expNegPotentialWeightedMeasure
        (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)) potential)
      firstVariation scalarCurvature lapPotential gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess := by
  have hfirst_pre :
      firstVariation =
        ∫ x,
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess
            (christoffelWeightedDivergenceTrace (I := I) (G.metric s0)
              nablaChristoffelVariation christoffelVariation gradPotential)
            shiftedTrace x
          ∂(expNegPotentialWeightedMeasure
              (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0))
              potential) := by
    refine hfirstVariation.trans ?_
    exact firstVar_pre510_ibp (I := I) (M := M) G hmeas hmeas_near
      hibp_near hscalar_deriv hgrad_deriv hlap_deriv hpotential_deriv
      htrace hmetric_reg horig_reg hclosed_reg hpotential0 hscalar0 hlap0
      hclosed_variation
  exact formula510_of_components (I := I) (cov := cov) (G.metric s0) hLC A
    nablaChristoffelVariation christoffelVariation gradPotential
    gInvDeriv componentDeriv hpotential hq hmeas hfirst_pre
    hfinal_int hdiv_int hshift_int hcorr_int hA hgrad
    hgInvDiff hADiff hgInvDeriv hADeriv hginvExt hzero hNabla hGamma
    hlap hgradSq hshift hqeq

end GeometryFormula510

end

end Perelman
end RicciFlow
end RicciFlower
