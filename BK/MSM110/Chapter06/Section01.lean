/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RicciFlower contributors
-/

import RicciFlower.RicciFlow.Evolution.Connection
import RicciFlower.RicciFlow.Evolution.Metric
import RicciFlower.RicciFlow.Evolution.Ricci
import RicciFlower.RicciFlow.Evolution.Scalar
import RicciFlower.RicciFlow.Evolution.Volume

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
# MSM110 Chapter 6.1

Minimal book companion for the curvature evolution section.  The canonical
proofs remain in `RicciFlower.RicciFlow.Evolution.*`; this module only gives
book-label aliases for the checked fixed-frame/integrated interfaces.
-/

namespace BK
namespace MSM110
namespace Chapter06
namespace Section01

noncomputable section

open Bundle RicciFlower.RicciFlow
open RicciFlower.Coordinates
open MeasureTheory
open RicciFlower.Analysis.Volume
open RicciFlower.Analysis.VolumeVariation
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {u : Set M}

/-- MSM110 Chapter 6.1, Ricci-flow specialization of inverse-metric evolution. -/
theorem eq_inverse_metric_ricci_flow
    {D : RicciFlower.Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> RicciFlower.Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hreg :
      MetricFrameTimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u)
    (t : RicciFlower.Realized.RealTimeInterval.RegularTime D)
    (x : M) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => gInv s x i j)
      (2 * raisedRicciCompInFrame (I := I) S gInv frame (t : Real) x i j)
      D.carrier
      (t : Real) :=
  RicciFlower.RicciFlow.evol_inverse_metric_inFrame
    (I := I) S hS gInv gInvDt frame hreg t x i j

/-- MSM110 Chapter 6.1, equation `eq:christoffel_symbols_ricci_flow`. -/
theorem eq_christoffel_symbols_ricci_flow
    {D : RicciFlower.Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> RicciFlower.Realized.InverseMetricComponents M Idx)
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
    (t : RicciFlower.Realized.RealTimeInterval.RegularTime D)
    (x : M) (hx : x ∈ u)
    (i j k : Idx) :
    HasDerivWithinAt
      (fun s : Real =>
        RicciFlower.Coordinates.christoffelSymbolInFrame
          (S.family.connection s) frame hframe x i j k)
      (RicciFlower.Coordinates.ricciFlowChristoffelEvolutionRHSInFrame
        (nablaRicLastRaisedInFrame (M := M) gInv nablaRic)
        (nablaRicDirectionRaisedInFrame (M := M) gInv nablaRic)
        (t : Real) x i j k)
      D.carrier
      (t : Real) :=
  RicciFlower.RicciFlow.evol_christoffel_inFrame
    (I := I) S hS gInv gInvDt frame hframe hu nablaRic hreg hnabla t x hx i j k

/-- MSM110 Chapter 6.1, local fixed-frame Ricci evolution from local variation
and the contracted commutator package. -/
theorem eq_ricci_tensor_ricci_flow_two_local
    {D : RicciFlower.Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> RicciFlower.Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> RicciFlower.Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hInv : SymmetricInverseMetricComponentsInFrameOn gInv)
    (h_var : RicciVariationFormulaInFrameOnLocal (I := I) S frame u
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric))
    (hcomm : RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric) :
    RicciEvolutionEquationInFrameOnLocal
      (I := I) S Rm04 gInv frame u
      (roughLapRicInFrame (M := M) gInv nabla2Ric) :=
  RicciFlower.RicciFlow.ricciEvolutionEquationInFrameOnLocal_of_variation_commutators
    (I := I) S Rm04 gInv frame u nabla2Ric hInv h_var hcomm

/-- MSM110 Chapter 6.1, equation `eq:ricci_tensor_ricci_flow_two`. -/
theorem eq_ricci_tensor_ricci_flow_two
    {D : RicciFlower.Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> RicciFlower.Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> RicciFlower.Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hInv : SymmetricInverseMetricComponentsInFrameOn gInv)
    (h_var : RicciVariationFormulaInFrameOn (I := I) S frame
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric))
    (hcomm : RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric)
    (t : RicciFlower.Realized.RealTimeInterval.RegularTime D)
    (x : M) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
      (roughLapRicInFrame (M := M) gInv nabla2Ric (t : Real) x i j -
        2 * rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j -
        2 * ricciQuadraticCompInFrame (I := I) S gInv frame
          (t : Real) x i j)
      D.carrier
      (t : Real) :=
  RicciFlower.RicciFlow.evol_ricci_inFrame_of_variation_commutators
    (I := I) S Rm04 gInv frame nabla2Ric hInv h_var hcomm t x i j

/-- MSM110 Chapter 6.1, equation `eq:ricci_tensor_ricci_flow_two`, in the
coordinate frame at a point, with the Ricci variation producer supplied by the
coordinate Christoffel calculation. -/
theorem eq_ricci_tensor_ricci_flow_two_coordFrame
    [IsManifold I (∞ + 1) M]
    {D : RicciFlower.Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (Rm13 : Real -> RicciFlower.Realized.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> RicciFlower.Realized.Tensor04Section (I := I) (M := M))
    (gInv :
      Real -> RicciFlower.Realized.InverseMetricComponents M
        (CoordinateIdx (𝕜 := Real) E))
    (gInvDt :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (nablaRic :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (nabla2Ric :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (hmetricReg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀))
    (hnablaReg :
      Nabla2RicciComponentsRegularInFrameOnLocal
        (I := I) S (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic nabla2Ric)
    (hRicTrace : ∀ s : Real,
      RicciFlower.Realized.RicciTensorRealizesRm13Trace
        (I := I) (S.ricci s) (Rm13 s))
    (hRm : ∀ s : Real,
      RicciFlower.Realized.Rm13RealizesConnection
        (I := I) (S.family.connection s) (Rm13 s))
    (hcurv : ∀ s : Real,
      RicciFlower.Realized.ConnectionCurvatureCoordAt
        (I := I) (S.family.connection s) x₀)
    (hmix :
      ChristoffelVariationMixedDerivativeInFrameOn (I := I) S
        (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic))
    (hInv : SymmetricInverseMetricComponentsInFrameOn gInv)
    (hcomm : RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv (coordinateFrameAt (I := I) x₀) nabla2Ric)
    (t : RicciFlower.Realized.RealTimeInterval.RegularTime D)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) s x₀ i j)
      (roughLapRicInFrame (M := M) gInv nabla2Ric (t : Real) x₀ i j -
        2 * rmRicciContractionCompInFrame (I := I) S Rm04 gInv
          (coordinateFrameAt (I := I) x₀) (t : Real) x₀ i j -
        2 * ricciQuadraticCompInFrame (I := I) S gInv
          (coordinateFrameAt (I := I) x₀) (t : Real) x₀ i j)
      D.carrier
      (t : Real) :=
  RicciFlower.RicciFlow.evol_ricci_coordFrameAt_of_christoffelEvolution_nabla2_commutators
    (I := I) S hS Rm13 Rm04 gInv gInvDt nablaRic nabla2Ric x₀ hmetricReg
    hnablaReg hRicTrace hRm hcurv hmix hInv hcomm t i j

/-- MSM110 Chapter 6.1, scalar contracted-Bianchi algebra bridge. -/
theorem scalar_contracted_bianchi_reduction
    {D : RicciFlower.Realized.RealTimeInterval}
    (scalarLap contractedRicciHessian : Real -> M -> Real)
    (hbianchi : ScalarSecondDerivativeContractedBianchiOn (D := D)
      scalarLap contractedRicciHessian) :
    ScalarContractedBianchiReductionOn (D := D)
      scalarLap contractedRicciHessian :=
  RicciFlower.RicciFlow.scalarContractedBianchiReductionOn_of_secondDerivativeContractedBianchi
    (M := M) scalarLap contractedRicciHessian hbianchi

/-- MSM110 Chapter 6.1, equation `eq:scalar_curv_evolu`. -/
theorem eq_scalar_curv_evolu
    {D : RicciFlower.Realized.RealTimeInterval}
    (scalar scalarLap contractedRicciHessian ricciNormSq : Real -> M -> Real)
    (hpre : ScalarPreBianchiEvolutionEquationOn (D := D)
      scalar scalarLap contractedRicciHessian ricciNormSq)
    (hbianchi : ScalarContractedBianchiReductionOn (D := D)
      scalarLap contractedRicciHessian) :
    ScalarEvolutionEquationOn (D := D) scalar scalarLap ricciNormSq :=
  RicciFlower.RicciFlow.msm110_ch6_1_scalar_curvature_evolution
    (M := M) scalar scalarLap contractedRicciHessian ricciNormSq hpre hbianchi

/-- MSM110 Chapter 6.1, equation `eq:scalar_curv_evolu`, traced from the
Ricci evolution equation. -/
theorem eq_scalar_curv_evolu_of_ricci_evolution
    {D : RicciFlower.Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> RicciFlower.Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> RicciFlower.Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (hframe : IsLocalFrameOn I E 1 frame Set.univ)
    (hTrace : forall (t : RicciFlower.Realized.RealTimeInterval.RegularTime D) (x : M),
      RicciFlower.Realized.RicciRealizesRm04FirstTraceAt (I := I)
        (S.ricci (t : Real) x) (Rm04 (t : Real) x)
        (gInv (t : Real) x)
        (hframe.toBasisAt (by simp : x ∈ (Set.univ : Set M))))
    (hOutput : forall (t : RicciFlower.Realized.RealTimeInterval.RegularTime D) (x : M),
      RicciFlower.Realized.Rm04OutputSkewAt (I := I) (Rm04 (t : Real) x))
    (hFirst : forall (t : RicciFlower.Realized.RealTimeInterval.RegularTime D) (x : M),
      RicciFlower.Realized.FirstBianchiAt (I := I) (Rm04 (t : Real) x))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (hInvSym : ∀ t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : ∀ t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i) :
    ScalarEvolutionEquationOn (D := D)
      (scalarTraceInFrame (I := I) S gInv frame)
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic)
      (ricciNormSqInFrame (I := I) S gInv frame) :=
  RicciFlower.RicciFlow.scalarEvolutionEquationOn_of_ricciEvolution
    (I := I) S Rm04 gInv frame roughLapRic
    hframe hTrace hOutput hFirst h_inv h_ricci hInvSym hRicSym

/-- MSM110 Chapter 6.1, equation `eq:evolution_of_volume_element`, in the
integrated moving-measure form used by the current volume API. -/
theorem eq_evolution_of_volume_element_integrated
    [CompactSpace M]
    (G : RicciFlower.Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : RicciFlower.Realized.RicciTensorField (I := I) (M := M) Real)
    {f : Real -> M -> Real} {t₀ : Real}
    (hEq : RicciFlower.Realized.MetricVariationEquationDerivAt (I := I) G Ric t₀)
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : Real => ∫ x, f s x ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x, (deriv (fun s : Real => f s x) t₀ -
            RicciFlower.RicciFlow.Evolution.Volume.scalarCurvatureFromRicciInVolumeFrame
              (I := I) (M := M) G Ric t₀ x * f t₀ x)
          ∂(volumeMeasureFamily (I := I) (M := M) G t₀))
      t₀ :=
  RicciFlower.RicciFlow.Evolution.Volume.volume_variation_ricciFlow_at_of_metricDeriv_canonicalScalar
    (I := I) (M := M) G Ric (f := f) hEq hg hf

/-- MSM110 Chapter 6.1, total-volume specialization of
`eq:evolution_of_volume_element`. -/
theorem total_volume_evolution_ricci_flow
    [CompactSpace M]
    (G : RicciFlower.Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : RicciFlower.Realized.RicciTensorField (I := I) (M := M) Real)
    {t₀ : Real}
    (hEq : RicciFlower.Realized.MetricVariationEquationDerivAt (I := I) G Ric t₀)
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) t₀) :
    HasDerivAt
      (fun s : Real => ∫ _x, (1 : Real) ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x, -
          RicciFlower.RicciFlow.Evolution.Volume.scalarCurvatureFromRicciInVolumeFrame
            (I := I) (M := M) G Ric t₀ x
          ∂(volumeMeasureFamily (I := I) (M := M) G t₀))
      t₀ :=
  RicciFlower.RicciFlow.Evolution.Volume.total_volume_variation_ricciFlow_at_of_metricDeriv
    (I := I) (M := M) G Ric hEq hg

/-! ## Remaining Chapter 6.1 statement scaffold

The declarations below are intentionally book-facing component statements.
They make the remaining Section 6.1 implementation targets visible without
moving the core RicciFlower APIs.  Proofs marked `sorry` are the actual future
producer frontiers.
-/

/-- General metric-variation RHS for
`partial_t Gamma^k_ij = 1/2 g^kl (nabla_i h_jl + nabla_j h_il - nabla_l h_ij)`. -/
def generalChristoffelVariationRHSInFrame
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (nablaH : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k : Idx) : Real :=
  (1 / 2 : Real) *
    ∑ l : Idx,
      gInv t x k l *
        (nablaH t x i j l + nablaH t x j i l - nablaH t x l i j)

/-- General metric-variation RHS for the first displayed `(3,1)` Riemann
variation formula in Lemma `lem:general_evolution_revisited`.  Here
`nabla2H t x a b c d` means `(nabla_a nabla_b h)_cd`. -/
def generalRiemann13VariationFirstRHSInFrame
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (nabla2H : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k l : Idx) : Real :=
  (1 / 2 : Real) *
    ∑ p : Idx,
      gInv t x l p *
        (nabla2H t x i j k p + nabla2H t x i k j p -
          nabla2H t x i p j k - nabla2H t x j i k p -
          nabla2H t x j k i p + nabla2H t x j p i k)

/-- General metric-variation RHS for the commuted second displayed `(3,1)`
Riemann variation formula in Lemma `lem:general_evolution_revisited`. -/
def generalRiemann13VariationSecondRHSInFrame
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (Rm13 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hComp : Real -> M -> Idx -> Idx -> Real)
    (nabla2H : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k l : Idx) : Real :=
  (1 / 2 : Real) *
    ∑ p : Idx,
      gInv t x l p *
        (nabla2H t x i k j p + nabla2H t x j p i k -
          nabla2H t x i p j k - nabla2H t x j k i p -
          (∑ q : Idx, Rm13 t x i j k q * hComp t x q p) -
          (∑ q : Idx, Rm13 t x i j p q * hComp t x k q))

/-- General metric-variation RHS for the first displayed Ricci variation
formula in Lemma `lem:general_evolution_revisited`. -/
def generalRicciVariationFirstRHSInFrame
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (nabla2H : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (j k : Idx) : Real :=
  (1 / 2 : Real) *
    ∑ p : Idx, ∑ q : Idx,
      gInv t x p q *
        (nabla2H t x q j k p + nabla2H t x q k j p -
          nabla2H t x q p j k - nabla2H t x j k q p)

/-- General metric-variation RHS for the scalar variation formula before the
divergence rewrite. -/
def generalScalarVariationRHSInFrame
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (hComp Ric : Real -> M -> Idx -> Idx -> Real)
    (nabla2H : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) : Real :=
  ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
    gInv t x i j * gInv t x k l *
      (-nabla2H t x i j k l + nabla2H t x i k j l -
        hComp t x i k * Ric t x j l)

/-- General metric-variation RHS for the pointwise volume-density trace term. -/
def generalVolumeTraceRHSInFrame
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (hComp : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) : Real :=
  (1 / 2 : Real) * ∑ i : Idx, ∑ j : Idx, gInv t x i j * hComp t x i j

/-- Book scaffold for Lemma `lem:general_evolution_revisited`, item 1. -/
theorem lem_general_evolution_revisited_christoffel_inFrame
    {D : RicciFlower.Realized.RealTimeInterval}
    (Gamma : Real -> M -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (nablaH : Real -> M -> Idx -> Idx -> Idx -> Real) :
    ∀ (t : RicciFlower.Realized.RealTimeInterval.RegularTime D) (x : M)
      (i j k : Idx),
      HasDerivWithinAt
        (fun s : Real => Gamma s x i j k)
        (generalChristoffelVariationRHSInFrame gInv nablaH (t : Real) x i j k)
        D.carrier
        (t : Real) := by
  sorry

/-- Book scaffold for Lemma `lem:general_evolution_revisited`, item 2, first
displayed `(3,1)` Riemann variation formula. -/
theorem lem_general_evolution_revisited_riemann13_first_inFrame
    {D : RicciFlower.Realized.RealTimeInterval}
    (Rm13 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (nabla2H : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) :
    ∀ (t : RicciFlower.Realized.RealTimeInterval.RegularTime D) (x : M)
      (i j k l : Idx),
      HasDerivWithinAt
        (fun s : Real => Rm13 s x i j k l)
        (generalRiemann13VariationFirstRHSInFrame gInv nabla2H
          (t : Real) x i j k l)
        D.carrier
        (t : Real) := by
  sorry

/-- Book scaffold for Lemma `lem:general_evolution_revisited`, item 2,
commuted `(3,1)` Riemann variation formula. -/
theorem lem_general_evolution_revisited_riemann13_second_inFrame
    {D : RicciFlower.Realized.RealTimeInterval}
    (Rm13 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (hComp : Real -> M -> Idx -> Idx -> Real)
    (nabla2H : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) :
    ∀ (t : RicciFlower.Realized.RealTimeInterval.RegularTime D) (x : M)
      (i j k l : Idx),
      HasDerivWithinAt
        (fun s : Real => Rm13 s x i j k l)
        (generalRiemann13VariationSecondRHSInFrame gInv Rm13 hComp nabla2H
          (t : Real) x i j k l)
        D.carrier
        (t : Real) := by
  sorry

/-- Book scaffold for Lemma `lem:general_evolution_revisited`, item 3, first
Ricci variation formula. -/
theorem lem_general_evolution_revisited_ricci_first_inFrame
    {D : RicciFlower.Realized.RealTimeInterval}
    (Ric : Real -> M -> Idx -> Idx -> Real)
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (nabla2H : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) :
    ∀ (t : RicciFlower.Realized.RealTimeInterval.RegularTime D) (x : M)
      (j k : Idx),
      HasDerivWithinAt
        (fun s : Real => Ric s x j k)
        (generalRicciVariationFirstRHSInFrame gInv nabla2H (t : Real) x j k)
        D.carrier
        (t : Real) := by
  sorry

/-- Book scaffold for Lemma `lem:general_evolution_revisited`, item 4, first
scalar variation formula. -/
theorem lem_general_evolution_revisited_scalar_first_inFrame
    {D : RicciFlower.Realized.RealTimeInterval}
    (scalar : Real -> M -> Real)
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (hComp Ric : Real -> M -> Idx -> Idx -> Real)
    (nabla2H : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) :
    ∀ (t : RicciFlower.Realized.RealTimeInterval.RegularTime D) (x : M),
      HasDerivWithinAt
        (fun s : Real => scalar s x)
        (generalScalarVariationRHSInFrame gInv hComp Ric nabla2H (t : Real) x)
        D.carrier
        (t : Real) := by
  sorry

/-- Ricci-flow RHS for
`eq:riemann_curvature_three_one_ricci_flow_one`. -/
def riemann13RicciFlowOneRHSInFrame
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k l : Idx) : Real :=
  ∑ p : Idx,
    gInv t x l p *
      (-nabla2Ric t x i j k p - nabla2Ric t x i k j p +
        nabla2Ric t x i p j k + nabla2Ric t x j i k p +
        nabla2Ric t x j k i p - nabla2Ric t x j p i k)

/-- MSM110 Chapter 6.1, equation
`eq:riemann_curvature_three_one_ricci_flow_one`, stated as a future
book-facing `(3,1)` component theorem. -/
theorem eq_riemann_curvature_three_one_ricci_flow_one
    {D : RicciFlower.Realized.RealTimeInterval}
    (Rm13 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) :
    ∀ (t : RicciFlower.Realized.RealTimeInterval.RegularTime D) (x : M)
      (i j k l : Idx),
      HasDerivWithinAt
        (fun s : Real => Rm13 s x i j k l)
        (riemann13RicciFlowOneRHSInFrame gInv nabla2Ric (t : Real) x i j k l)
        D.carrier
        (t : Real) := by
  sorry

/-- RHS for `eq:ricci_tensor_ricci_flow_one`. -/
def ricciTensorRicciFlowOneRHSInFrame
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (roughLapRic scalarHessian :
      Real -> M -> Idx -> Idx -> Real)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (j k : Idx) : Real :=
  roughLapRic t x j k + scalarHessian t x j k -
    ∑ p : Idx, ∑ q : Idx,
      gInv t x p q *
        (nabla2Ric t x q j k p + nabla2Ric t x q k j p)

/-- MSM110 Chapter 6.1, equation `eq:ricci_tensor_ricci_flow_one`. -/
theorem eq_ricci_tensor_ricci_flow_one
    {D : RicciFlower.Realized.RealTimeInterval}
    (Ric : Real -> M -> Idx -> Idx -> Real)
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (roughLapRic scalarHessian :
      Real -> M -> Idx -> Idx -> Real)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) :
    ∀ (t : RicciFlower.Realized.RealTimeInterval.RegularTime D) (x : M)
      (j k : Idx),
      HasDerivWithinAt
        (fun s : Real => Ric s x j k)
        (ricciTensorRicciFlowOneRHSInFrame
          gInv roughLapRic scalarHessian nabla2Ric (t : Real) x j k)
        D.carrier
        (t : Real) := by
  sorry

/-- Component lower-bound predicate used by the book-facing scalar maximum
principle statement. -/
def ScalarLowerBoundOn
    {D : RicciFlower.Realized.RealTimeInterval}
    (scalar : Real -> M -> Real) (rho : Real) : Prop :=
  ∀ (t : RicciFlower.Realized.RealTimeInterval.RegularTime D) (x : M),
    rho <= scalar (t : Real) x

/-- MSM110 Chapter 6.1, Lemma `lem:scalar_positivity_is_preserved`. -/
theorem lem_scalar_positivity_is_preserved
    {D : RicciFlower.Realized.RealTimeInterval}
    (scalar scalarLap ricciNormSq : Real -> M -> Real)
    (rho : Real)
    (hinit : ∀ x : M, rho <= scalar 0 x)
    (hevol : ScalarEvolutionEquationOn (D := D) scalar scalarLap ricciNormSq)
    (hnonneg :
      ∀ (t : RicciFlower.Realized.RealTimeInterval.RegularTime D) (x : M),
        0 <= ricciNormSq (t : Real) x) :
    ScalarLowerBoundOn (D := D) scalar rho := by
  sorry

/-- RHS for the dimension-three Ricci tensor evolution formula. -/
def ricciTensorRicciFlowDimensionThreeRHSInFrame
    (metricComp gInv : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (Ric : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (scalar ricciNormSq : Real -> M -> Real)
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (t : Real) (x : M) (j k : Fin 3) : Real :=
  roughLapRic t x j k + 3 * scalar t x * Ric t x j k -
    6 * (∑ p : Fin 3, ∑ q : Fin 3,
      gInv t x p q * Ric t x j p * Ric t x q k) +
    (2 * ricciNormSq t x - scalar t x ^ 2) * metricComp t x j k

/-- MSM110 Chapter 6.1, equation
`eq:orthogonal_decomposition_of_riemann_three_d`. -/
theorem eq_orthogonal_decomposition_of_riemann_three_d
    (Rm04 : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (metricComp Ric : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (scalar : Real -> M -> Real) :
    ∀ (t : Real) (x : M) (i j k l : Fin 3),
      Rm04 t x i j k l =
        Ric t x i l * metricComp t x j k +
          Ric t x j k * metricComp t x i l -
          Ric t x i k * metricComp t x j l -
          Ric t x j l * metricComp t x i k -
          (1 / 2 : Real) * scalar t x *
            (metricComp t x i l * metricComp t x j k -
              metricComp t x i k * metricComp t x j l) := by
  sorry

/-- MSM110 Chapter 6.1, equation
`eq:ricci_tensor_ricci_flow_dimension_three`. -/
theorem eq_ricci_tensor_ricci_flow_dimension_three
    {D : RicciFlower.Realized.RealTimeInterval}
    (Ric : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (metricComp gInv : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (scalar ricciNormSq : Real -> M -> Real)
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real) :
    ∀ (t : RicciFlower.Realized.RealTimeInterval.RegularTime D) (x : M)
      (j k : Fin 3),
      HasDerivWithinAt
        (fun s : Real => Ric s x j k)
        (ricciTensorRicciFlowDimensionThreeRHSInFrame
          metricComp gInv Ric scalar ricciNormSq roughLapRic (t : Real) x j k)
        D.carrier
        (t : Real) := by
  sorry

/-- Quadratic-form nonnegativity for a symmetric two-tensor in a fixed frame. -/
def TwoTensorNonnegativeInFrame
    (T : Real -> M -> Idx -> Idx -> Real) (t : Real) (x : M) : Prop :=
  ∀ v : Idx -> Real,
    0 <= ∑ i : Idx, ∑ j : Idx, v i * v j * T t x i j

/-- Quadratic-form positivity for a symmetric two-tensor in a fixed frame. -/
def TwoTensorPositiveInFrame
    (T : Real -> M -> Idx -> Idx -> Real) (t : Real) (x : M) : Prop :=
  ∀ v : Idx -> Real,
    (∃ i : Idx, v i ≠ 0) ->
      0 < ∑ i : Idx, ∑ j : Idx, v i * v j * T t x i j

/-- MSM110 Chapter 6.1, Corollary `cor:ricci_positivity_is_preserved`,
nonnegative form. -/
theorem cor_ricci_nonnegativity_is_preserved
    {D : RicciFlower.Realized.RealTimeInterval}
    (Ric : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (metricComp gInv : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (scalar ricciNormSq : Real -> M -> Real)
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (hevol :
      ∀ (t : RicciFlower.Realized.RealTimeInterval.RegularTime D) (x : M)
        (j k : Fin 3),
        HasDerivWithinAt (fun s : Real => Ric s x j k)
          (ricciTensorRicciFlowDimensionThreeRHSInFrame
            metricComp gInv Ric scalar ricciNormSq roughLapRic (t : Real) x j k)
          D.carrier (t : Real))
    (hinit : ∀ x : M, TwoTensorNonnegativeInFrame Ric 0 x) :
    ∀ (t : RicciFlower.Realized.RealTimeInterval.RegularTime D) (x : M),
      TwoTensorNonnegativeInFrame Ric (t : Real) x := by
  sorry

/-- MSM110 Chapter 6.1, Corollary `cor:ricci_positivity_is_preserved`,
positive form. -/
theorem cor_ricci_positivity_is_preserved
    {D : RicciFlower.Realized.RealTimeInterval}
    (Ric : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (metricComp gInv : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (scalar ricciNormSq : Real -> M -> Real)
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (hevol :
      ∀ (t : RicciFlower.Realized.RealTimeInterval.RegularTime D) (x : M)
        (j k : Fin 3),
        HasDerivWithinAt (fun s : Real => Ric s x j k)
          (ricciTensorRicciFlowDimensionThreeRHSInFrame
            metricComp gInv Ric scalar ricciNormSq roughLapRic (t : Real) x j k)
          D.carrier (t : Real))
    (hinit : ∀ x : M, TwoTensorPositiveInFrame Ric 0 x) :
    ∀ (t : RicciFlower.Realized.RealTimeInterval.RegularTime D) (x : M),
      TwoTensorPositiveInFrame Ric (t : Real) x := by
  sorry

/-- RHS for the `(3,1)` Riemann heat equation
`eq:riemann_curvature_three_one_ricci_flow`. -/
def riemann13HeatRHSInFrame
    (Rm13 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (gInv ricciOneUp : Real -> M -> Idx -> Idx -> Real)
    (roughLapRm13 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k l : Idx) : Real :=
  roughLapRm13 t x i j k l +
    (∑ p : Idx, ∑ q : Idx, ∑ r : Idx,
      gInv t x p q *
        (Rm13 t x i j p r * Rm13 t x r q k l -
          2 * Rm13 t x p i k r * Rm13 t x j q r l +
          2 * Rm13 t x p i r l * Rm13 t x j q k r)) -
    ((∑ p : Idx, ricciOneUp t x i p * Rm13 t x p j k l) +
      (∑ p : Idx, ricciOneUp t x j p * Rm13 t x i p k l) +
      (∑ p : Idx, ricciOneUp t x k p * Rm13 t x i j p l)) +
    (∑ p : Idx, ricciOneUp t x p l * Rm13 t x i j k p)

/-- MSM110 Chapter 6.1, equation
`eq:riemann_curvature_three_one_ricci_flow`. -/
theorem eq_riemann_curvature_three_one_ricci_flow
    {D : RicciFlower.Realized.RealTimeInterval}
    (Rm13 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (gInv ricciOneUp : Real -> M -> Idx -> Idx -> Real)
    (roughLapRm13 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) :
    ∀ (t : RicciFlower.Realized.RealTimeInterval.RegularTime D) (x : M)
      (i j k l : Idx),
      HasDerivWithinAt
        (fun s : Real => Rm13 s x i j k l)
        (riemann13HeatRHSInFrame Rm13 gInv ricciOneUp roughLapRm13
          (t : Real) x i j k l)
        D.carrier
        (t : Real) := by
  sorry

/-- RHS for the lowered `(4,0)` Riemann heat equation
`eq:riemann_curvature_four_zero_ricci_flow`. -/
def riemann04HeatRHSInFrame
    (Rm13 Rm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (gInv ricciOneUp : Real -> M -> Idx -> Idx -> Real)
    (roughLapRm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k l : Idx) : Real :=
  roughLapRm04 t x i j k l +
    (∑ p : Idx, ∑ q : Idx, ∑ r : Idx,
      gInv t x p q *
        (Rm13 t x i j p r * Rm04 t x r q k l -
          2 * Rm13 t x p i k r * Rm04 t x j q r l +
          2 * Rm04 t x p i r l * Rm13 t x j q k r)) -
    ((∑ p : Idx, ricciOneUp t x i p * Rm04 t x p j k l) +
      (∑ p : Idx, ricciOneUp t x j p * Rm04 t x i p k l) +
      (∑ p : Idx, ricciOneUp t x k p * Rm04 t x i j p l) +
      (∑ p : Idx, ricciOneUp t x l p * Rm04 t x i j k p))

/-- MSM110 Chapter 6.1, equation
`eq:riemann_curvature_four_zero_ricci_flow`. -/
theorem eq_riemann_curvature_four_zero_ricci_flow
    {D : RicciFlower.Realized.RealTimeInterval}
    (Rm13 Rm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (gInv ricciOneUp : Real -> M -> Idx -> Idx -> Real)
    (roughLapRm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) :
    ∀ (t : RicciFlower.Realized.RealTimeInterval.RegularTime D) (x : M)
      (i j k l : Idx),
      HasDerivWithinAt
        (fun s : Real => Rm04 s x i j k l)
        (riemann04HeatRHSInFrame Rm13 Rm04 gInv ricciOneUp roughLapRm04
          (t : Real) x i j k l)
        D.carrier
        (t : Real) := by
  sorry

/-- The quadratic tensor `B_ijkl` from equation `eq:define_bijkl`. -/
def bTensorInFrame
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (Rm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k l : Idx) : Real :=
  -∑ p : Idx, ∑ r : Idx, ∑ q : Idx, ∑ s : Idx,
    gInv t x p r * gInv t x q s *
      Rm04 t x i p j q * Rm04 t x k r l s

/-- Algebraic identities `B_ijkl = B_jilk = B_klij`. -/
def BTensorAlgebraicIdentitiesInFrame
    (B : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ (t : Real) (x : M) (i j k l : Idx),
    B t x i j k l = B t x j i l k ∧
      B t x i j k l = B t x k l i j

/-- MSM110 Chapter 6.1, equation `eq:bijkl_algebraic_identities`. -/
theorem eq_bijkl_algebraic_identities
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (Rm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) :
    BTensorAlgebraicIdentitiesInFrame
      (bTensorInFrame (M := M) gInv Rm04) := by
  sorry

/-- RHS for equation `eq:rm_minus_evolution_minus_in_minus_terms_minus_of_minus_bs`. -/
def riemann04BTensorRHSInFrame
    (Rm04 B : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (ricciOneUp : Real -> M -> Idx -> Idx -> Real)
    (roughLapRm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k l : Idx) : Real :=
  roughLapRm04 t x i j k l +
    2 * (B t x i j k l - B t x i j l k +
      B t x i k j l - B t x i l j k) -
    ((∑ p : Idx, ricciOneUp t x i p * Rm04 t x p j k l) +
      (∑ p : Idx, ricciOneUp t x j p * Rm04 t x i p k l) +
      (∑ p : Idx, ricciOneUp t x k p * Rm04 t x i j p l) +
      (∑ p : Idx, ricciOneUp t x l p * Rm04 t x i j k p))

/-- MSM110 Chapter 6.1, equation
`eq:rm_minus_evolution_minus_in_minus_terms_minus_of_minus_bs`. -/
theorem eq_rm_evolution_in_terms_of_bs
    {D : RicciFlower.Realized.RealTimeInterval}
    (Rm04 B : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (ricciOneUp : Real -> M -> Idx -> Idx -> Real)
    (roughLapRm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) :
    ∀ (t : RicciFlower.Realized.RealTimeInterval.RegularTime D) (x : M)
      (i j k l : Idx),
      HasDerivWithinAt
        (fun s : Real => Rm04 s x i j k l)
        (riemann04BTensorRHSInFrame Rm04 B ricciOneUp roughLapRm04
          (t : Real) x i j k l)
        D.carrier
        (t : Real) := by
  sorry

end

end Section01
end Chapter06
end MSM110
end BK
