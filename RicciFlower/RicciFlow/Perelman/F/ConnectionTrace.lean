import RicciFlower.RicciFlow.Perelman.F.ChartTrace


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
# Perelman F Connection Trace

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

private theorem partialDeriv_sum_mul2
    (U :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        E -> Real)
    (B :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> E -> Real)
    (dU :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (dB :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (y0 : E)
    (hUdiff : ∀ i j : CoordinateIdx (𝕜 := Real) E,
      DifferentiableAt Real (U i j) y0)
    (hBdiff : ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      DifferentiableAt Real (B p i j) y0)
    (hUderiv : ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (U i j) y0 = dU p i j)
    (hBderiv : ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (B p i j) y0 = dB p p i j) :
    (∑ p : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (fun y : E =>
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              U i j y * B p i j y) y0) =
      ∑ p : CoordinateIdx (𝕜 := Real) E,
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            (dU p i j * B p i j y0 + U i j y0 * dB p p i j) := by
  classical
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold RicciFlower.Analysis.DivergenceTheorem.partialDeriv
  have hi :
      ∀ i ∈ (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)),
        DifferentiableAt Real
          (fun y : E =>
            ∑ j : CoordinateIdx (𝕜 := Real) E, U i j y * B p i j y) y0 := by
    intro i _
    exact DifferentiableAt.fun_sum fun j _ => (hUdiff i j).mul (hBdiff p i j)
  rw [fderiv_fun_sum hi]
  simp only [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hj :
      ∀ j ∈ (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)),
        DifferentiableAt Real (fun y : E => U i j y * B p i j y) y0 := by
    intro j _
    exact (hUdiff i j).mul (hBdiff p i j)
  rw [fderiv_fun_sum hj]
  simp only [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_fun_mul (hUdiff i j) (hBdiff p i j)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  have hU' :
      (fderiv Real (U i j) y0) ((Module.finBasis Real E) p) = dU p i j := by
    simpa [RicciFlower.Analysis.DivergenceTheorem.partialDeriv] using
      hUderiv p i j
  have hB' :
      (fderiv Real (B p i j) y0) ((Module.finBasis Real E) p) =
        dB p p i j := by
    simpa [RicciFlower.Analysis.DivergenceTheorem.partialDeriv] using
      hBderiv p i j
  rw [hU', hB']
  ring

/-- Product-rule producer for the derivative input consumed by
`connTraceRaw_eq_gamma`.

It expands the fixed-chart derivative of the explicit trace-field coefficient
`sum_i sum_j g^{ij} A^p_ij` into the inverse-metric derivative term plus the
component derivative of `A`. -/
theorem connTraceDeriv
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (gInvDeriv :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (componentDeriv :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (x : M)
    (hgInvDiff : ∀ i j : CoordinateIdx (𝕜 := Real) E,
      DifferentiableAt Real
        (fun y : E =>
          inverseMetricFlatModelInChart_component (I := I) g x i j y)
        (extChartAt I x x))
    (hADiff : ∀ p i j : CoordinateIdx (𝕜 := Real) E,
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
    (hgInvDeriv : ∀ p i j : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (fun y : E =>
          inverseMetricFlatModelInChart_component (I := I) g x i j y)
        (extChartAt I x x) = gInvDeriv p i j)
    (hADeriv : ∀ p i j : CoordinateIdx (𝕜 := Real) E,
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
        (extChartAt I x x) = componentDeriv p p i j) :
      (∑ p : CoordinateIdx (𝕜 := Real) E,
        RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
          (fun y : E =>
            ∑ i : CoordinateIdx (𝕜 := Real) E,
              ∑ j : CoordinateIdx (𝕜 := Real) E,
                inverseMetricFlatModelInChart_component (I := I) g x i j y *
                  (A ((extChartAt I x).symm y)
                    (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
                      (I := I) (M := M) 1 x
                      ((continuousMultilinearMap_basis
                        (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                        (fun _ : Fin 1 => p)) ((extChartAt I x).symm y)))
                    (fun q : Fin 2 =>
                      coordinateFrameAt (I := I) x (if q = 0 then i else j)
                        ((extChartAt I x).symm y)))
          (extChartAt I x x)) =
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              (gInvDeriv p i j *
                  componentRS (I := I)
                    (coordinateFrameAt_basis (I := I) x
                      (coordinateFrameAt_mem (I := I) x))
                    (A x) (fun _ : Fin 1 => p)
                    (fun q : Fin 2 => if q = 0 then i else j) +
                inverseMetricFlatModelInChart_component (I := I) g x i j
                    (extChartAt I x x) *
                  componentDeriv p p i j) := by
  classical
  let U :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        E -> Real := fun i j y =>
    inverseMetricFlatModelInChart_component (I := I) g x i j y
  let B :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> E -> Real := fun p i j y =>
    (A ((extChartAt I x).symm y)
      (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 1 x
        ((continuousMultilinearMap_basis
          (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
          (fun _ : Fin 1 => p)) ((extChartAt I x).symm y)))
      (fun q : Fin 2 =>
        coordinateFrameAt (I := I) x (if q = 0 then i else j)
          ((extChartAt I x).symm y))
  have hprod :=
    partialDeriv_sum_mul2 (U := U) (B := B)
      (dU := gInvDeriv) (dB := componentDeriv)
      (y0 := extChartAt I x x)
      (by simpa [U] using hgInvDiff)
      (by simpa [B] using hADiff)
      (by simpa [U] using hgInvDeriv)
      (by simpa [B] using hADeriv)
  have hBcenter :
      ∀ p i j : CoordinateIdx (𝕜 := Real) E,
        B p i j (extChartAt I x x) =
          componentRS (I := I)
            (coordinateFrameAt_basis (I := I) x
              (coordinateFrameAt_mem (I := I) x))
            (A x) (fun _ : Fin 1 => p)
            (fun q : Fin 2 => if q = 0 then i else j) := by
    intro p i j
    haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      change IsManifold I ∞ M
      infer_instance
    have hsymm : (extChartAt I x).symm (extChartAt I x x) = x :=
      (extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)
    have hconst :
        Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 1 x
          ((continuousMultilinearMap_basis
            (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
            (fun _ : Fin 1 => p)) x =
          basisTensor0S (I := I)
            (coordinateFrameAt_basis (I := I) x
              (coordinateFrameAt_mem (I := I) x))
            (fun _ : Fin 1 => p) :=
      constInChart_basisTensor0S_coordFrame (𝕜 := Real) (I := I)
        (M := M) (r := 1) x (coordinateFrameAt_mem (I := I) x)
        (fun _ : Fin 1 => p)
    calc
      B p i j (extChartAt I x x) =
          (A ((extChartAt I x).symm (extChartAt I x x))
            (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x
              ((continuousMultilinearMap_basis
                (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                (fun _ : Fin 1 => p)) ((extChartAt I x).symm (extChartAt I x x))))
            (fun q : Fin 2 =>
          coordinateFrameAt (I := I) x (if q = 0 then i else j)
            ((extChartAt I x).symm (extChartAt I x x))) := by
          rfl
      _ =
          (A x
            (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x
              ((continuousMultilinearMap_basis
                (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                (fun _ : Fin 1 => p)) x))
            (fun q : Fin 2 =>
              coordinateFrameAt (I := I) x (if q = 0 then i else j) x) := by
          rw [hsymm]
      _ =
          componentRS (I := I)
            (coordinateFrameAt_basis (I := I) x
              (coordinateFrameAt_mem (I := I) x))
            (A x) (fun _ : Fin 1 => p)
            (fun q : Fin 2 => if q = 0 then i else j) := by
          rw [componentRS]
          simp [hconst, component0S, coordinateFrameAt_basis_apply]
  calc
    (∑ p : CoordinateIdx (𝕜 := Real) E,
      RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (fun y : E =>
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              inverseMetricFlatModelInChart_component (I := I) g x i j y *
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
        =
      ∑ p : CoordinateIdx (𝕜 := Real) E,
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            (gInvDeriv p i j * B p i j (extChartAt I x x) +
              U i j (extChartAt I x x) * componentDeriv p p i j) := by
      simpa [U, B] using hprod
    _ =
      ∑ p : CoordinateIdx (𝕜 := Real) E,
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            (gInvDeriv p i j *
                componentRS (I := I)
                  (coordinateFrameAt_basis (I := I) x
                    (coordinateFrameAt_mem (I := I) x))
                  (A x) (fun _ : Fin 1 => p)
                  (fun q : Fin 2 => if q = 0 then i else j) +
              inverseMetricFlatModelInChart_component (I := I) g x i j
                  (extChartAt I x x) *
                componentDeriv p p i j) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hBcenter p i j]

/-- The density-derivative correction in the Voss-Weyl divergence formula is
the Christoffel trace correction for the Levi-Civita connection. -/
theorem connTraceDensityCorr
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (g : SmoothRiemannianMetric I M)
    (hLC : RicciFlower.LeviCivita.IsLeviCivita (I := I) cov g)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (x : M) :
    (∑ p : CoordinateIdx (𝕜 := Real) E,
      (∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x x) *
            componentRS (I := I)
              (coordinateFrameAt_basis (I := I) x
                (coordinateFrameAt_mem (I := I) x))
              (A x) (fun _ : Fin 1 => p)
              (fun q : Fin 2 => if q = 0 then i else j)) *
        RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
          (RicciFlower.Analysis.DivergenceTheorem.chartDensityOnE
            (I := I) g x) (extChartAt I x x)) /
      RicciFlower.Analysis.Volume.chartDensity (I := I) g x x
      =
    ∑ p : CoordinateIdx (𝕜 := Real) E,
      (∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x x) *
            componentRS (I := I)
              (coordinateFrameAt_basis (I := I) x
                (coordinateFrameAt_mem (I := I) x))
              (A x) (fun _ : Fin 1 => p)
              (fun q : Fin 2 => if q = 0 then i else j)) *
        (∑ a : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame cov
            (coordinateFrameAt (I := I) x)
            (coordinateFrameAt_isLocalFrame_one (I := I) x) x p a a) := by
  classical
  let C : CoordinateIdx (𝕜 := Real) E → Real := fun p =>
    ∑ i : CoordinateIdx (𝕜 := Real) E,
      ∑ j : CoordinateIdx (𝕜 := Real) E,
        inverseMetricFlatModelInChart_component (I := I) g x i j
            (extChartAt I x x) *
          componentRS (I := I)
            (coordinateFrameAt_basis (I := I) x
              (coordinateFrameAt_mem (I := I) x))
            (A x) (fun _ : Fin 1 => p)
            (fun q : Fin 2 => if q = 0 then i else j)
  let ρ : Real := RicciFlower.Analysis.Volume.chartDensity (I := I) g x x
  let dρ : CoordinateIdx (𝕜 := Real) E → Real := fun p =>
    RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
      (RicciFlower.Analysis.DivergenceTheorem.chartDensityOnE
        (I := I) g x) (extChartAt I x x)
  have htrace :
      ∀ p : CoordinateIdx (𝕜 := Real) E,
        dρ p / ρ =
          ∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x p a a := by
    intro p
    simpa [dρ, ρ] using
      RicciFlower.LeviCivita.lcTrace_logDensity (I := I) g hLC x p
  change
    (∑ p : CoordinateIdx (𝕜 := Real) E, C p * dρ p) / ρ =
      ∑ p : CoordinateIdx (𝕜 := Real) E,
        C p *
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x p a a)
  rw [div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [show C p * dρ p * ρ⁻¹ = C p * (dρ p / ρ) by
    rw [div_eq_mul_inv]
    ring]
  rw [htrace p]

/-- Raw divergence bridge after the two contracted component identities have
been supplied: the Voss-Weyl coordinate divergence of `tr_g A` equals the
inverse-metric contraction of `nabla_p A^p_ij`.

The remaining producers for formula 5.10 are now precisely the two contracted
identities `hUtrace` and `hAtrace`: the first is `nabla g^{-1}=0` contracted
with `A`, and the second is the contracted coordinate formula for the
covariant derivative of the `(1,2)` tensor `A`. -/
theorem connTraceRaw_eq_gamma
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (g : SmoothRiemannianMetric I M)
    (hLC : RicciFlower.LeviCivita.IsLeviCivita (I := I) cov g)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (nablaChristoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (gInvDeriv :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (componentDeriv :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (x : M)
    (hderiv :
      (∑ p : CoordinateIdx (𝕜 := Real) E,
        RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
          (fun y : E =>
            ∑ i : CoordinateIdx (𝕜 := Real) E,
              ∑ j : CoordinateIdx (𝕜 := Real) E,
                inverseMetricFlatModelInChart_component (I := I) g x i j y *
                  (A ((extChartAt I x).symm y)
                    (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
                      (I := I) (M := M) 1 x
                      ((continuousMultilinearMap_basis
                        (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                        (fun _ : Fin 1 => p)) ((extChartAt I x).symm y)))
                    (fun q : Fin 2 =>
                      coordinateFrameAt (I := I) x (if q = 0 then i else j)
                        ((extChartAt I x).symm y)))
          (extChartAt I x x)) =
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              (gInvDeriv p i j *
                  componentRS (I := I)
                    (coordinateFrameAt_basis (I := I) x
                      (coordinateFrameAt_mem (I := I) x))
                    (A x) (fun _ : Fin 1 => p)
                    (fun q : Fin 2 => if q = 0 then i else j) +
                inverseMetricFlatModelInChart_component (I := I) g x i j
                    (extChartAt I x x) *
                  componentDeriv p p i j))
    (hUtrace : ∀ d : CoordinateIdx (𝕜 := Real) E,
      (∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          gInvDeriv d i j *
            componentRS (I := I)
              (coordinateFrameAt_basis (I := I) x
                (coordinateFrameAt_mem (I := I) x))
              (A x) (fun _ : Fin 1 => d)
              (fun q : Fin 2 => if q = 0 then i else j)) =
        -∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x i j
                (extChartAt I x x) *
              ((∑ a : CoordinateIdx (𝕜 := Real) E,
                christoffelSymbolInFrame cov
                  (coordinateFrameAt (I := I) x)
                  (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
                  componentRS (I := I)
                    (coordinateFrameAt_basis (I := I) x
                      (coordinateFrameAt_mem (I := I) x))
                    (A x) (fun _ : Fin 1 => d)
                    (fun q : Fin 2 => if q = 0 then a else j)) +
               (∑ a : CoordinateIdx (𝕜 := Real) E,
                christoffelSymbolInFrame cov
                  (coordinateFrameAt (I := I) x)
                  (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
                  componentRS (I := I)
                    (coordinateFrameAt_basis (I := I) x
                      (coordinateFrameAt_mem (I := I) x))
                    (A x) (fun _ : Fin 1 => d)
                    (fun q : Fin 2 => if q = 0 then i else a))))
    (hAtrace : ∀ i j : CoordinateIdx (𝕜 := Real) E,
      (∑ d : CoordinateIdx (𝕜 := Real) E,
        nablaChristoffelVariation x d d i j) =
        (∑ d : CoordinateIdx (𝕜 := Real) E, componentDeriv d d i j) +
          (∑ d : CoordinateIdx (𝕜 := Real) E,
            componentRS (I := I)
              (coordinateFrameAt_basis (I := I) x
                (coordinateFrameAt_mem (I := I) x))
              (A x) (fun _ : Fin 1 => d)
              (fun q : Fin 2 => if q = 0 then i else j) *
              (∑ a : CoordinateIdx (𝕜 := Real) E,
                christoffelSymbolInFrame cov
                  (coordinateFrameAt (I := I) x)
                  (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a a)) -
          (∑ d : CoordinateIdx (𝕜 := Real) E,
            ((∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
                componentRS (I := I)
                  (coordinateFrameAt_basis (I := I) x
                    (coordinateFrameAt_mem (I := I) x))
                  (A x) (fun _ : Fin 1 => d)
                  (fun q : Fin 2 => if q = 0 then a else j)) +
             (∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
                componentRS (I := I)
                  (coordinateFrameAt_basis (I := I) x
                    (coordinateFrameAt_mem (I := I) x))
                  (A x) (fun _ : Fin 1 => d)
                  (fun q : Fin 2 => if q = 0 then i else a))))) :
    connTraceRawDiv (I := I) g A x =
      gammaRawDivergenceTrace (I := I) g nablaChristoffelVariation x := by
  classical
  let U : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j =>
      inverseMetricFlatModelInChart_component (I := I) g x i j
        (extChartAt I x x)
  let Acomp :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real := fun p i j =>
    componentRS (I := I)
      (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
      (A x) (fun _ : Fin 1 => p) (fun q : Fin 2 => if q = 0 then i else j)
  let Gamma :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real := fun d a k =>
    christoffelSymbolInFrame cov
      (coordinateFrameAt (I := I) x)
      (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k
  have hraw := rawDivTraceAlg
    (U := U) (dU := gInvDeriv) (A := Acomp)
    (dA := componentDeriv)
    (nablaA := fun d k i j => nablaChristoffelVariation x d k i j)
    (Gamma := Gamma)
    (by simpa [U, Acomp, Gamma] using hUtrace)
    (by simpa [U, Acomp, Gamma] using hAtrace)
  rw [connTraceRawDiv_chart_explicit (I := I) g A x]
  rw [hderiv]
  rw [connTraceDensityCorr (I := I) (cov := cov) g hLC A x]
  simpa [gammaRawDivergenceTrace, U, Acomp, Gamma] using hraw

/-- The contracted `nabla g^{-1}=0` input needed by
`connTraceRaw_eq_gamma`.  This is the inverse-metric cancellation specialized
to the point-centered coordinate frame and the upper component slice `A^d_ij`
of the connection-variation tensor. -/
theorem connTraceUTrace
    [T2Space M] [SigmaCompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (gInvDeriv :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x : M)
    (hginvDeriv :
      ∀ d i j : CoordinateIdx (𝕜 := Real) E,
        gInvDeriv d i j =
          extDerivFun (I := I)
            (fun y : M =>
              inverseMetricFlatModelInChart_component (I := I) g x i j
                (extChartAt I x y))
            x (coordinateFrameAt (I := I) x d x))
    (hzero :
      ∀ d i j : CoordinateIdx (𝕜 := Real) E,
        RicciFlower.Coordinates.inverseMetricCovDerivForMetricCompInFrame
          (I := I)
          (fun y : M => fun a b : CoordinateIdx (𝕜 := Real) E =>
            inverseMetricFlatModelInChart_component (I := I) g x a b
              (extChartAt I x y))
          cov (coordinateFrameAt (I := I) x)
          (coordinateFrameAt_isLocalFrame_one (I := I) x)
          x d i j = 0) :
    ∀ d : CoordinateIdx (𝕜 := Real) E,
      (∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          gInvDeriv d i j *
            componentRS (I := I)
              (coordinateFrameAt_basis (I := I) x
                (coordinateFrameAt_mem (I := I) x))
              (A x) (fun _ : Fin 1 => d)
              (fun q : Fin 2 => if q = 0 then i else j)) =
        -∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x i j
                (extChartAt I x x) *
              ((∑ a : CoordinateIdx (𝕜 := Real) E,
                christoffelSymbolInFrame cov
                  (coordinateFrameAt (I := I) x)
                  (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
                  componentRS (I := I)
                    (coordinateFrameAt_basis (I := I) x
                      (coordinateFrameAt_mem (I := I) x))
                    (A x) (fun _ : Fin 1 => d)
                    (fun q : Fin 2 => if q = 0 then a else j)) +
               (∑ a : CoordinateIdx (𝕜 := Real) E,
                christoffelSymbolInFrame cov
                  (coordinateFrameAt (I := I) x)
                  (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
                  componentRS (I := I)
                    (coordinateFrameAt_basis (I := I) x
                      (coordinateFrameAt_mem (I := I) x))
                    (A x) (fun _ : Fin 1 => d)
                    (fun q : Fin 2 => if q = 0 then i else a))) := by
  classical
  intro d
  let Acomp : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j =>
      componentRS (I := I)
        (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
        (A x) (fun _ : Fin 1 => d) (fun q : Fin 2 => if q = 0 then i else j)
  have hcancel :=
    RicciFlower.LeviCivita.gInvTraceCancel
      (I := I)
      (gInv := fun y : M => fun a b : CoordinateIdx (𝕜 := Real) E =>
        inverseMetricFlatModelInChart_component (I := I) g x a b
          (extChartAt I x y))
      (metricDot := fun _ : M => Acomp)
      (cov := cov)
      (frame := coordinateFrameAt (I := I) x)
      (hframe := coordinateFrameAt_isLocalFrame_one (I := I) x)
      (x := x) (d := d) (hzero d)
  calc
    (∑ i : CoordinateIdx (𝕜 := Real) E,
      ∑ j : CoordinateIdx (𝕜 := Real) E,
        gInvDeriv d i j *
          componentRS (I := I)
            (coordinateFrameAt_basis (I := I) x
              (coordinateFrameAt_mem (I := I) x))
            (A x) (fun _ : Fin 1 => d)
            (fun q : Fin 2 => if q = 0 then i else j))
        =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          extDerivFun (I := I)
              (fun y : M =>
                inverseMetricFlatModelInChart_component (I := I) g x i j
                  (extChartAt I x y))
              x (coordinateFrameAt (I := I) x d x) *
            Acomp i j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hginvDeriv d i j]
    _ =
      -∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x x) *
            ((∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
                Acomp a j) +
             (∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
                Acomp i a)) := by
        simpa [Acomp] using hcancel
    _ =
      -∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x x) *
            ((∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
                componentRS (I := I)
                  (coordinateFrameAt_basis (I := I) x
                    (coordinateFrameAt_mem (I := I) x))
                  (A x) (fun _ : Fin 1 => d)
                  (fun q : Fin 2 => if q = 0 then a else j)) +
             (∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
                componentRS (I := I)
                  (coordinateFrameAt_basis (I := I) x
                    (coordinateFrameAt_mem (I := I) x))
                  (A x) (fun _ : Fin 1 => d)
                  (fun q : Fin 2 => if q = 0 then i else a))) := rfl

/-- Contracted coordinate formula for `nabla_p A^p_ij`, packaged in the exact
shape consumed by `connTraceRaw_eq_gamma`. -/
theorem connTraceATrace
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (nablaChristoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (componentDeriv :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (x : M)
    (hNabla : ∀ d k i j : CoordinateIdx (𝕜 := Real) E,
      nablaChristoffelVariation x d k i j =
        componentDeriv d k i j +
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
    (hGamma : ∀ d a k : CoordinateIdx (𝕜 := Real) E,
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k =
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x a d k) :
    ∀ i j : CoordinateIdx (𝕜 := Real) E,
      (∑ d : CoordinateIdx (𝕜 := Real) E,
        nablaChristoffelVariation x d d i j) =
        (∑ d : CoordinateIdx (𝕜 := Real) E, componentDeriv d d i j) +
          (∑ d : CoordinateIdx (𝕜 := Real) E,
            componentRS (I := I)
              (coordinateFrameAt_basis (I := I) x
                (coordinateFrameAt_mem (I := I) x))
              (A x) (fun _ : Fin 1 => d)
              (fun q : Fin 2 => if q = 0 then i else j) *
              (∑ a : CoordinateIdx (𝕜 := Real) E,
                christoffelSymbolInFrame cov
                  (coordinateFrameAt (I := I) x)
                  (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a a)) -
          (∑ d : CoordinateIdx (𝕜 := Real) E,
            ((∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
                componentRS (I := I)
                  (coordinateFrameAt_basis (I := I) x
                    (coordinateFrameAt_mem (I := I) x))
                  (A x) (fun _ : Fin 1 => d)
                  (fun q : Fin 2 => if q = 0 then a else j)) +
             (∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
                componentRS (I := I)
                  (coordinateFrameAt_basis (I := I) x
                    (coordinateFrameAt_mem (I := I) x))
                  (A x) (fun _ : Fin 1 => d)
                  (fun q : Fin 2 => if q = 0 then i else a)))) := by
  classical
  intro i j
  let Acomp :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real := fun p i j =>
    componentRS (I := I)
      (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
      (A x) (fun _ : Fin 1 => p) (fun q : Fin 2 => if q = 0 then i else j)
  let Gamma :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real := fun d a k =>
    christoffelSymbolInFrame cov
      (coordinateFrameAt (I := I) x)
      (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k
  have h :=
    traceNablaAlg (A := Acomp) (dA := componentDeriv)
      (nablaA := fun d k i j => nablaChristoffelVariation x d k i j)
      (Gamma := Gamma)
      (by simpa [Acomp, Gamma] using hNabla)
      (by simpa [Gamma] using hGamma)
      i j
  simpa [Acomp, Gamma] using h

/-- Raw-divergence normalization from the three local component producers:
the fixed-chart product rule, the contracted `nabla g^{-1}=0` cancellation,
and the coordinate formula for `nabla A`. -/
theorem connTraceRaw_of_components
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (g : SmoothRiemannianMetric I M)
    (hLC : RicciFlower.LeviCivita.IsLeviCivita (I := I) cov g)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (nablaChristoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (gInvDeriv :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (componentDeriv :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
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
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x a d k) :
    ∀ x : M,
      connTraceRawDiv (I := I) g A x =
        gammaRawDivergenceTrace (I := I) g nablaChristoffelVariation x := by
  intro x
  exact connTraceRaw_eq_gamma (I := I) (cov := cov) g hLC A
    nablaChristoffelVariation (gInvDeriv x) (componentDeriv x) x
    (connTraceDeriv (I := I) g A (gInvDeriv x) (componentDeriv x) x
      (hgInvDiff x) (hADiff x) (hgInvDeriv x) (hADeriv x))
    (connTraceUTrace (I := I) (cov := cov) g A (gInvDeriv x) x
      (hginvExt x) (hzero x))
    (connTraceATrace (I := I) (cov := cov) A nablaChristoffelVariation
      (componentDeriv x) x (hNabla x) (hGamma x))


end GeometryFormula510

end

end Perelman
end RicciFlow
end RicciFlower
