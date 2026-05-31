import RicciFlower.RicciFlow.Perelman.F.TraceAlgebra


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
# Perelman F Chart Trace

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

/-- On the coordinate-frame domain, the divergence theorem's chart coefficient
is the same coefficient as the `coordinateFrameAt` local-frame coefficient. -/
private theorem chartCoeff_eq_coordinateFrame_coeff
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (p : CoordinateIdx (𝕜 := Real) E) :
    RicciFlower.Analysis.DivergenceTheorem.chartCoeff (I := I) x₀ X p x =
      (coordinateFrameAt_isLocalFrame (I := I) x₀).coeff p x (X x) := by
  classical
  let e := coordinateTrivializationAt (I := I) x₀
  let b : Module.Basis (CoordinateIdx (𝕜 := Real) E) Real E := Module.finBasis Real E
  have hxE : x ∈ e.baseSet := by
    simpa [e, coordinateFrameSet] using hx
  have hcoeff :=
    Bundle.Trivialization.localFrame_coeff_apply_of_mem_baseSet
      (I := I) (e := e) (b := b) (x := x) hxE
      (fun y : M => X y) p
  have hchart :=
    Bundle.Trivialization.localFrame_coeff_eq_coeff
      (I := I) (e := e) (b := b) (s := fun y : M => X y)
      (x := x) (i := p) hxE
  have hbasis :
      (coordinateFrameAt_isLocalFrame (I := I) x₀).toBasisAt hx =
        e.basisAt b hxE := by
    ext j
    rw [IsLocalFrameOn.toBasisAt_coe]
    simpa [e, b, coordinateFrameAt] using
      (Bundle.Trivialization.localFrame_apply_of_mem_baseSet
        (e := e) (b := b) (i := j) hxE)
  rw [(coordinateFrameAt_isLocalFrame (I := I) x₀).coeff_apply_of_mem
    hx (fun y : M => X y) p]
  rw [hbasis]
  rw [← hcoeff]
  simpa [RicciFlower.Analysis.DivergenceTheorem.chartCoeff, e, b] using hchart.symm

/-- Local coordinate expression for the chart coefficient of the constructed
trace field.  This is the coefficient bridge needed before differentiating the
Voss-Weyl divergence formula. -/
theorem connTraceChartCoeff_eventually
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (x₀ : M) (p : CoordinateIdx (𝕜 := Real) E) :
    (fun y : M =>
        RicciFlower.Analysis.DivergenceTheorem.chartCoeff (I := I) x₀
          (RicciFlower.Realized.connTraceField (I := I) g A) p y)
      =ᶠ[nhds x₀]
      fun y : M =>
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                (extChartAt I x₀ y) *
              (A y
                (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
                  (I := I) (M := M) 1 x₀
                  ((continuousMultilinearMap_basis
                    (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                    (fun _ : Fin 1 => p)) y))
                (fun q : Fin 2 =>
                  coordinateFrameAt (I := I) x₀ (if q = 0 then i else j) y) := by
  classical
  have hcoeff :=
    RicciFlower.Realized.connTraceCoeff_eventually (I := I) g A x₀ p
  filter_upwards
    [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀), hcoeff] with y hy hcoeff_y
  rw [chartCoeff_eq_coordinateFrame_coeff
    (I := I) (RicciFlower.Realized.connTraceField (I := I) g A)
    x₀ hy p]
  exact hcoeff_y

/-- Model-chart version of `connTraceChartCoeff_eventually`.

This is the bridge needed before differentiating the Voss-Weyl expression:
near the chart center, the pulled-back chart coefficient of `tr_g A` is the
finite inverse-metric contraction of the pulled-back `(1,2)` tensor
components. -/
theorem connTraceChartCoeffOnE_eventually
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (x₀ : M) (p : CoordinateIdx (𝕜 := Real) E) :
    (fun y : E =>
        RicciFlower.Analysis.DivergenceTheorem.chartCoeffOnE (I := I) x₀
          (RicciFlower.Realized.connTraceField (I := I) g A) p y)
      =ᶠ[nhds (extChartAt I x₀ x₀)]
      fun y : E =>
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x₀ i j y *
              (A ((extChartAt I x₀).symm y)
                (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
                  (I := I) (M := M) 1 x₀
                  ((continuousMultilinearMap_basis
                    (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                    (fun _ : Fin 1 => p)) ((extChartAt I x₀).symm y)))
                (fun q : Fin 2 =>
                  coordinateFrameAt (I := I) x₀ (if q = 0 then i else j)
                    ((extChartAt I x₀).symm y)) := by
  classical
  have hM := connTraceChartCoeff_eventually (I := I) g A x₀ p
  let z₀ : E := extChartAt I x₀ x₀
  have hsymm_tend :
      Filter.Tendsto (fun z : E => (extChartAt I x₀).symm z) (nhds z₀) (nhds x₀) := by
    have hleft : (extChartAt I x₀).symm ((extChartAt I x₀) x₀) = x₀ :=
      (extChartAt I x₀).left_inv (mem_extChartAt_source (I := I) x₀)
    simpa only [ContinuousAt, z₀, hleft, Function.comp_def] using
      continuousAt_extChartAt_symm (I := I) x₀
  have hcomp := hM.comp_tendsto hsymm_tend
  filter_upwards [hcomp, extChartAt_target_mem_nhds' (I := I)
      (x := x₀) (y := z₀) (by simp [z₀])] with y hcoeff hy_target
  have hright : extChartAt I x₀ ((extChartAt I x₀).symm y) = y :=
    (extChartAt I x₀).right_inv hy_target
  have hcoeff' :
      RicciFlower.Analysis.DivergenceTheorem.chartCoeff (I := I) x₀
          (RicciFlower.Realized.connTraceField (I := I) g A) p
          ((extChartAt I x₀).symm y) =
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                (extChartAt I x₀ ((extChartAt I x₀).symm y)) *
              (A ((extChartAt I x₀).symm y)
                (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
                  (I := I) (M := M) 1 x₀
                  ((continuousMultilinearMap_basis
                    (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                    (fun _ : Fin 1 => p)) ((extChartAt I x₀).symm y)))
                (fun q : Fin 2 =>
                  coordinateFrameAt (I := I) x₀ (if q = 0 then i else j)
                    ((extChartAt I x₀).symm y)) := by
    simpa [Function.comp_def] using hcoeff
  rw [show
      RicciFlower.Analysis.DivergenceTheorem.chartCoeffOnE (I := I) x₀
          (RicciFlower.Realized.connTraceField (I := I) g A) p y =
        RicciFlower.Analysis.DivergenceTheorem.chartCoeff (I := I) x₀
          (RicciFlower.Realized.connTraceField (I := I) g A) p
          ((extChartAt I x₀).symm y) by rfl]
  rw [hcoeff']
  rw [hright]

/-- Partial-derivative form of `connTraceChartCoeffOnE_eventually`.

This lets the Voss-Weyl raw divergence formula differentiate the explicit
inverse-metric contraction instead of the abstract chart coefficient. -/
theorem connTraceChartCoeff_partial
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (x : M) (p : CoordinateIdx (𝕜 := Real) E) :
    RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (RicciFlower.Analysis.DivergenceTheorem.chartCoeffOnE (I := I) x
          (RicciFlower.Realized.connTraceField (I := I) g A) p)
        (extChartAt I x x)
      =
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
      (extChartAt I x x) := by
  have h :=
    connTraceChartCoeffOnE_eventually (I := I) g A x p
  unfold RicciFlower.Analysis.DivergenceTheorem.partialDeriv
  rw [Filter.EventuallyEq.fderiv_eq h]

/-- Center value of the chart coefficient of `tr_g A` in the point-centered
coordinate frame. -/
theorem connTraceChartCoeff_center
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (x : M) (p : CoordinateIdx (𝕜 := Real) E) :
    RicciFlower.Analysis.DivergenceTheorem.chartCoeffOnE (I := I) x
        (RicciFlower.Realized.connTraceField (I := I) g A) p
        (extChartAt I x x)
      =
    ∑ i : CoordinateIdx (𝕜 := Real) E,
      ∑ j : CoordinateIdx (𝕜 := Real) E,
        inverseMetricFlatModelInChart_component (I := I) g x i j
            (extChartAt I x x) *
          componentRS (I := I)
            (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
            (A x) (fun _ : Fin 1 => p)
            (fun q : Fin 2 => if q = 0 then i else j) := by
  classical
  have hcoeff :=
    connTraceChartCoeff_eventually (I := I) g A x p
  have hcenter := hcoeff.eq_of_nhds
  have hsymm : (extChartAt I x).symm (extChartAt I x x) = x :=
    (extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)
  have hxmem : x ∈ coordinateFrameSet (I := I) x :=
    coordinateFrameAt_mem (I := I) x
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  have hconst :
      Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 1 x
          ((continuousMultilinearMap_basis
            (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
            (fun _ : Fin 1 => p)) x =
        basisTensor0S (I := I)
          (coordinateFrameAt_basis (I := I) x hxmem)
          (fun _ : Fin 1 => p) := by
    simpa using
      (RicciFlower.Coordinates.constInChart_basisTensor0S_coordFrame
        (𝕜 := Real) (I := I) (x₀ := x) (x := x) hxmem
        (fun _ : Fin 1 => p))
  calc
    RicciFlower.Analysis.DivergenceTheorem.chartCoeffOnE (I := I) x
        (RicciFlower.Realized.connTraceField (I := I) g A) p
        (extChartAt I x x)
        =
      RicciFlower.Analysis.DivergenceTheorem.chartCoeff (I := I) x
        (RicciFlower.Realized.connTraceField (I := I) g A) p x := by
        simp [RicciFlower.Analysis.DivergenceTheorem.chartCoeffOnE]
    _ =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x x) *
            (A x
              (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
                (I := I) (M := M) 1 x
                ((continuousMultilinearMap_basis
                  (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                  (fun _ : Fin 1 => p)) x))
              (fun q : Fin 2 =>
                coordinateFrameAt (I := I) x (if q = 0 then i else j) x) := hcenter
    _ =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x x) *
            componentRS (I := I)
              (coordinateFrameAt_basis (I := I) x hxmem)
              (A x) (fun _ : Fin 1 => p)
              (fun q : Fin 2 => if q = 0 then i else j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        rw [componentRS]
        simp [hconst, component0S, coordinateFrameAt_basis_apply]

/-- Voss-Weyl expansion of the raw divergence of the constructed trace field.
The remaining formula 5.10 geometric work is to rewrite this expression into
the Levi-Civita covariant trace of the connection-variation tensor. -/
theorem connTraceRawDiv_voss
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (x : M) :
    connTraceRawDiv (I := I) g A x =
      (∑ p : CoordinateIdx (𝕜 := Real) E,
          RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
            (fun y : E =>
              RicciFlower.Analysis.DivergenceTheorem.chartCoeffOnE
                  (I := I) x
                  (RicciFlower.Realized.connTraceField (I := I) g A) p y *
                RicciFlower.Analysis.DivergenceTheorem.chartDensityOnE
                  (I := I) g x y)
            (extChartAt I x x)) /
        RicciFlower.Analysis.Volume.chartDensity (I := I) g x x := by
  rfl

/-- Product-rule expansion of the raw divergence of the constructed trace
field.  This is the next normalization after the Voss-Weyl chart expression:
the raw divergence is split into a derivative of the trace-field coordinate
coefficient and the chart-density derivative correction. -/
theorem connTraceRawDiv_chart_product
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (x : M) :
    connTraceRawDiv (I := I) g A x =
      (∑ p : CoordinateIdx (𝕜 := Real) E,
        RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
          (RicciFlower.Analysis.DivergenceTheorem.chartCoeffOnE
            (I := I) x (RicciFlower.Realized.connTraceField (I := I) g A) p)
          (extChartAt I x x)) +
        (∑ p : CoordinateIdx (𝕜 := Real) E,
          RicciFlower.Analysis.DivergenceTheorem.chartCoeffOnE
              (I := I) x (RicciFlower.Realized.connTraceField (I := I) g A) p
              (extChartAt I x x) *
            RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
              (RicciFlower.Analysis.DivergenceTheorem.chartDensityOnE
                (I := I) g x) (extChartAt I x x)) /
          RicciFlower.Analysis.Volume.chartDensity (I := I) g x x := by
  simpa [connTraceRawDiv] using
    RicciFlower.Analysis.DivergenceTheorem.divergence_g_chart_product
      (I := I) g (RicciFlower.Realized.connTraceField (I := I) g A) x

/-- Voss-Weyl product expansion with the constructed trace field's chart
coefficients replaced by the explicit finite contraction
`g^{ij} A^p_ij`.

The remaining conversion to `gammaRawDivergenceTrace` is the standard
Levi-Civita coordinate-divergence algebra: combine the density derivative with
the Christoffel trace and use `∇g^{-1}=0`. -/
theorem connTraceRawDiv_chart_explicit
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (x : M) :
    connTraceRawDiv (I := I) g A x =
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
          (extChartAt I x x)) +
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
          RicciFlower.Analysis.Volume.chartDensity (I := I) g x x := by
  classical
  rw [connTraceRawDiv_chart_product (I := I) g A x]
  congr 1
  · refine Finset.sum_congr rfl fun p _ => ?_
    exact connTraceChartCoeff_partial (I := I) g A x p
  · congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [connTraceChartCoeff_center (I := I) g A x p]


end GeometryFormula510

end

end Perelman
end RicciFlow
end RicciFlower
