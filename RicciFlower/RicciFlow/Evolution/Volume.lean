import RicciFlower.Analysis.VolumeVariation
import RicciFlower.Realized.Curvature
import RicciFlower.Realized.RicciFlow

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Volume evolution under Ricci flow

This file connects the local volume-variation interface to the realized Ricci-flow
metric equation.  It deliberately keeps the volume regularity hypotheses
explicit: proving that a Ricci-flow solution supplies
`Volume.MetricFamilyRegularAt` is a separate analytic/chart-continuity theorem.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow
namespace Evolution
namespace Volume

open MeasureTheory
open RicciFlower.Analysis.Volume
open RicciFlower.Analysis.VolumeVariation
open scoped BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {A : Type*} [CommRing A] [Algebra Real A]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The canonical moving chart frame used by the volume trace at each point. -/
abbrev volumeTraceFrame :
    Fin (Module.finrank Real E) → (x : M) → TangentSpace I x :=
  fun i x => chartBasisVecFiber (I := I) x i x

/-- The inverse Gram components in the canonical moving chart frame. -/
abbrev volumeTraceInvMetricComponents
    (g : RicciFlower.Analysis.Volume.SmoothRiemannianMetric I M) :
    M → Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → Real :=
  fun x i j => ((chartGramMatrix (I := I) g x x)⁻¹) i j

/-- Canonical scalar curvature for a realized Ricci tensor, using the volume
trace frame attached to the metric family. -/
abbrev scalarCurvatureFromRicciInVolumeFrame
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : Realized.RicciTensorField (I := I) (M := M) Real) :
    Real → M → Real :=
  fun t =>
    Realized.scalarCurvatureFromRicciTraceInFrame (I := I) (Ric t)
      (volumeTraceInvMetricComponents (I := I) (M := M) (G.metric t))
      (volumeTraceFrame (I := I) (M := M))

/-- The canonical volume-frame scalar curvature realizes the Ricci trace by
definition. -/
theorem scalarCurvatureFromRicciInVolumeFrame_realizes
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : Realized.RicciTensorField (I := I) (M := M) Real) (t : Real) :
    Realized.ScalarRealizesRicciTraceInFrame (I := I)
      (scalarCurvatureFromRicciInVolumeFrame (I := I) (M := M) G Ric t)
      (Ric t)
      (volumeTraceInvMetricComponents (I := I) (M := M) (G.metric t))
      (volumeTraceFrame (I := I) (M := M)) :=
  Realized.scalarCurvatureFromRicciTraceInFrame_realizes
    (I := I) (M := M) (Ric t)
    (volumeTraceInvMetricComponents (I := I) (M := M) (G.metric t))
    (volumeTraceFrame (I := I) (M := M))

/-- The volume-layer trace is the trace of the matrix of metric time
derivatives in the chart frame at the base point.

The hypothesis `hdt` is the bridge saying the chosen abstract time-derivative
datum agrees with the classical `deriv` at this time. -/
theorem traceTimeDerivMetricAt_eq_trace_metric_derivative
    (td : TimeDerivativeData Real A Real)
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    {t : Real} {x : M}
    (hdt : ∀ F : Real → Real, td.dt_apply F t = deriv F t) :
    traceTimeDerivMetricAt (I := I) G t x =
      Matrix.trace
        ((chartGramMatrix (I := I) (G.metric t) x x)⁻¹ *
          Matrix.of fun i j =>
            Realized.metricTimeDerivative td G t x
              (chartBasisVecFiber (I := I) x i x)
              (chartBasisVecFiber (I := I) x j x)) := by
  rw [traceTimeDerivMetricAt_eq, traceTimeDerivMetric_eq]
  congr 2
  ext i j
  have h := hdt
    (fun s : Real =>
      (G.metric s).inner x
        (chartBasisVecFiber (I := I) x i x)
        (chartBasisVecFiber (I := I) x j x))
  simpa [metricFamilyForMeasure, Realized.metricTimeDerivative, chartGramMatrix_apply]
    using h.symm

/-- Algebraic symmetry of the inverse chart Gram matrix. -/
private theorem chartGramMatrix_inv_symm
    (g : RicciFlower.Analysis.Volume.SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank Real E)) :
    ((chartGramMatrix (I := I) g x x)⁻¹) j i =
      ((chartGramMatrix (I := I) g x x)⁻¹) i j := by
  have hHerm :
      ((chartGramMatrix (I := I) g x x)⁻¹).IsHermitian :=
    (chartGramMatrix_isHermitian (I := I) g x x).inv
  simpa [star_trivial] using hHerm.apply i j

/-- The existing scalar-trace realization, specialized to the canonical moving
volume trace frame, gives exactly the raw component sum used by the trace
calculation. -/
theorem scalar_trace_eq_volume_trace_components
    (g : RicciFlower.Analysis.Volume.SmoothRiemannianMetric I M)
    (Ric : Realized.TwoTensorField (I := I) (M := M))
    (scalar : M → Real)
    (hScalar : Realized.ScalarRealizesRicciTraceInFrame (I := I)
      scalar Ric
      (volumeTraceInvMetricComponents (I := I) (M := M) g)
      (volumeTraceFrame (I := I) (M := M))) (x : M) :
    scalar x =
      ∑ i : Fin (Module.finrank Real E),
        ∑ j : Fin (Module.finrank Real E),
          ((chartGramMatrix (I := I) g x x)⁻¹) i j *
            Ric x
              (chartBasisVecFiber (I := I) x i x)
              (chartBasisVecFiber (I := I) x j x) := by
  simpa [volumeTraceInvMetricComponents, volumeTraceFrame] using
    Realized.scalar_eq_trace (I := I) scalar Ric
      (volumeTraceInvMetricComponents (I := I) (M := M) g)
      (volumeTraceFrame (I := I) (M := M)) hScalar x

/-- Trace specialization of the volume variation term under the Ricci-flow
metric equation.

The scalar hypothesis is pointwise and uses the chart frame at `x`.  It is the
local form of the existing scalar-as-Ricci-trace realization. -/
theorem traceTimeDerivMetricAt_eq_neg_two_scalar
    (td : TimeDerivativeData Real A Real)
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : Realized.RicciTensorField (I := I) (M := M) Real)
    (scalar : Real → M → Real)
    (hdt : ∀ (F : Real → Real) (t : Real), td.dt_apply F t = deriv F t)
    (hEq : Realized.MetricVariationEquation (I := I) td G Ric)
    {t : Real} {x : M}
    (hScalar :
      scalar t x =
        ∑ i : Fin (Module.finrank Real E),
          ∑ j : Fin (Module.finrank Real E),
            ((chartGramMatrix (I := I) (G.metric t) x x)⁻¹) i j *
              Ric t x
                (chartBasisVecFiber (I := I) x i x)
                (chartBasisVecFiber (I := I) x j x)) :
    traceTimeDerivMetricAt (I := I) G t x = (-2 : Real) * scalar t x := by
  classical
  let Gmat : Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
    chartGramMatrix (I := I) (G.metric t) x x
  let dG : Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
    Matrix.of fun i j =>
      Realized.metricTimeDerivative td G t x
        (chartBasisVecFiber (I := I) x i x)
        (chartBasisVecFiber (I := I) x j x)
  have htrace :
      traceTimeDerivMetricAt (I := I) G t x =
        Matrix.trace (Gmat⁻¹ * dG) := by
    simpa [Gmat, dG] using
      traceTimeDerivMetricAt_eq_trace_metric_derivative
        (I := I) (M := M) td G (t := t) (x := x) (fun F => hdt F t)
  have hdG :
      dG =
        Matrix.of fun i j : Fin (Module.finrank Real E) =>
          (-2 : Real) *
            Ric t x
              (chartBasisVecFiber (I := I) x i x)
              (chartBasisVecFiber (I := I) x j x) := by
    ext i j
    simpa [dG] using (hEq t x
      (chartBasisVecFiber (I := I) x i x)
      (chartBasisVecFiber (I := I) x j x))
  have hInvSymm :
      ∀ i j : Fin (Module.finrank Real E), Gmat⁻¹ j i = Gmat⁻¹ i j := by
    intro i j
    simpa [Gmat] using
      chartGramMatrix_inv_symm (I := I) (M := M) (G.metric t) x i j
  rw [htrace, hdG]
  calc
    Matrix.trace
        (Gmat⁻¹ *
          Matrix.of fun i j : Fin (Module.finrank Real E) =>
            (-2 : Real) *
              Ric t x
                (chartBasisVecFiber (I := I) x i x)
                (chartBasisVecFiber (I := I) x j x))
        =
        Matrix.trace
          ((Matrix.of fun i j : Fin (Module.finrank Real E) =>
            (-2 : Real) *
              Ric t x
                (chartBasisVecFiber (I := I) x i x)
                (chartBasisVecFiber (I := I) x j x)) * Gmat⁻¹) := by
          rw [Matrix.trace_mul_comm]
    _ =
        ∑ i : Fin (Module.finrank Real E),
          ∑ j : Fin (Module.finrank Real E),
            ((-2 : Real) *
              Ric t x
                (chartBasisVecFiber (I := I) x i x)
                (chartBasisVecFiber (I := I) x j x)) * Gmat⁻¹ j i := by
          simp [Matrix.trace, Matrix.mul_apply]
    _ =
        (-2 : Real) *
          (∑ i : Fin (Module.finrank Real E),
            ∑ j : Fin (Module.finrank Real E),
              Gmat⁻¹ i j *
                Ric t x
                  (chartBasisVecFiber (I := I) x i x)
                  (chartBasisVecFiber (I := I) x j x)) := by
          simp_rw [hInvSymm]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = (-2 : Real) * scalar t x := by
          rw [hScalar]

/-- Trace specialization under the Ricci-flow metric equation, using the
canonical scalar-trace realization predicate instead of an expanded component
sum hypothesis. -/
theorem traceTimeDerivMetricAt_eq_neg_two_scalar_of_scalarTrace
    (td : TimeDerivativeData Real A Real)
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : Realized.RicciTensorField (I := I) (M := M) Real)
    (scalar : Real → M → Real)
    (hdt : ∀ (F : Real → Real) (t : Real), td.dt_apply F t = deriv F t)
    (hEq : Realized.MetricVariationEquation (I := I) td G Ric)
    {t : Real}
    (hScalar : Realized.ScalarRealizesRicciTraceInFrame (I := I)
      (scalar t) (Ric t)
      (volumeTraceInvMetricComponents (I := I) (M := M) (G.metric t))
      (volumeTraceFrame (I := I) (M := M)))
    (x : M) :
    traceTimeDerivMetricAt (I := I) G t x = (-2 : Real) * scalar t x :=
  traceTimeDerivMetricAt_eq_neg_two_scalar
    (I := I) (M := M) td G Ric scalar hdt hEq (t := t) (x := x)
    (scalar_trace_eq_volume_trace_components
      (I := I) (M := M) (G.metric t) (Ric t) (scalar t) hScalar x)

/-- Trace specialization under the classical full-time Ricci-flow metric
variation equation. This is the preferred trace theorem for volume evolution,
because `traceTimeDerivMetricAt` is defined using classical `deriv`. -/
theorem traceTimeDerivMetricAt_eq_neg_two_scalar_of_metricDeriv
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : Realized.RicciTensorField (I := I) (M := M) Real)
    (scalar : Real → M → Real)
    {t : Real}
    (hEq : Realized.MetricVariationEquationDerivAt (I := I) G Ric t)
    (hScalar : Realized.ScalarRealizesRicciTraceInFrame (I := I)
      (scalar t) (Ric t)
      (volumeTraceInvMetricComponents (I := I) (M := M) (G.metric t))
      (volumeTraceFrame (I := I) (M := M)))
    (x : M) :
    traceTimeDerivMetricAt (I := I) G t x = (-2 : Real) * scalar t x := by
  classical
  let Gmat : Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
    chartGramMatrix (I := I) (G.metric t) x x
  let dG : Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
    Matrix.of fun i j =>
      deriv (fun s : Real =>
        (G.metric s).inner x
          (chartBasisVecFiber (I := I) x i x)
          (chartBasisVecFiber (I := I) x j x)) t
  have htrace :
      traceTimeDerivMetricAt (I := I) G t x =
        Matrix.trace (Gmat⁻¹ * dG) := by
    simp [traceTimeDerivMetric_eq, metricFamilyForMeasure,
      chartGramMatrix_apply, Gmat, dG]
  have hdG :
      dG =
        Matrix.of fun i j : Fin (Module.finrank Real E) =>
          (-2 : Real) *
            Ric t x
              (chartBasisVecFiber (I := I) x i x)
              (chartBasisVecFiber (I := I) x j x) := by
    ext i j
    simpa [dG] using
      Realized.metric_deriv_eq_neg_two_ricci_of_metricVariationEquationDerivAt
        (I := I) G Ric hEq x
        (chartBasisVecFiber (I := I) x i x)
        (chartBasisVecFiber (I := I) x j x)
  have hInvSymm :
      ∀ i j : Fin (Module.finrank Real E), Gmat⁻¹ j i = Gmat⁻¹ i j := by
    intro i j
    simpa [Gmat] using
      chartGramMatrix_inv_symm (I := I) (M := M) (G.metric t) x i j
  rw [htrace, hdG]
  calc
    Matrix.trace
        (Gmat⁻¹ *
          Matrix.of fun i j : Fin (Module.finrank Real E) =>
            (-2 : Real) *
              Ric t x
                (chartBasisVecFiber (I := I) x i x)
                (chartBasisVecFiber (I := I) x j x))
        =
        Matrix.trace
          ((Matrix.of fun i j : Fin (Module.finrank Real E) =>
            (-2 : Real) *
              Ric t x
                (chartBasisVecFiber (I := I) x i x)
                (chartBasisVecFiber (I := I) x j x)) * Gmat⁻¹) := by
          rw [Matrix.trace_mul_comm]
    _ =
        ∑ i : Fin (Module.finrank Real E),
          ∑ j : Fin (Module.finrank Real E),
            ((-2 : Real) *
              Ric t x
                (chartBasisVecFiber (I := I) x i x)
                (chartBasisVecFiber (I := I) x j x)) * Gmat⁻¹ j i := by
          simp [Matrix.trace, Matrix.mul_apply]
    _ =
        (-2 : Real) *
          (∑ i : Fin (Module.finrank Real E),
            ∑ j : Fin (Module.finrank Real E),
              Gmat⁻¹ i j *
                Ric t x
                  (chartBasisVecFiber (I := I) x i x)
                  (chartBasisVecFiber (I := I) x j x)) := by
          simp_rw [hInvSymm]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = (-2 : Real) * scalar t x := by
          rw [scalar_trace_eq_volume_trace_components
            (I := I) (M := M) (G.metric t) (Ric t) (scalar t) hScalar x]

/-- Ricci-flow specialization of the clean volume variation formula, assuming
the pointwise trace identity has already been supplied. -/
theorem volume_variation_ricciFlow_at
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (scalar : Real → M → Real)
    {f : Real → M → Real} {t₀ : Real}
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) t₀)
    (hf : FunctionRegularAt f t₀)
    (htrace :
      ∀ x : M, traceTimeDerivMetricAt (I := I) G t₀ x =
        (-2 : Real) * scalar t₀ x) :
    HasDerivAt
      (fun s : Real => ∫ x, f s x ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x, (deriv (fun s : Real => f s x) t₀ - scalar t₀ x * f t₀ x)
          ∂(volumeMeasureFamily (I := I) (M := M) G t₀))
      t₀ := by
  have hclean :=
    volume_variation_formula_clean_at (I := I) (M := M) G (f := f) (t₀ := t₀) hg hf
  refine hclean.congr_deriv ?_
  apply integral_congr_ae
  filter_upwards with x
  have hx := htrace x
  calc
    deriv (fun s : Real => f s x) t₀ +
        (1 / 2 : Real) * traceTimeDerivMetricAt (I := I) G t₀ x * f t₀ x
        =
        deriv (fun s : Real => f s x) t₀ +
          ((1 / 2 : Real) * ((-2 : Real) * scalar t₀ x)) * f t₀ x := by
          rw [hx]
    _ = deriv (fun s : Real => f s x) t₀ - scalar t₀ x * f t₀ x := by
          ring

/-- Ricci-flow specialization of volume variation using the metric variation
equation and a scalar-Ricci trace realization in the chart frame. -/
theorem volume_variation_ricciFlow_at_of_metricVariationEquation
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (td : TimeDerivativeData Real A Real)
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : Realized.RicciTensorField (I := I) (M := M) Real)
    (scalar : Real → M → Real)
    {f : Real → M → Real} {t₀ : Real}
    (hdt : ∀ (F : Real → Real) (t : Real), td.dt_apply F t = deriv F t)
    (hEq : Realized.MetricVariationEquation (I := I) td G Ric)
    (hScalar : Realized.ScalarRealizesRicciTraceInFrame (I := I)
      (scalar t₀) (Ric t₀)
      (volumeTraceInvMetricComponents (I := I) (M := M) (G.metric t₀))
      (volumeTraceFrame (I := I) (M := M)))
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : Real => ∫ x, f s x ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x, (deriv (fun s : Real => f s x) t₀ - scalar t₀ x * f t₀ x)
          ∂(volumeMeasureFamily (I := I) (M := M) G t₀))
      t₀ := by
  refine volume_variation_ricciFlow_at (I := I) (M := M) G scalar hg hf ?_
  intro x
  exact traceTimeDerivMetricAt_eq_neg_two_scalar_of_scalarTrace
    (I := I) (M := M) td G Ric scalar hdt hEq (t := t₀) hScalar x

/-- Ricci-flow specialization of volume variation using the classical full-time
metric family derivative equation. -/
theorem volume_variation_ricciFlow_at_of_metricDeriv
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : Realized.RicciTensorField (I := I) (M := M) Real)
    (scalar : Real → M → Real)
    {f : Real → M → Real} {t₀ : Real}
    (hEq : Realized.MetricVariationEquationDerivAt (I := I) G Ric t₀)
    (hScalar : Realized.ScalarRealizesRicciTraceInFrame (I := I)
      (scalar t₀) (Ric t₀)
      (volumeTraceInvMetricComponents (I := I) (M := M) (G.metric t₀))
      (volumeTraceFrame (I := I) (M := M)))
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : Real => ∫ x, f s x ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x, (deriv (fun s : Real => f s x) t₀ - scalar t₀ x * f t₀ x)
          ∂(volumeMeasureFamily (I := I) (M := M) G t₀))
      t₀ := by
  refine volume_variation_ricciFlow_at (I := I) (M := M) G scalar hg hf ?_
  intro x
  exact traceTimeDerivMetricAt_eq_neg_two_scalar_of_metricDeriv
    (I := I) (M := M) G Ric scalar hEq hScalar x

/-- Ricci-flow volume variation using the canonical scalar curvature obtained
as the volume-frame trace of Ricci. -/
theorem volume_variation_ricciFlow_at_of_metricDeriv_canonicalScalar
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : Realized.RicciTensorField (I := I) (M := M) Real)
    {f : Real → M → Real} {t₀ : Real}
    (hEq : Realized.MetricVariationEquationDerivAt (I := I) G Ric t₀)
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : Real => ∫ x, f s x ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x, (deriv (fun s : Real => f s x) t₀ -
            scalarCurvatureFromRicciInVolumeFrame (I := I) (M := M) G Ric t₀ x * f t₀ x)
          ∂(volumeMeasureFamily (I := I) (M := M) G t₀))
      t₀ :=
  volume_variation_ricciFlow_at_of_metricDeriv
    (I := I) (M := M) G Ric
    (scalarCurvatureFromRicciInVolumeFrame (I := I) (M := M) G Ric)
    hEq
    (scalarCurvatureFromRicciInVolumeFrame_realizes (I := I) (M := M) G Ric t₀)
    hg hf

/-- Total Riemannian volume evolves by `-∫ R dμ` under Ricci flow, with the
scalar curvature taken as the canonical volume-frame trace of Ricci. -/
theorem total_volume_variation_ricciFlow_at_of_metricDeriv
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : Realized.RicciTensorField (I := I) (M := M) Real)
    {t₀ : Real}
    (hEq : Realized.MetricVariationEquationDerivAt (I := I) G Ric t₀)
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) t₀) :
    HasDerivAt
      (fun s : Real => ∫ _x, (1 : Real) ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x, - scalarCurvatureFromRicciInVolumeFrame (I := I) (M := M) G Ric t₀ x
          ∂(volumeMeasureFamily (I := I) (M := M) G t₀))
      t₀ := by
  simpa [deriv_const] using
    (volume_variation_ricciFlow_at_of_metricDeriv_canonicalScalar
      (I := I) (M := M) G Ric (f := fun _ : Real => fun _ : M => (1 : Real))
      hEq hg (FunctionRegularAt_one (M := M) t₀))

end Volume
end Evolution
end RicciFlow
end RicciFlower
