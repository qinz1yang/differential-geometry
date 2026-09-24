import DifferentialGeometry.Geometry.Operator.Laplacian.VossWeylFormula
import DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section

open Bundle Manifold
open scoped BigOperators ContDiff Manifold

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]

theorem hasDerivAt_of_chart_weighted_heat_balance
    (g : ℝ → SmoothRiemannianMetric I M) (u : ℝ → M → ℝ)
    (α : M) {t r : ℝ} {x : M} (hx : x ∈ (chartAt H α).source)
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    (hρ : HasDerivAt (fun s => chartDensity (I := I) (g s) α x)
      (r * chartDensity (I := I) (g t) α x) t)
    (hbalance : HasDerivAt
      (fun s => chartDensity (I := I) (g s) α x * u s x)
      (∑ i : Fin (Module.finrank ℝ E),
        partialDeriv i (chartVossWeylIntegrand (I := I) (g t) α (u t) i)
          (extChartAt I α x)) t) :
    HasDerivAt (fun s => u s x)
      (laplacian (I := I) (LeviCivita (I := I) (g t)) (g t) (u t) x -
        r * u t x) t := by
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rwa [trivializationAt_baseSet_eq_chartAt_source]
  have hρne (s : ℝ) : chartDensity (I := I) (g s) α x ≠ 0 :=
    ne_of_gt (chartDensity_pos (I := I) (g s) α hxbase)
  have hquot := hbalance.fun_div hρ (hρne t)
  have heq : (fun s =>
      (chartDensity (I := I) (g s) α x * u s x) /
        chartDensity (I := I) (g s) α x) = (fun s => u s x) := by
    funext s
    field_simp [hρne s]
  rw [heq] at hquot
  apply hquot.congr_deriv
  rw [laplacian_levi_eq (I := I) (g t) hu x,
    voss_weyl_laplacian_formula_pointwise (I := I) (g t) α hu hx,
    chartVossWeylLaplacian_def]
  field_simp [hρne t]

theorem hasDerivAt_of_chart_spacetime_heat_balance
    (g : ℝ → SmoothRiemannianMetric I M) (u : ℝ → M → ℝ)
    (α : M) {t r : ℝ} {x : M} (hx : x ∈ (chartAt H α).source)
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    (hρ : HasDerivAt
      (fun s => chartDensityOnE (I := I) (g s) α (extChartAt I α x))
      (r * chartDensityOnE (I := I) (g t) α (extChartAt I α x)) t)
    (hweighted : DifferentiableAt ℝ
      (fun p : ℝ × E => chartDensityOnE (I := I) (g p.1) α p.2 *
        u p.1 ((extChartAt I α).symm p.2)) (t, extChartAt I α x))
    (hflux : ∀ i : Fin (Module.finrank ℝ E), DifferentiableAt ℝ
      (fun p : ℝ × E => chartVossWeylIntegrand (I := I) (g p.1) α (u p.1) i p.2)
      (t, extChartAt I α x))
    (hbalance :
      fderiv ℝ
        (fun p : ℝ × E => chartDensityOnE (I := I) (g p.1) α p.2 *
          u p.1 ((extChartAt I α).symm p.2)) (t, extChartAt I α x) (1, 0) =
      ∑ i : Fin (Module.finrank ℝ E),
        fderiv ℝ
          (fun p : ℝ × E =>
            chartVossWeylIntegrand (I := I) (g p.1) α (u p.1) i p.2)
          (t, extChartAt I α x) (0, chartModelBasis E i)) :
    HasDerivAt (fun s => u s x)
      (laplacian (I := I) (LeviCivita (I := I) (g t)) (g t) (u t) x -
        r * u t x) t := by
  have hxext : x ∈ (extChartAt I α).source := by
    rwa [extChartAt_source_eq_chartAt_source (I := I)]
  have hleft : (extChartAt I α).symm (extChartAt I α x) = x :=
    (extChartAt I α).left_inv hxext
  have hρ' : HasDerivAt (fun s => chartDensity (I := I) (g s) α x)
      (r * chartDensity (I := I) (g t) α x) t := by
    simpa only [chartDensityOnE, hleft] using hρ
  apply hasDerivAt_of_chart_weighted_heat_balance g u α hx hu hρ'
  have htime := hweighted.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (extChartAt I α x)))
  have hslice (i : Fin (Module.finrank ℝ E)) :
      partialDeriv i (chartVossWeylIntegrand (I := I) (g t) α (u t) i)
          (extChartAt I α x) =
        fderiv ℝ
          (fun p : ℝ × E =>
            chartVossWeylIntegrand (I := I) (g p.1) α (u p.1) i p.2)
          (t, extChartAt I α x) (0, chartModelBasis E i) := by
    have hcomp := (hflux i).hasFDerivAt.comp (extChartAt I α x)
      (hasFDerivAt_prodMk_right t (extChartAt I α x))
    unfold partialDeriv
    have heq := congrArg (fun L : E →L[ℝ] ℝ => L (chartModelBasis E i)) hcomp.fderiv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply] using heq
  have hsum :
      (∑ i : Fin (Module.finrank ℝ E),
        fderiv ℝ
          (fun p : ℝ × E =>
            chartVossWeylIntegrand (I := I) (g p.1) α (u p.1) i p.2)
          (t, extChartAt I α x) (0, chartModelBasis E i)) =
        ∑ i : Fin (Module.finrank ℝ E),
          partialDeriv i (chartVossWeylIntegrand (I := I) (g t) α (u t) i)
            (extChartAt I α x) := by
    exact Finset.sum_congr rfl (fun i _ => (hslice i).symm)
  have htime' := htime.congr_deriv (hbalance.trans hsum)
  simpa only [Function.comp_def, id_eq, chartDensityOnE, hleft] using htime'

end DifferentialGeometry.Analysis.Parabolic
