import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.BilinearH1ComplViaH3

/-!
# Chart-side `W^{2,2}` regularity for the once-differentiated chart-bilinear data

For `u_h ∈ laplacianDomainPow g 2` on a closed Riemannian manifold `(M, g)`,
the once-differentiated chart-bilinear data
`D₁ := diffChartBilinearH1ComplData_of_laplacianDomainPow_two g α l₁ hu_h …`
exposes a chart-side field

* `D₁.u_chart_deriv`  — the chart-pushed weak `l₁`-partial of `u_h.coeFn`.

The companion module `DiffChartBilinearH1ComplH3` discharges the **first**
chart Sobolev order witness `MemW1p 2 D₁.u_chart_deriv (chartTargetEuclid α)`
unconditionally from `u_h ∈ laplacianDomainPow g 2`.

This module discharges the **second** chart Sobolev order witness

```
MemWkp 2 2 D₁.u_chart_deriv (chartTargetEuclid α)
```

i.e. chart-`W^{2,2}` of the differentiated field. Mathematically, this is
equivalent to chart-`H³` regularity of the underlying chart-pull
`chartPushed (chartAtlasPOU I M) α u_h.coeFn`. It is *not* a consequence of
`u_h ∈ laplacianDomainPow g 2` alone: the two-sided `H²` regularity of
`u_h.coeFn` and `(1 - Δ_g) u_h` (which is unconditional for that class)
provides only chart-`H²` of the chart-pull.

The natural one-extra-order hypothesis is

```
h_chartPushed_memWkp32 :
  DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp 3 2
    (chartPushed (chartAtlasPOU I M) α
      ((H1ComplToLp g u_h) : M → ℝ))
    (chartTargetEuclid α)
```

— chart-`H³` of the chart-pull. From this, the chosen first weak partial in
direction `l₁` lies in `MemWkp 2 2 (chartTargetEuclid α)` by
`MemWkp.chosenWeakPartial_mem`. The chart-pushed weak-partial coercion
`D₁.u_chart_deriv` is almost-everywhere equal to this chosen first weak
partial on `volume.restrict (chartTargetEuclid α)`, by the σ-compact
exhaustion bridge `chartPushedWeakPartialLp_ae_eq_chosenFirstPartial_on_chartTarget`
already proved in the companion module. The conclusion follows by
`MemWkp_congr_ae`.

## Main result

* `diffChartBilinearH1Compl_u_chart_deriv_memWkp_two` — the chart-`W^{2,2}`
  membership witness of `D₁.u_chart_deriv` on `chartTargetEuclid α`, taking
  the chart-`H³` regularity of `chartPushed POU α u_h.coeFn` as the natural
  one-extra-order hypothesis. The existing constructor input hypotheses
  `h_base_f_chart_memW1p` and `h_once_identity` flow through without playing
  a substantive role in this discharge — the conclusion depends only on
  `u_h ∈ laplacianDomainPow g 2` and the chart-`H³` hypothesis.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DiffChartBilinearH1ComplH3Direct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplH3
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- From chart-`H³` of the chart-pull `chartPushed POU α u_h.coeFn`, the
canonical chosen first weak partial `chartPushedChosenFirstPartial g α u_h l₁`
lies in `MemWkp 2 2 (chartTargetEuclid α)`.

This follows directly from `MemWkp.chosenWeakPartial_mem`: an element of
`MemWkp (k+1) p` has its chosen weak partials in `MemWkp k p`. -/
theorem chartPushedChosenFirstPartial_memWkp_two_of_memWkp_three
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_chartPushed_memWkp32 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 3 2
        (chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (l₁ : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h l₁)
      (chartTargetEuclid (I := I) (M := M) α) := by
  exact h_chartPushed_memWkp32.chosenWeakPartial_mem l₁

/-- **`MemWkp 2 2 D₁.u_chart_deriv (chartTargetEuclid α)` discharge from
chart-`H³` regularity of the chart-pull of `u_h.coeFn`.**

For a closed Riemannian manifold `(M, g)`, chart point `α : M`, direction
`l₁`, and `u_h ∈ laplacianDomainPow g 2`, the chart-side first weak partial
`(diffChartBilinearH1ComplData_of_laplacianDomainPow_two g α l₁ hu_h
  h_base_f_chart_memW1p h_once_identity).u_chart_deriv` lies in
`MemWkp 2 2 (chartTargetEuclid α)`, provided the chart-pull
`chartPushed POU α u_h.coeFn` lies in `MemWkp 3 2 (chartTargetEuclid α)`
(equivalent to chart-`H³` of `u_h.coeFn`).

The existing constructor input hypotheses `h_base_f_chart_memW1p` and
`h_once_identity` flow through without playing a substantive role in this
discharge — the conclusion depends only on `u_h ∈ laplacianDomainPow g 2`
and the chart-`H³` hypothesis. -/
theorem diffChartBilinearH1Compl_u_chart_deriv_memWkp_two
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_base_f_chart_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).f_chart
      (chartTargetEuclid (I := I) (M := M) α))
    (h_once_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weak_partial l₁ y * ψ y
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
                (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
                  (laplacianDomainPow_succ_subset_laplacianDomain
                    (I := I) (M := M) g 1 hu_h)).weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₁ y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).u_chart y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₁ y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).f_chart y * ψ y
          ∂(volume : Measure EuclN)))
    (h_chartPushed_memWkp32 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 3 2
        (chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
        (I := I) (M := M) g α hu_h l₁
        h_base_f_chart_memW1p h_once_identity).u_chart_deriv
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  change DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
    (d := Module.finrank ℝ E) 2 2
    (((chartPushedWeakPartialLp (I := I) (M := M) g α l₁
      (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α l₁) u_h
     ) : EuclN → ℝ))
    (chartTargetEuclid (I := I) (M := M) α)
  have h_chosenFirst_memWkp_two :=
    chartPushedChosenFirstPartial_memWkp_two_of_memWkp_three
      (I := I) (M := M) g α h_chartPushed_memWkp32 l₁
  have h_ae := chartPushedWeakPartialLp_ae_eq_chosenFirstPartial_on_chartTarget
    (I := I) (M := M) g α hu_h l₁
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
    (k := 2) (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α) h_ae.symm).mp
    h_chosenFirst_memWkp_two

end DiffChartBilinearH1ComplH3Direct
end Laplacian
end Analysis
end DifferentialGeometry

end
