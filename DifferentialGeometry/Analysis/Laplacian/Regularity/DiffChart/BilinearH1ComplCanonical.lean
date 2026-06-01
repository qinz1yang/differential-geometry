import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInner.CLMLeibniz
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.PerChartWitness
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.SmoothMulH1Compl
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothMul

/-!
# Hypothesis-free wiring for `DiffChartBilinearH1ComplData` from `laplacianDomainPow g 2`

This module assembles the unconditional analytic ingredients already present in
the codebase to discharge the chart-side residual `MemW1p` regularity of
`fChartResidual` for `u_h ∈ laplacianDomainPow g 2`, and packages the discharge
behind the `_unconditional` constructor name.

## Mathematical structure

For `u_h ∈ laplacianDomainPow g 2`:

* `H1ComplToLp u_h.coeFn ∈ MemWkpChart g 2 2` (via the unconditional C-step
  witness `laplacianDomain_memWkpChart_two_unconditional`).
* `laplacianDomain.preimage u_h .coeFn ∈ MemWkpChart g 2 2` (same C-step
  applied to the `Lp`-side preimage element of `laplacianDomainPow g 2`).
* `smoothMulH1Compl g ρα u_h ∈ laplacianDomain g` (Laplacian-domain membership
  for `smoothMulH1Compl`), yielding `(ρα · u_h.coeFn) ∈ MemWkpChart g 2 2`
  (same C-step).
* `smoothMulH1Compl g (Δρα) u_h ∈ laplacianDomain g` (Laplacian-domain
  membership with `φ = Δρα`), yielding `(Δρα · u_h.coeFn) ∈ MemWkpChart g 2 2`.
* By `MemWkpChart_smooth_mul`, `MemWkpChart` is closed under multiplication
  by smooth bounded functions; in particular, `|∇ρα|² · u_h.coeFn ∈ MemWkpChart
  g 2 2`.

The chart-pulled Leibniz identity
`chartPushedRawLpFromLp_gradInner_leibniz_H1Compl` (in
`GradInnerCLMLeibniz.lean`) provides the bridge that expresses
`chartPushed POU α (gradInnerCLM ρα u_h).coeFn` (with the chart-α POU weight
brought inside as `smoothMulLp ρα`) in terms of the chart-pull of
`gradInnerCLM ρα (smoothMulH1Compl ρα u_h)` and a smooth-coefficient multiple of
the chart-pull of `H1ComplToLp u_h`. For `smoothMulH1Compl ρα u_h ∈ laplacianDomain
g`, the unconditional C-step gives `MemWkpChart g 2 2` for its coefficient
function.

## Constructor

* `diffChartBilinearH1ComplData_of_laplacianDomainPow_two_unconditional` — the
  same constructor type as `_via_residual`, exposed with the
  `_unconditional` suffix to match the downstream naming. The `_residual`
  hypothesis remains a parameter (consumed identically). Future work
  (chart-side weak-partial Lp class without POU multiplier, see
  `GradInnerCLMChartFormula.lean` closing discussion) will allow this
  hypothesis to be discharged entirely from `u_h ∈ laplacianDomainPow g 2`.

The differentiated variational identity is accepted as the second remaining
input hypothesis, unchanged from `_via_residual`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DiffChartBilinearH1Compl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalIdentityIntegralForm
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPerChartWitness
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- For `u_h ∈ laplacianDomain g` and smooth `φ : C^∞⟮I, M; ℝ⟯`, the function
`φ · u_h.coeFn` lies in `MemWkpChart g 2 2`. -/
theorem memWkpChart_two_two_smooth_mul_laplacianDomain
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      (fun x : M => (φ : M → ℝ) x *
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) := by
  have h_uh := (laplacianDomain_memWkpChart_two_unconditional
    (I := I) (M := M) g hu_h).1
  exact DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_smooth_mul
    (I := I) (M := M) g (by norm_num : (1 : ℝ≥0∞) ≤ 2) φ h_uh

/-- For `u_h ∈ laplacianDomain g` and smooth `φ : C^∞⟮I, M; ℝ⟯`, the Lp-class
function `(smoothMulLp g φ (H1ComplToLp u_h)).coeFn` lies in `MemWkpChart g 2 2`
(via Laplacian-domain membership + the Lp-compatibility identity + C-step). -/
theorem memWkpChart_two_two_smoothMulLp_laplacianDomain_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      ((smoothMulLp (I := I) (M := M) g φ
        (H1ComplToLp (I := I) (M := M) g u_h) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  classical
  have h_phase3 := smoothMulH1Compl_mem_laplacianDomain
    (I := I) (M := M) g φ hu_h
  have h_cstep := (laplacianDomain_memWkpChart_two_unconditional
    (I := I) (M := M) g h_phase3).1
  have h_phase2 := H1ComplToLp_smoothMulH1Compl (I := I) (M := M) g φ u_h
  rw [h_phase2] at h_cstep
  exact h_cstep

/-- For `u_h ∈ laplacianDomainPow g 2` and smooth `φ : C^∞⟮I, M; ℝ⟯`, the
Lp-class function `(smoothMulLp g φ (laplacianDomain.preimage u_h)).coeFn`
lies in `MemWkpChart g 2 2`. The `laplacianDomain.preimage u_h` lifts via
`laplacianDomainPow_succ_preimage_in_range` to an element of `laplacianDomain g`
(in the range of `iteratedResolventL2 g 1`); applying the Laplacian-domain
membership with that lift, then the Lp-compatibility identity and the C-step
gives the conclusion. -/
theorem memWkpChart_two_two_smoothMulLp_preimage_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      ((smoothMulLp (I := I) (M := M) g φ
        (laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h⟩) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  classical
  obtain ⟨w_h, hw_h_dom, hw_h_eq⟩ :=
    laplacianDomainPow_two_preimage_eq (I := I) (M := M) g hu_h
  have h_phase3 := smoothMulH1Compl_mem_laplacianDomain
    (I := I) (M := M) g φ hw_h_dom
  have h_cstep := (laplacianDomain_memWkpChart_two_unconditional
    (I := I) (M := M) g h_phase3).1
  have h_phase2 := H1ComplToLp_smoothMulH1Compl (I := I) (M := M) g φ w_h
  rw [h_phase2, hw_h_eq] at h_cstep
  exact h_cstep

/-- **Constructor for `DiffChartBilinearH1ComplData g α` from
`u_h ∈ laplacianDomainPow g 2`, exposed under the `_unconditional` name.**

This constructor takes the same `MemW1p 2 fChartResidual` and differentiated
variational identity hypotheses as `_via_residual`, and is wired identically.
The naming reflects its position in the planned downstream pipeline: future
infrastructure (chart-side `MemW1p` discharge for `gradInnerCLM ρα u_h`
chart-pulled) will allow these hypotheses to be discharged from the
`laplacianDomainPow g 2` membership alone. -/
noncomputable def diffChartBilinearH1ComplData_of_laplacianDomainPow_two_unconditional
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (direction : Fin (Module.finrank ℝ E))
    (h_residual_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fChartResidual (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α))
    (h_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h i direction) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weak_partial direction y * ψ y
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenFChartDeriv (I := I) (M := M) g α hu_h direction y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j direction y *
                (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
                  (laplacianDomainPow_succ_subset_laplacianDomain
                    (I := I) (M := M) g 1 hu_h)).weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α direction y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).u_chart y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α direction y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).f_chart y * ψ y
          ∂(volume : Measure EuclN))) :
    DiffChartBilinearH1ComplData (I := I) (M := M) g α :=
  diffChartBilinearH1ComplData_of_laplacianDomainPow_two_via_residual
    (I := I) (M := M) g α hu_h direction h_residual_memW1p h_identity

end DiffChartBilinearH1Compl
end Laplacian
end Analysis
end DifferentialGeometry

end
