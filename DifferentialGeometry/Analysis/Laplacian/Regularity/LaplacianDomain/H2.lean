import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.H2FromSmooth
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartBilinear.UniformDiffQuotBoundCanonical
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartHk.H2NonSmooth
import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothDensity

/-!
# Manifold-level non-smooth `H²` interior regularity for `laplacianDomain g`:
chart-bilinear-data plus uniform-difference-quotient route

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` and an
element `u_h ∈ laplacianDomain g`, this module records the chart-local non-smooth
`H²` regularity output obtained by routing through the chart-bilinear data
structure `chartBilinearH1ComplData_of_laplacianDomain` and the unconditional
uniform-in-`h` difference-quotient bound
`chartBilinearH1Compl_uniform_diffQuot_bound_of_data`.

The principal contribution of this module is the chart-local conversion: from
the chart-bilinear data structure plus an explicit choice of smooth cutoff `η`
satisfying the standard Nirenberg cutoff hypotheses, we produce the uniform
`L²` difference-quotient bound on `D.weak_partial i` from the unconditional
form, and then convert it via `h2_chart_loc_of_uniform_bound` into actual
weak second partial derivatives `g_{i, k}` on a precompact subdomain `Ω''` of
the chart target.

## Headline

`chartH2_localBound_of_laplacianDomain` packages the chart-local non-smooth
`H²` regularity output for the chart-bilinear data of an element of
`laplacianDomain g`: it consumes a smooth Nirenberg cutoff `η` plus the standard
support hypotheses and produces, for each pair of coordinate indices `(i, k)`,
a weak `k`-partial derivative `g_{i, k}` of `D.weak_partial i` on the precompact
subdomain `Ω''` where `η ≡ 1`, with a quantitative `L²` norm bound.

## Conversion from `Ω''`-local `H²` evidence to a `MemWkp 2 2` witness on the
full chart-target image

The chart-pushed POU function `chartPushed (chartAtlasPOU I M) α u` vanishes
pointwise on `chartTargetEuclid α` outside the chart-α image of `tsupport (ρ_α)`
(by `chartPushed_eq_zero_off_chartImagePOUTsupport`). The lift to a per-chart
`MemWkp 2 2 (chartPushed POU α u) (chartTargetEuclid α)` witness is the natural
target of an extension-by-zero / Leibniz-rule packaging of the chart-local
evidence delivered here. This packaging is captured in the per-chart witness
hypothesis of the upstream `laplacianDomain_memWkpChart_two`, and the
manifold-level packaging proceeds via that theorem.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace LaplacianDomainH2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearUniformDiffQuotBoundCanonical
open DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainH2FromSmooth
open DifferentialGeometry.Analysis.Laplacian.ManifoldH2NonSmooth
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- **Chart-local `H²` regularity from chart-bilinear data and the
unconditional uniform difference-quotient bound.**

For a closed Riemannian manifold `(M, g)`, chart point `α : M`, and an element
`u_h ∈ laplacianDomain g`, plus a smooth Nirenberg cutoff `η` satisfying the
standard hypotheses (`tsupport η ⊆ Ω'`, `cthickening |h| (tsupport η) ⊆ Ω'`
for `|h| ≤ 1`, `closure Ω' ⊆ chartTargetEuclid α`, etc.) and a precompact
open `Ω''` with closure inside `chartTargetEuclid α` and `η ≡ 1` on `Ω''`,
the chart-pulled weak partials `D.weak_partial i` of the chart-pushed Lp class
admit, on `Ω''`, weak `k`-partial derivatives `g_{i, k}` in `L²(Ω'')` with
quantitative norm bound.

This is the chart-local non-smooth `H²` regularity statement, derived
unconditionally from `u_h ∈ laplacianDomain g`. -/
theorem chartH2_localBound_of_laplacianDomain
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : EuclN, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' Ω'' : Set EuclN} (hΩ' : IsOpen Ω')
    (hΩ'_chart : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hΩ'_compact : IsCompact (closure Ω'))
    (hη_in_Ω' : tsupport η ⊆ Ω')
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ 1 →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (hη_one_on_Ω'' : ∀ x ∈ Ω'', η x = 1)
    (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (h_room :
      Metric.cthickening (1 : ℝ) (closure Ω'') ⊆
        chartTargetEuclid (I := I) (M := M) α) :
    ∃ (M_bound : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ),
      (∀ i k, 0 ≤ M_bound i k) ∧
      (∀ i k : Fin (Module.finrank ℝ E),
        ∃ g_ik : EuclN → ℝ,
          MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
          DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
            ((chartBilinearH1ComplData_of_laplacianDomain
              (I := I) (M := M) g α hu_h).weak_partial i) Ω'' ∧
          eLpNorm g_ik 2 ((volume : Measure EuclN).restrict Ω'') ≤
            ENNReal.ofReal (M_bound i k)) := by
  classical
  set D := chartBilinearH1ComplData_of_laplacianDomain
    (I := I) (M := M) g α hu_h with hD_def
  obtain ⟨M_bound, hM_nn, h_uniform_bd⟩ :=
    chartBilinearH1Compl_uniform_diffQuot_bound_of_data
      (I := I) (M := M) (g := g) (α := α) D
      hη hη_supp hη_range hN h_fderiv_eta
      hΩ' hΩ'_chart hΩ'_compact hη_in_Ω' (R₀ := 1) one_pos hh_supp_in_Ω'
      hη_one_on_Ω'' hΩ''_open.measurableSet
  have hh₀ : (0 : ℝ) < 1 := by norm_num
  have h_h2 :=
    h2_chart_loc_of_uniform_bound
      (I := I) (M := M) (g := g) (α := α) D
      hΩ''_open hΩ''_compact_closure hh₀ h_room
      hM_nn h_uniform_bd
  exact ⟨M_bound, hM_nn, h_h2⟩

/-- **Manifold-level non-smooth `H²` regularity for `laplacianDomain g`,
chart-bilinear / Nirenberg route.**

Re-export of `laplacianDomain_memWkpChart_two`: for a closed Riemannian
manifold `(M, g)` and `u_h ∈ laplacianDomain g`, given per-chart
`ChartH2NonSmoothPOUWitness` data, the canonical function representative
`(H1ComplToLp u_h : M → ℝ)` lies in `MemWkpChart g 2 2` with finite chart-based
norm.

The chart-local `H²` regularity output
`chartH2_localBound_of_laplacianDomain` (above) is the natural per-chart
analytical input to the per-chart witness data; the witness is assembled from
this output via the extension-by-zero / Leibniz-rule packaging mapping
chart-local weak second partials of `D.weak_partial i` to weak second partials
of the chart-pushed POU function on the full chart-target image. -/
theorem laplacianDomain_memWkpChart_two_chartBilinearRoute
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) < ⊤ :=
  laplacianDomain_memWkpChart_two (I := I) (M := M) g hu_h h_witness

end LaplacianDomainH2
end Laplacian
end Analysis
end DifferentialGeometry
