import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartHk.H2NonSmooth
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartBilinear.UniformDiffQuotBoundCanonical

/-!
# Quantitative per-chart `H²` interior regularity for non-smooth weak solutions

This module upgrades the hypothesis-bearing per-chart `H²` regularity
result `h2_chart_loc_of_uniform_bound` to a *quantitative* statement in
which the uniform difference-quotient hypothesis has been **discharged**.

The hypothesis-bearing form requires the caller to supply a uniform
`L²(Ω'')` bound on `D_h^k (D.weak_partial i)`. The discharge is provided
by `chartBilinearH1Compl_uniform_diffQuot_bound_of_data_quantitative`,
which produces — for a standard Nirenberg cutoff `η` with a precompact
target `Ω'` inside the chart target and `Ω'' ⊆ Ω'` on which `η ≡ 1` —
an explicit chart-geometric constant `C_geom i k ≥ 0`, **uniform over
the bilinear data `D`**, with

  `‖D_h^k (D.weak_partial i)‖_{L²(Ω'')} ≤`
  `  ENNReal.ofReal (C_geom i k · √(∑_l ‖D.weak_partial l‖²_{L²(closure Ω')}`
  `    + ‖D.u_chart‖²_{L²(closure Ω')} + ‖D.f_chart‖²_{L²(closure Ω')}))`.

Feeding this discharged bound into `h2_chart_loc_of_uniform_bound` with
`M_bound i k := C_geom i k · √(DATA)` and `h₀ := R₀` yields the headline
of this file.

## Main results

* `h2_chart_loc_of_data_quantitative`: for a standard Nirenberg cutoff
  `η`, there is a chart-geometric constant `C_geom i k ≥ 0`, uniform
  over `D`, such that for every `ChartBilinearH1ComplData D` the `i`-th
  weak partial `D.weak_partial i` admits a weak `k`-partial derivative
  `g_{i,k} ∈ L²(Ω'')` with `‖g_{i,k}‖_{L²(Ω'')} ≤ C_geom i k · √(DATA)`,
  where `DATA` collects the `L²(closure Ω')` norms of the weak partials,
  `u_chart`, and `f_chart`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartH2NonSmooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearUniformDiffQuotBoundCanonical
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- **Quantitative per-chart `H²` regularity from the chart-bilinear data.**

This is the explicit-constant analogue of `h2_chart_loc_of_uniform_bound`
with the uniform difference-quotient hypothesis **discharged**.

Given a standard Nirenberg cutoff `η` on the Euclidean chart space — with
a precompact target `Ω'` inside the chart target, a difference-quotient
radius `R₀ > 0` whose cthickening of `tsupport η` stays inside `Ω'`, and a
subregion `Ω'' ⊆ Ω'` on which `η ≡ 1` — together with the room hypothesis
`cthickening R₀ (closure Ω'') ⊆ chartTargetEuclid α`, there is a
chart-geometric constant `C_geom i k ≥ 0`, **uniform over the bilinear
data `D`**, such that for **every** `ChartBilinearH1ComplData D` and every
pair `(i, k)` the `i`-th weak partial `D.weak_partial i` admits a weak
`k`-partial derivative `g_{i,k} ∈ L²(Ω'')` with

  `‖g_{i,k}‖_{L²(Ω'')} ≤`
  `  ENNReal.ofReal (C_geom i k · √(∑_l ‖D.weak_partial l‖²_{L²(closure Ω')}`
  `    + ‖D.u_chart‖²_{L²(closure Ω')} + ‖D.f_chart‖²_{L²(closure Ω')}))`.

Because `C_geom` is quantified **before** `D`, the bound is uniform over
all bilinear data: the chart-localising cutoff and the smooth elliptic
extension of the metric depend only on `g`, `α`, `Ω'`, `η`, never on `D`.
-/
theorem h2_chart_loc_of_data_quantitative
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : EuclN, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' Ω'' : Set EuclN} (hΩ' : IsOpen Ω')
    (hΩ'_chart : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hΩ'_compact : IsCompact (closure Ω'))
    (hη_in_Ω' : tsupport η ⊆ Ω')
    {R₀ : ℝ} (hR₀_pos : 0 < R₀)
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (hη_one_on_Ω'' : ∀ x ∈ Ω'', η x = 1)
    (hΩ''_open : IsOpen Ω'') (hΩ''_compact_closure : IsCompact (closure Ω''))
    (h_room : Metric.cthickening R₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    ∃ C_geom : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ,
      (∀ i k, 0 ≤ C_geom i k) ∧
      ∀ (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
        (i k : Fin (Module.finrank ℝ E)),
        ∃ g_ik : EuclN → ℝ,
          MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
          DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
            (D.weak_partial i) Ω'' ∧
          eLpNorm g_ik 2 ((volume : Measure EuclN).restrict Ω'') ≤
            ENNReal.ofReal (C_geom i k * Real.sqrt (
              (∑ l : Fin (Module.finrank ℝ E),
                (eLpNorm (D.weak_partial l) 2
                  ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
              + (eLpNorm D.u_chart 2
                  ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2
              + (eLpNorm D.f_chart 2
                  ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)) := by
  classical
  obtain ⟨C_geom, hC_geom_nn, hC_geom⟩ :=
    chartBilinearH1Compl_uniform_diffQuot_bound_of_data_quantitative
      (I := I) (M := M) (E := E) (H := H) (g := g) (α := α)
      hη hη_supp hη_range hN h_fderiv_eta hΩ' hΩ'_chart hΩ'_compact
      hη_in_Ω' hR₀_pos hh_supp_in_Ω' hη_one_on_Ω'' hΩ''_open.measurableSet
  refine ⟨C_geom, hC_geom_nn, fun D i k => ?_⟩
  obtain ⟨g_ik, hg_ik_memLp, hg_ik_partial, hg_ik_norm⟩ :=
    h2_chart_loc_of_uniform_bound (I := I) (M := M) (g := g) (α := α)
      D hΩ''_open hΩ''_compact_closure hR₀_pos h_room
      (M_bound := fun i k => C_geom i k * Real.sqrt (
        (∑ l : Fin (Module.finrank ℝ E),
          (eLpNorm (D.weak_partial l) 2
            ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
        + (eLpNorm D.u_chart 2
            ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2
        + (eLpNorm D.f_chart 2
            ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2))
      (hM_nn := fun i k => mul_nonneg (hC_geom_nn i k) (Real.sqrt_nonneg _))
      (h_uniform_bd := fun i k h hpos hle => hC_geom D hpos hle)
      i k
  exact ⟨g_ik, hg_ik_memLp, hg_ik_partial, hg_ik_norm⟩

end ChartH2NonSmooth
end Laplacian
end Analysis
end DifferentialGeometry
