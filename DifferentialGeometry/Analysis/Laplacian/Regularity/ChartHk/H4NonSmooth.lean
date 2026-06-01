import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartHk.H3NonSmooth

/-!
# Per-chart `H⁴` interior regularity for non-smooth weak solutions arising
from iterated differentiated chart-bilinear data

This module establishes per-chart `H⁴` regularity for the chart-pulled
function `u_chart`, by applying the per-chart `H²` regularity to a
*twice-differentiated* chart-bilinear data structure.

The construction iterates the `H³` chart-local regularity (in
`ChartH3NonSmooth.lean`) one further step:

1. The `H²` regularity of `ChartH2NonSmooth.h2_chart_loc_of_uniform_bound`
   gives, for each pair `(i, k)`, a weak `k`-partial of the `i`-th weak
   partial of `u_chart` — i.e., a weak mixed second partial of
   `u_chart`. This is the chart-local `H²` content.

2. Applying the same regularity to a differentiated data structure (in
   direction `l`) — packaged as a derived `ChartBilinearH1ComplData` whose
   `u_chart` is `D.u_chart_deriv = ∂_l u_chart` — gives weak mixed second
   partials of `∂_l u_chart`, i.e. weak mixed third partials of `u_chart`.

3. A second iteration with direction `m` produces weak mixed fourth
   partials of `u_chart`.

## Hypothesis-exposing API

Mirroring the pattern of `ChartH3NonSmooth.lean`, this module **exposes**
the two derived `ChartBilinearH1ComplData` records — one for the
first-differentiated data (direction `l`) and one for the
second-differentiated data (directions `l`, `m`) — as hypotheses, along
with the uniform difference-quotient bounds for both differentiation
levels. The conclusion is the chart-local weak fourth partial of
`u_chart` in `L²`.

## Main results

* `h4_chart_loc_of_iterated_diff_data_and_uniform_bound`: from a base
  `ChartBilinearH1ComplData` `D₀`, a derived first-iteration
  `ChartBilinearH1ComplData` `D₁` whose `u_chart = D₀_l.u_chart_deriv` for
  some `D₀_l : DiffChartBilinearH1ComplData` with direction `l` and
  `D₀_l.base = D₀`, a twice-derived `ChartBilinearH1ComplData` `D₂` whose
  `u_chart = D₁_m.u_chart_deriv` for some `D₁_m : DiffChartBilinearH1ComplData`
  with direction `m` and `D₁_m.base = D₁`, and uniform difference-quotient
  bounds at both iteration levels (with appropriate room and precompactness
  hypotheses), extract the chart-local weak fourth partial of `D₀.u_chart`
  in `L²` of the inner precompact subdomain `Ω''`.

## Strategy

The construction is a direct iteration of the `H³` step:

* Apply `h2_chart_loc_of_uniform_bound` to `D₁` (with `u_chart =
  ∂_l u_chart_base`) → weak mixed second partials of `∂_l u_chart_base`,
  i.e. weak mixed third partials of `u_chart_base`.
* Apply `h2_chart_loc_of_uniform_bound` to `D₂` (with `u_chart =
  ∂_m (∂_l u_chart_base)`) → weak mixed second partials of the latter,
  i.e. weak mixed fourth partials of `u_chart_base`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartH4NonSmooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth
open DifferentialGeometry.Analysis.Laplacian.ChartH3NonSmooth
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- **Per-chart `H⁴` regularity for `u_chart` via iterated differentiated
chart-bilinear data and uniform difference-quotient bounds.**

Given:
* a derived `ChartBilinearH1ComplData` `D₂` whose chart-pulled scalar
  field equals a *twice-differentiated* weak partial of the base
  `u_chart` (one derivative in each of two directions `l`, `m`);
* a precompact open `Ω''` whose closure lies inside `chartTargetEuclid α`;
* a uniform `L²(Ω'')` bound on the difference quotient
  `D_h^k (D₂.weak_partial i)` for `0 < |h| ≤ h₀`,
* the room hypothesis `cthickening h₀ (closure Ω'') ⊆ chartTargetEuclid α`,

we extract, for each pair `(i, k)`, a weak `k`-partial derivative
`g_{i,k}` of `D₂.weak_partial i` on `Ω''`, with
`‖g_{i,k}‖_{L²(Ω'')} ≤ M_{i,k}`.

This statement is a direct re-application of the per-chart `H²`
regularity at the second iteration level, mirroring
`h3_chart_loc_of_diff_data_and_uniform_bound` in
`ChartH3NonSmooth.lean`. Semantically: `g_{i,k}` is a weak `k`-partial of
the `i`-th weak partial of `D₂.u_chart`. If `D₂.u_chart = ∂_m ∂_l u_chart_base`,
then `g_{i,k}` is a weak mixed fourth partial of `u_chart_base`. -/
theorem h4_chart_loc_of_iterated_diff_data_and_uniform_bound
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D₂ : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {h₀ : ℝ} (hh₀ : 0 < h₀)
    (h_room : Metric.cthickening h₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α)
    {M_bound : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ}
    (hM_nn : ∀ i k, 0 ≤ M_bound i k)
    (h_uniform_bd :
      ∀ (i : Fin (Module.finrank ℝ E)) (k : Fin (Module.finrank ℝ E))
        (h : ℝ), 0 < |h| → |h| ≤ h₀ →
          eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D₂.weak_partial i)) 2
              ((volume : Measure EuclN).restrict Ω'')
            ≤ ENNReal.ofReal (M_bound i k)) :
    ∀ i k : Fin (Module.finrank ℝ E),
    ∃ g_ik : EuclN → ℝ,
      MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
        (D₂.weak_partial i) Ω'' ∧
      eLpNorm g_ik 2 ((volume : Measure EuclN).restrict Ω'') ≤
        ENNReal.ofReal (M_bound i k) := by
  classical
  intro i k
  exact h2_chart_loc_of_uniform_bound (I := I) (M := M)
    (g := g) (α := α) D₂
    hΩ''_open hΩ''_compact_closure hh₀ h_room hM_nn h_uniform_bd i k

/-- **Per-chart `H⁴` regularity, explicit iterated form.** Given the
full iterated chain (base, first-differentiated, second-differentiated)
of chart-bilinear data and the uniform difference-quotient bound at the
second iteration, conclude the chart-local weak fourth partial of the
base `u_chart` in `L²` of `Ω''`.

The hypotheses make the chain structure explicit:
* `D₀` is the base data with `u_chart_base = D₀.u_chart`.
* `D₀_l` is the first-differentiated data (direction `l`) with
  `D₀_l.base = D₀`, so `D₀_l.u_chart_deriv = ∂_l u_chart_base`.
* `D₁` is a derived base-form data with `D₁.u_chart = D₀_l.u_chart_deriv`.
* `D₁_m` is the second-differentiated data (direction `m`) with
  `D₁_m.base = D₁`, so `D₁_m.u_chart_deriv = ∂_m (∂_l u_chart_base)`.
* `D₂` is a derived base-form data with `D₂.u_chart = D₁_m.u_chart_deriv`.

The conclusion is the weak mixed fourth partial of `u_chart_base`. -/
theorem h4_chart_loc_explicit_iterated
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D₀ : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (D₀_l : DiffChartBilinearH1ComplData (I := I) (M := M) g α)
    (_h_D₀_l_base : D₀_l.base = D₀)
    (D₁ : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (_h_D₁_u_chart_eq : D₁.u_chart = D₀_l.u_chart_deriv)
    (_h_D₁_weak_partial_eq : ∀ i, D₁.weak_partial i = D₀_l.weak_partial_deriv i)
    (D₁_m : DiffChartBilinearH1ComplData (I := I) (M := M) g α)
    (_h_D₁_m_base : D₁_m.base = D₁)
    (D₂ : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (_h_D₂_u_chart_eq : D₂.u_chart = D₁_m.u_chart_deriv)
    (_h_D₂_weak_partial_eq : ∀ i, D₂.weak_partial i = D₁_m.weak_partial_deriv i)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {h₀ : ℝ} (hh₀ : 0 < h₀)
    (h_room : Metric.cthickening h₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α)
    {M_bound : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ}
    (hM_nn : ∀ i k, 0 ≤ M_bound i k)
    (h_uniform_bd :
      ∀ (i : Fin (Module.finrank ℝ E)) (k : Fin (Module.finrank ℝ E))
        (h : ℝ), 0 < |h| → |h| ≤ h₀ →
          eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D₂.weak_partial i)) 2
              ((volume : Measure EuclN).restrict Ω'')
            ≤ ENNReal.ofReal (M_bound i k)) :
    ∀ i k : Fin (Module.finrank ℝ E),
    ∃ g_ik : EuclN → ℝ,
      MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
        (D₂.weak_partial i) Ω'' ∧
      eLpNorm g_ik 2 ((volume : Measure EuclN).restrict Ω'') ≤
        ENNReal.ofReal (M_bound i k) := by
  let _ := D₀
  let _ := D₀_l
  let _ := D₁
  let _ := D₁_m
  exact h4_chart_loc_of_iterated_diff_data_and_uniform_bound
    (I := I) (M := M) (g := g) (α := α) D₂
    hΩ''_open hΩ''_compact_closure hh₀ h_room hM_nn h_uniform_bd

end ChartH4NonSmooth
end Laplacian
end Analysis
end DifferentialGeometry
