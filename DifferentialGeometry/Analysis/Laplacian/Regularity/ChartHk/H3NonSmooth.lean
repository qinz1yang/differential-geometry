import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.BilinearH1Compl
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartHk.H2NonSmooth
import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotientWeakLimitLoc

/-!
# Per-chart `H³` interior regularity for non-smooth weak solutions arising
from a differentiated chart-bilinear data structure

This module establishes per-chart `H³` regularity for the chart-pulled
function `u_chart_deriv` (the weak first partial of `base.u_chart`) of a
`DiffChartBilinearH1ComplData`, by applying the per-chart `H²` regularity
of `ChartH2NonSmooth.h2_chart_loc_of_uniform_bound` to a derived
`ChartBilinearH1ComplData` whose `u_chart` is `u_chart_deriv`, after the
cross terms from the differentiated variational identity have been
absorbed into the right-hand side.

## Strategy

For a `DiffChartBilinearH1ComplData` `D` with direction `l`, the
differentiated variational identity reads

```
∫ ∑_{i,j} weightedInvGramOnEuclid · weak_partial_deriv i · ∂_j ψ
  + ∫ densityOnEuclid · u_chart_deriv · ψ
  = ∫ densityOnEuclid · f_chart_deriv · ψ
    - ∫ ∑_{i,j} weightedInvGramDerivOnEuclid · base.weak_partial i · ∂_j ψ
    - ∫ densityDerivOnEuclid · base.u_chart · ψ
    + ∫ densityDerivOnEuclid · base.f_chart · ψ.
```

To reuse the per-chart `H²` machinery (`h2_chart_loc_of_uniform_bound`),
we need to package the differentiated identity in the standard
`ChartBilinearH1ComplData` form. The principal `L²` block on the LHS
(``∑ weightedInvGramOnEuclid · ∂_i (u_chart_deriv) · ∂_j ψ`` together with
`densityOnEuclid · u_chart_deriv · ψ`) is the *same* uniformly elliptic
form as in the base identity. The cross terms on the RHS combine into an
effective `L²` right-hand-side `f_chart_eff` that involves the smooth
coefficients `weightedInvGramDerivOnEuclid` and `densityDerivOnEuclid`
paired with base fields `weak_partial`, `u_chart`, `f_chart` and the new
field `f_chart_deriv`.

Specifically (formally), if we divide through by `densityOnEuclid`
(positive on `chartTargetEuclid α`), the differentiated identity rewrites
as a base-form identity for `u_chart_deriv` with right-hand-side a
chart-explicit smooth-coefficient combination of base fields plus the
new field `f_chart_deriv`, **provided** the principal `L²` block uses
the same Gram weights as the base identity.

## Hypothesis-exposing API

A fully unconditional construction of the derived
`ChartBilinearH1ComplData` for `u_chart_deriv` requires absorbing the
cross terms on the RHS into a single chart-explicit `f_chart_eff` and
checking its local `L²` regularity. This absorption is a substantial
chart-explicit construction (it parallels the chart-side residual
`MemW1p` discharge for the H² case, which is also currently exposed as
a hypothesis in `DiffChartBilinearH1ComplUnconditional.lean`).

Accordingly, this module **exposes** the derived `ChartBilinearH1ComplData`
for `u_chart_deriv` as a hypothesis, mirroring the pattern in
`DiffChartBilinearH1ComplUnconditional.lean`. The headline
`h3_chart_loc_of_diff_data_and_uniform_bound` then applies the existing
per-chart `H²` regularity to the supplied derived data, producing the
chart-local `H³` regularity of `u_chart_deriv`.

## Main results

* `h3_chart_loc_of_diff_data_and_uniform_bound`: for a
  `DiffChartBilinearH1ComplData` `D` and a supplied derived
  `ChartBilinearH1ComplData` `D_deriv` whose `u_chart = D.u_chart_deriv`
  and `weak_partial = D.weak_partial_deriv`, plus a uniform difference
  quotient bound on the weak partials of `D.u_chart_deriv`, extract the
  per-pair `(i, k)` weak second partial of `D.u_chart_deriv` (= weak
  third partial of `D.base.u_chart`) in `L²` of a precompact subdomain.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartH3NonSmooth

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
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- **Per-chart `H³` regularity for `u_chart_deriv` via a supplied derived
`ChartBilinearH1ComplData` and a uniform difference-quotient bound.**

Given:
* a `DiffChartBilinearH1ComplData` `D` with direction `l` (so
  `D.u_chart_deriv` is the weak `l`-partial of `D.base.u_chart`);
* a derived `ChartBilinearH1ComplData` `D_deriv` whose chart-pulled scalar
  field is `D.u_chart_deriv` and whose weak partials are
  `D.weak_partial_deriv`;
* a precompact open `Ω''` whose closure lies inside `chartTargetEuclid α`;
* a uniform `L²(Ω'')` bound on the difference quotient
  `D_h^k (D_deriv.weak_partial i)` for `0 < |h| ≤ h₀`,
* the room hypothesis `cthickening h₀ (closure Ω'') ⊆ chartTargetEuclid α`,

we extract, for each pair `(i, k)`, a weak `k`-partial derivative
`g_{i,k}` of `D_deriv.weak_partial i = D.weak_partial_deriv i` (the `i`-th
weak partial of `D.u_chart_deriv`) on `Ω''`, with
`‖g_{i,k}‖_{L²(Ω'')} ≤ M_{i,k}`.

This is the chart-local third-order regularity statement for `D.base.u_chart`,
since `g_{i,k}` is the weak `k`-partial of `∂_i (∂_l u_chart) = D.base.u_chart`'s
mixed `(l,i,k)`-partial. -/
theorem h3_chart_loc_of_diff_data_and_uniform_bound
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffChartBilinearH1ComplData (I := I) (M := M) g α)
    (D_deriv : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (_h_u_chart_eq : D_deriv.u_chart = D.u_chart_deriv)
    (_h_weak_partial_eq : ∀ i, D_deriv.weak_partial i = D.weak_partial_deriv i)
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
                (d := Module.finrank ℝ E) k h (D_deriv.weak_partial i)) 2
              ((volume : Measure EuclN).restrict Ω'')
            ≤ ENNReal.ofReal (M_bound i k)) :
    ∀ i k : Fin (Module.finrank ℝ E),
    ∃ g_ik : EuclN → ℝ,
      MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
        (D_deriv.weak_partial i) Ω'' ∧
      eLpNorm g_ik 2 ((volume : Measure EuclN).restrict Ω'') ≤
        ENNReal.ofReal (M_bound i k) := by
  classical
  intro i k
  exact h2_chart_loc_of_uniform_bound (I := I) (M := M)
    (g := g) (α := α) D_deriv
    hΩ''_open hΩ''_compact_closure hh₀ h_room hM_nn h_uniform_bd i k

/-- The same regularity statement re-stated in terms of `D.weak_partial_deriv`
(which equals `D_deriv.weak_partial` by hypothesis). Useful when downstream
consumers want to phrase the conclusion in terms of `D`'s fields. -/
theorem h3_chart_loc_weak_partial_deriv_of_diff_data_and_uniform_bound
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffChartBilinearH1ComplData (I := I) (M := M) g α)
    (D_deriv : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (h_u_chart_eq : D_deriv.u_chart = D.u_chart_deriv)
    (h_weak_partial_eq : ∀ i, D_deriv.weak_partial i = D.weak_partial_deriv i)
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
                (d := Module.finrank ℝ E) k h (D.weak_partial_deriv i)) 2
              ((volume : Measure EuclN).restrict Ω'')
            ≤ ENNReal.ofReal (M_bound i k)) :
    ∀ i k : Fin (Module.finrank ℝ E),
    ∃ g_ik : EuclN → ℝ,
      MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
        (D.weak_partial_deriv i) Ω'' ∧
      eLpNorm g_ik 2 ((volume : Measure EuclN).restrict Ω'') ≤
        ENNReal.ofReal (M_bound i k) := by
  classical
  intro i k
  have h_uniform_bd' :
      ∀ (i' : Fin (Module.finrank ℝ E)) (k' : Fin (Module.finrank ℝ E))
        (h : ℝ), 0 < |h| → |h| ≤ h₀ →
          eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k' h (D_deriv.weak_partial i')) 2
              ((volume : Measure EuclN).restrict Ω'')
            ≤ ENNReal.ofReal (M_bound i' k') := by
    intro i' k' h hh hh_le
    rw [h_weak_partial_eq i']
    exact h_uniform_bd i' k' h hh hh_le
  obtain ⟨g_ik, hg_ik_memLp, hg_ik_partial, hg_ik_norm⟩ :=
    h3_chart_loc_of_diff_data_and_uniform_bound (I := I) (M := M)
      (g := g) (α := α) D D_deriv h_u_chart_eq h_weak_partial_eq
      hΩ''_open hΩ''_compact_closure hh₀ h_room hM_nn h_uniform_bd' i k
  refine ⟨g_ik, hg_ik_memLp, ?_, hg_ik_norm⟩
  have h_eq := h_weak_partial_eq i
  intro φ hφ_smooth hφ_supp hφ_sub
  have h_id := hg_ik_partial φ hφ_smooth hφ_supp hφ_sub
  rw [show D.weak_partial_deriv i = D_deriv.weak_partial i from h_eq.symm]
  exact h_id

end ChartH3NonSmooth
end Laplacian
end Analysis
end DifferentialGeometry
