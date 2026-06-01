import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartBilinear.H1Compl
import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotientWeakLimitLoc
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity

/-!
# Per-chart `H²` interior regularity for non-smooth weak solutions
arising from the chart-bilinear data structure

This module establishes per-chart `H²` regularity for non-smooth weak
solutions of the variational Laplacian on a closed Riemannian manifold,
using the localized difference-quotient infrastructure
(`hasWeakPartialDeriv_of_diffQuot_uniform_bound_loc`) and the non-smooth
chart-bilinear identity packaged in `ChartBilinearH1ComplData`.

The headline result `h2_chart_loc_of_uniform_bound` produces, for a
precompact `Ω''` inside the chart target, a weak second `k`-partial
derivative of the explicit `i`-th weak partial `D.weak_partial i` (lying
in `L²(Ω'')`), with a quantitative bound in terms of the supplied uniform
difference-quotient bound on `Ω''`.

## Strategy

The argument is the standard Nirenberg difference-quotient method,
adapted to the non-smooth setting:

1. From the variational identity packaged in `ChartBilinearH1ComplData`,
   the caller deduces a uniform-in-`h` `L²(Ω'')` bound on the difference
   quotient `D_h^k (D.weak_partial i)` (this step requires re-deriving
   the Nirenberg cross-bounds for weak solutions and is supplied as a
   hypothesis).
2. Apply `hasWeakPartialDeriv_of_diffQuot_uniform_bound_loc` to extract
   a weak `k`-partial derivative `g_{i,k} ∈ L²(Ω'')`.

The localized converter requires `MemLp (D.weak_partial i) 2 (volume.restrict Ω)`
for some open precompact `Ω` containing `cthickening h₀ (closure Ω'')`. We
extract this from `D.weak_partial_locally_memLp` applied to the closure of
`Ω`, which is a compact subset of `chartTargetEuclid α`.

## Main results

* `h2_chart_loc_of_uniform_bound`: for a chart-bilinear data structure
  `D : ChartBilinearH1ComplData g α` and a uniform-in-`h` bound on the
  difference quotient of each weak partial of `D.u_chart`, extract weak
  second partial derivatives in `L²(Ω'')` with quantitative `L²` bound.
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
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- **Per-chart `H²` regularity from a uniform diffQuot bound.**

Given:
* a chart-bilinear data structure `D : ChartBilinearH1ComplData g α`,
  encoding the chart-pulled `u`, `f`, the explicit weak partials of
  `D.u_chart`, and the variational identity;
* a precompact open `Ω''` whose closure lies inside `chartTargetEuclid α`;
* a uniform `L²(Ω'')` bound on `D_h^k (D.weak_partial i)` for `0 < |h| ≤ h₀`,
* the room hypothesis `cthickening h₀ (closure Ω'') ⊆ chartTargetEuclid α`,

we extract for each pair `(i, k)` a weak `k`-partial derivative `g_{i,k}`
of `D.weak_partial i` (the `i`-th weak partial of `D.u_chart`) on `Ω''`,
with `‖g_{i,k}‖_{L²(Ω'')} ≤ M_{i,k}`.

This is the localized Nirenberg conclusion in non-smooth chart form. -/
theorem h2_chart_loc_of_uniform_bound
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
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
                (d := Module.finrank ℝ E) k h (D.weak_partial i)) 2
              ((volume : Measure EuclN).restrict Ω'')
            ≤ ENNReal.ofReal (M_bound i k)) :
    ∀ i k : Fin (Module.finrank ℝ E),
    ∃ g_ik : EuclN → ℝ,
      MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
        (D.weak_partial i) Ω'' ∧
      eLpNorm g_ik 2 ((volume : Measure EuclN).restrict Ω'') ≤
        ENNReal.ofReal (M_bound i k) := by
  classical
  intro i k
  have h_cthick_compact : IsCompact (Metric.cthickening h₀ (closure Ω'')) :=
    hΩ''_compact_closure.cthickening
  obtain ⟨δ, hδ_pos, hδ_subset⟩ :=
    h_cthick_compact.exists_cthickening_subset_open
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_room
  set Ω : Set EuclN := Metric.thickening δ (Metric.cthickening h₀ (closure Ω''))
    with hΩ_def
  have hΩ_open : IsOpen Ω := Metric.isOpen_thickening
  have h_cthick_in_Ω : Metric.cthickening h₀ (closure Ω'') ⊆ Ω :=
    Metric.self_subset_thickening hδ_pos _
  have hΩ_in_cthick : Ω ⊆ Metric.cthickening δ (Metric.cthickening h₀ (closure Ω'')) :=
    Metric.thickening_subset_cthickening _ _
  have h_cthick_outer_compact :
      IsCompact (Metric.cthickening δ (Metric.cthickening h₀ (closure Ω''))) :=
    h_cthick_compact.cthickening
  have h_closureΩ_subset :
      closure Ω ⊆ Metric.cthickening δ (Metric.cthickening h₀ (closure Ω'')) := by
    apply closure_minimal hΩ_in_cthick Metric.isClosed_cthickening
  have h_closureΩ_compact : IsCompact (closure Ω) :=
    h_cthick_outer_compact.of_isClosed_subset isClosed_closure h_closureΩ_subset
  have hΩ_in_chart : closure Ω ⊆ chartTargetEuclid (I := I) (M := M) α :=
    h_closureΩ_subset.trans hδ_subset
  have h_room_Ω : Metric.cthickening h₀ (closure Ω'') ⊆ Ω := h_cthick_in_Ω
  have h_closureΩ''_in_Ω : closure Ω'' ⊆ Ω := by
    intro y hy
    apply h_cthick_in_Ω
    apply Metric.self_subset_cthickening _ hy
  have h_wp_memLp_closureΩ :
      MemLp (D.weak_partial i) 2
        ((volume : Measure EuclN).restrict (closure Ω)) :=
    D.weak_partial_locally_memLp i (closure Ω) h_closureΩ_compact hΩ_in_chart
  have h_wp_memLp_Ω :
      MemLp (D.weak_partial i) 2
        ((volume : Measure EuclN).restrict Ω) :=
    h_wp_memLp_closureΩ.mono_measure (Measure.restrict_mono subset_closure le_rfl)
  have h_bdd : ∀ h : ℝ, 0 < |h| → |h| ≤ h₀ →
      eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weak_partial i)) 2
          ((volume : Measure EuclN).restrict Ω'')
        ≤ ENNReal.ofReal (M_bound i k) :=
    fun h hh hh_le => h_uniform_bd i k h hh hh_le
  obtain ⟨g_ik, hg_ik_memLp, hg_ik_partial, hg_ik_norm⟩ :=
    hasWeakPartialDeriv_of_diffQuot_uniform_bound_loc
      (d := Module.finrank ℝ E)
      hΩ_open hΩ''_open hΩ''_compact_closure h_closureΩ''_in_Ω
      hh₀ h_room_Ω h_wp_memLp_Ω k (hM_nn i k) h_bdd
  exact ⟨g_ik, hg_ik_memLp, hg_ik_partial, hg_ik_norm⟩

end ChartH2NonSmooth
end Laplacian
end Analysis
end DifferentialGeometry
