import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.TensorChartBilinearData
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartHk.H2NonSmoothQuant

/-!
# Quantitative non-smooth interior `H²` regularity for a tensor chart component

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, the chart-local
elliptic-regularity analysis of the connection Laplacian `Δ_∇` on
`(r, s)`-tensor sections proceeds component by component. After the principal
part of the connection-Laplacian chart Dirichlet form is decoupled per scalar
chart component, each chart `P₀`-component of a possibly non-smooth tensor
field satisfies a **scalar** divergence-form elliptic identity with principal
symbol `weightedInvGramOnEuclid g α` (`= √(det g) · gⁱʲ`) — the *same*
principal symbol as the scalar Laplace–Beltrami operator. That per-component
data is packaged in `TensorChartBilinearH1ComplData g r s α P₀`, a thin wrapper
whose single field `toChartData : ChartBilinearH1ComplData g α` is exactly the
scalar divergence-form weak-elliptic data structure.

The project already has a *quantitative* scalar non-smooth interior
`H²`-regularity engine for `ChartBilinearH1ComplData`:

* `DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth.h2_chart_loc_of_data_quantitative`
  — given a standard Nirenberg cutoff `η` (with precompact target `Ω'` inside
  the chart target, difference-quotient radius `R₀`, and a subregion `Ω'' ⊆ Ω'`
  on which `η ≡ 1`), it produces an explicit chart-geometric constant
  `C_geom i k ≥ 0`, **uniform over the bilinear data `D`**, such that for every
  `ChartBilinearH1ComplData D` and every pair `(i, k)` the `i`-th weak partial
  `D.weak_partial i` admits a weak `k`-partial derivative `g_{i,k} ∈ L²(Ω'')`
  with `‖g_{i,k}‖_{L²(Ω'')} ≤ C_geom i k · √(DATA D)`, where `DATA D` collects
  the `L²(closure Ω')` norms of the weak partials, `u_chart`, and `f_chart`.

Because the principal symbol `weightedInvGramOnEuclid g α` and the entire
`ChartBilinearH1ComplData` interface are **shared** between the scalar and the
per-component tensor settings, the quantitative tensor interior-regularity
statement is the exact tensor-level mirror of the scalar conclusion, and no new
analysis is needed. This module is a **thin delegate**: it re-exposes the
scalar quantitative engine's conclusion at the tensor level by unfolding the
`toChartData` field.

## Main results

* `tensor_h2_chart_loc_of_data_quantitative` — for a standard Nirenberg cutoff
  `η`, there is a chart-geometric constant `C_geom i k ≥ 0`, uniform over `D`,
  such that for every `TensorChartBilinearH1ComplData g r s α P₀` and every pair
  `(i, k)` the `i`-th weak partial `D.weak_partial i` admits a weak `k`-partial
  derivative `g_{i,k} ∈ L²(Ω'')` with `‖g_{i,k}‖_{L²(Ω'')} ≤ C_geom i k ·
  √(DATA D)`. This is the quantitative tensor analogue of
  `h2_chart_loc_of_data_quantitative` and the explicit-constant upgrade of
  `tensor_h2_chart_loc_of_uniform_bound`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth
open DifferentialGeometry.Analysis.Sobolev

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- **Quantitative non-smooth interior `H²`/`W^{2,2}_loc` regularity for a
tensor chart component.**

This is the explicit-constant analogue of `tensor_h2_chart_loc_of_uniform_bound`
with the uniform difference-quotient hypothesis **discharged**, and the
tensor-level mirror of the scalar `h2_chart_loc_of_data_quantitative`.

Given a standard Nirenberg cutoff `η` on the Euclidean chart space — with a
precompact target `Ω'` inside the chart target, a difference-quotient radius
`R₀ > 0` whose cthickening of `tsupport η` stays inside `Ω'`, and a subregion
`Ω'' ⊆ Ω'` on which `η ≡ 1` — together with the room hypothesis
`cthickening R₀ (closure Ω'') ⊆ chartTargetEuclid α`, there is a chart-geometric
constant `C_geom i k ≥ 0`, **uniform over the tensor bilinear data `D`**, such
that for **every** `TensorChartBilinearH1ComplData g r s α P₀` and every pair
`(i, k)` the `i`-th weak partial `D.weak_partial i` (the `i`-th weak partial of
the chart `P₀`-component `D.u_chart`) admits a weak `k`-partial derivative
`g_{i,k} ∈ L²(Ω'')` with

  `‖g_{i,k}‖_{L²(Ω'')} ≤`
  `  ENNReal.ofReal (C_geom i k · √(∑_l ‖D.weak_partial l‖²_{L²(closure Ω')}`
  `    + ‖D.u_chart‖²_{L²(closure Ω')} + ‖D.f_chart‖²_{L²(closure Ω')}))`.

Because `C_geom` is quantified **before** `D`, the bound is uniform over all
tensor bilinear data: the chart-localising cutoff and the smooth elliptic
extension of the metric depend only on `g`, `α`, `Ω'`, `η`, never on `D`.

This is a **thin delegate** to the scalar quantitative interior-regularity
engine `h2_chart_loc_of_data_quantitative`: because
`TensorChartBilinearH1ComplData` is a thin wrapper whose `toChartData` field is
the scalar divergence-form data structure, the projections `D.weak_partial`,
`D.u_chart`, `D.f_chart` are definitionally those of `D.toChartData`, and the
principal symbol `weightedInvGramOnEuclid g α` is shared between the scalar and
tensor settings, the scalar quantitative conclusion applies verbatim. -/
theorem tensor_h2_chart_loc_of_data_quantitative
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
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
      ∀ (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
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
  obtain ⟨C_geom, hC_geom_nn, hC_geom⟩ := h2_chart_loc_of_data_quantitative
    (I := I) (M := M) (g := g) (α := α)
    hη hη_supp hη_range hN h_fderiv_eta hΩ' hΩ'_chart hΩ'_compact
    hη_in_Ω' hR₀_pos hh_supp_in_Ω' hη_one_on_Ω'' hΩ''_open hΩ''_compact_closure
    h_room
  refine ⟨C_geom, hC_geom_nn, fun D i k => ?_⟩
  exact hC_geom D.toChartData i k

section ElaborationTests

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
  (g : SmoothRiemannianMetric I M) (r s : ℕ)

/-- The quantitative tensor adapter consumes a standard Nirenberg cutoff and
produces a chart-geometric constant `C_geom`, uniform over the tensor bilinear
data `D`, bounding the per-`(i, k)` weak second partial of `D.weak_partial i` in
`L²(Ω'')`. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s)
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
      ∀ (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
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
                  ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)) :=
  tensor_h2_chart_loc_of_data_quantitative hη hη_supp hη_range hN h_fderiv_eta
    hΩ' hΩ'_chart hΩ'_compact hη_in_Ω' hR₀_pos hh_supp_in_Ω' hη_one_on_Ω''
    hΩ''_open hΩ''_compact_closure h_room

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
