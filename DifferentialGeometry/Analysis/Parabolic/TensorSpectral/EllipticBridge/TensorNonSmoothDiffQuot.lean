import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.TensorChartBilinearData
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartHk.H2NonSmooth

/-!
# Non-smooth interior `H²` regularity for a tensor chart component

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

The project already has a scalar non-smooth interior `H²`-regularity engine for
`ChartBilinearH1ComplData`:

* `DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth.h2_chart_loc_of_uniform_bound`
  — given a `ChartBilinearH1ComplData g α`, a precompact open `Ω''` with
  closure inside the chart target, a difference-quotient radius `h₀`, the
  room hypothesis `Metric.cthickening h₀ (closure Ω'') ⊆ chartTargetEuclid α`,
  and a uniform-in-`h` `L²(Ω'')` bound on `diffQuot k h (weak_partial i)`,
  it extracts for every `(i, k)` a weak `k`-partial derivative of
  `weak_partial i` lying in `L²(Ω'')`, with the supplied quantitative `L²`
  bound. This is the localized Nirenberg difference-quotient conclusion: the
  chart component is `W^{2,2}` on the interior set `Ω''`.

Because the principal symbol `weightedInvGramOnEuclid g α` and the entire
`ChartBilinearH1ComplData` interface are **shared** between the scalar and the
per-component tensor settings, the tensor interior-regularity statement is the
exact tensor-level mirror of the scalar conclusion, and no new analysis is
needed. This module is a **thin delegate**: it re-exposes the scalar engine's
conclusion at the tensor level by unfolding the `toChartData` field.

## Main results

* `tensor_h2_chart_loc_of_uniform_bound` — for a
  `TensorChartBilinearH1ComplData g r s α P₀`, a precompact open `Ω''` inside
  the chart target, a uniform-in-`h` difference-quotient bound on each
  `D.weak_partial i`, and the room hypothesis, extract for every `(i, k)` a
  weak `k`-partial derivative of `D.weak_partial i` in `L²(Ω'')` with
  quantitative `L²` bound. This is the tensor analogue of
  `h2_chart_loc_of_uniform_bound`.
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

/-- **Non-smooth interior `H²`/`W^{2,2}_loc` regularity for a tensor chart
component.**

Given:
* a chart-bilinear divergence-form data structure
  `D : TensorChartBilinearH1ComplData g r s α P₀` for one chart `P₀`-component
  of a possibly non-smooth `(r, s)`-tensor field on a closed Riemannian
  manifold;
* a precompact open `Ω''` whose closure lies inside `chartTargetEuclid α`;
* a difference-quotient radius `h₀ > 0` and the room hypothesis
  `Metric.cthickening h₀ (closure Ω'') ⊆ chartTargetEuclid α`;
* nonnegative `M_bound i k` and a uniform-in-`h` `L²(Ω'')` bound on the
  difference quotient `D_h^k (D.weak_partial i)` for `0 < |h| ≤ h₀`,

we extract for each pair `(i, k)` a weak `k`-partial derivative `g_ik` of
`D.weak_partial i` (the `i`-th weak partial of the chart component
`D.u_chart`) on `Ω''`, lying in `L²(Ω'')` with `‖g_ik‖_{L²(Ω'')} ≤ M_bound i k`.

Equivalently: the chart `P₀`-component `D.u_chart` of the tensor field has
interior `W^{2,2}` regularity on `Ω''` — a weak `H¹` partial of each
`weak_partial`.

This is a **thin delegate** to the scalar interior-regularity engine
`h2_chart_loc_of_uniform_bound`: because `TensorChartBilinearH1ComplData` is a
thin wrapper whose `toChartData` field is the scalar divergence-form data
structure, and the principal symbol `weightedInvGramOnEuclid g α` is shared
between the scalar and tensor settings, the scalar Nirenberg
difference-quotient conclusion applies verbatim. It is the tensor analogue of
`h2_chart_loc_of_uniform_bound`. -/
theorem tensor_h2_chart_loc_of_uniform_bound
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
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
  exact h2_chart_loc_of_uniform_bound (I := I) (M := M)
    (g := g) (α := α) D.toChartData
    hΩ''_open hΩ''_compact_closure hh₀ h_room hM_nn h_uniform_bd

section ElaborationTests

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
  (g : SmoothRiemannianMetric I M) (r s : ℕ)

/-- The tensor adapter consumes a `TensorChartBilinearH1ComplData` and produces
the per-`(i, k)` weak second partial of `D.weak_partial i` in `L²(Ω'')`. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
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
            ≤ ENNReal.ofReal (M_bound i k))
    (i k : Fin (Module.finrank ℝ E)) :
    ∃ g_ik : EuclN → ℝ,
      MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
        (D.weak_partial i) Ω'' ∧
      eLpNorm g_ik 2 ((volume : Measure EuclN).restrict Ω'') ≤
        ENNReal.ofReal (M_bound i k) :=
  tensor_h2_chart_loc_of_uniform_bound D hΩ''_open hΩ''_compact_closure hh₀
    h_room hM_nn h_uniform_bd i k

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
