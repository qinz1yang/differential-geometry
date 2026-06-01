import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorVariationalIdentity
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.TensorNonSmoothDiffQuotQuant

/-!
# Quantitative non-smooth interior `H²` regularity for the eigenvector chart component

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`ι` with nonzero resolvent eigenvalue, a chart center `α : M`, and a component
multi-index `P₀`, the chart `P₀`-component of the abstract connection-Laplacian
eigenvector is, by the variational-identity assembly of
`EigenvectorVariationalIdentity`, a `TensorChartBilinearH1ComplData g r s α P₀`
— namely `eigenvectorTensorChartBilinearData g r s ι α P₀`.

The project already has a *quantitative* tensor non-smooth interior `H²`
regularity engine for `TensorChartBilinearH1ComplData`:

* `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensor_h2_chart_loc_of_data_quantitative`
  — given a standard Nirenberg cutoff `η` (with precompact target `Ω'` inside
  the chart target, difference-quotient radius `R₀`, and a subregion `Ω'' ⊆ Ω'`
  on which `η ≡ 1`), it produces an explicit chart-geometric constant
  `C_geom i k ≥ 0`, **uniform over the tensor bilinear data `D`**, such that for
  every `TensorChartBilinearH1ComplData D` and every pair `(i, k)` the `i`-th
  weak partial `D.weak_partial i` admits a weak `k`-partial derivative
  `g_{i,k} ∈ L²(Ω'')` with `‖g_{i,k}‖_{L²(Ω'')} ≤ C_geom i k · √(DATA D)`.

Instantiating that engine's `∀ D` at the eigenvector's own chart-bilinear data
`eigenvectorTensorChartBilinearData g r s ι α P₀` yields the
eigenvector-specific quantitative interior-regularity statement. This module is
a **thin delegate**: it specialises the uniform-over-`D` tensor engine to the
single data structure that the eigenvector chart component furnishes.

## Main results

* `eigenvector_chartComponent_h2_quantitative` — for a standard
  Nirenberg cutoff `η`, there is a chart-geometric constant `C_geom i k ≥ 0`
  such that for every pair `(i, k)` the `i`-th weak partial of the eigenvector
  chart component admits a weak `k`-partial derivative `g_{i,k} ∈ L²(Ω'')` with
  `‖g_{i,k}‖_{L²(Ω'')} ≤ C_geom i k · √(DATA)`, where `DATA` collects the
  `L²(closure Ω')` norms of the weak partials, `u_chart`, and `f_chart` of the
  eigenvector chart-bilinear data. This is the eigenvector specialisation of
  `tensor_h2_chart_loc_of_data_quantitative`.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
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
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
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

/-- **Quantitative non-smooth interior `H²`/`W^{2,2}_loc` regularity for the
eigenvector chart component (chart-locality-free).**

Chart-locality-free twin of `eigenvector_chartComponent_h2_quantitative`: the
chart `P₀`-component of the abstract connection-Laplacian eigenvector is packaged
by the chart-locality-free data `eigenvectorTensorChartBilinearData
g r s ι α P₀` into `TensorChartBilinearH1ComplData g r s α P₀`, and the
quantitative tensor interior-regularity engine
`tensor_h2_chart_loc_of_data_quantitative` — uniform over **every**
`TensorChartBilinearH1ComplData g r s α P₀` — is specialised to it. No atlas /
chart-locality hypothesis appears.

Given a standard Nirenberg cutoff `η` on the Euclidean chart space — with a
precompact target `Ω'` inside the chart target, a difference-quotient radius
`R₀ > 0` whose cthickening of `tsupport η` stays inside `Ω'`, and a subregion
`Ω'' ⊆ Ω'` on which `η ≡ 1` — together with the room hypothesis
`cthickening R₀ (closure Ω'') ⊆ chartTargetEuclid α`, there is a chart-geometric
constant `C_geom i k ≥ 0` such that for every pair `(i, k)` the `i`-th weak
partial of the eigenvector chart-bilinear data
`(eigenvectorTensorChartBilinearData g r s ι α P₀).weak_partial i`
admits a weak `k`-partial derivative `g_{i,k} ∈ L²(Ω'')` with

  `‖g_{i,k}‖_{L²(Ω'')} ≤ ENNReal.ofReal (C_geom i k · √(DATA))`,

where `DATA` is the energy expression of the chart-bilinear data: the sum of the
`L²(closure Ω')` norms-squared of all weak partials, plus the `L²(closure Ω')`
norms-squared of `u_chart` and `f_chart`. This is a **thin delegate** to the
uniform-over-`D` tensor quantitative engine. -/
theorem eigenvector_chartComponent_h2_quantitative
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ι : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
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
      ∀ (i k : Fin (Module.finrank ℝ E)),
        ∃ g_ik : EuclN → ℝ,
          MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
          DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
            ((eigenvectorTensorChartBilinearData (I := I) (M := M)
              g r s ι α P₀).weak_partial i) Ω'' ∧
          eLpNorm g_ik 2 ((volume : Measure EuclN).restrict Ω'') ≤
            ENNReal.ofReal (C_geom i k * Real.sqrt (
              (∑ l : Fin (Module.finrank ℝ E),
                (eLpNorm ((eigenvectorTensorChartBilinearData (I := I) (M := M)
                    g r s ι α P₀).weak_partial l) 2
                  ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
              + (eLpNorm (eigenvectorTensorChartBilinearData (I := I) (M := M)
                    g r s ι α P₀).u_chart 2
                  ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2
              + (eLpNorm (eigenvectorTensorChartBilinearData (I := I) (M := M)
                    g r s ι α P₀).f_chart 2
                  ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)) := by
  classical
  obtain ⟨C_geom, hC_geom_nn, hC_geom⟩ :=
    tensor_h2_chart_loc_of_data_quantitative (I := I) (M := M) (g := g)
      (α := α) (r := r) (s := s) (P₀ := P₀)
      hη hη_supp hη_range hN h_fderiv_eta hΩ' hΩ'_chart hΩ'_compact
      hη_in_Ω' hR₀_pos hh_supp_in_Ω' hη_one_on_Ω'' hΩ''_open
      hΩ''_compact_closure h_room
  exact ⟨C_geom, hC_geom_nn,
    fun i k => hC_geom
      (eigenvectorTensorChartBilinearData (I := I) (M := M)
        g r s ι α P₀) i k⟩

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
