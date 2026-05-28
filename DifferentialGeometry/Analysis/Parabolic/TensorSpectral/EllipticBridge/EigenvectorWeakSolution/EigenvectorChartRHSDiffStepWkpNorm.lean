import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorDifferentiatedRHSWkpNorm
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorDifferentiatedRHSWkp

/-!
# `K`-graded explicit-norm `wkpNorm` bounds for the chart-RHS-difference step

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, and a component multi-index `P₀`, the recursive
iterated differentiated chart-RHS chain produces, at level `(m+1)`, the
chart-density-divided differentiated numerator
`eigenvectorChartRHSDiffNumerator … m l fChartEffPrev / densityOnEuclid g α` and
its compact-kernel indicator, the standalone inductive step
`eigenvectorChartIteratedStep`.

The order-`K` explicit-norm bound for the differentiated chart-RHS *numerator*
itself is `eigenvectorChartRHSDiffNumerator_wkpNorm_le`: there is a nonnegative
constant `C` with

```
wkpNorm K 2 (eigenvectorChartRHSDiffNumerator … m l fChartEffPrev)
    (chartTargetEuclid α)
  ≤ ENNReal.ofReal C * diffNumeratorAggregateK …,
```

`diffNumeratorAggregateK` being the honest finite aggregate of order-`K` source
norms. This file records the two chained quantitative `wkpNorm` bounds for the
two further constructions, against the *same* aggregate:

* `eigenvectorChartRHSDiffNumerator_div_density_wkpNorm_le` — for the
  chart-density-divided numerator `numerator / densityOnEuclid g α`;
* `eigenvectorChartIteratedStep_wkpNorm_le` — for the standalone inductive step
  `eigenvectorChartIteratedStep`.

## Strategy

For the density-divided numerator, `numerator / densityOnEuclid g α` is rewritten
as `(1 / densityOnEuclid g α) · numerator`. The reciprocal `1 / densityOnEuclid g
α` is `C^∞` on the open chart target — the chart density is `C^∞` and strictly
positive there — but only `ContDiffOn` the chart target, not globally smooth, so
the global-smoothness Leibniz bound `wkpNorm_smul_smooth_bounded_le` does not
apply directly. The smooth-coefficient `wkpNorm` bound with ae-vanishing
(`wkpNorm_coef_mul_factor_le`, replicated here from the differentiated-numerator
campaign) cuts the chart-target-smooth coefficient off into a globally smooth
compactly supported representative `χ · coef`, applies the global Leibniz bound,
and transfers back through the ae-vanishing of the numerator off the
partition-of-unity kernel. It also requires `MemWkp K 2` of the numerator, which
is re-derived layer-by-layer from the same iterated-weak-partial hypotheses
`h_iter` carried by `eigenvectorChartRHSDiffNumerator_wkpNorm_le`. Chaining that
headline numerator bound then closes the density-divided bound; the two constants
fold into one.

For the standalone inductive step, `eigenvectorChartIteratedStep … m dirs
fChartEffPrev l` is `Set.indicator (chartPouKernel α)` of the chart-density-divided
differentiated numerator `eigenvectorChartRHSDiffNumerator … m (Fin.snoc dirs l)
fChartEffPrev / densityOnEuclid g α` (via
`eigenvectorChartIteratedStepNumerator_eq_rhsDiffNumerator`). On the open chart
target the indicator agrees almost everywhere with the underlying quotient: on the
kernel the indicator returns the quotient, off the kernel both the indicator and
the quotient ae-vanish (the latter by
`eigenvectorChartRHSDiffNumerator_div_density_ae_zero_off_chartPouKernel`).
`wkpNorm_congr_ae` transfers the order-`K` `wkpNorm` across this ae-equality, and
the density-divided bound above closes the chain.

## Main results

* `eigenvectorChartRHSDiffNumerator_div_density_wkpNorm_le` — the `K`-graded
  explicit-norm `wkpNorm` bound for the chart-density-divided differentiated
  numerator.
* `eigenvectorChartIteratedStep_wkpNorm_le` — the `K`-graded explicit-norm
  `wkpNorm` bound for the standalone inductive step.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## The quantitative smooth-coefficient `wkpNorm` bound with ae-vanishing

The workhorse for the density-divided numerator. Given a coefficient smooth on
the open chart target, a factor in `MemWkp K 2` on the chart target that
ae-vanishes off the compact partition-of-unity kernel, the product `coef ·
factor` lies in `MemWkp K 2` on the chart target and its order-`K` Sobolev norm
is bounded by an explicit constant times the order-`K` norm of the factor.

The proof cuts the coefficient off to a globally smooth compactly supported
representative `χ · coef` (smooth cutoff `χ` equal to `1` on a closed thickening
of the kernel, supported in the chart target). Its iterated derivatives up to
order `K` are uniformly bounded, so the global-smoothness Leibniz bound
`wkpNorm_smul_smooth_bounded_le` applies. The cut-off product `(χ · coef) ·
factor` agrees almost everywhere with `coef · factor` on `volume.restrict` of the
chart target — on the thickening `χ = 1`; off the kernel the factor ae-vanishes —
so `wkpNorm` and `MemWkp` transfer.

This is the quantitative companion of the qualitative `memWkp_coef_mul_factor`. -/

private lemma wkpNorm_coef_mul_factor_le
    (α : M) (K : ℕ)
    {coef factor : EuclN → ℝ}
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α))
    (hfactor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 factor
      (chartTargetEuclid (I := I) (M := M) α))
    (hfactor_ae_zero : factor =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => coef y * factor y) (chartTargetEuclid (I := I) (M := M) α) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => coef y * factor y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            wkpNorm (d := Module.finrank ℝ E) K 2 factor
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set Kα : Set EuclN := chartPouKernel (I := I) (M := M) α with hKα_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hKα_compact : IsCompact Kα := chartPouKernel_isCompact (I := I) (M := M) α
  have hKα_in : Kα ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- A smooth cutoff `χ` equal to `1` on `cthickening δ Kα`, supported in `Ω`.
  obtain ⟨δ, χ, hδ_pos, hδ_in, hχ_smooth, hχ_cs, _hχ_range, hχ_one, hχ_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      hKα_compact hΩ_open hKα_in
  -- `χ · coef` is globally smooth: smooth on `tsupport χ ⊆ Ω`, identically zero
  -- (hence smooth) on the open complement of `tsupport χ`.
  have hχ_coef_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y * coef y) := by
    have h_open_compl : IsOpen ((tsupport χ)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy_supp : y ∈ tsupport χ
    · have hy_chart : y ∈ Ω := hχ_tsupp hy_supp
      exact hχ_smooth.contDiffAt.mul
        ((hcoef_chart y hy_chart).contDiffAt (hΩ_open.mem_nhds hy_chart))
    · have h_eq_zero : (fun y => χ y * coef y)
          =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_open_compl.mem_nhds hy_supp] with z hz
        rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq h_eq_zero
  have hχ_coef_cs : HasCompactSupport (fun y => χ y * coef y) :=
    HasCompactSupport.mul_right hχ_cs
  -- Uniform bound on the iterated derivatives of `χ · coef` up to order `K`.
  obtain ⟨C₀, hC₀_nn, hC₀_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hχ_coef_smooth hχ_coef_cs K
  -- `(χ · coef) · factor ∈ MemWkp K 2`, via `MemWkp.smul_smooth_bounded`.
  have h_prod_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (χ y * coef y) * factor y) Ω :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hχ_coef_smooth
      (fun j _hj y _hy => hC₀_bd y j _hj) hfactor_memWkp
  -- The quantitative Leibniz bound for the cutoff product `χ · coef`.
  obtain ⟨Kc, _hKc_pos, hKc_bd⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hΩ_open hχ_coef_smooth
      hC₀_nn (fun j _hj y _hy => hC₀_bd y j _hj)
  -- `(χ · coef) · factor =ᵃᵉ coef · factor` on `volume.restrict Ω`.
  set Cδ : Set EuclN := Metric.cthickening δ Kα with hCδ_def
  have hCδ_closed : IsClosed Cδ := Metric.isClosed_cthickening
  have hCδ_meas : MeasurableSet Cδ := hCδ_closed.measurableSet
  have h_ae_eq : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => coef y * factor y) := by
    -- On `Cδ ⊆ Ω`: `χ = 1`, so `(χ · coef) · factor = coef · factor`.
    have h_eq_on_Cδ : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict Cδ]
        (fun y => coef y * factor y) := by
      refine (ae_restrict_iff' hCδ_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      have hχy : χ y = 1 := hχ_one y hy
      change (χ y * coef y) * factor y = coef y * factor y
      rw [hχy]; ring
    -- On `Ω \ Cδ ⊆ Ω \ Kα`: `factor` ae-vanishes.
    have hKα_in_Cδ : Kα ⊆ Cδ := Metric.self_subset_cthickening _
    have h_diff_sub : Ω \ Cδ ⊆ Ω \ Kα := fun y hy =>
      ⟨hy.1, fun hyK => hy.2 (hKα_in_Cδ hyK)⟩
    have h_factor_ae_zero_diff : factor =ᵐ[(volume : Measure EuclN).restrict
        (Ω \ Cδ)] (fun _ => (0 : ℝ)) := by
      have h_abs : (volume : Measure EuclN).restrict (Ω \ Cδ) ≪
          (volume : Measure EuclN).restrict (Ω \ Kα) :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono h_diff_sub le_rfl)
      exact h_abs.ae_le hfactor_ae_zero
    have h_eq_on_diff : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict (Ω \ Cδ)]
        (fun y => coef y * factor y) := by
      filter_upwards [h_factor_ae_zero_diff] with y hy
      show (χ y * coef y) * factor y = coef y * factor y
      rw [hy]; ring
    have h_eq_on_inter : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict (Ω ∩ Cδ)]
        (fun y => coef y * factor y) := by
      have h_abs : (volume : Measure EuclN).restrict (Ω ∩ Cδ) ≪
          (volume : Measure EuclN).restrict Cδ :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono Set.inter_subset_right le_rfl)
      exact h_abs.ae_le h_eq_on_Cδ
    have h_diff_meas : MeasurableSet (Ω \ Cδ) := hΩ_meas.diff hCδ_meas
    have h_cover : Ω = (Ω ∩ Cδ) ∪ (Ω \ Cδ) := by
      ext y; constructor
      · intro hy
        by_cases h : y ∈ Cδ
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
      · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    have h_disj : Disjoint (Ω ∩ Cδ) (Ω \ Cδ) :=
      Set.disjoint_left.mpr fun y hy hy' => hy'.2 hy.2
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict ((Ω ∩ Cδ) ∪ (Ω \ Cδ)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, MeasureTheory.Measure.restrict_union h_disj h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  -- Transfer `MemWkp K 2` through the ae-equality.
  have h_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω :=
    (MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).mp h_prod_memWkp
  refine ⟨h_memWkp, Kc, le_of_lt _hKc_pos, ?_⟩
  -- Transfer the `wkpNorm` bound through the ae-equality.
  have h_norm_eq : wkpNorm (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω =
      wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => (χ y * coef y) * factor y) Ω :=
    (wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).symm
  rw [h_norm_eq]
  exact hKc_bd hfactor_memWkp

/-! ## The factor-uniform smooth-coefficient `wkpNorm` bound with ae-vanishing

The factor-uniform twin of `wkpNorm_coef_mul_factor_le`. The smooth cutoff
representative `χ · coef`, its uniform iterated-derivative bound `C₀`, and the
Leibniz constant `Kc` depend only on the chart-target-smooth coefficient `coef`
and the order `K`, not on the factor being multiplied — `wkpNorm_smul_smooth_bounded_le`
already produces a factor-uniform `Kc`. Only the factor-membership, factor-ae-vanishing,
and the resulting ae-equality vary with the factor. Hoisting the cutoff data
before the `∀ factor` therefore yields a single nonnegative constant `C`
bounding `wkpNorm K 2 (coef · factor)` by `ENNReal.ofReal C · wkpNorm K 2 factor`
for every admissible factor at once. -/

private lemma wkpNorm_coef_mul_factor_le_uniform
    (α : M) (K : ℕ)
    {coef : EuclN → ℝ}
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ factor : EuclN → ℝ,
      MemWkp (d := Module.finrank ℝ E) K 2 factor
          (chartTargetEuclid (I := I) (M := M) α) →
      (factor =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) →
      MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => coef y * factor y)
          (chartTargetEuclid (I := I) (M := M) α) ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => coef y * factor y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            wkpNorm (d := Module.finrank ℝ E) K 2 factor
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set Kα : Set EuclN := chartPouKernel (I := I) (M := M) α with hKα_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hKα_compact : IsCompact Kα := chartPouKernel_isCompact (I := I) (M := M) α
  have hKα_in : Kα ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- A smooth cutoff `χ` equal to `1` on `cthickening δ Kα`, supported in `Ω`.
  obtain ⟨δ, χ, hδ_pos, hδ_in, hχ_smooth, hχ_cs, _hχ_range, hχ_one, hχ_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      hKα_compact hΩ_open hKα_in
  -- `χ · coef` is globally smooth: smooth on `tsupport χ ⊆ Ω`, identically zero
  -- (hence smooth) on the open complement of `tsupport χ`.
  have hχ_coef_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y * coef y) := by
    have h_open_compl : IsOpen ((tsupport χ)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy_supp : y ∈ tsupport χ
    · have hy_chart : y ∈ Ω := hχ_tsupp hy_supp
      exact hχ_smooth.contDiffAt.mul
        ((hcoef_chart y hy_chart).contDiffAt (hΩ_open.mem_nhds hy_chart))
    · have h_eq_zero : (fun y => χ y * coef y)
          =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_open_compl.mem_nhds hy_supp] with z hz
        rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq h_eq_zero
  have hχ_coef_cs : HasCompactSupport (fun y => χ y * coef y) :=
    HasCompactSupport.mul_right hχ_cs
  -- Uniform bound on the iterated derivatives of `χ · coef` up to order `K`.
  obtain ⟨C₀, hC₀_nn, hC₀_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hχ_coef_smooth hχ_coef_cs K
  -- The factor-uniform quantitative Leibniz bound for the cutoff product.
  obtain ⟨Kc, _hKc_pos, hKc_bd⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hΩ_open hχ_coef_smooth
      hC₀_nn (fun j _hj y _hy => hC₀_bd y j _hj)
  set Cδ : Set EuclN := Metric.cthickening δ Kα with hCδ_def
  have hCδ_closed : IsClosed Cδ := Metric.isClosed_cthickening
  have hCδ_meas : MeasurableSet Cδ := hCδ_closed.measurableSet
  refine ⟨Kc, le_of_lt _hKc_pos, fun factor hfactor_memWkp hfactor_ae_zero => ?_⟩
  -- `(χ · coef) · factor ∈ MemWkp K 2`, via `MemWkp.smul_smooth_bounded`.
  have h_prod_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (χ y * coef y) * factor y) Ω :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hχ_coef_smooth
      (fun j _hj y _hy => hC₀_bd y j _hj) hfactor_memWkp
  -- `(χ · coef) · factor =ᵃᵉ coef · factor` on `volume.restrict Ω`.
  have h_ae_eq : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => coef y * factor y) := by
    -- On `Cδ ⊆ Ω`: `χ = 1`, so `(χ · coef) · factor = coef · factor`.
    have h_eq_on_Cδ : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict Cδ]
        (fun y => coef y * factor y) := by
      refine (ae_restrict_iff' hCδ_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      have hχy : χ y = 1 := hχ_one y hy
      change (χ y * coef y) * factor y = coef y * factor y
      rw [hχy]; ring
    -- On `Ω \ Cδ ⊆ Ω \ Kα`: `factor` ae-vanishes.
    have hKα_in_Cδ : Kα ⊆ Cδ := Metric.self_subset_cthickening _
    have h_diff_sub : Ω \ Cδ ⊆ Ω \ Kα := fun y hy =>
      ⟨hy.1, fun hyK => hy.2 (hKα_in_Cδ hyK)⟩
    have h_factor_ae_zero_diff : factor =ᵐ[(volume : Measure EuclN).restrict
        (Ω \ Cδ)] (fun _ => (0 : ℝ)) := by
      have h_abs : (volume : Measure EuclN).restrict (Ω \ Cδ) ≪
          (volume : Measure EuclN).restrict (Ω \ Kα) :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono h_diff_sub le_rfl)
      exact h_abs.ae_le hfactor_ae_zero
    have h_eq_on_diff : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict (Ω \ Cδ)]
        (fun y => coef y * factor y) := by
      filter_upwards [h_factor_ae_zero_diff] with y hy
      show (χ y * coef y) * factor y = coef y * factor y
      rw [hy]; ring
    have h_eq_on_inter : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict (Ω ∩ Cδ)]
        (fun y => coef y * factor y) := by
      have h_abs : (volume : Measure EuclN).restrict (Ω ∩ Cδ) ≪
          (volume : Measure EuclN).restrict Cδ :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono Set.inter_subset_right le_rfl)
      exact h_abs.ae_le h_eq_on_Cδ
    have h_diff_meas : MeasurableSet (Ω \ Cδ) := hΩ_meas.diff hCδ_meas
    have h_cover : Ω = (Ω ∩ Cδ) ∪ (Ω \ Cδ) := by
      ext y; constructor
      · intro hy
        by_cases h : y ∈ Cδ
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
      · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    have h_disj : Disjoint (Ω ∩ Cδ) (Ω \ Cδ) :=
      Set.disjoint_left.mpr fun y hy hy' => hy'.2 hy.2
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict ((Ω ∩ Cδ) ∪ (Ω \ Cδ)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, MeasureTheory.Measure.restrict_union h_disj h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  -- Transfer `MemWkp K 2` through the ae-equality.
  have h_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω :=
    (MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).mp h_prod_memWkp
  refine ⟨h_memWkp, ?_⟩
  -- Transfer the `wkpNorm` bound through the ae-equality.
  have h_norm_eq : wkpNorm (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω =
      wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => (χ y * coef y) * factor y) Ω :=
    (wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).symm
  rw [h_norm_eq]
  exact hKc_bd hfactor_memWkp

/-! ## A finite-sum closure for `MemWkp K 2`

The differentiated numerator's layers `A`, `B` are finite double sums; the helper
below propagates `MemWkp K 2` through a finite sum indexed by an arbitrary
`Finset`. -/

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma memWkp_finset_sum
    {α : M} {K : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → EuclN → ℝ}
    (hf : ∀ i ∈ s, MemWkp (d := Module.finrank ℝ E) K 2 (f i)
      (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ i ∈ s, f i y) (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact MemWkp_zero_fun (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open
  | insert i s his ih =>
      have hi : MemWkp (d := Module.finrank ℝ E) K 2 (f i)
          (chartTargetEuclid (I := I) (M := M) α) :=
        hf i (Finset.mem_insert_self _ _)
      have hsum := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      have h_eq : (fun y => ∑ j ∈ insert i s, f j y) =
          (fun y => f i y + ∑ j ∈ s, f j y) := by
        funext y; rw [Finset.sum_insert his]
      rw [h_eq]
      exact MemWkp.add (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open hi hsum

/-! ## The reciprocal chart density

The differentiated numerator is divided by the chart density; the reciprocal
`1 / densityOnEuclid g α` is `C^∞` on the open chart target because the chart
density is `C^∞` and strictly positive there. -/

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
/-- The reciprocal `1 / densityOnEuclid g α` of the chart density is `C^∞` on the
open Euclidean chart target: the chart density is `C^∞`
(`densityOnEuclid_contDiffOn`) and strictly positive (`densityOnEuclid_pos`)
there. -/
lemma one_div_densityOnEuclid_contDiffOn_chartTargetEuclid
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => 1 / densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  contDiffOn_const.div (densityOnEuclid_contDiffOn (I := I) g α)
    (fun _ hy => (densityOnEuclid_pos (I := I) g α hy).ne')

/-! ## The layer-`A` smooth coefficient

Layer `A`'s coefficient is the `∂_b`-evaluation of `weightedInvGramDerivOnEuclid`,
which is `C^∞` on the open chart target. -/

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
/-- The layer-`A` coefficient `∂_b (weightedInvGramDerivOnEuclid g α a b lₙ)` is
`C^∞` on the open chart target. -/
private lemma layerA_coeff_contDiffOn_chartTargetEuclid
    (g : SmoothRiemannianMetric I M) (α : M)
    (lₙ : Fin (Module.finrank ℝ E)) (a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b lₙ) y)
          (EuclideanSpace.single b 1))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_diffOn : ContDiffOn ℝ (⊤ : ℕ∞)
      (weightedInvGramDerivOnEuclid (I := I) g α a b lₙ)
      (chartTargetEuclid (I := I) (M := M) α) :=
    weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b lₙ
  have h_fderiv : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b lₙ) y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_diffOn).2
  have h_eval : ContDiff ℝ (⊤ : ℕ∞)
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single b 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single b (1 : ℝ))).contDiff
  exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)

/-! ## The differentiated chart-RHS numerator ae-vanishes off the kernel

Every layer factor of the differentiated numerator — the iterated mixed weak
partials of the eigenvector chart component, and `fChartEffPrev` with its chosen
weak `lₙ`-partial — ae-vanishes on `chartTargetEuclid α \ chartPouKernel α`. Hence
each layer (a coefficient times such a factor) does, and so does their `+`/`-`
combination. -/

omit [CompleteSpace E] in
/-- The differentiated chart-RHS numerator ae-vanishes off the partition-of-unity
kernel `chartPouKernel α`: each of its five layer factors ae-vanishes on
`chartTargetEuclid α \ chartPouKernel α`, so each layer and their `+`/`-`
combination does. -/
lemma eigenvectorChartRHSDiffNumerator_ae_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_prev_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    eigenvectorChartRHSDiffNumerator (I := I) (M := M)
        g r s h_atlas i α P₀ m l fChartEffPrev
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  -- Layer-A factors: every level-`(m+1)` mixed partial `Fin.cons a (Fin.init l)`.
  have hA_ae : ∀ a : Fin (Module.finrank ℝ E),
      eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) := fun a =>
    eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel (I := I) (M := M)
      g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))
  -- Layer-B factors: the chosen weak `b`-partials of those.
  have hB_ae : ∀ a b : Fin (Module.finrank ℝ E),
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) := fun a b =>
    chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
      (I := I) (M := M) α (hA_ae a) b
  -- Layer-C factor: the level-`m` mixed partial in `Fin.init l`.
  have hC_ae := eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
    (I := I) (M := M) g r s h_atlas i α P₀ m (Fin.init l)
  -- Layer-E factor: the chosen weak `lₙ`-partial of `fChartEffPrev`.
  have hE_ae := chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
    (I := I) (M := M) α h_prev_zero (l (Fin.last m))
  -- Layer A is ae-zero on the diff.
  have hA_sum_ae : (fun y => ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    have h_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)),
        ∀ a : Fin (Module.finrank ℝ E),
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y = 0 := by
      rw [Filter.eventually_all]
      intro a
      exact hA_ae a
    filter_upwards [h_all] with y hy
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    change (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
          (l (Fin.last m))) y)
        (EuclideanSpace.single b 1) *
      eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y = 0
    rw [hy a]; ring
  -- Layer B is ae-zero on the diff.
  have hB_sum_ae : (fun y => ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    have h_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)),
        ∀ a : Fin (Module.finrank ℝ E), ∀ b : Fin (Module.finrank ℝ E),
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y = 0 := by
      rw [Filter.eventually_all]
      intro a
      rw [Filter.eventually_all]
      intro b
      exact hB_ae a b
    filter_upwards [h_all] with y hy
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    change weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α) y = 0
    rw [hy a b]; ring
  -- Layer C is ae-zero on the diff.
  have hC_term_ae : (fun y =>
      densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ m (Fin.init l) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hC_ae] with y hy
    show densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ m (Fin.init l) y = 0
    rw [hy]; ring
  -- Layer D is ae-zero on the diff.
  have hD_term_ae : (fun y =>
      densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y * fChartEffPrev y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [h_prev_zero] with y hy
    show densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      fChartEffPrev y = 0
    rw [hy]; ring
  -- Layer E is ae-zero on the diff.
  have hE_term_ae : (fun y =>
      densityOnEuclid (I := I) g α y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
          fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hE_ae] with y hy
    show densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y = 0
    rw [hy]; ring
  -- Combine: the numerator is `A + B - C + D + E`, each ae-zero on the diff.
  filter_upwards [hA_sum_ae, hB_sum_ae, hC_term_ae, hD_term_ae, hE_term_ae]
    with y hA hB hC hD hE
  show eigenvectorChartRHSDiffNumerator (I := I) (M := M)
      g r s h_atlas i α P₀ m l fChartEffPrev y = 0
  unfold eigenvectorChartRHSDiffNumerator
  rw [hA, hB, hC, hD, hE]; ring

/-! ## `MemWkp K 2` of the differentiated chart-RHS numerator from `h_iter`

The headline numerator `wkpNorm` bound `eigenvectorChartRHSDiffNumerator_wkpNorm_le`
carries, as a genuine regularity hypothesis, the `W^{2 + K, 2}` membership
`h_iter` of every iterated weak partial feeding the numerator. The smooth-coefficient
`wkpNorm` bound with ae-vanishing already proves the *bound*; the helper below
extracts, from exactly the same hypotheses, the companion `MemWkp K 2` membership
of the numerator on the open chart target — needed to feed the numerator to
`wkpNorm_smul_smooth_bounded_le` when multiplying by the reciprocal density. The
proof mirrors `eigenvectorChartRHSDiffNumerator_memWkp` layer by layer, but takes
the iterated-weak-partial memberships directly from `h_iter` rather than from a
chart-component regularity hypothesis. -/

omit [CompleteSpace E] in
lemma eigenvectorChartRHSDiffNumerator_memWkp_of_iter
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_iter : ∀ (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev : MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartRHSDiffNumerator (I := I) (M := M)
        g r s h_atlas i α P₀ m l fChartEffPrev)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  -- Layer A: `∑_{a,b} (∂_b weightedInvGram) · ((m+1)-fold mixed partial)`.
  have hA : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                (l (Fin.last m))) y)
              (EuclideanSpace.single b 1) *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_pair : ∀ a b : Fin (Module.finrank ℝ E),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y =>
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                  (l (Fin.last m))) y)
                (EuclideanSpace.single b 1) *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
          (chartTargetEuclid (I := I) (M := M) α) := by
      intro a b
      have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) :=
        (h_iter (m + 1) (Fin.cons a (Fin.init l))).le_of_le (by omega)
      have h_factor_ae_zero :=
        eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s h_atlas i α P₀ (m + 1)
          (Fin.cons a (Fin.init l))
      exact (wkpNorm_coef_mul_factor_le (I := I) (M := M) α K
        (layerA_coeff_contDiffOn_chartTargetEuclid (I := I) (M := M)
          g α (l (Fin.last m)) a b) h_factor_memWkp h_factor_ae_zero).1
    have h_inner : ∀ a : Fin (Module.finrank ℝ E),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => ∑ b : Fin (Module.finrank ℝ E),
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                  (l (Fin.last m))) y)
                (EuclideanSpace.single b 1) *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
          (chartTargetEuclid (I := I) (M := M) α) := fun a =>
      memWkp_finset_sum (I := I) (M := M) (α := α) (K := K) Finset.univ
        (fun b _hb => h_pair a b)
    exact memWkp_finset_sum (I := I) (M := M) (α := α) (K := K) Finset.univ
      (fun a _ha => h_inner a)
  -- Layer B: `∑_{a,b} weightedInvGram · (∂_b-weak-partial of the (m+1)-fold partial)`.
  have hB : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
              (chartTargetEuclid (I := I) (M := M) α) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_pair : ∀ a b : Fin (Module.finrank ℝ E),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y =>
            weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α) y)
          (chartTargetEuclid (I := I) (M := M) α) := by
      intro a b
      -- The level-`(m+1)` mixed partial lies in `MemWkp (K + 1) 2`.
      have h_inner_memWkp_succ : MemWkp (d := Module.finrank ℝ E) (K + 1) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) :=
        (h_iter (m + 1) (Fin.cons a (Fin.init l))).le_of_le (by omega)
      -- The chosen weak `b`-partial of it is `MemWkp K 2`.
      have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α))
          (chartTargetEuclid (I := I) (M := M) α) :=
        h_inner_memWkp_succ.chosenWeakPartial_mem b
      -- The chosen weak `b`-partial ae-vanishes off the kernel.
      have h_inner_ae :=
        eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s h_atlas i α P₀ (m + 1)
          (Fin.cons a (Fin.init l))
      have h_factor_ae_zero :=
        chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
          (I := I) (M := M) α h_inner_ae b
      exact (wkpNorm_coef_mul_factor_le (I := I) (M := M) α K
        (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b
          (l (Fin.last m))) h_factor_memWkp h_factor_ae_zero).1
    have h_inner : ∀ a : Fin (Module.finrank ℝ E),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => ∑ b : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α) y)
          (chartTargetEuclid (I := I) (M := M) α) := fun a =>
      memWkp_finset_sum (I := I) (M := M) (α := α) (K := K) Finset.univ
        (fun b _hb => h_pair a b)
    exact memWkp_finset_sum (I := I) (M := M) (α := α) (K := K) Finset.univ
      (fun a _ha => h_inner a)
  -- Layer C: `(∂_{lₙ} densityDeriv) · (m-fold mixed partial in `Fin.init l`)`.
  have hC : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ m (Fin.init l) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ m (Fin.init l))
        (chartTargetEuclid (I := I) (M := M) α) :=
      (h_iter m (Fin.init l)).le_of_le (by omega)
    have h_factor_ae_zero :=
      eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s h_atlas i α P₀ m (Fin.init l)
    exact (wkpNorm_coef_mul_factor_le (I := I) (M := M) α K
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
      h_factor_memWkp h_factor_ae_zero).1
  -- Layer D: `(∂_{lₙ} densityDeriv) · fChartEffPrev`.
  have hD : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y * fChartEffPrev y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (wkpNorm_coef_mul_factor_le (I := I) (M := M) α K
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
      (h_prev.le_of_le (by omega)) h_prev_zero).1
  -- Layer E: `densityOnEuclid · (∂_{lₙ}-weak-partial of fChartEffPrev)`.
  have hE : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        densityOnEuclid (I := I) g α y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
            fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
          fChartEffPrev (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
      h_prev.chosenWeakPartial_mem (l (Fin.last m))
    have h_factor_ae_zero :=
      chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
        (I := I) (M := M) α h_prev_zero (l (Fin.last m))
    exact (wkpNorm_coef_mul_factor_le (I := I) (M := M) α K
      (densityOnEuclid_contDiffOn (I := I) g α)
      h_factor_memWkp h_factor_ae_zero).1
  -- Combine the five layers: numerator = A + B - C + D + E.
  have h_step1 := MemWkp.add (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open hA hB
  have h_step2 := MemWkp.sub (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open h_step1 hC
  have h_step3 := MemWkp.add (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open h_step2 hD
  have h_step4 := MemWkp.add (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open h_step3 hE
  -- The assembled sum is definitionally the numerator.
  have h_eq : (fun y =>
      ((((∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                (l (Fin.last m))) y)
              (EuclideanSpace.single b 1) *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y) +
        (∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α) y)) -
        densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ m (Fin.init l) y) +
        densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
          fChartEffPrev y) +
        densityOnEuclid (I := I) g α y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
            fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y) =
      eigenvectorChartRHSDiffNumerator (I := I) (M := M)
        g r s h_atlas i α P₀ m l fChartEffPrev := by
    funext y
    rfl
  rw [← h_eq]
  exact h_step4

/-! ## `wkpNorm` bound for the chart-density-divided differentiated numerator -/

section DivDensityBound

omit [CompleteSpace E] in
/-- **The `K`-graded explicit-norm `wkpNorm` bound for the chart-density-divided
differentiated chart-RHS numerator.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, a component multi-index `P₀`, a level `m`, a
regularity order `K`, a direction multi-index `l : Fin (m+1) → Fin n`, and a
previous-level right-hand side `fChartEffPrev : EuclN → ℝ`, there is a
nonnegative constant `C` such that the order-`K` Sobolev norm of the
chart-density-divided differentiated chart-RHS numerator
`eigenvectorChartRHSDiffNumerator g r s h_atlas i α P₀ m l fChartEffPrev /
densityOnEuclid g α` on the open Euclidean chart target `chartTargetEuclid α` is
bounded by `ENNReal.ofReal C` times the finite aggregate `diffNumeratorAggregateK`
of the order-`K` source norms — the *same* aggregate appearing in
`eigenvectorChartRHSDiffNumerator_wkpNorm_le`.

The hypotheses are exactly those of `eigenvectorChartRHSDiffNumerator_wkpNorm_le`:
every `(m+1)`-fold and `m`-fold iterated weak partial of the eigenvector chart
component appearing in the numerator lies in `W^{2 + K, 2}(chartTargetEuclid α)`
(the regularity hypothesis `h_iter`); and the previous-level right-hand side
`fChartEffPrev` lies in `W^{K + 1, 2}(chartTargetEuclid α)` (the hypothesis
`h_prev`) and vanishes almost everywhere off the partition-of-unity kernel
`chartPouKernel α` (the support hypothesis `h_prev_zero`).

The quotient `numerator / densityOnEuclid g α` is rewritten as
`(1 / densityOnEuclid g α) · numerator`. The reciprocal `1 / densityOnEuclid g α`
is `C^∞` on the open chart target; the smooth-coefficient `wkpNorm` bound with
ae-vanishing `wkpNorm_coef_mul_factor_le` cuts it off to a globally smooth
compactly supported representative and bounds `wkpNorm K 2 ((1/density) ·
numerator)` by `ENNReal.ofReal C' · wkpNorm K 2 numerator`. Chaining
`eigenvectorChartRHSDiffNumerator_wkpNorm_le` closes the bound; the two
constants fold into the single nonnegative `C`. -/
theorem eigenvectorChartRHSDiffNumerator_div_density_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (h_iter : ∀ (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev : MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y =>
            eigenvectorChartRHSDiffNumerator (I := I) (M := M)
              g r s h_atlas i α P₀ m l fChartEffPrev y /
            densityOnEuclid (I := I) g α y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregateK (I := I) (M := M)
            g r s h_atlas i α P₀ m K l fChartEffPrev := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set A := diffNumeratorAggregateK (I := I) (M := M)
    g r s h_atlas i α P₀ m K l fChartEffPrev with hA_def
  set numFun : EuclN → ℝ := eigenvectorChartRHSDiffNumerator (I := I) (M := M)
    g r s h_atlas i α P₀ m l fChartEffPrev with hnumFun_def
  -- Rewrite the quotient as `(1 / density) · numerator`.
  have h_eq : (fun y => numFun y / densityOnEuclid (I := I) g α y) =
      (fun y => (1 / densityOnEuclid (I := I) g α y) * numFun y) := by
    funext y
    rw [one_div, mul_comm, ← div_eq_mul_inv]
  rw [h_eq]
  -- The numerator's order-`K` `wkpNorm` is bounded by `ofReal C₁ * A`.
  obtain ⟨C₁, hC₁_nn, hC₁⟩ := eigenvectorChartRHSDiffNumerator_wkpNorm_le
    (I := I) (M := M) g r s h_atlas i α P₀ m K l fChartEffPrev
    h_iter h_prev h_prev_zero
  rw [← hΩ_def, ← hA_def, ← hnumFun_def] at hC₁
  -- The numerator is `MemWkp K 2` on the chart target — re-derived from `h_iter`.
  have h_num_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 numFun Ω := by
    rw [hnumFun_def, ← hΩ_def] at *
    exact eigenvectorChartRHSDiffNumerator_memWkp_of_iter
      (I := I) (M := M) g r s h_atlas i α P₀ m K l
      h_iter h_prev h_prev_zero
  -- The numerator ae-vanishes off the partition-of-unity kernel.
  have h_num_ae_zero :
      numFun =ᵐ[(volume : Measure EuclN).restrict
        (Ω \ chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
    rw [hnumFun_def, hΩ_def]
    exact eigenvectorChartRHSDiffNumerator_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s h_atlas i α P₀ m l h_prev_zero
  -- The reciprocal density times the numerator: smooth-coefficient `wkpNorm` bound.
  obtain ⟨_h_prod_mem, C₂, hC₂_nn, hC₂⟩ := wkpNorm_coef_mul_factor_le
    (I := I) (M := M) α K
    (one_div_densityOnEuclid_contDiffOn_chartTargetEuclid (I := I) (M := M) g α)
    h_num_memWkp h_num_ae_zero
  rw [← hΩ_def] at hC₂
  -- Chain: `wkpNorm ((1/density) · num) ≤ ofReal C₂ · wkpNorm num`
  --        `≤ ofReal C₂ · (ofReal C₁ · A) = ofReal (C₂ * C₁) · A`.
  refine ⟨C₂ * C₁, mul_nonneg hC₂_nn hC₁_nn, ?_⟩
  calc
    wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => (1 / densityOnEuclid (I := I) g α y) * numFun y) Ω
        ≤ ENNReal.ofReal C₂ * wkpNorm (d := Module.finrank ℝ E) K 2 numFun Ω :=
          hC₂
    _ ≤ ENNReal.ofReal C₂ * (ENNReal.ofReal C₁ * A) := by
          gcongr
    _ = ENNReal.ofReal (C₂ * C₁) * A := by
          rw [ENNReal.ofReal_mul hC₂_nn, mul_assoc]

omit [CompleteSpace E] in
/-- **The uniform-constant `K`-graded explicit-norm `wkpNorm` bound for the
chart-density-divided differentiated chart-RHS numerator.**

The constant-uniform form of `eigenvectorChartRHSDiffNumerator_div_density_wkpNorm_le`:
a single nonnegative constant `C` — geometric, the combined Leibniz constant of
the `C^∞` reciprocal chart density and the numerator's per-layer Leibniz
constants, independent of the eigenbasis index — serves *every* eigenbasis index
`i`. For each `i`, the order-`K` Sobolev norm of the chart-density-divided
differentiated chart-RHS numerator
`eigenvectorChartRHSDiffNumerator g r s h_atlas i α P₀ m l (fChartEffPrev i) /
densityOnEuclid g α` on the open Euclidean chart target `chartTargetEuclid α` is
bounded by `ENNReal.ofReal C` times the finite aggregate `diffNumeratorAggregateK`
of the order-`K` source norms of that `i` — the *same* aggregate appearing in
`eigenvectorChartRHSDiffNumerator_wkpNorm_le_uniform`.

The genuine regularity hypotheses are uniform over `i`: every `(m+1)`-fold and
`m`-fold iterated weak partial of every eigenvector chart component lies in
`W^{2 + K, 2}(chartTargetEuclid α)` (`h_iter`); each previous-level right-hand
side `fChartEffPrev i` lies in `W^{K + 1, 2}(chartTargetEuclid α)` (`h_prev`) and
vanishes almost everywhere off the partition-of-unity kernel `chartPouKernel α`
(`h_prev_zero`).

A `_uniform` statement cannot be derived from its per-`i` original (one cannot
get `∃ C, ∀ i` from `∀ i, ∃ C`); this carries its own proof — the per-`i` proof
of `eigenvectorChartRHSDiffNumerator_div_density_wkpNorm_le` with the two
geometric constants hoisted before the `∀ i` via the constant-uniform numerator
bound `eigenvectorChartRHSDiffNumerator_wkpNorm_le_uniform` and the factor-uniform
smooth-coefficient bound `wkpNorm_coef_mul_factor_le_uniform`. -/
theorem eigenvectorChartRHSDiffNumerator_div_density_wkpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_iter : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      (fChartEffPrev i) =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y =>
              eigenvectorChartRHSDiffNumerator (I := I) (M := M)
                g r s h_atlas i α P₀ m l (fChartEffPrev i) y /
              densityOnEuclid (I := I) g α y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK (I := I) (M := M)
              g r s h_atlas i α P₀ m K l (fChartEffPrev i) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  -- The numerator's order-`K` `wkpNorm` bound — `i`-uniform constant `C₁`.
  obtain ⟨C₁, hC₁_nn, hC₁⟩ := eigenvectorChartRHSDiffNumerator_wkpNorm_le_uniform
    (I := I) (M := M) g r s h_atlas α P₀ m K l fChartEffPrev
    h_iter h_prev h_prev_zero
  -- The reciprocal-density smooth-coefficient bound — factor-uniform constant `C₂`.
  obtain ⟨C₂, hC₂_nn, hC₂⟩ := wkpNorm_coef_mul_factor_le_uniform
    (I := I) (M := M) α K
    (one_div_densityOnEuclid_contDiffOn_chartTargetEuclid (I := I) (M := M) g α)
  -- The headline constant: the product of the two geometric constants.
  refine ⟨C₂ * C₁, mul_nonneg hC₂_nn hC₁_nn, fun i => ?_⟩
  set A := diffNumeratorAggregateK (I := I) (M := M)
    g r s h_atlas i α P₀ m K l (fChartEffPrev i) with hA_def
  set numFun : EuclN → ℝ := eigenvectorChartRHSDiffNumerator (I := I) (M := M)
    g r s h_atlas i α P₀ m l (fChartEffPrev i) with hnumFun_def
  -- Rewrite the quotient as `(1 / density) · numerator`.
  have h_eq : (fun y => numFun y / densityOnEuclid (I := I) g α y) =
      (fun y => (1 / densityOnEuclid (I := I) g α y) * numFun y) := by
    funext y
    rw [one_div, mul_comm, ← div_eq_mul_inv]
  rw [h_eq]
  -- The numerator's order-`K` `wkpNorm` bound for this `i`.
  have hC₁_i : wkpNorm (d := Module.finrank ℝ E) K 2 numFun Ω
      ≤ ENNReal.ofReal C₁ * A := by
    have := hC₁ i
    rw [← hnumFun_def, ← hΩ_def, ← hA_def] at this
    exact this
  -- The numerator is `MemWkp K 2` on the chart target — re-derived from `h_iter i`.
  have h_num_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 numFun Ω := by
    rw [hnumFun_def, hΩ_def]
    exact eigenvectorChartRHSDiffNumerator_memWkp_of_iter
      (I := I) (M := M) g r s h_atlas i α P₀ m K l
      (h_iter i) (h_prev i) (h_prev_zero i)
  -- The numerator ae-vanishes off the partition-of-unity kernel.
  have h_num_ae_zero :
      numFun =ᵐ[(volume : Measure EuclN).restrict
        (Ω \ chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
    rw [hnumFun_def, hΩ_def]
    exact eigenvectorChartRHSDiffNumerator_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s h_atlas i α P₀ m l (h_prev_zero i)
  -- The factor-uniform smooth-coefficient bound, instantiated at `numFun`.
  have hC₂_i := (hC₂ numFun h_num_memWkp h_num_ae_zero).2
  rw [← hΩ_def] at hC₂_i
  -- Chain: `wkpNorm ((1/density) · num) ≤ ofReal C₂ · wkpNorm num`
  --        `≤ ofReal C₂ · (ofReal C₁ · A) = ofReal (C₂ * C₁) · A`.
  calc
    wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => (1 / densityOnEuclid (I := I) g α y) * numFun y) Ω
        ≤ ENNReal.ofReal C₂ * wkpNorm (d := Module.finrank ℝ E) K 2 numFun Ω :=
          hC₂_i
    _ ≤ ENNReal.ofReal C₂ * (ENNReal.ofReal C₁ * A) := by
          gcongr
    _ = ENNReal.ofReal (C₂ * C₁) * A := by
          rw [ENNReal.ofReal_mul hC₂_nn, mul_assoc]

end DivDensityBound

/-! ## `wkpNorm` bound for the standalone inductive step

`eigenvectorChartIteratedStep … m dirs fChartEffPrev l` is the indicator of the
compact partition-of-unity kernel applied to the chart-density-divided
differentiated numerator. Stripping the indicator through an ae-equality on the
open chart target and chaining the density-divided bound gives the `K`-graded
`wkpNorm` bound. -/

section IteratedStepBound

omit [CompleteSpace E] in
/-- **The `K`-graded explicit-norm `wkpNorm` bound for the standalone inductive
step.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, a component multi-index `P₀`, a level `m`, a
regularity order `K`, a level-`m` direction multi-index `dirs : Fin m → Fin n`, a
new direction `l : Fin n`, and a previous-level right-hand side `fChartEffPrev :
EuclN → ℝ`, there is a nonnegative constant `C` such that the order-`K` Sobolev
norm of the level-`(m+1)` standalone inductive step `eigenvectorChartIteratedStep
g r s h_atlas i α P₀ m dirs fChartEffPrev l` on the open Euclidean chart target
`chartTargetEuclid α` is bounded by `ENNReal.ofReal C` times the finite aggregate
`diffNumeratorAggregateK` of the order-`K` source norms, evaluated at the
snoc-extended direction multi-index `Fin.snoc dirs l`.

The hypotheses are those of `eigenvectorChartRHSDiffNumerator_wkpNorm_le` at the
snoc-extended index: every iterated weak partial feeding the differentiated
numerator lies in `W^{2 + K, 2}(chartTargetEuclid α)` (`h_iter`); the previous-level
right-hand side `fChartEffPrev` lies in `W^{K + 1, 2}(chartTargetEuclid α)`
(`h_prev`) and vanishes almost everywhere off `chartPouKernel α` (`h_prev_zero`).

The step is `Set.indicator (chartPouKernel α)` of the chart-density-divided
differentiated numerator `eigenvectorChartRHSDiffNumerator … m (Fin.snoc dirs l)
fChartEffPrev / densityOnEuclid g α` (via
`eigenvectorChartIteratedStepNumerator_eq_rhsDiffNumerator`). On the open chart
target the indicator agrees almost everywhere with the underlying quotient: on the
kernel the indicator returns the quotient, off the kernel both the indicator and
the quotient ae-vanish. `wkpNorm_congr_ae` transfers the order-`K` `wkpNorm`
across this ae-equality, and
`eigenvectorChartRHSDiffNumerator_div_density_wkpNorm_le` closes the bound. -/
theorem eigenvectorChartIteratedStep_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (l : Fin (Module.finrank ℝ E))
    (h_iter : ∀ (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev : MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartIteratedStep (I := I) (M := M)
            g r s h_atlas i α P₀ m dirs fChartEffPrev l)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregateK (I := I) (M := M)
            g r s h_atlas i α P₀ m K (Fin.snoc dirs l) fChartEffPrev := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  -- `eigenvectorChartIteratedStep = indicator (chartPouKernel α) Q`, where
  -- `Q = eigenvectorChartRHSDiffNumerator … (Fin.snoc dirs l) / density`.
  set Q : EuclN → ℝ := fun y =>
    eigenvectorChartRHSDiffNumerator (I := I) (M := M)
      g r s h_atlas i α P₀ m (Fin.snoc dirs l) fChartEffPrev y /
    densityOnEuclid (I := I) g α y with hQ_def
  -- The standalone step is the indicator of the kernel applied to `Q`.
  have h_step_eq :
      eigenvectorChartIteratedStep (I := I) (M := M)
        g r s h_atlas i α P₀ m dirs fChartEffPrev l =
      Set.indicator (chartPouKernel (I := I) (M := M) α) Q := by
    unfold eigenvectorChartIteratedStep
    have h_num := eigenvectorChartIteratedStepNumerator_eq_rhsDiffNumerator
      (I := I) (M := M) g r s h_atlas i α P₀ m dirs fChartEffPrev l
    funext y
    simp only [hQ_def]
    rw [h_num]
  -- `Q` ae-vanishes off the partition-of-unity kernel — the public restatement.
  have hQ_ae_zero : Q =ᵐ[(volume : Measure EuclN).restrict
      (Ω \ chartPouKernel (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
    rw [hQ_def, hΩ_def]
    exact eigenvectorChartRHSDiffNumerator_div_density_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s h_atlas i α P₀ m (Fin.snoc dirs l) h_prev_zero
  -- `indicator (chartPouKernel α) Q =ᵐ Q` on the open chart target.
  -- Split `Ω = (Ω ∩ chartPouKernel α) ∪ (Ω \ chartPouKernel α)`:
  --  on the kernel intersection, the indicator returns `Q`;
  --  off the kernel, the indicator vanishes and `Q =ᵐ 0`.
  have h_indicator_ae_eq_Q :
      Set.indicator (chartPouKernel (I := I) (M := M) α) Q =ᵐ[
        (volume : Measure EuclN).restrict Ω] Q := by
    set Kα : Set EuclN := chartPouKernel (I := I) (M := M) α with hKα_def
    have hΩ_meas : MeasurableSet Ω :=
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
    have hKα_meas : MeasurableSet Kα :=
      chartPouKernel_measurableSet (I := I) (M := M) α
    -- On `Ω ∩ Kα`: `indicator Kα Q = Q`.
    have h_inter_meas : MeasurableSet (Ω ∩ Kα) := hΩ_meas.inter hKα_meas
    have h_eq_on_inter : Set.indicator Kα Q =ᵐ[
        (volume : Measure EuclN).restrict (Ω ∩ Kα)] Q := by
      refine (ae_restrict_iff' h_inter_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      exact Set.indicator_of_mem hy.2 _
    -- On `Ω \ Kα`: `indicator Kα Q = 0` and `Q =ᵐ 0`.
    have h_diff_meas : MeasurableSet (Ω \ Kα) := hΩ_meas.diff hKα_meas
    have h_indicator_ae_zero : Set.indicator Kα Q =ᵐ[
        (volume : Measure EuclN).restrict (Ω \ Kα)]
        (fun _ : EuclN => (0 : ℝ)) := by
      refine (ae_restrict_iff' h_diff_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      exact Set.indicator_of_notMem hy.2 _
    have h_eq_on_diff : Set.indicator Kα Q =ᵐ[
        (volume : Measure EuclN).restrict (Ω \ Kα)] Q := by
      filter_upwards [h_indicator_ae_zero, hQ_ae_zero] with y h0 hQ0
      rw [h0, hQ0]
    -- Cover `Ω` by the two disjoint pieces and recombine the ae-equalities.
    have h_cover : Ω = (Ω ∩ Kα) ∪ (Ω \ Kα) := by
      ext y; constructor
      · intro hy
        by_cases h : y ∈ Kα
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
      · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    have h_disj : Disjoint (Ω ∩ Kα) (Ω \ Kα) :=
      Set.disjoint_left.mpr fun y hy hy' => hy'.2 hy.2
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict ((Ω ∩ Kα) ∪ (Ω \ Kα)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, MeasureTheory.Measure.restrict_union h_disj h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  -- The order-`K` `wkpNorm` of the step equals that of `Q` via the ae-equality.
  have h_norm_eq : wkpNorm (d := Module.finrank ℝ E) K 2
      (eigenvectorChartIteratedStep (I := I) (M := M)
        g r s h_atlas i α P₀ m dirs fChartEffPrev l) Ω =
      wkpNorm (d := Module.finrank ℝ E) K 2 Q Ω := by
    rw [h_step_eq]
    exact wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_indicator_ae_eq_Q
  -- The density-divided bound for the snoc-extended differentiated numerator.
  obtain ⟨C, hC_nn, hC⟩ := eigenvectorChartRHSDiffNumerator_div_density_wkpNorm_le
    (I := I) (M := M) g r s h_atlas i α P₀ m K (Fin.snoc dirs l) fChartEffPrev
    h_iter h_prev h_prev_zero
  refine ⟨C, hC_nn, ?_⟩
  rw [← hΩ_def] at hC
  rw [h_norm_eq, hQ_def]
  exact hC

omit [CompleteSpace E] in
/-- **The uniform-constant `K`-graded explicit-norm `wkpNorm` bound for the
standalone inductive step.**

The constant-uniform form of `eigenvectorChartIteratedStep_wkpNorm_le`: a single
nonnegative constant `C` — geometric, inherited unchanged from
`eigenvectorChartRHSDiffNumerator_div_density_wkpNorm_le_uniform`, independent of
the eigenbasis index — serves *every* eigenbasis index `i`. For each `i`, the
order-`K` Sobolev norm of the level-`(m+1)` standalone inductive step
`eigenvectorChartIteratedStep g r s h_atlas i α P₀ m dirs (fChartEffPrev i) l` on
the open Euclidean chart target `chartTargetEuclid α` is bounded by
`ENNReal.ofReal C` times the finite aggregate `diffNumeratorAggregateK` of the
order-`K` source norms of that `i`, evaluated at the snoc-extended direction
multi-index `Fin.snoc dirs l`.

The genuine regularity hypotheses are uniform over `i`: every iterated weak
partial feeding the differentiated numerator lies in
`W^{2 + K, 2}(chartTargetEuclid α)` (`h_iter`); each previous-level right-hand
side `fChartEffPrev i` lies in `W^{K + 1, 2}(chartTargetEuclid α)` (`h_prev`) and
vanishes almost everywhere off the partition-of-unity kernel `chartPouKernel α`
(`h_prev_zero`).

A `_uniform` statement cannot be derived from its per-`i` original (one cannot
get `∃ C, ∀ i` from `∀ i, ∃ C`); this carries its own proof — the per-`i` proof
of `eigenvectorChartIteratedStep_wkpNorm_le` with the constant hoisted before the
`∀ i` via the constant-uniform density-divided numerator bound
`eigenvectorChartRHSDiffNumerator_div_density_wkpNorm_le_uniform`. The
indicator-stripping ae-equality remains per-`i`. -/
theorem eigenvectorChartIteratedStep_wkpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (l : Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_iter : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      (fChartEffPrev i) =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartIteratedStep (I := I) (M := M)
              g r s h_atlas i α P₀ m dirs (fChartEffPrev i) l)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK (I := I) (M := M)
              g r s h_atlas i α P₀ m K (Fin.snoc dirs l) (fChartEffPrev i) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  -- The density-divided bound for the snoc-extended numerator — `i`-uniform `C`.
  obtain ⟨C, hC_nn, hC⟩ :=
    eigenvectorChartRHSDiffNumerator_div_density_wkpNorm_le_uniform
      (I := I) (M := M) g r s h_atlas α P₀ m K (Fin.snoc dirs l) fChartEffPrev
      h_iter h_prev h_prev_zero
  refine ⟨C, hC_nn, fun i => ?_⟩
  -- `eigenvectorChartIteratedStep = indicator (chartPouKernel α) Q`, where
  -- `Q = eigenvectorChartRHSDiffNumerator … (Fin.snoc dirs l) / density`.
  set Q : EuclN → ℝ := fun y =>
    eigenvectorChartRHSDiffNumerator (I := I) (M := M)
      g r s h_atlas i α P₀ m (Fin.snoc dirs l) (fChartEffPrev i) y /
    densityOnEuclid (I := I) g α y with hQ_def
  -- The standalone step is the indicator of the kernel applied to `Q`.
  have h_step_eq :
      eigenvectorChartIteratedStep (I := I) (M := M)
        g r s h_atlas i α P₀ m dirs (fChartEffPrev i) l =
      Set.indicator (chartPouKernel (I := I) (M := M) α) Q := by
    unfold eigenvectorChartIteratedStep
    have h_num := eigenvectorChartIteratedStepNumerator_eq_rhsDiffNumerator
      (I := I) (M := M) g r s h_atlas i α P₀ m dirs (fChartEffPrev i) l
    funext y
    simp only [hQ_def]
    rw [h_num]
  -- `Q` ae-vanishes off the partition-of-unity kernel — the public restatement.
  have hQ_ae_zero : Q =ᵐ[(volume : Measure EuclN).restrict
      (Ω \ chartPouKernel (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
    rw [hQ_def, hΩ_def]
    exact eigenvectorChartRHSDiffNumerator_div_density_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s h_atlas i α P₀ m (Fin.snoc dirs l)
      (h_prev_zero i)
  -- `indicator (chartPouKernel α) Q =ᵐ Q` on the open chart target.
  -- Split `Ω = (Ω ∩ chartPouKernel α) ∪ (Ω \ chartPouKernel α)`:
  --  on the kernel intersection, the indicator returns `Q`;
  --  off the kernel, the indicator vanishes and `Q =ᵐ 0`.
  have h_indicator_ae_eq_Q :
      Set.indicator (chartPouKernel (I := I) (M := M) α) Q =ᵐ[
        (volume : Measure EuclN).restrict Ω] Q := by
    set Kα : Set EuclN := chartPouKernel (I := I) (M := M) α with hKα_def
    have hΩ_meas : MeasurableSet Ω :=
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
    have hKα_meas : MeasurableSet Kα :=
      chartPouKernel_measurableSet (I := I) (M := M) α
    -- On `Ω ∩ Kα`: `indicator Kα Q = Q`.
    have h_inter_meas : MeasurableSet (Ω ∩ Kα) := hΩ_meas.inter hKα_meas
    have h_eq_on_inter : Set.indicator Kα Q =ᵐ[
        (volume : Measure EuclN).restrict (Ω ∩ Kα)] Q := by
      refine (ae_restrict_iff' h_inter_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      exact Set.indicator_of_mem hy.2 _
    -- On `Ω \ Kα`: `indicator Kα Q = 0` and `Q =ᵐ 0`.
    have h_diff_meas : MeasurableSet (Ω \ Kα) := hΩ_meas.diff hKα_meas
    have h_indicator_ae_zero : Set.indicator Kα Q =ᵐ[
        (volume : Measure EuclN).restrict (Ω \ Kα)]
        (fun _ : EuclN => (0 : ℝ)) := by
      refine (ae_restrict_iff' h_diff_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      exact Set.indicator_of_notMem hy.2 _
    have h_eq_on_diff : Set.indicator Kα Q =ᵐ[
        (volume : Measure EuclN).restrict (Ω \ Kα)] Q := by
      filter_upwards [h_indicator_ae_zero, hQ_ae_zero] with y h0 hQ0
      rw [h0, hQ0]
    -- Cover `Ω` by the two disjoint pieces and recombine the ae-equalities.
    have h_cover : Ω = (Ω ∩ Kα) ∪ (Ω \ Kα) := by
      ext y; constructor
      · intro hy
        by_cases h : y ∈ Kα
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
      · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    have h_disj : Disjoint (Ω ∩ Kα) (Ω \ Kα) :=
      Set.disjoint_left.mpr fun y hy hy' => hy'.2 hy.2
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict ((Ω ∩ Kα) ∪ (Ω \ Kα)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, MeasureTheory.Measure.restrict_union h_disj h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  -- The order-`K` `wkpNorm` of the step equals that of `Q` via the ae-equality.
  have h_norm_eq : wkpNorm (d := Module.finrank ℝ E) K 2
      (eigenvectorChartIteratedStep (I := I) (M := M)
        g r s h_atlas i α P₀ m dirs (fChartEffPrev i) l) Ω =
      wkpNorm (d := Module.finrank ℝ E) K 2 Q Ω := by
    rw [h_step_eq]
    exact wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_indicator_ae_eq_Q
  -- The density-divided bound for this `i`, against the snoc-extended aggregate.
  have hC_i := hC i
  rw [← hΩ_def] at hC_i
  rw [h_norm_eq, hQ_def]
  exact hC_i

end IteratedStepBound

/-! ## Sanity tests -/

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (h_iter : ∀ (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev : MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y =>
            eigenvectorChartRHSDiffNumerator (I := I) (M := M)
              g r s h_atlas i α P₀ m l fChartEffPrev y /
            densityOnEuclid (I := I) g α y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregateK (I := I) (M := M)
            g r s h_atlas i α P₀ m K l fChartEffPrev :=
  eigenvectorChartRHSDiffNumerator_div_density_wkpNorm_le (I := I) (M := M)
    g r s h_atlas i α P₀ m K l fChartEffPrev h_iter h_prev h_prev_zero

example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (l : Fin (Module.finrank ℝ E))
    (h_iter : ∀ (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev : MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartIteratedStep (I := I) (M := M)
            g r s h_atlas i α P₀ m dirs fChartEffPrev l)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregateK (I := I) (M := M)
            g r s h_atlas i α P₀ m K (Fin.snoc dirs l) fChartEffPrev :=
  eigenvectorChartIteratedStep_wkpNorm_le (I := I) (M := M)
    g r s h_atlas i α P₀ m K dirs l h_iter h_prev h_prev_zero

end ElaborationTests

/-! ## Chart-locality-free twins

The chart-locality-free `_unconditional` companions of the `h_atlas`-carrying
declarations above. Each statement and proof transfers verbatim, with the
`m`-fold mixed weak partials re-keyed onto
`eigenvectorChartIteratedPartial_unconditional` (built on the
intrinsic-compactness eigenvector
`tensorResolventEigenbasisVec_ofCompact (tensorResolventL2_isCompactOperator_intrinsic g r s) i`),
the five-layer numerator onto `eigenvectorChartRHSDiffNumerator_unconditional`,
the aggregate onto `diffNumeratorAggregateK_unconditional`, the standalone
inductive step onto `eigenvectorChartIteratedStep_unconditional`, and the
ae-vanishing-off-the-kernel facts onto
`eigenvectorChartIteratedPartial_unconditional_ae_zero_off_chartPouKernel`,
`eigenvectorChartRHSDiffNumerator_unconditional_div_density_ae_zero_off_chartPouKernel`
and `eigenvectorChartIteratedStepNumerator_unconditional_eq_rhsDiffNumerator`. -/

/-- Chart-locality-free twin of
`eigenvectorChartRHSDiffNumerator_ae_zero_off_chartPouKernel`. -/
lemma eigenvectorChartRHSDiffNumerator_ae_zero_off_chartPouKernel_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_prev_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    eigenvectorChartRHSDiffNumerator_unconditional (I := I) (M := M)
        g r s i α P₀ m l fChartEffPrev
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  -- Layer-A factors: every level-`(m+1)` mixed partial `Fin.cons a (Fin.init l)`.
  have hA_ae : ∀ a : Fin (Module.finrank ℝ E),
      eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
        g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) := fun a =>
    eigenvectorChartIteratedPartial_unconditional_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))
  -- Layer-B factors: the chosen weak `b`-partials of those.
  have hB_ae : ∀ a b : Fin (Module.finrank ℝ E),
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) := fun a b =>
    chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
      (I := I) (M := M) α (hA_ae a) b
  -- Layer-C factor: the level-`m` mixed partial in `Fin.init l`.
  have hC_ae := eigenvectorChartIteratedPartial_unconditional_ae_zero_off_chartPouKernel
    (I := I) (M := M) g r s i α P₀ m (Fin.init l)
  -- Layer-E factor: the chosen weak `lₙ`-partial of `fChartEffPrev`.
  have hE_ae := chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
    (I := I) (M := M) α h_prev_zero (l (Fin.last m))
  -- Layer A is ae-zero on the diff.
  have hA_sum_ae : (fun y => ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    have h_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)),
        ∀ a : Fin (Module.finrank ℝ E),
          eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y = 0 := by
      rw [Filter.eventually_all]
      intro a
      exact hA_ae a
    filter_upwards [h_all] with y hy
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    change (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
          (l (Fin.last m))) y)
        (EuclideanSpace.single b 1) *
      eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
        g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y = 0
    rw [hy a]; ring
  -- Layer B is ae-zero on the diff.
  have hB_sum_ae : (fun y => ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    have h_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)),
        ∀ a : Fin (Module.finrank ℝ E), ∀ b : Fin (Module.finrank ℝ E),
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y = 0 := by
      rw [Filter.eventually_all]
      intro a
      rw [Filter.eventually_all]
      intro b
      exact hB_ae a b
    filter_upwards [h_all] with y hy
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    change weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α) y = 0
    rw [hy a b]; ring
  -- Layer C is ae-zero on the diff.
  have hC_term_ae : (fun y =>
      densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
        eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ m (Fin.init l) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hC_ae] with y hy
    show densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
        g r s i α P₀ m (Fin.init l) y = 0
    rw [hy]; ring
  -- Layer D is ae-zero on the diff.
  have hD_term_ae : (fun y =>
      densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y * fChartEffPrev y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [h_prev_zero] with y hy
    show densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      fChartEffPrev y = 0
    rw [hy]; ring
  -- Layer E is ae-zero on the diff.
  have hE_term_ae : (fun y =>
      densityOnEuclid (I := I) g α y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
          fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hE_ae] with y hy
    show densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y = 0
    rw [hy]; ring
  -- Combine: the numerator is `A + B - C + D + E`, each ae-zero on the diff.
  filter_upwards [hA_sum_ae, hB_sum_ae, hC_term_ae, hD_term_ae, hE_term_ae]
    with y hA hB hC hD hE
  show eigenvectorChartRHSDiffNumerator_unconditional (I := I) (M := M)
      g r s i α P₀ m l fChartEffPrev y = 0
  unfold eigenvectorChartRHSDiffNumerator_unconditional
  rw [hA, hB, hC, hD, hE]; ring

/-- Chart-locality-free twin of
`eigenvectorChartRHSDiffNumerator_memWkp_of_iter`. -/
lemma eigenvectorChartRHSDiffNumerator_memWkp_of_iter_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_iter : ∀ (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev : MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartRHSDiffNumerator_unconditional (I := I) (M := M)
        g r s i α P₀ m l fChartEffPrev)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  -- Layer A: `∑_{a,b} (∂_b weightedInvGram) · ((m+1)-fold mixed partial)`.
  have hA : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                (l (Fin.last m))) y)
              (EuclideanSpace.single b 1) *
            eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_pair : ∀ a b : Fin (Module.finrank ℝ E),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y =>
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                  (l (Fin.last m))) y)
                (EuclideanSpace.single b 1) *
              eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
          (chartTargetEuclid (I := I) (M := M) α) := by
      intro a b
      have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) :=
        (h_iter (m + 1) (Fin.cons a (Fin.init l))).le_of_le (by omega)
      have h_factor_ae_zero :=
        eigenvectorChartIteratedPartial_unconditional_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ (m + 1)
          (Fin.cons a (Fin.init l))
      exact (wkpNorm_coef_mul_factor_le (I := I) (M := M) α K
        (layerA_coeff_contDiffOn_chartTargetEuclid (I := I) (M := M)
          g α (l (Fin.last m)) a b) h_factor_memWkp h_factor_ae_zero).1
    have h_inner : ∀ a : Fin (Module.finrank ℝ E),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => ∑ b : Fin (Module.finrank ℝ E),
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                  (l (Fin.last m))) y)
                (EuclideanSpace.single b 1) *
              eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
          (chartTargetEuclid (I := I) (M := M) α) := fun a =>
      memWkp_finset_sum (I := I) (M := M) (α := α) (K := K) Finset.univ
        (fun b _hb => h_pair a b)
    exact memWkp_finset_sum (I := I) (M := M) (α := α) (K := K) Finset.univ
      (fun a _ha => h_inner a)
  -- Layer B: `∑_{a,b} weightedInvGram · (∂_b-weak-partial of the (m+1)-fold partial)`.
  have hB : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
              (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
              (chartTargetEuclid (I := I) (M := M) α) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_pair : ∀ a b : Fin (Module.finrank ℝ E),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y =>
            weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α) y)
          (chartTargetEuclid (I := I) (M := M) α) := by
      intro a b
      -- The level-`(m+1)` mixed partial lies in `MemWkp (K + 1) 2`.
      have h_inner_memWkp_succ : MemWkp (d := Module.finrank ℝ E) (K + 1) 2
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) :=
        (h_iter (m + 1) (Fin.cons a (Fin.init l))).le_of_le (by omega)
      -- The chosen weak `b`-partial of it is `MemWkp K 2`.
      have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α))
          (chartTargetEuclid (I := I) (M := M) α) :=
        h_inner_memWkp_succ.chosenWeakPartial_mem b
      -- The chosen weak `b`-partial ae-vanishes off the kernel.
      have h_inner_ae :=
        eigenvectorChartIteratedPartial_unconditional_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ (m + 1)
          (Fin.cons a (Fin.init l))
      have h_factor_ae_zero :=
        chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
          (I := I) (M := M) α h_inner_ae b
      exact (wkpNorm_coef_mul_factor_le (I := I) (M := M) α K
        (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b
          (l (Fin.last m))) h_factor_memWkp h_factor_ae_zero).1
    have h_inner : ∀ a : Fin (Module.finrank ℝ E),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => ∑ b : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α) y)
          (chartTargetEuclid (I := I) (M := M) α) := fun a =>
      memWkp_finset_sum (I := I) (M := M) (α := α) (K := K) Finset.univ
        (fun b _hb => h_pair a b)
    exact memWkp_finset_sum (I := I) (M := M) (α := α) (K := K) Finset.univ
      (fun a _ha => h_inner a)
  -- Layer C: `(∂_{lₙ} densityDeriv) · (m-fold mixed partial in `Fin.init l`)`.
  have hC : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
          eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ m (Fin.init l) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ m (Fin.init l))
        (chartTargetEuclid (I := I) (M := M) α) :=
      (h_iter m (Fin.init l)).le_of_le (by omega)
    have h_factor_ae_zero :=
      eigenvectorChartIteratedPartial_unconditional_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ m (Fin.init l)
    exact (wkpNorm_coef_mul_factor_le (I := I) (M := M) α K
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
      h_factor_memWkp h_factor_ae_zero).1
  -- Layer D: `(∂_{lₙ} densityDeriv) · fChartEffPrev`.
  have hD : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y * fChartEffPrev y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (wkpNorm_coef_mul_factor_le (I := I) (M := M) α K
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
      (h_prev.le_of_le (by omega)) h_prev_zero).1
  -- Layer E: `densityOnEuclid · (∂_{lₙ}-weak-partial of fChartEffPrev)`.
  have hE : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        densityOnEuclid (I := I) g α y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
            fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
          fChartEffPrev (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
      h_prev.chosenWeakPartial_mem (l (Fin.last m))
    have h_factor_ae_zero :=
      chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
        (I := I) (M := M) α h_prev_zero (l (Fin.last m))
    exact (wkpNorm_coef_mul_factor_le (I := I) (M := M) α K
      (densityOnEuclid_contDiffOn (I := I) g α)
      h_factor_memWkp h_factor_ae_zero).1
  -- Combine the five layers: numerator = A + B - C + D + E.
  have h_step1 := MemWkp.add (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open hA hB
  have h_step2 := MemWkp.sub (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open h_step1 hC
  have h_step3 := MemWkp.add (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open h_step2 hD
  have h_step4 := MemWkp.add (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open h_step3 hE
  -- The assembled sum is definitionally the numerator.
  have h_eq : (fun y =>
      ((((∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                (l (Fin.last m))) y)
              (EuclideanSpace.single b 1) *
            eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y) +
        (∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α) y)) -
        densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
          eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ m (Fin.init l) y) +
        densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
          fChartEffPrev y) +
        densityOnEuclid (I := I) g α y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
            fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y) =
      eigenvectorChartRHSDiffNumerator_unconditional (I := I) (M := M)
        g r s i α P₀ m l fChartEffPrev := by
    funext y
    rfl
  rw [← h_eq]
  exact h_step4

/-! ## Chart-locality-free `wkpNorm` bound for the chart-density-divided numerator -/

section DivDensityBoundUnconditional

/-- Chart-locality-free twin of
`eigenvectorChartRHSDiffNumerator_div_density_wkpNorm_le`. -/
theorem eigenvectorChartRHSDiffNumerator_div_density_wkpNorm_le_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (h_iter : ∀ (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev : MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y =>
            eigenvectorChartRHSDiffNumerator_unconditional (I := I) (M := M)
              g r s i α P₀ m l fChartEffPrev y /
            densityOnEuclid (I := I) g α y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregateK_unconditional (I := I) (M := M)
            g r s i α P₀ m K l fChartEffPrev := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set A := diffNumeratorAggregateK_unconditional (I := I) (M := M)
    g r s i α P₀ m K l fChartEffPrev with hA_def
  set numFun : EuclN → ℝ := eigenvectorChartRHSDiffNumerator_unconditional
    (I := I) (M := M) g r s i α P₀ m l fChartEffPrev with hnumFun_def
  -- Rewrite the quotient as `(1 / density) · numerator`.
  have h_eq : (fun y => numFun y / densityOnEuclid (I := I) g α y) =
      (fun y => (1 / densityOnEuclid (I := I) g α y) * numFun y) := by
    funext y
    rw [one_div, mul_comm, ← div_eq_mul_inv]
  rw [h_eq]
  -- The numerator's order-`K` `wkpNorm` is bounded by `ofReal C₁ * A`.
  obtain ⟨C₁, hC₁_nn, hC₁⟩ := eigenvectorChartRHSDiffNumerator_wkpNorm_le_unconditional
    (I := I) (M := M) g r s i α P₀ m K l fChartEffPrev
    h_iter h_prev h_prev_zero
  rw [← hΩ_def, ← hA_def, ← hnumFun_def] at hC₁
  -- The numerator is `MemWkp K 2` on the chart target — re-derived from `h_iter`.
  have h_num_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 numFun Ω := by
    rw [hnumFun_def, ← hΩ_def] at *
    exact eigenvectorChartRHSDiffNumerator_memWkp_of_iter_unconditional
      (I := I) (M := M) g r s i α P₀ m K l
      h_iter h_prev h_prev_zero
  -- The numerator ae-vanishes off the partition-of-unity kernel.
  have h_num_ae_zero :
      numFun =ᵐ[(volume : Measure EuclN).restrict
        (Ω \ chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
    rw [hnumFun_def, hΩ_def]
    exact eigenvectorChartRHSDiffNumerator_ae_zero_off_chartPouKernel_unconditional
      (I := I) (M := M) g r s i α P₀ m l h_prev_zero
  -- The reciprocal density times the numerator: smooth-coefficient `wkpNorm` bound.
  obtain ⟨_h_prod_mem, C₂, hC₂_nn, hC₂⟩ := wkpNorm_coef_mul_factor_le
    (I := I) (M := M) α K
    (one_div_densityOnEuclid_contDiffOn_chartTargetEuclid (I := I) (M := M) g α)
    h_num_memWkp h_num_ae_zero
  rw [← hΩ_def] at hC₂
  -- Chain: `wkpNorm ((1/density) · num) ≤ ofReal C₂ · wkpNorm num`
  --        `≤ ofReal C₂ · (ofReal C₁ · A) = ofReal (C₂ * C₁) · A`.
  refine ⟨C₂ * C₁, mul_nonneg hC₂_nn hC₁_nn, ?_⟩
  calc
    wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => (1 / densityOnEuclid (I := I) g α y) * numFun y) Ω
        ≤ ENNReal.ofReal C₂ * wkpNorm (d := Module.finrank ℝ E) K 2 numFun Ω :=
          hC₂
    _ ≤ ENNReal.ofReal C₂ * (ENNReal.ofReal C₁ * A) := by
          gcongr
    _ = ENNReal.ofReal (C₂ * C₁) * A := by
          rw [ENNReal.ofReal_mul hC₂_nn, mul_assoc]

/-- Chart-locality-free twin of
`eigenvectorChartRHSDiffNumerator_div_density_wkpNorm_le_uniform`. -/
theorem eigenvectorChartRHSDiffNumerator_div_density_wkpNorm_le_uniform_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_iter : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      (fChartEffPrev i) =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y =>
              eigenvectorChartRHSDiffNumerator_unconditional (I := I) (M := M)
                g r s i α P₀ m l (fChartEffPrev i) y /
              densityOnEuclid (I := I) g α y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK_unconditional (I := I) (M := M)
              g r s i α P₀ m K l (fChartEffPrev i) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  -- The numerator's order-`K` `wkpNorm` bound — `i`-uniform constant `C₁`.
  obtain ⟨C₁, hC₁_nn, hC₁⟩ :=
    eigenvectorChartRHSDiffNumerator_wkpNorm_le_uniform_unconditional
      (I := I) (M := M) g r s α P₀ m K l fChartEffPrev
      h_iter h_prev h_prev_zero
  -- The reciprocal-density smooth-coefficient bound — factor-uniform constant `C₂`.
  obtain ⟨C₂, hC₂_nn, hC₂⟩ := wkpNorm_coef_mul_factor_le_uniform
    (I := I) (M := M) α K
    (one_div_densityOnEuclid_contDiffOn_chartTargetEuclid (I := I) (M := M) g α)
  -- The headline constant: the product of the two geometric constants.
  refine ⟨C₂ * C₁, mul_nonneg hC₂_nn hC₁_nn, fun i => ?_⟩
  set A := diffNumeratorAggregateK_unconditional (I := I) (M := M)
    g r s i α P₀ m K l (fChartEffPrev i) with hA_def
  set numFun : EuclN → ℝ := eigenvectorChartRHSDiffNumerator_unconditional
    (I := I) (M := M) g r s i α P₀ m l (fChartEffPrev i) with hnumFun_def
  -- Rewrite the quotient as `(1 / density) · numerator`.
  have h_eq : (fun y => numFun y / densityOnEuclid (I := I) g α y) =
      (fun y => (1 / densityOnEuclid (I := I) g α y) * numFun y) := by
    funext y
    rw [one_div, mul_comm, ← div_eq_mul_inv]
  rw [h_eq]
  -- The numerator's order-`K` `wkpNorm` bound for this `i`.
  have hC₁_i : wkpNorm (d := Module.finrank ℝ E) K 2 numFun Ω
      ≤ ENNReal.ofReal C₁ * A := by
    have := hC₁ i
    rw [← hnumFun_def, ← hΩ_def, ← hA_def] at this
    exact this
  -- The numerator is `MemWkp K 2` on the chart target — re-derived from `h_iter i`.
  have h_num_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 numFun Ω := by
    rw [hnumFun_def, hΩ_def]
    exact eigenvectorChartRHSDiffNumerator_memWkp_of_iter_unconditional
      (I := I) (M := M) g r s i α P₀ m K l
      (h_iter i) (h_prev i) (h_prev_zero i)
  -- The numerator ae-vanishes off the partition-of-unity kernel.
  have h_num_ae_zero :
      numFun =ᵐ[(volume : Measure EuclN).restrict
        (Ω \ chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
    rw [hnumFun_def, hΩ_def]
    exact eigenvectorChartRHSDiffNumerator_ae_zero_off_chartPouKernel_unconditional
      (I := I) (M := M) g r s i α P₀ m l (h_prev_zero i)
  -- The factor-uniform smooth-coefficient bound, instantiated at `numFun`.
  have hC₂_i := (hC₂ numFun h_num_memWkp h_num_ae_zero).2
  rw [← hΩ_def] at hC₂_i
  -- Chain: `wkpNorm ((1/density) · num) ≤ ofReal C₂ · wkpNorm num`
  --        `≤ ofReal C₂ · (ofReal C₁ · A) = ofReal (C₂ * C₁) · A`.
  calc
    wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => (1 / densityOnEuclid (I := I) g α y) * numFun y) Ω
        ≤ ENNReal.ofReal C₂ * wkpNorm (d := Module.finrank ℝ E) K 2 numFun Ω :=
          hC₂_i
    _ ≤ ENNReal.ofReal C₂ * (ENNReal.ofReal C₁ * A) := by
          gcongr
    _ = ENNReal.ofReal (C₂ * C₁) * A := by
          rw [ENNReal.ofReal_mul hC₂_nn, mul_assoc]

end DivDensityBoundUnconditional

/-! ## Chart-locality-free `wkpNorm` bound for the standalone inductive step -/

section IteratedStepBoundUnconditional

/-- Chart-locality-free twin of `eigenvectorChartIteratedStep_wkpNorm_le`. -/
theorem eigenvectorChartIteratedStep_wkpNorm_le_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (l : Fin (Module.finrank ℝ E))
    (h_iter : ∀ (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev : MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartIteratedStep_unconditional (I := I) (M := M)
            g r s i α P₀ m dirs fChartEffPrev l)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregateK_unconditional (I := I) (M := M)
            g r s i α P₀ m K (Fin.snoc dirs l) fChartEffPrev := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  -- `eigenvectorChartIteratedStep_unconditional = indicator (chartPouKernel α) Q`,
  -- where `Q = eigenvectorChartRHSDiffNumerator_unconditional … (Fin.snoc dirs l)
  -- / density`.
  set Q : EuclN → ℝ := fun y =>
    eigenvectorChartRHSDiffNumerator_unconditional (I := I) (M := M)
      g r s i α P₀ m (Fin.snoc dirs l) fChartEffPrev y /
    densityOnEuclid (I := I) g α y with hQ_def
  -- The standalone step is the indicator of the kernel applied to `Q`.
  have h_step_eq :
      eigenvectorChartIteratedStep_unconditional (I := I) (M := M)
        g r s i α P₀ m dirs fChartEffPrev l =
      Set.indicator (chartPouKernel (I := I) (M := M) α) Q := by
    unfold eigenvectorChartIteratedStep_unconditional
    have h_num := eigenvectorChartIteratedStepNumerator_unconditional_eq_rhsDiffNumerator
      (I := I) (M := M) g r s i α P₀ m dirs fChartEffPrev l
    funext y
    simp only [hQ_def]
    rw [h_num]
  -- `Q` ae-vanishes off the partition-of-unity kernel — the public restatement.
  have hQ_ae_zero : Q =ᵐ[(volume : Measure EuclN).restrict
      (Ω \ chartPouKernel (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
    rw [hQ_def, hΩ_def]
    exact eigenvectorChartRHSDiffNumerator_unconditional_div_density_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P₀ m (Fin.snoc dirs l) h_prev_zero
  -- `indicator (chartPouKernel α) Q =ᵐ Q` on the open chart target.
  -- Split `Ω = (Ω ∩ chartPouKernel α) ∪ (Ω \ chartPouKernel α)`:
  --  on the kernel intersection, the indicator returns `Q`;
  --  off the kernel, the indicator vanishes and `Q =ᵐ 0`.
  have h_indicator_ae_eq_Q :
      Set.indicator (chartPouKernel (I := I) (M := M) α) Q =ᵐ[
        (volume : Measure EuclN).restrict Ω] Q := by
    set Kα : Set EuclN := chartPouKernel (I := I) (M := M) α with hKα_def
    have hΩ_meas : MeasurableSet Ω :=
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
    have hKα_meas : MeasurableSet Kα :=
      chartPouKernel_measurableSet (I := I) (M := M) α
    -- On `Ω ∩ Kα`: `indicator Kα Q = Q`.
    have h_inter_meas : MeasurableSet (Ω ∩ Kα) := hΩ_meas.inter hKα_meas
    have h_eq_on_inter : Set.indicator Kα Q =ᵐ[
        (volume : Measure EuclN).restrict (Ω ∩ Kα)] Q := by
      refine (ae_restrict_iff' h_inter_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      exact Set.indicator_of_mem hy.2 _
    -- On `Ω \ Kα`: `indicator Kα Q = 0` and `Q =ᵐ 0`.
    have h_diff_meas : MeasurableSet (Ω \ Kα) := hΩ_meas.diff hKα_meas
    have h_indicator_ae_zero : Set.indicator Kα Q =ᵐ[
        (volume : Measure EuclN).restrict (Ω \ Kα)]
        (fun _ : EuclN => (0 : ℝ)) := by
      refine (ae_restrict_iff' h_diff_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      exact Set.indicator_of_notMem hy.2 _
    have h_eq_on_diff : Set.indicator Kα Q =ᵐ[
        (volume : Measure EuclN).restrict (Ω \ Kα)] Q := by
      filter_upwards [h_indicator_ae_zero, hQ_ae_zero] with y h0 hQ0
      rw [h0, hQ0]
    -- Cover `Ω` by the two disjoint pieces and recombine the ae-equalities.
    have h_cover : Ω = (Ω ∩ Kα) ∪ (Ω \ Kα) := by
      ext y; constructor
      · intro hy
        by_cases h : y ∈ Kα
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
      · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    have h_disj : Disjoint (Ω ∩ Kα) (Ω \ Kα) :=
      Set.disjoint_left.mpr fun y hy hy' => hy'.2 hy.2
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict ((Ω ∩ Kα) ∪ (Ω \ Kα)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, MeasureTheory.Measure.restrict_union h_disj h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  -- The order-`K` `wkpNorm` of the step equals that of `Q` via the ae-equality.
  have h_norm_eq : wkpNorm (d := Module.finrank ℝ E) K 2
      (eigenvectorChartIteratedStep_unconditional (I := I) (M := M)
        g r s i α P₀ m dirs fChartEffPrev l) Ω =
      wkpNorm (d := Module.finrank ℝ E) K 2 Q Ω := by
    rw [h_step_eq]
    exact wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_indicator_ae_eq_Q
  -- The density-divided bound for the snoc-extended differentiated numerator.
  obtain ⟨C, hC_nn, hC⟩ :=
    eigenvectorChartRHSDiffNumerator_div_density_wkpNorm_le_unconditional
      (I := I) (M := M) g r s i α P₀ m K (Fin.snoc dirs l) fChartEffPrev
      h_iter h_prev h_prev_zero
  refine ⟨C, hC_nn, ?_⟩
  rw [← hΩ_def] at hC
  rw [h_norm_eq, hQ_def]
  exact hC

/-- Chart-locality-free twin of `eigenvectorChartIteratedStep_wkpNorm_le_uniform`. -/
theorem eigenvectorChartIteratedStep_wkpNorm_le_uniform_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (l : Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_iter : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      (fChartEffPrev i) =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartIteratedStep_unconditional (I := I) (M := M)
              g r s i α P₀ m dirs (fChartEffPrev i) l)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK_unconditional (I := I) (M := M)
              g r s i α P₀ m K (Fin.snoc dirs l) (fChartEffPrev i) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  -- The density-divided bound for the snoc-extended numerator — `i`-uniform `C`.
  obtain ⟨C, hC_nn, hC⟩ :=
    eigenvectorChartRHSDiffNumerator_div_density_wkpNorm_le_uniform_unconditional
      (I := I) (M := M) g r s α P₀ m K (Fin.snoc dirs l) fChartEffPrev
      h_iter h_prev h_prev_zero
  refine ⟨C, hC_nn, fun i => ?_⟩
  -- `eigenvectorChartIteratedStep_unconditional = indicator (chartPouKernel α) Q`,
  -- where `Q = eigenvectorChartRHSDiffNumerator_unconditional … (Fin.snoc dirs l)
  -- / density`.
  set Q : EuclN → ℝ := fun y =>
    eigenvectorChartRHSDiffNumerator_unconditional (I := I) (M := M)
      g r s i α P₀ m (Fin.snoc dirs l) (fChartEffPrev i) y /
    densityOnEuclid (I := I) g α y with hQ_def
  -- The standalone step is the indicator of the kernel applied to `Q`.
  have h_step_eq :
      eigenvectorChartIteratedStep_unconditional (I := I) (M := M)
        g r s i α P₀ m dirs (fChartEffPrev i) l =
      Set.indicator (chartPouKernel (I := I) (M := M) α) Q := by
    unfold eigenvectorChartIteratedStep_unconditional
    have h_num := eigenvectorChartIteratedStepNumerator_unconditional_eq_rhsDiffNumerator
      (I := I) (M := M) g r s i α P₀ m dirs (fChartEffPrev i) l
    funext y
    simp only [hQ_def]
    rw [h_num]
  -- `Q` ae-vanishes off the partition-of-unity kernel — the public restatement.
  have hQ_ae_zero : Q =ᵐ[(volume : Measure EuclN).restrict
      (Ω \ chartPouKernel (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
    rw [hQ_def, hΩ_def]
    exact eigenvectorChartRHSDiffNumerator_unconditional_div_density_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P₀ m (Fin.snoc dirs l)
      (h_prev_zero i)
  -- `indicator (chartPouKernel α) Q =ᵐ Q` on the open chart target.
  -- Split `Ω = (Ω ∩ chartPouKernel α) ∪ (Ω \ chartPouKernel α)`:
  --  on the kernel intersection, the indicator returns `Q`;
  --  off the kernel, the indicator vanishes and `Q =ᵐ 0`.
  have h_indicator_ae_eq_Q :
      Set.indicator (chartPouKernel (I := I) (M := M) α) Q =ᵐ[
        (volume : Measure EuclN).restrict Ω] Q := by
    set Kα : Set EuclN := chartPouKernel (I := I) (M := M) α with hKα_def
    have hΩ_meas : MeasurableSet Ω :=
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
    have hKα_meas : MeasurableSet Kα :=
      chartPouKernel_measurableSet (I := I) (M := M) α
    -- On `Ω ∩ Kα`: `indicator Kα Q = Q`.
    have h_inter_meas : MeasurableSet (Ω ∩ Kα) := hΩ_meas.inter hKα_meas
    have h_eq_on_inter : Set.indicator Kα Q =ᵐ[
        (volume : Measure EuclN).restrict (Ω ∩ Kα)] Q := by
      refine (ae_restrict_iff' h_inter_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      exact Set.indicator_of_mem hy.2 _
    -- On `Ω \ Kα`: `indicator Kα Q = 0` and `Q =ᵐ 0`.
    have h_diff_meas : MeasurableSet (Ω \ Kα) := hΩ_meas.diff hKα_meas
    have h_indicator_ae_zero : Set.indicator Kα Q =ᵐ[
        (volume : Measure EuclN).restrict (Ω \ Kα)]
        (fun _ : EuclN => (0 : ℝ)) := by
      refine (ae_restrict_iff' h_diff_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      exact Set.indicator_of_notMem hy.2 _
    have h_eq_on_diff : Set.indicator Kα Q =ᵐ[
        (volume : Measure EuclN).restrict (Ω \ Kα)] Q := by
      filter_upwards [h_indicator_ae_zero, hQ_ae_zero] with y h0 hQ0
      rw [h0, hQ0]
    -- Cover `Ω` by the two disjoint pieces and recombine the ae-equalities.
    have h_cover : Ω = (Ω ∩ Kα) ∪ (Ω \ Kα) := by
      ext y; constructor
      · intro hy
        by_cases h : y ∈ Kα
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
      · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    have h_disj : Disjoint (Ω ∩ Kα) (Ω \ Kα) :=
      Set.disjoint_left.mpr fun y hy hy' => hy'.2 hy.2
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict ((Ω ∩ Kα) ∪ (Ω \ Kα)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, MeasureTheory.Measure.restrict_union h_disj h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  -- The order-`K` `wkpNorm` of the step equals that of `Q` via the ae-equality.
  have h_norm_eq : wkpNorm (d := Module.finrank ℝ E) K 2
      (eigenvectorChartIteratedStep_unconditional (I := I) (M := M)
        g r s i α P₀ m dirs (fChartEffPrev i) l) Ω =
      wkpNorm (d := Module.finrank ℝ E) K 2 Q Ω := by
    rw [h_step_eq]
    exact wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_indicator_ae_eq_Q
  -- The density-divided bound for this `i`, against the snoc-extended aggregate.
  have hC_i := hC i
  rw [← hΩ_def] at hC_i
  rw [h_norm_eq, hQ_def]
  exact hC_i

end IteratedStepBoundUnconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
