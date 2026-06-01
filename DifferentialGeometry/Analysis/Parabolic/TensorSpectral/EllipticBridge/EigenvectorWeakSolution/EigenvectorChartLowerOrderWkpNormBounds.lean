import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHSMemWkp
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartLowerOrderLimits
import DifferentialGeometry.Analysis.Sobolev.Euclidean.MultiplyQuantK
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevQuant

/-!
# Order-`K` iterated-Sobolev norm bounds for three eigenvector chart limit objects

The chart-Euclidean right-hand side of the connection-Laplacian eigenvector's
weak-solution assembly is built from `C^∞`-coefficient-weighted lower-order limit
objects. Three of them are finite sums of `chartPouKernel α`-indicator-cut `C^∞`
coefficients against the chart-component / chart-partial atoms `componentLpLimit`
and `partialLpLimit`:

* `covPrincipalRotationCoeffLimit g r s i α P₀` — a four-fold sum
  over `(P, Q, k, l)` of the kernel-cut `C^∞` factor `principalRotationFactor`
  against the chart-partial atom `partialLpLimit P k`;
* `covLowerOrderRotationValueCoeffLimit g r s i α P₀` — a four-fold
  sum over `(P, Q, k, l)` of the kernel-cut `C^∞` factor `valuePartialFactor`
  against `partialLpLimit P k`, plus a five-fold sum over
  `(P, Q, k, l, p)` of the kernel-cut `C^∞` factor `valueComponentFactor` against
  `componentLpLimit p`;
* `weightedGradCoeffDivLimit g r s i α P₀ l` — a four-fold sum over
  `(P, Q, k, p)` of the kernel-cut chart-Euclidean partial of the `C^∞` factor
  `weightedGradFactor` against `componentLpLimit p`, plus a
  four-fold sum over `(P, Q, k, p)` of the kernel-cut `weightedGradFactor` against
  `partialLpLimit p l`.

The order-`0` companions `eLpNorm_covPrincipalRotationCoeffLimit_le`,
`eLpNorm_covLowerOrderRotationValueCoeffLimit_le` and
`eLpNorm_weightedGradCoeffDivLimit_le` bound the `eLpNorm` — i.e. the `wkpNorm` at
Sobolev order `0` — of each limit object, against a chart-pulled weighted measure,
by a nonnegative constant times a finite sum of the source atoms' `eLpNorm`. This
file records their order-`K` generalisations: for an arbitrary order `K` there is
a nonnegative constant `C` with

```
wkpNorm K 2 (<limit object> …) (chartTargetEuclid α)
  ≤ ENNReal.ofReal C * <AGGREGATE_K>,
```

where `<AGGREGATE_K>` is the order-`K` analogue of the order-`0` `eLpNorm` atom
sum: the finite sum of the order-`K` `wkpNorm` of the chart-component /
chart-partial atoms `componentLpLimit` / `partialLpLimit` on the open Euclidean
chart target.

## Strategy

Each limit object is a finite (double / quadruple) sum whose summands carry an
`indicator (chartPouKernel α)` cut of a `C^∞`-on-the-chart-target coefficient,
times an atom (`componentLpLimit` or `partialLpLimit`). The atoms are `W^{K,2}`
on the chart target, given the order-`(K + 1)` partition-of-unity regularity
input `h_pou`: the component atom is `μ` times the canonical eigenvector chart
component, which is `W^{K,2}` by the Summand-1 route; the partial atom is `μ`
times the eigenvector weak chart partial, which is `W^{K,2}` because the chart
component is `W^{K+1,2}` and a weak partial of a `W^{K+1,2}` function is
`W^{K,2}`. The atoms also vanish almost everywhere off the compact
partition-of-unity kernel, so the indicator cut is absorbed: the indicator-cut
summand agrees almost everywhere with the bare `C^∞`-coefficient product, whose
order-`K` `wkpNorm` is controlled — through a smooth-coefficient cutoff and the
global-smoothness Leibniz bound `wkpNorm_smul_smooth_bounded_le` — by an explicit
constant times the order-`K` `wkpNorm` of the atom. The triangle inequality
`wkpNorm_sum_le` over the nested finite sums assembles the per-summand bounds;
every summation multiplicity and every per-coefficient constant folds into a
single nonnegative `C`.

## Main results

* `wkpNorm_covPrincipalRotationCoeffLimit_le_unconditional`
* `wkpNorm_covLowerOrderRotationValueCoeffLimit_le_unconditional`
* `wkpNorm_weightedGradCoeffDivLimit_le_unconditional`
* `wkpNorm_covPrincipalRotationCoeffLimit_le_uniform_unconditional`
* `wkpNorm_covLowerOrderRotationValueCoeffLimit_le_uniform_unconditional`
* `wkpNorm_weightedGradCoeffDivLimit_le_uniform_unconditional`

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology
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
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section LowerOrderWkpNormBounds

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

private lemma wkpNorm_coef_mul_factor_le
    (α : M) (K : ℕ)
    {coef factor : EuclN → ℝ}
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α))
    (hfactor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 factor
      (chartTargetEuclid (I := I) (M := M) α))
    (hfactor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α → factor y = 0) :
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
  obtain ⟨δ, χ, hδ_pos, hδ_in, hχ_smooth, hχ_cs, _hχ_range, hχ_one, hχ_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      hKα_compact hΩ_open hKα_in
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
  obtain ⟨C₀, hC₀_nn, hC₀_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hχ_coef_smooth hχ_coef_cs K
  have h_prod_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (χ y * coef y) * factor y) Ω :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hχ_coef_smooth
      (fun j _hj y _hy => hC₀_bd y j _hj) hfactor_memWkp
  obtain ⟨Kc, hKc_pos, hKc_bd⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hΩ_open hχ_coef_smooth
      hC₀_nn (fun j _hj y _hy => hC₀_bd y j _hj)
  set Cδ : Set EuclN := Metric.cthickening δ Kα with hCδ_def
  have hCδ_closed : IsClosed Cδ := Metric.isClosed_cthickening
  have hCδ_meas : MeasurableSet Cδ := hCδ_closed.measurableSet
  have hfactor_ae_zero' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ Kα → factor y = 0 := by
    have h := hfactor_ae_zero
    rw [chartL2Measure] at h
    exact h
  have h_ae_eq : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => coef y * factor y) := by
    have h_eq_on_inter : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict (Ω ∩ Cδ)]
        (fun y => coef y * factor y) := by
      refine (ae_restrict_iff' (hΩ_meas.inter hCδ_meas)).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      have hχy : χ y = 1 := hχ_one y hy.2
      change (χ y * coef y) * factor y = coef y * factor y
      rw [hχy]; ring
    have hKα_in_Cδ : Kα ⊆ Cδ := Metric.self_subset_cthickening _
    have h_eq_on_diff : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict (Ω \ Cδ)]
        (fun y => coef y * factor y) := by
      have h_diff_in_Ω : (volume : Measure EuclN).restrict (Ω \ Cδ) ≤
          (volume : Measure EuclN).restrict Ω :=
        Measure.restrict_mono Set.diff_subset le_rfl
      have h_factor_diff : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
          factor y = 0 := by
        have h_lift : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
            y ∉ Kα → factor y = 0 :=
          (Measure.absolutelyContinuous_of_le h_diff_in_Ω).ae_le hfactor_ae_zero'
        have h_off : ∀ᵐ _y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
            _y ∈ Ω \ Cδ := ae_restrict_mem (hΩ_meas.diff hCδ_meas)
        filter_upwards [h_lift, h_off] with y hy hy_mem
        exact hy (fun hyK => hy_mem.2 (hKα_in_Cδ hyK))
      filter_upwards [h_factor_diff] with y hy
      show (χ y * coef y) * factor y = coef y * factor y
      rw [hy]; ring
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
    rw [hΩ_restrict_eq, Measure.restrict_union h_disj h_diff_meas]
    exact (ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  have h_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω :=
    (MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).mp h_prod_memWkp
  refine ⟨h_memWkp, Kc, le_of_lt hKc_pos, ?_⟩
  have h_norm_eq : wkpNorm (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω =
      wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => (χ y * coef y) * factor y) Ω :=
    (wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).symm
  rw [h_norm_eq]
  exact hKc_bd hfactor_memWkp

private lemma wkpNorm_indicatorFactor_mul_atom_le
    (α : M) (K : ℕ) {coef G : EuclN → ℝ}
    (hcoef : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α))
    (hG_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 G
      (chartTargetEuclid (I := I) (M := M) α))
    (hG_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α → G y = 0) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) coef y * G y)
        (chartTargetEuclid (I := I) (M := M) α) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) coef y *
              G y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            wkpNorm (d := Module.finrank ℝ E) K 2 G
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨h_mul_memWkp, C, hC_nn, hC_bd⟩ :=
    wkpNorm_coef_mul_factor_le (I := I) (M := M) α K hcoef hG_memWkp hG_zero
  have hG_zero' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ chartPouKernel (I := I) (M := M) α → G y = 0 := by
    have h := hG_zero
    rw [chartL2Measure] at h
    exact h
  have h_prod_eq : (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
        coef y * G y)
      =ᵐ[(volume : Measure EuclN).restrict Ω] (fun y => coef y * G y) := by
    filter_upwards [hG_zero'] with y hy
    by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, zero_mul, hy hyK, mul_zero]
  refine ⟨(MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_prod_eq).mpr h_mul_memWkp,
    C, hC_nn, ?_⟩
  rw [wkpNorm_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_prod_eq]
  exact hC_bd

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma memWkp_finsetSum
    {α : M} {K : ℕ} {ι : Type*} (T : Finset ι)
    {F : ι → EuclN → ℝ}
    (hF : ∀ j ∈ T, MemWkp (d := Module.finrank ℝ E) K 2 (F j)
      (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ j ∈ T, F j y) (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  induction T using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact MemWkp_zero_fun (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open
  | insert j T hj ih =>
      have hj_mem : MemWkp (d := Module.finrank ℝ E) K 2 (F j)
          (chartTargetEuclid (I := I) (M := M) α) :=
        hF j (Finset.mem_insert_self _ _)
      have hsum := ih (fun j' hj' => hF j' (Finset.mem_insert_of_mem hj'))
      have h_eq : (fun y => ∑ j' ∈ insert j T, F j' y) =
          (fun y => F j y + ∑ j' ∈ T, F j' y) := by
        funext y; rw [Finset.sum_insert hj]
      rw [h_eq]
      exact MemWkp.add (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open hj_mem hsum

omit [CompleteSpace E] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [SigmaCompactSpace M] in
/-- A finite indexed family of `MemWkp K 2` summands, each `wkpNorm`-bounded by
`ENNReal.ofReal C` times the order-`K` `wkpNorm` of an atom selected by a
projection `proj`, has its summed `wkpNorm` bounded by `ENNReal.ofReal` of an
explicit constant times the sum, over the distinct atoms, of the atoms'
order-`K` `wkpNorm`. -/
private lemma wkpNorm_finsetSum_le_const_mul_atomSum
    {α : M} {K : ℕ} {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (F : ι → EuclN → ℝ) (atom : κ → EuclN → ℝ)
    (proj : ι → κ) (hproj : ∀ j ∈ S, proj j ∈ T)
    (C : ℝ) (_hC_nn : 0 ≤ C)
    (hF : ∀ j ∈ S, MemWkp (d := Module.finrank ℝ E) K 2 (F j)
      (chartTargetEuclid (I := I) (M := M) α))
    (h_bd : ∀ j ∈ S,
      wkpNorm (d := Module.finrank ℝ E) K 2 (F j)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          wkpNorm (d := Module.finrank ℝ E) K 2 (atom (proj j))
            (chartTargetEuclid (I := I) (M := M) α)) :
    wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ j ∈ S, F j y) (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal (C * S.card)
        * ∑ p ∈ T, wkpNorm (d := Module.finrank ℝ E) K 2 (atom p)
            (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_tri := wkpNorm_sum_le (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open S F hF
  have h_step : ∑ j ∈ S, wkpNorm (d := Module.finrank ℝ E) K 2 (F j)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ∑ _j ∈ S, ENNReal.ofReal C
        * ∑ p ∈ T, wkpNorm (d := Module.finrank ℝ E) K 2 (atom p)
            (chartTargetEuclid (I := I) (M := M) α) := by
    refine Finset.sum_le_sum (fun j hj => ?_)
    refine (h_bd j hj).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
    exact Finset.single_le_sum
      (f := fun p => wkpNorm (d := Module.finrank ℝ E) K 2 (atom p)
        (chartTargetEuclid (I := I) (M := M) α))
      (fun p _ => zero_le _) (hproj j hj)
  have h_const : ∑ _j ∈ S, ENNReal.ofReal C
        * ∑ p ∈ T, wkpNorm (d := Module.finrank ℝ E) K 2 (atom p)
            (chartTargetEuclid (I := I) (M := M) α)
      = (S.card : ℝ≥0∞) * (ENNReal.ofReal C
        * ∑ p ∈ T, wkpNorm (d := Module.finrank ℝ E) K 2 (atom p)
            (chartTargetEuclid (I := I) (M := M) α)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h_cast : (S.card : ℝ≥0∞) * ENNReal.ofReal C
      = ENNReal.ofReal (C * S.card) := by
    rw [mul_comm C, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  calc
    wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ j ∈ S, F j y) (chartTargetEuclid (I := I) (M := M) α)
        ≤ ∑ j ∈ S, wkpNorm (d := Module.finrank ℝ E) K 2 (F j)
            (chartTargetEuclid (I := I) (M := M) α) := h_tri
    _ ≤ ∑ _j ∈ S, ENNReal.ofReal C
          * ∑ p ∈ T, wkpNorm (d := Module.finrank ℝ E) K 2 (atom p)
              (chartTargetEuclid (I := I) (M := M) α) := h_step
    _ = (S.card : ℝ≥0∞) * (ENNReal.ofReal C
          * ∑ p ∈ T, wkpNorm (d := Module.finrank ℝ E) K 2 (atom p)
              (chartTargetEuclid (I := I) (M := M) α)) := h_const
    _ = ((S.card : ℝ≥0∞) * ENNReal.ofReal C)
          * ∑ p ∈ T, wkpNorm (d := Module.finrank ℝ E) K 2 (atom p)
              (chartTargetEuclid (I := I) (M := M) α) := by rw [mul_assoc]
    _ = ENNReal.ofReal (C * S.card)
          * ∑ p ∈ T, wkpNorm (d := Module.finrank ℝ E) K 2 (atom p)
              (chartTargetEuclid (I := I) (M := M) α) := by rw [h_cast]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
/-- **A weak chart partial of a `W^{K+1,2}` function is `W^{K,2}`.** For an open
set `Ω`, a weak `k`-th partial `gpart` of a function `u` that is `W^{K+1,2}` on
`Ω`, with `gpart` itself `L²` on `Ω`, lies in `W^{K,2}` on `Ω`.

`u ∈ W^{K+1,2}` is in particular `W^{1,2}`, so `chosenWeakPartial' 2 k u Ω` is a
weak `k`-th partial of `u` and lies in `W^{K,2}` (`MemWkp.chosenWeakPartial_mem`).
Both `gpart` and `chosenWeakPartial' 2 k u Ω` are weak `k`-th partials of `u` and
locally integrable, so they agree almost everywhere; `MemWkp` is invariant under
almost-everywhere equality. -/
private lemma memWkp_of_weakPartial_of_memWkp_succ
    {K : ℕ} {Ω : Set EuclN} (hΩ : IsOpen Ω)
    (k : Fin (Module.finrank ℝ E))
    {gpart u : EuclN → ℝ}
    (hgpart_memLp : MemLp gpart 2 ((volume : Measure EuclN).restrict Ω))
    (hgpart_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      gpart u Ω)
    (hu : MemWkp (d := Module.finrank ℝ E) (K + 1) 2 u Ω) :
    MemWkp (d := Module.finrank ℝ E) K 2 gpart Ω := by
  classical
  have hu_w1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u Ω := hu.memW1p
  have h_chosen_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u Ω) u Ω :=
    chosenWeakPartial'_isWeakPartial_of_mem hu_w1p k
  have h_chosen_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u Ω) Ω :=
    hu.chosenWeakPartial_mem k
  have hgpart_loc : LocallyIntegrable gpart
      ((volume : Measure EuclN).restrict Ω) :=
    hgpart_memLp.locallyIntegrable (by norm_num)
  have h_chosen_loc : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u Ω)
      ((volume : Measure EuclN).restrict Ω) :=
    h_chosen_memWkp.memLp.locallyIntegrable (by norm_num)
  have h_ae : gpart =ᵐ[(volume : Measure EuclN).restrict Ω]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u Ω :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ hgpart_weak h_chosen_weak
      hgpart_loc h_chosen_loc
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ h_ae).mpr h_chosen_memWkp

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
/-- **A weak chart partial inherits the off-kernel vanishing of the
differentiated function.** For an open set `Ω`, a closed set `Kc`, a weak `k`-th
partial `gp` of a `W^{1,2}`-on-`Ω` function `u` that vanishes almost everywhere
off `Kc`, with `gp` itself `L²` on `Ω`, the weak partial `gp` vanishes almost
everywhere off `Kc`.

The open subset `V := Ω \ Kc` carries `u =ᵐ 0`. The chosen weak `k`-th partial
of `u` on `V` is therefore almost everywhere zero on `V`
(`chosenWeakPartial'_ae_zero_of_ae_zero`); it and the restriction of `gp` to `V`
are both weak `k`-th partials of `u` on `V`, so they agree almost everywhere on
`V`, whence `gp =ᵐ 0` on `V`. -/
private lemma hasWeakPartialDeriv_ae_zero_off_of_ae_zero_off
    {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    (k : Fin (Module.finrank ℝ E))
    {Kc : Set EuclN} (hKc_closed : IsClosed Kc)
    {gp u : EuclN → ℝ}
    (hgp_memLp : MemLp gp 2 ((volume : Measure EuclN).restrict Ω))
    (hgp_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      gp u Ω)
    (hu_w1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u Ω)
    (hu_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ Kc → u y = 0) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ Kc → gp y = 0 := by
  classical
  set V : Set EuclN := Ω \ Kc with hV_def
  have hV_open : IsOpen V := hΩ_open.sdiff hKc_closed
  have hV_sub : V ⊆ Ω := Set.diff_subset
  have hV_meas : MeasurableSet V := hV_open.measurableSet
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hu_zero_V : u =ᵐ[(volume : Measure EuclN).restrict V]
      (fun _ : EuclN => (0 : ℝ)) := by
    have h_lift : ∀ᵐ y ∂((volume : Measure EuclN).restrict V),
        y ∉ Kc → u y = 0 :=
      (Measure.absolutelyContinuous_of_le
        (Measure.restrict_mono hV_sub le_rfl)).ae_le hu_zero
    have h_mem : ∀ᵐ y ∂((volume : Measure EuclN).restrict V), y ∈ V :=
      ae_restrict_mem hV_meas
    filter_upwards [h_lift, h_mem] with y hy hy_mem
    exact hy hy_mem.2
  have hu_w1p_V : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u V :=
    MemW1p.mono_set hV_open hV_sub hu_w1p
  have h_chosen_zero : chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u V
      =ᵐ[(volume : Measure EuclN).restrict V] (fun _ : EuclN => (0 : ℝ)) :=
    chosenWeakPartial'_ae_zero_of_ae_zero (d := Module.finrank ℝ E)
      (by norm_num) hV_open hu_zero_V k
  have h_chosen_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u V) u V :=
    chosenWeakPartial'_isWeakPartial_of_mem hu_w1p_V k
  have hgp_weak_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      gp u V :=
    DeGiorgi.HasWeakPartialDeriv.restrict hV_open hV_sub hgp_weak
  have hgp_loc_V : LocallyIntegrable gp
      ((volume : Measure EuclN).restrict V) :=
    (hgp_memLp.mono_measure (Measure.restrict_mono hV_sub le_rfl)).locallyIntegrable
      (by norm_num)
  have h_chosen_loc_V : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u V)
      ((volume : Measure EuclN).restrict V) :=
    (chosenWeakPartial'_memLp_of_mem hu_w1p_V k).locallyIntegrable (by norm_num)
  have h_gp_eq : gp =ᵐ[(volume : Measure EuclN).restrict V]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u V :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hV_open hgp_weak_V h_chosen_weak
      hgp_loc_V h_chosen_loc_V
  have hgp_zero_V : gp =ᵐ[(volume : Measure EuclN).restrict V]
      (fun _ : EuclN => (0 : ℝ)) := h_gp_eq.trans h_chosen_zero
  have hgp_zero_V' : ∀ᵐ y ∂(volume : Measure EuclN),
      y ∈ V → gp y = 0 := by
    have h := (ae_restrict_iff' hV_meas).mp hgp_zero_V
    filter_upwards [h] with y hy hy_mem
    exact hy hy_mem
  refine (ae_restrict_iff' hΩ_meas).mpr ?_
  filter_upwards [hgp_zero_V'] with y hy hy_mem hy_notKc
  exact hy ⟨hy_mem, hy_notKc⟩

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- From a finite (`Fintype`-indexed) family of `wkpNorm` bounds — each summand
bounded by `ENNReal.ofReal Cⱼ` times the projected atom's `wkpNorm` — extract a
single nonnegative constant valid uniformly across the family. The uniform
constant is the sum of all the per-summand constants. -/
private lemma exists_uniform_const_of_finite_wkpNorm_bounds
    {α : M} {K : ℕ} {ι κ : Type*} [Finite ι]
    (F : ι → EuclN → ℝ) (atom : κ → EuclN → ℝ) (proj : ι → κ)
    (h_data : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2 (F j)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          wkpNorm (d := Module.finrank ℝ E) K 2 (atom (proj j))
            (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ι,
      wkpNorm (d := Module.finrank ℝ E) K 2 (F j)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          wkpNorm (d := Module.finrank ℝ E) K 2 (atom (proj j))
            (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  refine ⟨∑ j : ι, (h_data j).choose, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun j _ => (h_data j).choose_spec.1)
  · intro j
    refine (h_data j).choose_spec.2.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
    refine ENNReal.ofReal_le_ofReal ?_
    exact Finset.single_le_sum
      (f := fun j' => (h_data j').choose)
      (fun j' _ => (h_data j').choose_spec.1) (Finset.mem_univ j)

end LowerOrderWkpNormBounds

section LowerOrderWkpNormBoundsUniform

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

/-- **Eigenbasis-uniform smooth-coefficient `wkpNorm` bound.** Given a
coefficient smooth on the open Euclidean chart target, there is a *single*
nonnegative constant `C` such that for every factor in `MemWkp K 2` on the chart
target that vanishes almost everywhere off the compact partition-of-unity
kernel, the product `coef · factor` lies in `MemWkp K 2` and its order-`K`
Sobolev norm is bounded by `ENNReal.ofReal C` times the order-`K` norm of the
factor.

This is `wkpNorm_coef_mul_factor_le` with the factor moved into a `∀ factor`
quantifier inside the `∃ C`. The hoist is sound because the constant — the
Leibniz constant of the globally smooth compactly supported cutoff `χ · coef`,
produced by `wkpNorm_smul_smooth_bounded_le` from a uniform bound on the
iterated derivatives of `χ · coef` up to order `K` — is determined by `coef`,
`K` and `α` alone, independently of the factor. -/
private lemma wkpNorm_coef_mul_factor_le_uniform
    (α : M) (K : ℕ) {coef : EuclN → ℝ}
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {factor : EuclN → ℝ},
      MemWkp (d := Module.finrank ℝ E) K 2 factor
          (chartTargetEuclid (I := I) (M := M) α) →
      (∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∉ chartPouKernel (I := I) (M := M) α → factor y = 0) →
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
  obtain ⟨δ, χ, hδ_pos, hδ_in, hχ_smooth, hχ_cs, _hχ_range, hχ_one, hχ_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      hKα_compact hΩ_open hKα_in
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
  obtain ⟨C₀, hC₀_nn, hC₀_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hχ_coef_smooth hχ_coef_cs K
  obtain ⟨Kc, hKc_pos, hKc_bd⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hΩ_open hχ_coef_smooth
      hC₀_nn (fun j _hj y _hy => hC₀_bd y j _hj)
  refine ⟨Kc, le_of_lt hKc_pos, ?_⟩
  intro factor hfactor_memWkp hfactor_ae_zero
  have h_prod_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (χ y * coef y) * factor y) Ω :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hχ_coef_smooth
      (fun j _hj y _hy => hC₀_bd y j _hj) hfactor_memWkp
  set Cδ : Set EuclN := Metric.cthickening δ Kα with hCδ_def
  have hCδ_closed : IsClosed Cδ := Metric.isClosed_cthickening
  have hCδ_meas : MeasurableSet Cδ := hCδ_closed.measurableSet
  have hfactor_ae_zero' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ Kα → factor y = 0 := by
    have h := hfactor_ae_zero
    rw [chartL2Measure] at h
    exact h
  have h_ae_eq : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => coef y * factor y) := by
    have h_eq_on_inter : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict (Ω ∩ Cδ)]
        (fun y => coef y * factor y) := by
      refine (ae_restrict_iff' (hΩ_meas.inter hCδ_meas)).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      have hχy : χ y = 1 := hχ_one y hy.2
      change (χ y * coef y) * factor y = coef y * factor y
      rw [hχy]; ring
    have hKα_in_Cδ : Kα ⊆ Cδ := Metric.self_subset_cthickening _
    have h_eq_on_diff : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict (Ω \ Cδ)]
        (fun y => coef y * factor y) := by
      have h_diff_in_Ω : (volume : Measure EuclN).restrict (Ω \ Cδ) ≤
          (volume : Measure EuclN).restrict Ω :=
        Measure.restrict_mono Set.diff_subset le_rfl
      have h_factor_diff : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
          factor y = 0 := by
        have h_lift : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
            y ∉ Kα → factor y = 0 :=
          (Measure.absolutelyContinuous_of_le h_diff_in_Ω).ae_le hfactor_ae_zero'
        have h_off : ∀ᵐ _y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
            _y ∈ Ω \ Cδ := ae_restrict_mem (hΩ_meas.diff hCδ_meas)
        filter_upwards [h_lift, h_off] with y hy hy_mem
        exact hy (fun hyK => hy_mem.2 (hKα_in_Cδ hyK))
      filter_upwards [h_factor_diff] with y hy
      show (χ y * coef y) * factor y = coef y * factor y
      rw [hy]; ring
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
    rw [hΩ_restrict_eq, Measure.restrict_union h_disj h_diff_meas]
    exact (ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  have h_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω :=
    (MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).mp h_prod_memWkp
  refine ⟨h_memWkp, ?_⟩
  have h_norm_eq : wkpNorm (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω =
      wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => (χ y * coef y) * factor y) Ω :=
    (wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).symm
  rw [h_norm_eq]
  exact hKc_bd hfactor_memWkp

/-- **Eigenbasis-uniform per-summand explicit-norm `wkpNorm` bound.** Given a
coefficient smooth on the open Euclidean chart target, there is a *single*
nonnegative constant `C` such that for every atom `G` in `MemWkp K 2` on the
chart target that vanishes almost everywhere off the compact partition-of-unity
kernel, the `chartPouKernel α`-indicator cut of the coefficient times `G` lies
in `MemWkp K 2` and its order-`K` `wkpNorm` is bounded by `ENNReal.ofReal C`
times the order-`K` `wkpNorm` of `G`.

This is `wkpNorm_indicatorFactor_mul_atom_le` with the atom moved into a
`∀ G` quantifier inside the `∃ C`; the constant is the factor-independent one
delivered by `wkpNorm_coef_mul_factor_le_uniform`. Off the kernel the atom
ae-vanishes, so the indicator-cut coefficient agrees almost everywhere with the
uncut `C^∞` coefficient. -/
private lemma wkpNorm_indicatorFactor_mul_atom_le_uniform
    (α : M) (K : ℕ) {coef : EuclN → ℝ}
    (hcoef : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {G : EuclN → ℝ},
      MemWkp (d := Module.finrank ℝ E) K 2 G
          (chartTargetEuclid (I := I) (M := M) α) →
      (∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∉ chartPouKernel (I := I) (M := M) α → G y = 0) →
      MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) coef y *
            G y)
          (chartTargetEuclid (I := I) (M := M) α) ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) coef y *
              G y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            wkpNorm (d := Module.finrank ℝ E) K 2 G
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    wkpNorm_coef_mul_factor_le_uniform (I := I) (M := M) α K hcoef
  refine ⟨C, hC_nn, ?_⟩
  intro G hG_memWkp hG_zero
  obtain ⟨h_mul_memWkp, hC_bd'⟩ := hC_bd hG_memWkp hG_zero
  have hG_zero' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ chartPouKernel (I := I) (M := M) α → G y = 0 := by
    have h := hG_zero
    rw [chartL2Measure] at h
    exact h
  have h_prod_eq : (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
        coef y * G y)
      =ᵐ[(volume : Measure EuclN).restrict Ω] (fun y => coef y * G y) := by
    filter_upwards [hG_zero'] with y hy
    by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, zero_mul, hy hyK, mul_zero]
  refine ⟨(MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_prod_eq).mpr h_mul_memWkp, ?_⟩
  rw [wkpNorm_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_prod_eq]
  exact hC_bd'

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- **Eigenbasis-uniform finite-family `wkpNorm` constant collection.** Given a
finite (`Finite`-indexed) family of `wkpNorm` bounds, additionally indexed by an
eigenbasis index `δ`, with each summand bounded by `ENNReal.ofReal` of a
`δ`-independent per-summand constant `Cf j` times the projected atom's
`wkpNorm`, there is a *single* nonnegative constant `C` — hoisted before the
`∀ δ` — bounding every summand uniformly. -/
private lemma exists_uniform_const_of_finite_wkpNorm_bounds_uniform
    {α : M} {K : ℕ} {δ ι κ : Type*} [Finite ι]
    (F : δ → ι → EuclN → ℝ) (atom : δ → κ → EuclN → ℝ) (proj : ι → κ)
    (Cf : ι → ℝ) (hCf_nn : ∀ j : ι, 0 ≤ Cf j)
    (h_data : ∀ (d : δ), ∀ j : ι,
      wkpNorm (d := Module.finrank ℝ E) K 2 (F d j)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Cf j) *
          wkpNorm (d := Module.finrank ℝ E) K 2 (atom d (proj j))
            (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : δ), ∀ j : ι,
      wkpNorm (d := Module.finrank ℝ E) K 2 (F d j)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          wkpNorm (d := Module.finrank ℝ E) K 2 (atom d (proj j))
            (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  refine ⟨∑ j : ι, Cf j, Finset.sum_nonneg (fun j _ => hCf_nn j), ?_⟩
  intro d j
  refine (h_data d j).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
  refine ENNReal.ofReal_le_ofReal ?_
  exact Finset.single_le_sum
    (f := fun j' => Cf j') (fun j' _ => hCf_nn j') (Finset.mem_univ j)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `eigenvectorVec_pou_memWkp`: the partition-of-unity
Euclidean chart components of the canonical eigenbasis vector
`tensorResolventEigenbasisVec … i` are `MemWkp N 2` on every chart
target, given that those of the `L²`-coercion of the resolvent are `MemWkp N 2`.
The two chart components differ by the nonzero scalar `μ⁻¹`, and `MemWkp` is
scalar-invariant. -/
private lemma eigenvectorVec_pou_memWkp
    (i : TensorEigenIdx (I := I) (M := M) g r s) (N : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) N 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (Q : TensorCompIdx (E := E) r s) :
    MemWkp (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  have h_res : MemWkp (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    h_pou β Q
  have h_chart_eq := eigenvector_chartComponent_eq (I := I) (M := M)
    g r s i β Q
  have h_ae : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          i) β Q :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) := by
    have h_smul := Lp.coeFn_smul (i.fst.val)⁻¹
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) β Q)
    have h_smul' : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) β]
        (fun y => (i.fst.val)⁻¹ •
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) := by
      rw [h_chart_eq]
      exact h_smul
    filter_upwards [h_smul'] with y hy
    rw [hy, smul_eq_mul]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_res (i.fst.val)⁻¹)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- The component atom `componentLpLimit g r s i α P` vanishes almost
everywhere off the compact partition-of-unity kernel `chartPouKernel α`.
Chart-locality-free twin of `componentLpLimit_ae_zero_off_chartPouKernel`. -/
private lemma componentLpLimit_ae_zero_off_chartPouKernel
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        ((componentLpLimit (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
  classical
  have h_smul : (fun y => ((componentLpLimit (I := I) (M := M)
        g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => i.fst.val •
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
    rw [componentLpLimit]
    exact Lp.coeFn_smul i.fst.val _
  have h_comp_zero := tensorL2ChartComponent_ae_zero_off_chartPouKernel
    (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
    α P
  filter_upwards [h_smul, h_comp_zero] with y hy hy_zero hyK
  rw [hy, smul_eq_mul, hy_zero hyK, mul_zero]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- The chart-partial atom `partialLpLimit g r s i α P k` vanishes
almost everywhere off the compact partition-of-unity kernel `chartPouKernel α`,
given the order-`(K + 1)` partition-of-unity regularity input `h_pou`.
Chart-locality-free twin of `partialLpLimit_ae_zero_off_chartPouKernel`. -/
private lemma partialLpLimit_ae_zero_off_chartPouKernel
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        ((partialLpLimit (I := I) (M := M) g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_comp_w1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    (eigenvectorVec_pou_memWkp (I := I) (M := M) g r s i (K + 1)
      h_pou α P).memW1p
  have h_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (eigenvectorChartWeakPartial (I := I) (M := M)
        g r s i α P k)
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorChartWeakPartial_hasWeakPartialDeriv (I := I) (M := M)
      g r s i α P k
  have h_weak_memLp : MemLp
      (eigenvectorChartWeakPartial (I := I) (M := M)
        g r s i α P k) 2
      ((volume : Measure EuclN).restrict Ω) := by
    rw [eigenvectorChartWeakPartial]
    exact Lp.memLp _
  have h_comp_zero := tensorL2ChartComponent_ae_zero_off_chartPouKernel
    (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
    α P
  have h_weak_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ chartPouKernel (I := I) (M := M) α →
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s i α P k y = 0 :=
    hasWeakPartialDeriv_ae_zero_off_of_ae_zero_off hΩ_open k
      (chartPouKernel_isCompact (I := I) (M := M) α).isClosed
      h_weak_memLp h_weak h_comp_w1p
      (by rw [← chartL2Measure]; exact h_comp_zero)
  have h_ae : (fun y => ((partialLpLimit (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => i.fst.val •
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s i α P k y) := by
    rw [partialLpLimit, eigenvectorChartWeakPartial]
    exact Lp.coeFn_smul i.fst.val _
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have h_weak_zero' : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s i α P k y = 0 := by
    rw [chartL2Measure]; exact h_weak_zero
  filter_upwards [h_ae, h_weak_zero'] with y hy hy_zero hyK
  rw [hy, smul_eq_mul, hy_zero hyK, mul_zero]

/-- **Eigenbasis-uniform order-`K` `wkpNorm` bound for the principal rotation
coefficient limit (chart-locality-free).** Chart-locality-free twin of
`wkpNorm_covPrincipalRotationCoeffLimit_le_uniform`: a *single* nonnegative
constant `C`, independent of the eigenbasis index `i`, serves every `i`
simultaneously, with every limit object keyed on the canonical eigenbasis vector
`tensorResolventEigenbasisVec … i` and the order-`(K + 1)`
partition-of-unity regularity input `h_pou` keyed on
`eigenvectorResolvent`. -/
theorem wkpNorm_covPrincipalRotationCoeffLimit_le_uniform_unconditional
    (K : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
            (covPrincipalRotationCoeffLimit (I := I) (M := M)
              g r s i α P₀ : EuclN → ℝ)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            (∑ P : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                wkpNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((partialLpLimit (I := I) (M := M)
                      g r s i α P k :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set Cf : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) → ℝ := fun x =>
    (wkpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) α K
      (principalRotationFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2)).choose
    with hCf_def
  have hCf_spec : ∀ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      0 ≤ Cf x ∧ ∀ {G : EuclN → ℝ},
        MemWkp (d := Module.finrank ℝ E) K 2 G Ω →
        (∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
          y ∉ chartPouKernel (I := I) (M := M) α → G y = 0) →
        MemWkp (d := Module.finrank ℝ E) K 2
            (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (principalRotationFactor (I := I) (M := M)
                g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2) y * G y) Ω ∧
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (principalRotationFactor (I := I) (M := M)
                  g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2) y * G y) Ω
            ≤ ENNReal.ofReal (Cf x) *
              wkpNorm (d := Module.finrank ℝ E) K 2 G Ω :=
    fun x =>
      (wkpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) α K
        (principalRotationFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2)).choose_spec
  set F : TensorEigenIdx (I := I) (M := M) g r s →
      (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
      → EuclN → ℝ :=
    fun i x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (principalRotationFactor (I := I) (M := M)
            g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2) y *
        ((partialLpLimit (I := I) (M := M) g r s i α x.1 x.2.2.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  set partAtom : TensorEigenIdx (I := I) (M := M) g r s →
      (TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)) → EuclN → ℝ :=
    fun i pk y =>
    ((partialLpLimit (I := I) (M := M) g r s i α pk.1 pk.2 :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hpartAtom_def
  obtain ⟨Csum, hCsum_nn, hCsum_bd⟩ :=
    exists_uniform_const_of_finite_wkpNorm_bounds_uniform (I := I) (M := M)
      (α := α) (K := K) F partAtom (fun x => (x.1, x.2.2.1)) Cf
      (fun x => (hCf_spec x).1)
      (fun i x => by
        have hatom := (hCf_spec x).2
          (partialLpLimit_memWkp (I := I) (M := M)
            g r s i α x.1 x.2.2.1 K (h_pou i))
          (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
            g r s i α x.1 x.2.2.1 K (h_pou i))
        exact hatom.2)
  refine ⟨Csum * (Finset.univ : Finset (TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E))).card, by positivity, fun i => ?_⟩
  have h_memWkp : ∀ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) K 2 (F i x) Ω := by
    intro x
    have hatom := (hCf_spec x).2
      (partialLpLimit_memWkp (I := I) (M := M)
        g r s i α x.1 x.2.2.1 K (h_pou i))
      (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s i α x.1 x.2.2.1 K (h_pou i))
    exact hatom.1
  have h_bound :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E), F i x y) Ω
        ≤ ENNReal.ofReal (Csum * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card)
          * ∑ pk : TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E),
              wkpNorm (d := Module.finrank ℝ E) K 2 (partAtom i pk) Ω :=
    wkpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M)
      (α := α) (K := K) Finset.univ Finset.univ (F i) (partAtom i)
      (fun x => (x.1, x.2.2.1)) (fun x _ => Finset.mem_univ _)
      Csum hCsum_nn
      (fun x _ => h_memWkp x)
      (fun x _ => hCsum_bd i x)
  have h_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E), F i x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (principalRotationFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M) g r s i α P k :
                    EuclN → ℝ) y) := by
    funext y
    rw [hF_def]
    simp only [Fintype.sum_prod_type]
  have h_atom_eq : ∑ pk : TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E), wkpNorm (d := Module.finrank ℝ E) K 2
        (partAtom i pk) Ω
      = ∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              Ω := by
    rw [Fintype.sum_prod_type]
  rw [show (covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s i α P₀ : EuclN → ℝ)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (principalRotationFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M) g r s i α P k :
                    EuclN → ℝ) y) from rfl]
  rw [← h_eq, hΩ_def, ← h_atom_eq]
  exact h_bound

/-- **Eigenbasis-uniform order-`K` `wkpNorm` bound for the lower-order rotation
value coefficient limit (chart-locality-free).** Chart-locality-free twin of
`wkpNorm_covLowerOrderRotationValueCoeffLimit_le_uniform`. -/
theorem wkpNorm_covLowerOrderRotationValueCoeffLimit_le_uniform_unconditional
    (K : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
            (covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
              g r s i α P₀ : EuclN → ℝ)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            ((∑ P : TensorCompIdx (E := E) r s,
                ∑ k : Fin (Module.finrank ℝ E),
                  wkpNorm (d := Module.finrank ℝ E) K 2
                    (fun y => ((partialLpLimit (I := I) (M := M)
                        g r s i α P k :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) y)
                    (chartTargetEuclid (I := I) (M := M) α))
              + (∑ p : TensorCompIdx (E := E) r s,
                  wkpNorm (d := Module.finrank ℝ E) K 2
                    (fun y => ((componentLpLimit (I := I) (M := M)
                        g r s i α p :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) y)
                    (chartTargetEuclid (I := I) (M := M) α))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set CfP : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) → ℝ := fun x =>
    (wkpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) α K
      (valuePartialFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2)).choose
    with hCfP_def
  have hCfP_spec : ∀ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
      0 ≤ CfP x ∧ ∀ {G : EuclN → ℝ},
        MemWkp (d := Module.finrank ℝ E) K 2 G Ω →
        (∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
          y ∉ chartPouKernel (I := I) (M := M) α → G y = 0) →
        MemWkp (d := Module.finrank ℝ E) K 2
            (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (valuePartialFactor (I := I) (M := M)
                g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2) y * G y) Ω ∧
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (valuePartialFactor (I := I) (M := M)
                  g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2) y * G y) Ω
            ≤ ENNReal.ofReal (CfP x) *
              wkpNorm (d := Module.finrank ℝ E) K 2 G Ω :=
    fun x =>
      (wkpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) α K
        (valuePartialFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2)).choose_spec
  set CfC : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) → ℝ := fun x =>
    (wkpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) α K
      (valueComponentFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)).choose
    with hCfC_def
  have hCfC_spec : ∀ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s),
      0 ≤ CfC x ∧ ∀ {G : EuclN → ℝ},
        MemWkp (d := Module.finrank ℝ E) K 2 G Ω →
        (∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
          y ∉ chartPouKernel (I := I) (M := M) α → G y = 0) →
        MemWkp (d := Module.finrank ℝ E) K 2
            (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (valueComponentFactor (I := I) (M := M)
                g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) y * G y) Ω ∧
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (valueComponentFactor (I := I) (M := M)
                  g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) y * G y) Ω
            ≤ ENNReal.ofReal (CfC x) *
              wkpNorm (d := Module.finrank ℝ E) K 2 G Ω :=
    fun x =>
      (wkpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) α K
        (valueComponentFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)).choose_spec
  set Fpart : TensorEigenIdx (I := I) (M := M) g r s → (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) → EuclN → ℝ :=
    fun i x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (valuePartialFactor (I := I) (M := M)
            g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2) y *
        ((partialLpLimit (I := I) (M := M) g r s i α x.1 x.2.2.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFpart_def
  set Fcomp : TensorEigenIdx (I := I) (M := M) g r s → (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun i x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (valueComponentFactor (I := I) (M := M)
            g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) y *
        ((componentLpLimit (I := I) (M := M) g r s i α x.2.2.2.2 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFcomp_def
  set partAtom : TensorEigenIdx (I := I) (M := M) g r s →
      (TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)) → EuclN → ℝ :=
    fun i pk y =>
    ((partialLpLimit (I := I) (M := M) g r s i α pk.1 pk.2 :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hpartAtom_def
  set compAtom : TensorEigenIdx (I := I) (M := M) g r s →
      TensorCompIdx (E := E) r s → EuclN → ℝ :=
    fun i p y =>
    ((componentLpLimit (I := I) (M := M) g r s i α p :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hcompAtom_def
  obtain ⟨Cpart, hCpart_nn, hCpart_bd⟩ :=
    exists_uniform_const_of_finite_wkpNorm_bounds_uniform (I := I) (M := M)
      (α := α) (K := K) Fpart partAtom (fun x => (x.1, x.2.2.1)) CfP
      (fun x => (hCfP_spec x).1)
      (fun i x => by
        have hatom := (hCfP_spec x).2
          (partialLpLimit_memWkp (I := I) (M := M)
            g r s i α x.1 x.2.2.1 K (h_pou i))
          (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
            g r s i α x.1 x.2.2.1 K (h_pou i))
        exact hatom.2)
  obtain ⟨Ccomp, hCcomp_nn, hCcomp_bd⟩ :=
    exists_uniform_const_of_finite_wkpNorm_bounds_uniform (I := I) (M := M)
      (α := α) (K := K) Fcomp compAtom (fun x => x.2.2.2.2) CfC
      (fun x => (hCfC_spec x).1)
      (fun i x => by
        have hatom := (hCfC_spec x).2
          (componentLpLimit_memWkp (I := I) (M := M)
            g r s i α x.2.2.2.2 K (h_pou i))
          (componentLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
            g r s i α x.2.2.2.2)
        exact hatom.2)
  refine ⟨max
      (Cpart * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card)
      (Ccomp * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card),
    le_trans (by positivity) (le_max_left _ _), fun i => ?_⟩
  set Cmax : ℝ := max
      (Cpart * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card)
      (Ccomp * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card) with hCmax_def
  have h_part_memWkp : ∀ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) K 2 (Fpart i x) Ω := by
    intro x
    have hatom := (hCfP_spec x).2
      (partialLpLimit_memWkp (I := I) (M := M)
        g r s i α x.1 x.2.2.1 K (h_pou i))
      (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s i α x.1 x.2.2.1 K (h_pou i))
    exact hatom.1
  have h_comp_memWkp : ∀ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) K 2 (Fcomp i x) Ω := by
    intro x
    have hatom := (hCfC_spec x).2
      (componentLpLimit_memWkp (I := I) (M := M)
        g r s i α x.2.2.2.2 K (h_pou i))
      (componentLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s i α x.2.2.2.2)
    exact hatom.1
  have h_part_bound :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)), Fpart i x y) Ω
        ≤ ENNReal.ofReal (Cpart * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card)
          * ∑ pk : TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E),
              wkpNorm (d := Module.finrank ℝ E) K 2 (partAtom i pk) Ω :=
    wkpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M)
      (α := α) (K := K) Finset.univ Finset.univ (Fpart i) (partAtom i)
      (fun x => (x.1, x.2.2.1)) (fun x _ => Finset.mem_univ _)
      Cpart hCpart_nn
      (fun x _ => h_part_memWkp x)
      (fun x _ => hCpart_bd i x)
  have h_comp_bound :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y) Ω
        ≤ ENNReal.ofReal (Ccomp * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
          * ∑ p : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) K 2 (compAtom i p) Ω :=
    wkpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M)
      (α := α) (K := K) Finset.univ Finset.univ (Fcomp i) (compAtom i)
      (fun x => x.2.2.2.2) (fun x _ => Finset.mem_univ _)
      Ccomp hCcomp_nn
      (fun x _ => h_comp_memWkp x)
      (fun x _ => hCcomp_bd i x)
  have h_part_eq : (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)), Fpart i x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (valuePartialFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M) g r s i α P k :
                    EuclN → ℝ) y) := by
    funext y
    rw [hFpart_def]
    simp only [Fintype.sum_prod_type]
  have h_comp_eq : (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (valueComponentFactor (I := I) (M := M)
                        g r s α P₀ P Q k l p) y *
                    (componentLpLimit (I := I) (M := M) g r s i α p :
                      EuclN → ℝ) y) := by
    funext y
    rw [hFcomp_def]
    simp only [Fintype.sum_prod_type]
  have h_part_atom_eq : ∑ pk : TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E), wkpNorm (d := Module.finrank ℝ E) K 2
        (partAtom i pk) Ω
      = ∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              Ω := by
    rw [Fintype.sum_prod_type]
  have hpart : wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)), Fpart i x y) Ω
      ≤ ENNReal.ofReal Cmax *
        ∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              Ω := by
    rw [← h_part_atom_eq]
    refine h_part_bound.trans ?_
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (le_max_left _ _)) (zero_le _)
  have hcomp : wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y) Ω
      ≤ ENNReal.ofReal Cmax *
        ∑ p : TensorCompIdx (E := E) r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((componentLpLimit (I := I) (M := M)
                g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            Ω := by
    refine h_comp_bound.trans ?_
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (le_max_right _ _)) (zero_le _)
  have h_part_group_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)), Fpart i x y) Ω :=
    memWkp_finsetSum (I := I) (M := M) _ (fun x _ => h_part_memWkp x)
  have h_comp_group_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y) Ω :=
    memWkp_finsetSum (I := I) (M := M) _ (fun x _ => h_comp_memWkp x)
  rw [show (covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
        g r s i α P₀ : EuclN → ℝ)
      = (fun y => (∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (valuePartialFactor (I := I) (M := M)
                        g r s α P₀ P Q k l) y *
                    (partialLpLimit (I := I) (M := M) g r s i α P k :
                      EuclN → ℝ) y)
          + ∑ P : TensorCompIdx (E := E) r s,
              ∑ Q : TensorCompIdx (E := E) r s,
                ∑ k : Fin (Module.finrank ℝ E),
                  ∑ l : Fin (Module.finrank ℝ E),
                    ∑ p : TensorCompIdx (E := E) r s,
                      Set.indicator (chartPouKernel (I := I) (M := M) α)
                          (valueComponentFactor (I := I) (M := M)
                            g r s α P₀ P Q k l p) y *
                        (componentLpLimit (I := I) (M := M)
                          g r s i α p : EuclN → ℝ) y) from rfl]
  have h_bridge : (fun y => (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (valuePartialFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M) g r s i α P k :
                    EuclN → ℝ) y)
        + ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ∑ p : TensorCompIdx (E := E) r s,
                    Set.indicator (chartPouKernel (I := I) (M := M) α)
                        (valueComponentFactor (I := I) (M := M)
                          g r s α P₀ P Q k l p) y *
                      (componentLpLimit (I := I) (M := M)
                        g r s i α p : EuclN → ℝ) y)
      = (fun y => (∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)), Fpart i x y)
          + ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y) := by
    funext y
    rw [← congrFun h_part_eq y, ← congrFun h_comp_eq y]
  rw [h_bridge]
  calc
    wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => (∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)), Fpart i x y)
        + ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y) Ω
        ≤ wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)), Fpart i x y) Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y) Ω :=
        wkpNorm_add_le (d := Module.finrank ℝ E)
          (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open
          h_part_group_memWkp h_comp_group_memWkp
    _ ≤ ENNReal.ofReal Cmax *
          (∑ P : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((partialLpLimit (I := I) (M := M)
                    g r s i α P k :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) Ω)
        + ENNReal.ofReal Cmax *
          (∑ p : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((componentLpLimit (I := I) (M := M)
                  g r s i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y) Ω) :=
        add_le_add hpart hcomp
    _ = ENNReal.ofReal Cmax *
          ((∑ P : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                wkpNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((partialLpLimit (I := I) (M := M)
                      g r s i α P k :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y) Ω)
            + (∑ p : TensorCompIdx (E := E) r s,
                wkpNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((componentLpLimit (I := I) (M := M)
                      g r s i α p :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y) Ω)) := by
      rw [mul_add]

/-- **Eigenbasis-uniform order-`K` `wkpNorm` bound for the chart-density-weighted
lower-order gradient divergence coefficient limit (chart-locality-free).**
Chart-locality-free twin of `wkpNorm_weightedGradCoeffDivLimit_le_uniform`. -/
theorem wkpNorm_weightedGradCoeffDivLimit_le_uniform_unconditional
    (K : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
            (weightedGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ l : EuclN → ℝ)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            ((∑ p : TensorCompIdx (E := E) r s,
                wkpNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((componentLpLimit (I := I) (M := M)
                      g r s i α p :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) α))
              + (∑ p : TensorCompIdx (E := E) r s,
                  ∑ l' : Fin (Module.finrank ℝ E),
                    wkpNorm (d := Module.finrank ℝ E) K 2
                      (fun y => ((partialLpLimit (I := I) (M := M)
                          g r s i α p l' :
                        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                        EuclN → ℝ) y)
                      (chartTargetEuclid (I := I) (M := M) α))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set CfC : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) → ℝ := fun x =>
    (wkpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) α K
      (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)).choose
    with hCfC_def
  have hCfC_spec : ∀ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s),
      0 ≤ CfC x ∧ ∀ {G : EuclN → ℝ},
        MemWkp (d := Module.finrank ℝ E) K 2 G Ω →
        (∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
          y ∉ chartPouKernel (I := I) (M := M) α → G y = 0) →
        MemWkp (d := Module.finrank ℝ E) K 2
            (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (euclidPartial (E := E) l
                (weightedGradFactor (I := I) (M := M)
                  g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)) y * G y) Ω ∧
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (weightedGradFactor (I := I) (M := M)
                    g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)) y * G y) Ω
            ≤ ENNReal.ofReal (CfC x) *
              wkpNorm (d := Module.finrank ℝ E) K 2 G Ω :=
    fun x =>
      (wkpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) α K
        (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)).choose_spec
  set CfP : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) → ℝ := fun x =>
    (wkpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) α K
      (weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)).choose
    with hCfP_def
  have hCfP_spec : ∀ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s),
      0 ≤ CfP x ∧ ∀ {G : EuclN → ℝ},
        MemWkp (d := Module.finrank ℝ E) K 2 G Ω →
        (∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
          y ∉ chartPouKernel (I := I) (M := M) α → G y = 0) →
        MemWkp (d := Module.finrank ℝ E) K 2
            (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (weightedGradFactor (I := I) (M := M)
                g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2) y * G y) Ω ∧
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (weightedGradFactor (I := I) (M := M)
                  g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2) y * G y) Ω
            ≤ ENNReal.ofReal (CfP x) *
              wkpNorm (d := Module.finrank ℝ E) K 2 G Ω :=
    fun x =>
      (wkpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) α K
        (weightedGradFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)).choose_spec
  set Fcomp : TensorEigenIdx (I := I) (M := M) g r s → (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun i x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (euclidPartial (E := E) l
            (weightedGradFactor (I := I) (M := M)
              g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)) y *
        ((componentLpLimit (I := I) (M := M) g r s i α x.2.2.2 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFcomp_def
  set Fpart : TensorEigenIdx (I := I) (M := M) g r s → (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun i x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (weightedGradFactor (I := I) (M := M)
            g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2) y *
        ((partialLpLimit (I := I) (M := M) g r s i α x.2.2.2 l :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFpart_def
  set compAtom : TensorEigenIdx (I := I) (M := M) g r s →
      TensorCompIdx (E := E) r s → EuclN → ℝ :=
    fun i p y =>
    ((componentLpLimit (I := I) (M := M) g r s i α p :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hcompAtom_def
  set partAtom : TensorEigenIdx (I := I) (M := M) g r s →
      (TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)) → EuclN → ℝ :=
    fun i pl y =>
    ((partialLpLimit (I := I) (M := M) g r s i α pl.1 pl.2 :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hpartAtom_def
  obtain ⟨Ccomp, hCcomp_nn, hCcomp_bd⟩ :=
    exists_uniform_const_of_finite_wkpNorm_bounds_uniform (I := I) (M := M)
      (α := α) (K := K) Fcomp compAtom (fun x => x.2.2.2) CfC
      (fun x => (hCfC_spec x).1)
      (fun i x => by
        have hatom := (hCfC_spec x).2
          (componentLpLimit_memWkp (I := I) (M := M)
            g r s i α x.2.2.2 K (h_pou i))
          (componentLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
            g r s i α x.2.2.2)
        exact hatom.2)
  obtain ⟨Cpart, hCpart_nn, hCpart_bd⟩ :=
    exists_uniform_const_of_finite_wkpNorm_bounds_uniform (I := I) (M := M)
      (α := α) (K := K) Fpart partAtom (fun x => (x.2.2.2, l)) CfP
      (fun x => (hCfP_spec x).1)
      (fun i x => by
        have hatom := (hCfP_spec x).2
          (partialLpLimit_memWkp (I := I) (M := M)
            g r s i α x.2.2.2 l K (h_pou i))
          (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
            g r s i α x.2.2.2 l K (h_pou i))
        exact hatom.2)
  refine ⟨max
      (Ccomp * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
      (Cpart * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card),
    le_trans (by positivity) (le_max_left _ _), fun i => ?_⟩
  set Cmax : ℝ := max
      (Ccomp * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
      (Cpart * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card) with hCmax_def
  have h_comp_memWkp : ∀ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) K 2 (Fcomp i x) Ω := by
    intro x
    have hatom := (hCfC_spec x).2
      (componentLpLimit_memWkp (I := I) (M := M)
        g r s i α x.2.2.2 K (h_pou i))
      (componentLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s i α x.2.2.2)
    exact hatom.1
  have h_part_memWkp : ∀ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) K 2 (Fpart i x) Ω := by
    intro x
    have hatom := (hCfP_spec x).2
      (partialLpLimit_memWkp (I := I) (M := M)
        g r s i α x.2.2.2 l K (h_pou i))
      (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s i α x.2.2.2 l K (h_pou i))
    exact hatom.1
  have h_comp_bound :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y) Ω
        ≤ ENNReal.ofReal (Ccomp * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
          * ∑ p : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) K 2 (compAtom i p) Ω :=
    wkpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M)
      (α := α) (K := K) Finset.univ Finset.univ (Fcomp i) (compAtom i)
      (fun x => x.2.2.2) (fun x _ => Finset.mem_univ _)
      Ccomp hCcomp_nn
      (fun x _ => h_comp_memWkp x)
      (fun x _ => hCcomp_bd i x)
  have h_part_bound :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fpart i x y) Ω
        ≤ ENNReal.ofReal (Cpart * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
          * ∑ pl : TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E),
              wkpNorm (d := Module.finrank ℝ E) K 2 (partAtom i pl) Ω :=
    wkpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M)
      (α := α) (K := K) Finset.univ Finset.univ (Fpart i) (partAtom i)
      (fun x => (x.2.2.2, l)) (fun x _ => Finset.mem_univ _)
      Cpart hCpart_nn
      (fun x _ => h_part_memWkp x)
      (fun x _ => hCpart_bd i x)
  have h_comp_eq : (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (euclidPartial (E := E) l
                      (weightedGradFactor (I := I) (M := M)
                        g r s α P₀ l P Q k p)) y *
                  (componentLpLimit (I := I) (M := M) g r s i α p :
                    EuclN → ℝ) y) := by
    funext y
    rw [hFcomp_def]
    simp only [Fintype.sum_prod_type]
  have h_part_eq : (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fpart i x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (weightedGradFactor (I := I) (M := M)
                      g r s α P₀ l P Q k p) y *
                  (partialLpLimit (I := I) (M := M) g r s i α p l :
                    EuclN → ℝ) y) := by
    funext y
    rw [hFpart_def]
    simp only [Fintype.sum_prod_type]
  have h_part_atom_eq : ∑ pl : TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E), wkpNorm (d := Module.finrank ℝ E) K 2
        (partAtom i pl) Ω
      = ∑ p : TensorCompIdx (E := E) r s,
          ∑ l' : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α p l' :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              Ω := by
    rw [Fintype.sum_prod_type]
  have hcomp : wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y) Ω
      ≤ ENNReal.ofReal Cmax *
        ∑ p : TensorCompIdx (E := E) r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((componentLpLimit (I := I) (M := M)
                g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            Ω := by
    refine h_comp_bound.trans ?_
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (le_max_left _ _)) (zero_le _)
  have hpart : wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fpart i x y) Ω
      ≤ ENNReal.ofReal Cmax *
        ∑ p : TensorCompIdx (E := E) r s,
          ∑ l' : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α p l' :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              Ω := by
    rw [← h_part_atom_eq]
    refine h_part_bound.trans ?_
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (le_max_right _ _)) (zero_le _)
  have h_comp_group_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y) Ω :=
    memWkp_finsetSum (I := I) (M := M) _ (fun x _ => h_comp_memWkp x)
  have h_part_group_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fpart i x y) Ω :=
    memWkp_finsetSum (I := I) (M := M) _ (fun x _ => h_part_memWkp x)
  rw [show (weightedGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ l : EuclN → ℝ)
      = (fun y => (∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (euclidPartial (E := E) l
                        (weightedGradFactor (I := I) (M := M)
                          g r s α P₀ l P Q k p)) y *
                    (componentLpLimit (I := I) (M := M) g r s i α p :
                      EuclN → ℝ) y)
          + ∑ P : TensorCompIdx (E := E) r s,
              ∑ Q : TensorCompIdx (E := E) r s,
                ∑ k : Fin (Module.finrank ℝ E),
                  ∑ p : TensorCompIdx (E := E) r s,
                    Set.indicator (chartPouKernel (I := I) (M := M) α)
                        (weightedGradFactor (I := I) (M := M)
                          g r s α P₀ l P Q k p) y *
                      (partialLpLimit (I := I) (M := M) g r s i α p l :
                        EuclN → ℝ) y) from rfl]
  have h_bridge : (fun y => (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (euclidPartial (E := E) l
                      (weightedGradFactor (I := I) (M := M)
                        g r s α P₀ l P Q k p)) y *
                  (componentLpLimit (I := I) (M := M) g r s i α p :
                    EuclN → ℝ) y)
        + ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (weightedGradFactor (I := I) (M := M)
                        g r s α P₀ l P Q k p) y *
                    (partialLpLimit (I := I) (M := M) g r s i α p l :
                      EuclN → ℝ) y)
      = (fun y => (∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y)
          + ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fpart i x y) := by
    funext y
    rw [← congrFun h_comp_eq y, ← congrFun h_part_eq y]
  rw [h_bridge]
  calc
    wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => (∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y)
        + ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fpart i x y) Ω
        ≤ wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y) Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fpart i x y) Ω :=
        wkpNorm_add_le (d := Module.finrank ℝ E)
          (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open
          h_comp_group_memWkp h_part_group_memWkp
    _ ≤ ENNReal.ofReal Cmax *
          (∑ p : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((componentLpLimit (I := I) (M := M)
                  g r s i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y) Ω)
        + ENNReal.ofReal Cmax *
          (∑ p : TensorCompIdx (E := E) r s,
            ∑ l' : Fin (Module.finrank ℝ E),
              wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((partialLpLimit (I := I) (M := M)
                    g r s i α p l' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) Ω) :=
        add_le_add hcomp hpart
    _ = ENNReal.ofReal Cmax *
          ((∑ p : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((componentLpLimit (I := I) (M := M)
                    g r s i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) Ω)
            + (∑ p : TensorCompIdx (E := E) r s,
                ∑ l' : Fin (Module.finrank ℝ E),
                  wkpNorm (d := Module.finrank ℝ E) K 2
                    (fun y => ((partialLpLimit (I := I) (M := M)
                        g r s i α p l' :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) y) Ω)) := by
      rw [mul_add]

end LowerOrderWkpNormBoundsUniform

section LowerOrderWkpNormBoundsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

/-- Chart-locality-free twin of `wkpNorm_covPrincipalRotationCoeffLimit_le`. -/
theorem wkpNorm_covPrincipalRotationCoeffLimit_le_unconditional
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (K : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (covPrincipalRotationCoeffLimit (I := I) (M := M)
            g r s i α P₀ : EuclN → ℝ)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          (∑ P : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((partialLpLimit (I := I) (M := M)
                    g r s i α P k :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set partAtom : (TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E))
      → EuclN → ℝ := fun pk y =>
    ((partialLpLimit (I := I) (M := M) g r s i α pk.1 pk.2 :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hpartAtom_def
  set F : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (principalRotationFactor (I := I) (M := M)
            g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2) y *
        ((partialLpLimit (I := I) (M := M) g r s i α x.1 x.2.2.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  have h_data : ∀ x ∈ (Finset.univ :
      Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))),
      MemWkp (d := Module.finrank ℝ E) K 2 (F x) Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧
          wkpNorm (d := Module.finrank ℝ E) K 2 (F x) Ω
            ≤ ENNReal.ofReal C *
              wkpNorm (d := Module.finrank ℝ E) K 2
                (partAtom (x.1, x.2.2.1)) Ω := by
    intro x _
    exact wkpNorm_indicatorFactor_mul_atom_le (I := I) (M := M) α K
      (principalRotationFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2)
      (partialLpLimit_memWkp (I := I) (M := M)
        g r s i α x.1 x.2.2.1 K h_pou)
      (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s i α x.1 x.2.2.1 K h_pou)
  obtain ⟨Csum, hCsum_nn, hCsum_bd⟩ :=
    exists_uniform_const_of_finite_wkpNorm_bounds (I := I) (M := M)
      (α := α) (K := K) F partAtom (fun x => (x.1, x.2.2.1))
      (fun x => (h_data x (Finset.mem_univ x)).2)
  have h_bound :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E), F x y) Ω
        ≤ ENNReal.ofReal (Csum * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card)
          * ∑ pk : TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E),
              wkpNorm (d := Module.finrank ℝ E) K 2 (partAtom pk) Ω :=
    wkpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M)
      (α := α) (K := K) Finset.univ Finset.univ F partAtom
      (fun x => (x.1, x.2.2.1)) (fun x _ => Finset.mem_univ _)
      Csum hCsum_nn
      (fun x hx => (h_data x hx).1)
      (fun x _ => hCsum_bd x)
  have h_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E), F x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (principalRotationFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M) g r s i α P k :
                    EuclN → ℝ) y) := by
    funext y
    rw [hF_def]
    simp only [Fintype.sum_prod_type]
  have h_atom_eq : ∑ pk : TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E), wkpNorm (d := Module.finrank ℝ E) K 2
        (partAtom pk) Ω
      = ∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              Ω := by
    rw [Fintype.sum_prod_type]
  refine ⟨Csum * (Finset.univ :
      Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card,
    by positivity, ?_⟩
  rw [show (covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s i α P₀ : EuclN → ℝ)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (principalRotationFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M) g r s i α P k :
                    EuclN → ℝ) y) from rfl]
  rw [← h_eq, hΩ_def, ← h_atom_eq]
  exact h_bound

/-- Chart-locality-free twin of `wkpNorm_covLowerOrderRotationValueCoeffLimit_le`. -/
theorem wkpNorm_covLowerOrderRotationValueCoeffLimit_le_unconditional
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (K : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
            g r s i α P₀ : EuclN → ℝ)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          ((∑ P : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                wkpNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((partialLpLimit (I := I) (M := M)
                      g r s i α P k :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) α))
            + (∑ p : TensorCompIdx (E := E) r s,
                wkpNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((componentLpLimit (I := I) (M := M)
                      g r s i α p :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) α))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set partAtom : (TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E))
      → EuclN → ℝ := fun pk y =>
    ((partialLpLimit (I := I) (M := M) g r s i α pk.1 pk.2 :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hpartAtom_def
  set compAtom : TensorCompIdx (E := E) r s → EuclN → ℝ := fun p y =>
    ((componentLpLimit (I := I) (M := M) g r s i α p :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hcompAtom_def
  set Fpart : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (valuePartialFactor (I := I) (M := M)
            g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2) y *
        ((partialLpLimit (I := I) (M := M) g r s i α x.1 x.2.2.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFpart_def
  set Fcomp : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (valueComponentFactor (I := I) (M := M)
            g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) y *
        ((componentLpLimit (I := I) (M := M) g r s i α x.2.2.2.2 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFcomp_def
  have h_part_data : ∀ x ∈ (Finset.univ :
      Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))),
      MemWkp (d := Module.finrank ℝ E) K 2 (Fpart x) Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧
          wkpNorm (d := Module.finrank ℝ E) K 2 (Fpart x) Ω
            ≤ ENNReal.ofReal C *
              wkpNorm (d := Module.finrank ℝ E) K 2
                (partAtom (x.1, x.2.2.1)) Ω := by
    intro x _
    exact wkpNorm_indicatorFactor_mul_atom_le (I := I) (M := M) α K
      (valuePartialFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2)
      (partialLpLimit_memWkp (I := I) (M := M)
        g r s i α x.1 x.2.2.1 K h_pou)
      (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s i α x.1 x.2.2.1 K h_pou)
  have h_comp_data : ∀ x ∈ (Finset.univ :
      Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
        × TensorCompIdx (E := E) r s)),
      MemWkp (d := Module.finrank ℝ E) K 2 (Fcomp x) Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧
          wkpNorm (d := Module.finrank ℝ E) K 2 (Fcomp x) Ω
            ≤ ENNReal.ofReal C *
              wkpNorm (d := Module.finrank ℝ E) K 2
                (compAtom x.2.2.2.2) Ω := by
    intro x _
    exact wkpNorm_indicatorFactor_mul_atom_le (I := I) (M := M) α K
      (valueComponentFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      (componentLpLimit_memWkp (I := I) (M := M)
        g r s i α x.2.2.2.2 K h_pou)
      (componentLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s i α x.2.2.2.2)
  obtain ⟨Cpart, hCpart_nn, hCpart_bd⟩ :=
    exists_uniform_const_of_finite_wkpNorm_bounds (I := I) (M := M)
      (α := α) (K := K) Fpart partAtom (fun x => (x.1, x.2.2.1))
      (fun x => (h_part_data x (Finset.mem_univ x)).2)
  obtain ⟨Ccomp, hCcomp_nn, hCcomp_bd⟩ :=
    exists_uniform_const_of_finite_wkpNorm_bounds (I := I) (M := M)
      (α := α) (K := K) Fcomp compAtom (fun x => x.2.2.2.2)
      (fun x => (h_comp_data x (Finset.mem_univ x)).2)
  have h_part_bound :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E), Fpart x y) Ω
        ≤ ENNReal.ofReal (Cpart * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card)
          * ∑ pk : TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E),
              wkpNorm (d := Module.finrank ℝ E) K 2 (partAtom pk) Ω :=
    wkpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M)
      (α := α) (K := K) Finset.univ Finset.univ Fpart partAtom
      (fun x => (x.1, x.2.2.1)) (fun x _ => Finset.mem_univ _)
      Cpart hCpart_nn
      (fun x hx => (h_part_data x hx).1)
      (fun x _ => hCpart_bd x)
  have h_comp_bound :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
            Fcomp x y) Ω
        ≤ ENNReal.ofReal (Ccomp * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
              × TensorCompIdx (E := E) r s)).card)
          * ∑ p : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) K 2 (compAtom p) Ω :=
    wkpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M)
      (α := α) (K := K) Finset.univ Finset.univ Fcomp compAtom
      (fun x => x.2.2.2.2) (fun x _ => Finset.mem_univ _)
      Ccomp hCcomp_nn
      (fun x hx => (h_comp_data x hx).1)
      (fun x _ => hCcomp_bd x)
  have h_part_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E), Fpart x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (valuePartialFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M) g r s i α P k :
                    EuclN → ℝ) y) := by
    funext y
    rw [hFpart_def]
    simp only [Fintype.sum_prod_type]
  have h_comp_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s, Fcomp x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (valueComponentFactor (I := I) (M := M)
                        g r s α P₀ P Q k l p) y *
                    (componentLpLimit (I := I) (M := M) g r s i α p :
                      EuclN → ℝ) y) := by
    funext y
    rw [hFcomp_def]
    simp only [Fintype.sum_prod_type]
  have h_part_atom_eq : ∑ pk : TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E), wkpNorm (d := Module.finrank ℝ E) K 2
        (partAtom pk) Ω
      = ∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              Ω := by
    rw [Fintype.sum_prod_type]
  refine ⟨max
      (Cpart * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card)
      (Ccomp * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s)).card),
    le_trans (by positivity) (le_max_left _ _), ?_⟩
  set Cmax : ℝ := max
      (Cpart * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card)
      (Ccomp * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s)).card) with hCmax_def
  have hpart : wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E), Fpart x y) Ω
      ≤ ENNReal.ofReal Cmax *
        ∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              Ω := by
    rw [← h_part_atom_eq]
    refine h_part_bound.trans ?_
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left _ _)) (zero_le _)
  have hcomp : wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
          Fcomp x y) Ω
      ≤ ENNReal.ofReal Cmax *
        ∑ p : TensorCompIdx (E := E) r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((componentLpLimit (I := I) (M := M)
                g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            Ω := by
    refine h_comp_bound.trans ?_
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_right _ _)) (zero_le _)
  have h_part_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ x : TensorCompIdx (E := E) r s
        × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
        × Fin (Module.finrank ℝ E), Fpart x y) Ω :=
    memWkp_finsetSum (I := I) (M := M) _ (fun x hx => (h_part_data x hx).1)
  have h_comp_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ x : TensorCompIdx (E := E) r s
        × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
        Fcomp x y) Ω :=
    memWkp_finsetSum (I := I) (M := M) _ (fun x hx => (h_comp_data x hx).1)
  rw [show (covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
        g r s i α P₀ : EuclN → ℝ)
      = (fun y => (∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (valuePartialFactor (I := I) (M := M)
                        g r s α P₀ P Q k l) y *
                    (partialLpLimit (I := I) (M := M) g r s i α P k :
                      EuclN → ℝ) y)
          + ∑ P : TensorCompIdx (E := E) r s,
              ∑ Q : TensorCompIdx (E := E) r s,
                ∑ k : Fin (Module.finrank ℝ E),
                  ∑ l : Fin (Module.finrank ℝ E),
                    ∑ p : TensorCompIdx (E := E) r s,
                      Set.indicator (chartPouKernel (I := I) (M := M) α)
                          (valueComponentFactor (I := I) (M := M)
                            g r s α P₀ P Q k l p) y *
                        (componentLpLimit (I := I) (M := M)
                          g r s i α p : EuclN → ℝ) y) from rfl]
  have h_bridge : (fun y => (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (valuePartialFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M) g r s i α P k :
                    EuclN → ℝ) y)
        + ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ∑ p : TensorCompIdx (E := E) r s,
                    Set.indicator (chartPouKernel (I := I) (M := M) α)
                        (valueComponentFactor (I := I) (M := M)
                          g r s α P₀ P Q k l p) y *
                      (componentLpLimit (I := I) (M := M)
                        g r s i α p : EuclN → ℝ) y)
      = (fun y => (∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E), Fpart x y)
          + ∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
              × TensorCompIdx (E := E) r s, Fcomp x y) := by
    funext y
    rw [← congrFun h_part_eq y, ← congrFun h_comp_eq y]
  rw [h_bridge]
  calc
    wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => (∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E), Fpart x y)
        + ∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
            × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
            × TensorCompIdx (E := E) r s, Fcomp x y) Ω
        ≤ wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ x : TensorCompIdx (E := E) r s
                × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
                × Fin (Module.finrank ℝ E), Fpart x y) Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ x : TensorCompIdx (E := E) r s
                × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
                × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
                Fcomp x y) Ω :=
        wkpNorm_add_le (d := Module.finrank ℝ E)
          (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_part_memWkp h_comp_memWkp
    _ ≤ ENNReal.ofReal Cmax *
          (∑ P : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((partialLpLimit (I := I) (M := M)
                    g r s i α P k :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) Ω)
        + ENNReal.ofReal Cmax *
          (∑ p : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((componentLpLimit (I := I) (M := M)
                  g r s i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y) Ω) :=
        add_le_add hpart hcomp
    _ = ENNReal.ofReal Cmax *
          ((∑ P : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                wkpNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((partialLpLimit (I := I) (M := M)
                      g r s i α P k :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y) Ω)
            + (∑ p : TensorCompIdx (E := E) r s,
                wkpNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((componentLpLimit (I := I) (M := M)
                      g r s i α p :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y) Ω)) := by
      rw [mul_add]

/-- Chart-locality-free twin of `wkpNorm_weightedGradCoeffDivLimit_le`. -/
theorem wkpNorm_weightedGradCoeffDivLimit_le_unconditional
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (K : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l : EuclN → ℝ)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          ((∑ p : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((componentLpLimit (I := I) (M := M)
                    g r s i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) α))
            + (∑ p : TensorCompIdx (E := E) r s,
                ∑ l' : Fin (Module.finrank ℝ E),
                  wkpNorm (d := Module.finrank ℝ E) K 2
                    (fun y => ((partialLpLimit (I := I) (M := M)
                        g r s i α p l' :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) y)
                    (chartTargetEuclid (I := I) (M := M) α))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set compAtom : TensorCompIdx (E := E) r s → EuclN → ℝ := fun p y =>
    ((componentLpLimit (I := I) (M := M) g r s i α p :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hcompAtom_def
  set partAtom : (TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E))
      → EuclN → ℝ := fun pl y =>
    ((partialLpLimit (I := I) (M := M) g r s i α pl.1 pl.2 :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hpartAtom_def
  set Fcomp : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (euclidPartial (E := E) l
            (weightedGradFactor (I := I) (M := M)
              g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)) y *
        ((componentLpLimit (I := I) (M := M) g r s i α x.2.2.2 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFcomp_def
  set Fpart : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (weightedGradFactor (I := I) (M := M)
            g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2) y *
        ((partialLpLimit (I := I) (M := M) g r s i α x.2.2.2 l :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFpart_def
  have h_comp_data : ∀ x ∈ (Finset.univ :
      Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)),
      MemWkp (d := Module.finrank ℝ E) K 2 (Fcomp x) Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧
          wkpNorm (d := Module.finrank ℝ E) K 2 (Fcomp x) Ω
            ≤ ENNReal.ofReal C *
              wkpNorm (d := Module.finrank ℝ E) K 2
                (compAtom x.2.2.2) Ω := by
    intro x _
    exact wkpNorm_indicatorFactor_mul_atom_le (I := I) (M := M) α K
      (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)
      (componentLpLimit_memWkp (I := I) (M := M)
        g r s i α x.2.2.2 K h_pou)
      (componentLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s i α x.2.2.2)
  have h_part_data : ∀ x ∈ (Finset.univ :
      Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)),
      MemWkp (d := Module.finrank ℝ E) K 2 (Fpart x) Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧
          wkpNorm (d := Module.finrank ℝ E) K 2 (Fpart x) Ω
            ≤ ENNReal.ofReal C *
              wkpNorm (d := Module.finrank ℝ E) K 2
                (partAtom (x.2.2.2, l)) Ω := by
    intro x _
    exact wkpNorm_indicatorFactor_mul_atom_le (I := I) (M := M) α K
      (weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)
      (partialLpLimit_memWkp (I := I) (M := M)
        g r s i α x.2.2.2 l K h_pou)
      (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s i α x.2.2.2 l K h_pou)
  obtain ⟨Ccomp, hCcomp_nn, hCcomp_bd⟩ :=
    exists_uniform_const_of_finite_wkpNorm_bounds (I := I) (M := M)
      (α := α) (K := K) Fcomp compAtom (fun x => x.2.2.2)
      (fun x => (h_comp_data x (Finset.mem_univ x)).2)
  obtain ⟨Cpart, hCpart_nn, hCpart_bd⟩ :=
    exists_uniform_const_of_finite_wkpNorm_bounds (I := I) (M := M)
      (α := α) (K := K) Fpart partAtom (fun x => (x.2.2.2, l))
      (fun x => (h_part_data x (Finset.mem_univ x)).2)
  have h_comp_bound :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × TensorCompIdx (E := E) r s, Fcomp x y) Ω
        ≤ ENNReal.ofReal (Ccomp * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
          * ∑ p : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) K 2 (compAtom p) Ω :=
    wkpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M)
      (α := α) (K := K) Finset.univ Finset.univ Fcomp compAtom
      (fun x => x.2.2.2) (fun x _ => Finset.mem_univ _)
      Ccomp hCcomp_nn
      (fun x hx => (h_comp_data x hx).1)
      (fun x _ => hCcomp_bd x)
  have h_part_bound :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × TensorCompIdx (E := E) r s, Fpart x y) Ω
        ≤ ENNReal.ofReal (Cpart * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
          * ∑ pl : TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E),
              wkpNorm (d := Module.finrank ℝ E) K 2 (partAtom pl) Ω :=
    wkpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M)
      (α := α) (K := K) Finset.univ Finset.univ Fpart partAtom
      (fun x => (x.2.2.2, l)) (fun x _ => Finset.mem_univ _)
      Cpart hCpart_nn
      (fun x hx => (h_part_data x hx).1)
      (fun x _ => hCpart_bd x)
  have h_comp_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s, Fcomp x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (euclidPartial (E := E) l
                      (weightedGradFactor (I := I) (M := M)
                        g r s α P₀ l P Q k p)) y *
                  (componentLpLimit (I := I) (M := M) g r s i α p :
                    EuclN → ℝ) y) := by
    funext y
    rw [hFcomp_def]
    simp only [Fintype.sum_prod_type]
  have h_part_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s, Fpart x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (weightedGradFactor (I := I) (M := M)
                      g r s α P₀ l P Q k p) y *
                  (partialLpLimit (I := I) (M := M) g r s i α p l :
                    EuclN → ℝ) y) := by
    funext y
    rw [hFpart_def]
    simp only [Fintype.sum_prod_type]
  have h_part_atom_eq : ∑ pl : TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E), wkpNorm (d := Module.finrank ℝ E) K 2
        (partAtom pl) Ω
      = ∑ p : TensorCompIdx (E := E) r s,
          ∑ l' : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α p l' :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              Ω := by
    rw [Fintype.sum_prod_type]
  refine ⟨max
      (Ccomp * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
      (Cpart * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card),
    le_trans (by positivity) (le_max_left _ _), ?_⟩
  set Cmax : ℝ := max
      (Ccomp * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
      (Cpart * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
    with hCmax_def
  have hcomp : wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s, Fcomp x y) Ω
      ≤ ENNReal.ofReal Cmax *
        ∑ p : TensorCompIdx (E := E) r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((componentLpLimit (I := I) (M := M)
                g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            Ω := by
    refine h_comp_bound.trans ?_
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left _ _)) (zero_le _)
  have hpart : wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s, Fpart x y) Ω
      ≤ ENNReal.ofReal Cmax *
        ∑ p : TensorCompIdx (E := E) r s,
          ∑ l' : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α p l' :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              Ω := by
    rw [← h_part_atom_eq]
    refine h_part_bound.trans ?_
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_right _ _)) (zero_le _)
  have h_comp_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ x : TensorCompIdx (E := E) r s
        × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
        × TensorCompIdx (E := E) r s, Fcomp x y) Ω :=
    memWkp_finsetSum (I := I) (M := M) _ (fun x hx => (h_comp_data x hx).1)
  have h_part_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ x : TensorCompIdx (E := E) r s
        × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
        × TensorCompIdx (E := E) r s, Fpart x y) Ω :=
    memWkp_finsetSum (I := I) (M := M) _ (fun x hx => (h_part_data x hx).1)
  rw [show (weightedGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ l : EuclN → ℝ)
      = (fun y => (∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (euclidPartial (E := E) l
                        (weightedGradFactor (I := I) (M := M)
                          g r s α P₀ l P Q k p)) y *
                    (componentLpLimit (I := I) (M := M) g r s i α p :
                      EuclN → ℝ) y)
          + ∑ P : TensorCompIdx (E := E) r s,
              ∑ Q : TensorCompIdx (E := E) r s,
                ∑ k : Fin (Module.finrank ℝ E),
                  ∑ p : TensorCompIdx (E := E) r s,
                    Set.indicator (chartPouKernel (I := I) (M := M) α)
                        (weightedGradFactor (I := I) (M := M)
                          g r s α P₀ l P Q k p) y *
                      (partialLpLimit (I := I) (M := M) g r s i α p l :
                        EuclN → ℝ) y) from rfl]
  have h_bridge : (fun y => (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (euclidPartial (E := E) l
                      (weightedGradFactor (I := I) (M := M)
                        g r s α P₀ l P Q k p)) y *
                  (componentLpLimit (I := I) (M := M) g r s i α p :
                    EuclN → ℝ) y)
        + ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (weightedGradFactor (I := I) (M := M)
                        g r s α P₀ l P Q k p) y *
                    (partialLpLimit (I := I) (M := M) g r s i α p l :
                      EuclN → ℝ) y)
      = (fun y => (∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × TensorCompIdx (E := E) r s, Fcomp x y)
          + ∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
              Fpart x y) := by
    funext y
    rw [← congrFun h_comp_eq y, ← congrFun h_part_eq y]
  rw [h_bridge]
  calc
    wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => (∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s, Fcomp x y)
        + ∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
            × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
            Fpart x y) Ω
        ≤ wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ x : TensorCompIdx (E := E) r s
                × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
                × TensorCompIdx (E := E) r s, Fcomp x y) Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ x : TensorCompIdx (E := E) r s
                × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
                × TensorCompIdx (E := E) r s, Fpart x y) Ω :=
        wkpNorm_add_le (d := Module.finrank ℝ E)
          (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_comp_memWkp h_part_memWkp
    _ ≤ ENNReal.ofReal Cmax *
          (∑ p : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((componentLpLimit (I := I) (M := M)
                  g r s i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y) Ω)
        + ENNReal.ofReal Cmax *
          (∑ p : TensorCompIdx (E := E) r s,
            ∑ l' : Fin (Module.finrank ℝ E),
              wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((partialLpLimit (I := I) (M := M)
                    g r s i α p l' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) Ω) :=
        add_le_add hcomp hpart
    _ = ENNReal.ofReal Cmax *
          ((∑ p : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((componentLpLimit (I := I) (M := M)
                    g r s i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) Ω)
            + (∑ p : TensorCompIdx (E := E) r s,
                ∑ l' : Fin (Module.finrank ℝ E),
                  wkpNorm (d := Module.finrank ℝ E) K 2
                    (fun y => ((partialLpLimit (I := I) (M := M)
                        g r s i α p l' :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) y) Ω)) := by
      rw [mul_add]

end LowerOrderWkpNormBoundsUnconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
