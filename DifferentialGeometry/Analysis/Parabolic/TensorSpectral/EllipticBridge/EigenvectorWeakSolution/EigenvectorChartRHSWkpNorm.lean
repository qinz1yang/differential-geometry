import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHSMemWkp
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartCrossRotationWkpNormBounds
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartLowerOrderWkpNormBounds
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartCrossRightDivWkpNormBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorDifferentiatedRHS

/-!
# The order-`K` `wkpNorm`-graded bound for the eigenvector chart right-hand side

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i` with resolvent eigenvalue `μ := i.fst.val`, a chart center `α : M`, and a
component multi-index `P₀`, the chart-Euclidean right-hand side
`eigenvectorChartRHS g r s i α P₀` of the eigenvector
weak-solution assembly is the explicit `densityOnEuclid`-and-`C^∞`-coefficient-
weighted seven-term bracket combination scaled overall by `μ⁻¹`.

This file records the order-`K` iterated-Sobolev (`wkpNorm`) twin of the
order-`0` weighted-`eLpNorm` bound `eigenvectorChartRHS_eLpNorm_le`: given the
order-`(K + 1)` partition-of-unity regularity input `h_pou`, there is a
nonnegative constant `C` with

```
wkpNorm K 2 (eigenvectorChartRHS g r s i α P₀) (chartTargetEuclid α)
  ≤ ENNReal.ofReal (μ⁻¹ * C) * <AGGREGATE>,
```

where `<AGGREGATE>` is the honest finite sum of the order-`K` `wkpNorm`s of the
source quantities of the bracket — the order-`K` `wkpNorm`-graded analogue of
the order-`0` `eLpNorm` aggregate:

* the canonical eigenvector chart component `eigenvectorChartComponentFun`;
* the cross-left limit object's transport aggregate — the double sum, over the
  transport chart centres of `α` and of each transport centre, of the
  order-`(K + 1)` resolvent-inclusion partition-of-unity chart-component norms;
* the cross-right limit object's transport aggregate — the double sum, over the
  transport chart centres of `α`, of the order-`K` resolvent-inclusion
  partition-of-unity chart-component norms;
* the chart-partial atoms `partialLpLimit` (summed over component multi-index
  and chart direction);
* the chart-component atoms `componentLpLimit` (summed over the component
  multi-indices);
* the cutoff chart-component limit objects `crossRightLimitComponent` (summed
  over the component multi-indices);
* the cutoff chart-partial atoms `cutoffPartialLpLimit` (summed over component
  multi-index and chart direction).

## Strategy

The bracket is the `μ⁻¹`-scalar multiple of a seven-term `+`/`-` combination of
functions `EuclN → ℝ`. By the scalar homogeneity `wkpNorm K (c • f) = ‖c‖ₑ ·
wkpNorm K f` the overall `wkpNorm` is `‖μ⁻¹‖ₑ` times the `wkpNorm` of the
bracket, and `‖μ⁻¹‖ₑ = ENNReal.ofReal μ⁻¹` since the resolvent eigenvalue lies
in `(0, 1]`.

Iterated Minkowski (`wkpNorm_add_le` / `wkpNorm_sub_le`) bounds the `wkpNorm` of
the seven-term bracket by the sum of the `wkpNorm`s of the seven terms — each
bracket term is `W^{K,2}` by its companion `eigenvectorChartRHS_summand…_memWkp`
lemma. Each term is then bounded by a constant times a sub-aggregate of the
source quantities:

* the canonical eigenvector chart-component term is the source quantity itself;
* the two cross-Leibniz double-sum terms have, per summand, a `C^∞` coefficient
  product and a `W^{K,2}` cross-limit object that vanishes almost everywhere off
  the compact cutoff chart kernel; the smooth-coefficient `wkpNorm` bound
  `wkpNorm_smoothCoef_mul_aeZeroFactor_le` controls the summand and the
  companion lemmas `wkpNorm_crossLeftLimitComponent_le` /
  `wkpNorm_crossRightLimitComponent_le` control the cross-limit object;
* the two lower-order coefficient-limit terms are bounded directly by the
  companion lemmas `wkpNorm_covPrincipalRotationCoeffLimit_le` and
  `wkpNorm_covLowerOrderRotationValueCoeffLimit_le`;
* the two divergence-limit terms are products of the `C^∞` reciprocal chart
  density `1 / densityOnEuclid g α` with a divergence limit; the
  smooth-coefficient `wkpNorm` bound and the companion lemmas
  `wkpNorm_weightedGradCoeffDivLimit_le` and
  `wkpNorm_crossRightGradCoeffDivLimit_le` control them.

Every sub-aggregate is dominated by the full aggregate (the order-`K` `wkpNorm`s
are nonnegative `ℝ≥0∞` quantities), so the seven per-term constants and the
finite-sum multiplicities fold into a single nonnegative constant `C`.

## Main result

* `eigenvectorChartRHS_wkpNorm_le` — the order-`K` `wkpNorm`-graded bound for the
  eigenvector chart right-hand side.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

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

section SmoothCoefBound

set_option linter.unusedSectionVars false in
/-- **Quantitative smooth-coefficient `wkpNorm` bound with ae-vanishing factor.**
For a coefficient `coef : EuclN → ℝ` that is `C^∞` on the open Euclidean chart
target, a compact kernel `Kkern` inside the chart target, and a factor that is
`MemWkp K 2` on the chart target and vanishes almost everywhere off `Kkern`, the
pointwise product `coef · factor` lies in `MemWkp K 2` on the chart target and
there is a nonnegative constant `C` with

```
wkpNorm K 2 (fun y => coef y * factor y) (chartTargetEuclid α)
  ≤ ENNReal.ofReal C * wkpNorm K 2 factor (chartTargetEuclid α).
```

The coefficient is cut off to a globally `C^∞` compactly-supported
representative `χ · coef`; a uniform bound on its iterated derivatives up to
order `K` feeds `MemWkp.smul_smooth_bounded` and the quantitative Leibniz bound
`wkpNorm_smul_smooth_bounded_le`, and the cut-off product agrees almost
everywhere with `coef · factor`. -/
private lemma wkpNorm_smoothCoef_mul_aeZeroFactor_le
    (α : M) (K : ℕ)
    {coef factor : EuclN → ℝ}
    {Kkern : Set EuclN}
    (hKkern_compact : IsCompact Kkern)
    (hKkern_in : Kkern ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α))
    (hfactor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 factor
      (chartTargetEuclid (I := I) (M := M) α))
    (hfactor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ Kkern → factor y = 0) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => coef y * factor y)
        (chartTargetEuclid (I := I) (M := M) α) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => coef y * factor y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            wkpNorm (d := Module.finrank ℝ E) K 2 factor
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  obtain ⟨δ, χ, hδ_pos, hδ_in, hχ_smooth, hχ_cs, _hχ_range, hχ_one, hχ_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      hKkern_compact hΩ_open hKkern_in
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
      hC₀_nn (fun j hj y _hy => hC₀_bd y j hj)
  set Cδ : Set EuclN := Metric.cthickening δ Kkern with hCδ_def
  have hCδ_closed : IsClosed Cδ := Metric.isClosed_cthickening
  have hCδ_meas : MeasurableSet Cδ := hCδ_closed.measurableSet
  have hfactor_ae_zero' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ Kkern → factor y = 0 := by
    have h := hfactor_ae_zero
    rw [chartL2Measure] at h
    exact h
  have h_eq_on_inter : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict (Ω ∩ Cδ)]
      (fun y => coef y * factor y) := by
    refine (ae_restrict_iff' (hΩ_meas.inter hCδ_meas)).mpr ?_
    refine Filter.Eventually.of_forall fun y hy => ?_
    have hχy : χ y = 1 := hχ_one y hy.2
    change (χ y * coef y) * factor y = coef y * factor y
    rw [hχy]; ring
  have hKkern_in_Cδ : Kkern ⊆ Cδ := Metric.self_subset_cthickening _
  have h_eq_on_diff : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict (Ω \ Cδ)]
      (fun y => coef y * factor y) := by
    have h_diff_in_Ω : (volume : Measure EuclN).restrict (Ω \ Cδ) ≤
        (volume : Measure EuclN).restrict Ω :=
      Measure.restrict_mono Set.diff_subset le_rfl
    have h_factor_diff : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
        factor y = 0 := by
      have h_lift : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
          y ∉ Kkern → factor y = 0 :=
        (Measure.absolutelyContinuous_of_le h_diff_in_Ω).ae_le hfactor_ae_zero'
      have h_off : ∀ᵐ _y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
          _y ∈ Ω \ Cδ := ae_restrict_mem (hΩ_meas.diff hCδ_meas)
      filter_upwards [h_lift, h_off] with y hy hy_mem
      exact hy (fun hyK => hy_mem.2 (hKkern_in_Cδ hyK))
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
  have h_ae_eq : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => coef y * factor y) := by
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict ((Ω ∩ Cδ) ∪ (Ω \ Cδ)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, Measure.restrict_union h_disj h_diff_meas]
    exact (ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  have h_prod_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (χ y * coef y) * factor y) Ω :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hχ_coef_smooth
      (fun j hj y _hy => hC₀_bd y j hj) hfactor_memWkp
  have h_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω :=
    (MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).mp h_prod_memWkp
  refine ⟨h_memWkp, Kc, le_of_lt hKc_pos, ?_⟩
  have h_norm_eq : wkpNorm (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω
      = wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => (χ y * coef y) * factor y) Ω :=
    (wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).symm
  rw [h_norm_eq]
  exact hKc_bd hfactor_memWkp

set_option linter.unusedSectionVars false in
/-- **`MemWkp` is closed under finite `Finset`-indexed sums.** A finite-`Finset`
sum of `MemWkp k 2` functions on an open set is also `MemWkp k 2`. -/
private lemma memWkpFinsetSum
    {k : ℕ} {Ω : Set EuclN} (hΩ : IsOpen Ω)
    {ι : Type*} (S : Finset ι) (f : ι → EuclN → ℝ)
    (hf : ∀ j ∈ S, MemWkp (d := Module.finrank ℝ E) k 2 (f j) Ω) :
    MemWkp (d := Module.finrank ℝ E) k 2
      (fun y => ∑ j ∈ S, f j y) Ω := by
  classical
  induction S using Finset.induction with
  | empty =>
      simpa using MemWkp_zero_fun (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ
  | insert a t ha iht =>
      have h_split : (fun y => ∑ j ∈ insert a t, f j y) =
          (fun y => f a y + ∑ j ∈ t, f j y) := by
        funext y; rw [Finset.sum_insert ha]
      rw [h_split]
      refine MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ
        (hf a (Finset.mem_insert_self a t)) ?_
      exact iht (fun j hj => hf j (Finset.mem_insert_of_mem hj))

end SmoothCoefBound

set_option linter.unusedSectionVars false in
/-- The reciprocal `1 / densityOnEuclid g α` of the chart density is `C^∞` on the
open Euclidean chart target: the chart density is `C^∞`
(`densityOnEuclid_contDiffOn`) and strictly positive (`densityOnEuclid_pos`)
there, so the quotient `1 / densityOnEuclid g α` is `C^∞`. -/
private lemma one_div_densityOnEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ ∞ (fun y => 1 / densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  contDiffOn_const.div (densityOnEuclid_contDiffOn (I := I) g α)
    (fun _ hy => (densityOnEuclid_pos (I := I) g α hy).ne')

section Aggregation

set_option linter.unusedSectionVars false in
/-- A finite indexed family of `W^{K,2}` summands on an open set, each
`wkpNorm`-bounded by `ENNReal.ofReal Cⱼ` times a fixed aggregate quantity `A`,
has its summed `wkpNorm` bounded by `ENNReal.ofReal` of an explicit nonnegative
constant times `A`. -/
private lemma wkpNorm_sum_le_const_mul_aggregate
    {ι : Type*} [Fintype ι] {K : ℕ} {Ω : Set EuclN} (hΩ : IsOpen Ω)
    (F : ι → EuclN → ℝ) (A : ℝ≥0∞)
    (hF : ∀ j : ι, MemWkp (d := Module.finrank ℝ E) K 2 (F j) Ω)
    (hbd : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2 (F j) Ω ≤ ENNReal.ofReal C * A) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2 (fun y => ∑ j : ι, F j y) Ω
        ≤ ENNReal.ofReal C * A := by
  classical
  choose Cf hCf_nn hCf using hbd
  refine ⟨(∑ j : ι, Cf j) * (Fintype.card ι : ℝ),
    mul_nonneg (Finset.sum_nonneg (fun j _ => hCf_nn j)) (by positivity), ?_⟩
  have h_tri : wkpNorm (d := Module.finrank ℝ E) K 2
      (fun y => ∑ j : ι, F j y) Ω ≤ ∑ j : ι,
        wkpNorm (d := Module.finrank ℝ E) K 2 (F j) Ω :=
    wkpNorm_sum_le (d := Module.finrank ℝ E) (by norm_num) hΩ
      (Finset.univ : Finset ι) F (fun j _ => hF j)
  have h_step : ∑ j : ι, wkpNorm (d := Module.finrank ℝ E) K 2 (F j) Ω
      ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine (hCf j).trans ?_
    gcongr
    exact Finset.single_le_sum (fun k _ => hCf_nn k) (Finset.mem_univ j)
  have h_const : ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A
      = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_cast : (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)
      = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) := by
    rw [mul_comm (∑ j : ι, Cf j), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast]
  calc
    wkpNorm (d := Module.finrank ℝ E) K 2 (fun y => ∑ j : ι, F j y) Ω
        ≤ ∑ j : ι, wkpNorm (d := Module.finrank ℝ E) K 2 (F j) Ω := h_tri
    _ ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A := h_step
    _ = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A) := h_const
    _ = ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)) * A := by
        rw [mul_assoc]
    _ = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) * A := by
        rw [h_cast]

end Aggregation

section Domination

/-- Each of the seven summands of a seven-fold `ℝ≥0∞` sum is dominated by the
sum. -/
private lemma le_sevenSum (a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ℝ≥0∞) :
    a₁ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧
      a₂ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧
      a₃ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧
      a₄ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧
      a₅ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧
      a₆ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ∧
      a₇ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc a₁ ≤ a₁ + a₂ := le_self_add
      _ ≤ a₁ + a₂ + a₃ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ := le_self_add
  · calc a₂ ≤ a₁ + a₂ := le_add_self
      _ ≤ a₁ + a₂ + a₃ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ := le_self_add
  · calc a₃ ≤ a₁ + a₂ + a₃ := le_add_self
      _ ≤ a₁ + a₂ + a₃ + a₄ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ := le_self_add
  · calc a₄ ≤ a₁ + a₂ + a₃ + a₄ := le_add_self
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ := le_self_add
  · calc a₅ ≤ a₁ + a₂ + a₃ + a₄ + a₅ := le_add_self
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_self_add
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ := le_self_add
  · calc a₆ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ := le_add_self
      _ ≤ a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ := le_self_add
  · exact le_add_self

end Domination

/-- The conversion `ENNReal.ofReal 2 = (2 : ℝ≥0∞)`. -/
private lemma ofReal_two : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.ofReal_natCast]
  norm_num

section BracketBound

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)

set_option linter.unusedSectionVars false in
/-- **The triangle inequality for `wkpNorm` under subtraction.** The order-`K`
`wkpNorm` is invariant under negation, so `wkpNorm_add_le` for `u + (-v)`
delivers the subtraction analogue. -/
private lemma wkpNorm_sub_le
    {Ω : Set EuclN} (hΩ : IsOpen Ω) {u v : EuclN → ℝ}
    (hu : MemWkp (d := Module.finrank ℝ E) K 2 u Ω)
    (hv : MemWkp (d := Module.finrank ℝ E) K 2 v Ω) :
    wkpNorm (d := Module.finrank ℝ E) K 2 (fun y => u y - v y) Ω ≤
      wkpNorm (d := Module.finrank ℝ E) K 2 u Ω +
        wkpNorm (d := Module.finrank ℝ E) K 2 v Ω := by
  classical
  have h_fun : (fun y => u y - v y) = (fun y => u y + (fun y => - v y) y) := by
    funext y; ring
  rw [h_fun]
  have hv_neg : MemWkp (d := Module.finrank ℝ E) K 2 (fun y => - v y) Ω :=
    MemWkp.neg (d := Module.finrank ℝ E) (by norm_num) hΩ hv
  refine le_trans (wkpNorm_add_le (d := Module.finrank ℝ E)
    (by norm_num) hΩ hu hv_neg) ?_
  have h_neg_eq : wkpNorm (d := Module.finrank ℝ E) K 2 (fun y => - v y) Ω =
      wkpNorm (d := Module.finrank ℝ E) K 2 v Ω := by
    have h_smul : (fun y => - v y) = (fun y => (-1 : ℝ) * v y) := by
      funext y; ring
    rw [h_smul, wkpNorm_const_smul (d := Module.finrank ℝ E)
      (by norm_num) hΩ hv (-1)]
    simp
  rw [h_neg_eq]

end BracketBound

section MainBound

set_option linter.unusedSectionVars false in
/-- The resolvent eigenvalue `μ := i.fst.val` is strictly positive: the
eigenspace at `μ` is non-trivial, so it contains a non-zero eigenvector, and the
resolvent eigenvalues lie in the unit interval `(0, 1]`. -/
private lemma eigenIdx_val_pos
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 < i.fst.val := by
  obtain ⟨u, hu_mem, hu_ne⟩ := i.fst.hasEigenvalue.exists_hasEigenvector
  have hu_in : u ∈ tensorResolventEigenspace
      (I := I) (M := M) g r s i.fst.val := hu_mem
  exact (tensorResolvent_eigenvalue_mem_unit_interval
    (I := I) (M := M) g r s hu_in hu_ne).1

end MainBound

section UniformBounds

set_option linter.unusedSectionVars false in
/-- **Factor-uniform quantitative smooth-coefficient `wkpNorm` bound with
ae-vanishing factor.** The `factor`-uniform companion of
`wkpNorm_smoothCoef_mul_aeZeroFactor_le`: for a coefficient `coef : EuclN → ℝ`
that is `C^∞` on the open Euclidean chart target and a compact kernel `Kkern`
inside the chart target, there is a *single* nonnegative constant `C` such that
for *every* factor that is `MemWkp K 2` on the chart target and vanishes almost
everywhere off `Kkern`, the pointwise product `coef · factor` lies in
`MemWkp K 2` and `wkpNorm K 2 (coef · factor) ≤ ENNReal.ofReal C · wkpNorm K 2
factor`. The `∀ factor` quantifier moves inside the `∃ C`. -/
private lemma wkpNorm_smoothCoef_mul_aeZeroFactor_le_uniform
    (α : M) (K : ℕ)
    {coef : EuclN → ℝ}
    {Kkern : Set EuclN}
    (hKkern_compact : IsCompact Kkern)
    (hKkern_in : Kkern ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ factor : EuclN → ℝ,
        MemWkp (d := Module.finrank ℝ E) K 2 factor
            (chartTargetEuclid (I := I) (M := M) α) →
        (∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
          y ∉ Kkern → factor y = 0) →
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
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  obtain ⟨δ, χ, hδ_pos, hδ_in, hχ_smooth, hχ_cs, _hχ_range, hχ_one, hχ_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      hKkern_compact hΩ_open hKkern_in
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
      hC₀_nn (fun j hj y _hy => hC₀_bd y j hj)
  refine ⟨Kc, le_of_lt hKc_pos, fun factor hfactor_memWkp hfactor_ae_zero => ?_⟩
  set Cδ : Set EuclN := Metric.cthickening δ Kkern with hCδ_def
  have hCδ_closed : IsClosed Cδ := Metric.isClosed_cthickening
  have hCδ_meas : MeasurableSet Cδ := hCδ_closed.measurableSet
  have hfactor_ae_zero' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ Kkern → factor y = 0 := by
    have h := hfactor_ae_zero
    rw [chartL2Measure] at h
    exact h
  have h_eq_on_inter : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict (Ω ∩ Cδ)]
      (fun y => coef y * factor y) := by
    refine (ae_restrict_iff' (hΩ_meas.inter hCδ_meas)).mpr ?_
    refine Filter.Eventually.of_forall fun y hy => ?_
    have hχy : χ y = 1 := hχ_one y hy.2
    change (χ y * coef y) * factor y = coef y * factor y
    rw [hχy]; ring
  have hKkern_in_Cδ : Kkern ⊆ Cδ := Metric.self_subset_cthickening _
  have h_eq_on_diff : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict (Ω \ Cδ)]
      (fun y => coef y * factor y) := by
    have h_diff_in_Ω : (volume : Measure EuclN).restrict (Ω \ Cδ) ≤
        (volume : Measure EuclN).restrict Ω :=
      Measure.restrict_mono Set.diff_subset le_rfl
    have h_factor_diff : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
        factor y = 0 := by
      have h_lift : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
          y ∉ Kkern → factor y = 0 :=
        (Measure.absolutelyContinuous_of_le h_diff_in_Ω).ae_le hfactor_ae_zero'
      have h_off : ∀ᵐ _y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
          _y ∈ Ω \ Cδ := ae_restrict_mem (hΩ_meas.diff hCδ_meas)
      filter_upwards [h_lift, h_off] with y hy hy_mem
      exact hy (fun hyK => hy_mem.2 (hKkern_in_Cδ hyK))
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
  have h_ae_eq : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => coef y * factor y) := by
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict ((Ω ∩ Cδ) ∪ (Ω \ Cδ)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, Measure.restrict_union h_disj h_diff_meas]
    exact (ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  have h_prod_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (χ y * coef y) * factor y) Ω :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hχ_coef_smooth
      (fun j hj y _hy => hC₀_bd y j hj) hfactor_memWkp
  have h_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω :=
    (MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).mp h_prod_memWkp
  refine ⟨h_memWkp, ?_⟩
  have h_norm_eq : wkpNorm (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω
      = wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => (χ y * coef y) * factor y) Ω :=
    (wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).symm
  rw [h_norm_eq]
  exact hKc_bd hfactor_memWkp

set_option linter.unusedSectionVars false in
/-- **Eigenbasis-uniform finite-sum aggregation.** A finite indexed family `F`
of `W^{K,2}` summands on an open set, each `wkpNorm`-bounded — uniformly over a
parameter `δ` — by `ENNReal.ofReal Cⱼ` times a `δ`-indexed aggregate `A d`, has
its summed `wkpNorm` bounded, uniformly over `δ`, by `ENNReal.ofReal` of an
explicit nonnegative constant times `A d`. The single constant — the sum of the
per-summand constants times the index cardinality — is hoisted before the
`∀ d`. -/
private lemma wkpNorm_sum_le_const_mul_aggregate_uniform
    {ι : Type*} [Fintype ι] {δ : Type*} {K : ℕ} {Ω : Set EuclN} (hΩ : IsOpen Ω)
    (F : ι → δ → EuclN → ℝ) (A : δ → ℝ≥0∞)
    (hF : ∀ (j : ι) (d : δ),
      MemWkp (d := Module.finrank ℝ E) K 2 (F j d) Ω)
    (hbd : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧
      ∀ d : δ, wkpNorm (d := Module.finrank ℝ E) K 2 (F j d) Ω
        ≤ ENNReal.ofReal C * A d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ d : δ, wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ j : ι, F j d y) Ω
        ≤ ENNReal.ofReal C * A d := by
  classical
  choose Cf hCf_nn hCf using hbd
  refine ⟨(∑ j : ι, Cf j) * (Fintype.card ι : ℝ),
    mul_nonneg (Finset.sum_nonneg (fun j _ => hCf_nn j)) (by positivity),
    fun d => ?_⟩
  have h_tri : wkpNorm (d := Module.finrank ℝ E) K 2
      (fun y => ∑ j : ι, F j d y) Ω ≤ ∑ j : ι,
        wkpNorm (d := Module.finrank ℝ E) K 2 (F j d) Ω :=
    wkpNorm_sum_le (d := Module.finrank ℝ E) (by norm_num) hΩ
      (Finset.univ : Finset ι) (fun j => F j d) (fun j _ => hF j d)
  have h_step : ∑ j : ι, wkpNorm (d := Module.finrank ℝ E) K 2 (F j d) Ω
      ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A d := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine (hCf j d).trans ?_
    gcongr
    exact Finset.single_le_sum (fun k _ => hCf_nn k) (Finset.mem_univ j)
  have h_const : ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A d
      = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A d) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_cast : (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)
      = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) := by
    rw [mul_comm (∑ j : ι, Cf j), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast]
  calc
    wkpNorm (d := Module.finrank ℝ E) K 2 (fun y => ∑ j : ι, F j d y) Ω
        ≤ ∑ j : ι, wkpNorm (d := Module.finrank ℝ E) K 2 (F j d) Ω := h_tri
    _ ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A d := h_step
    _ = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A d) := h_const
    _ = ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)) * A d := by
        rw [mul_assoc]
    _ = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) * A d := by
        rw [h_cast]

end UniformBounds

section Unconditional

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

/-- Chart-locality-free twin of `PouRegularity`. -/
private def PouRegularity
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ) : Prop :=
  ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
    MemWkp (d := Module.finrank ℝ E) (K + 1) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) β)

section BracketTermsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s)

/-- Chart-locality-free twin of `rhsTerm1`. -/
private def rhsTerm1 : EuclN → ℝ :=
  fun y =>
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i) α P₀ :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y

/-- Chart-locality-free twin of `rhsTerm2`. -/
private def rhsTerm2 : EuclN → ℝ :=
  fun y => ∑ P : TensorCompIdx (E := E) r (s + 1),
    ∑ Q : TensorCompIdx (E := E) r (s + 1),
      (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossLeftLimitComponent (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y

/-- Chart-locality-free twin of `rhsTerm3`. -/
private def rhsTerm3 : EuclN → ℝ :=
  fun y => ∑ P : TensorCompIdx (E := E) r s,
    ∑ Q : TensorCompIdx (E := E) r s,
      (covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossRightLimitComponent (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y

/-- Chart-locality-free twin of `rhsTerm4`. -/
private def rhsTerm4 : EuclN → ℝ :=
  covPrincipalRotationCoeffLimit (I := I) (M := M) g r s i α P₀

/-- Chart-locality-free twin of `rhsTerm5`. -/
private def rhsTerm5 : EuclN → ℝ :=
  covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
    g r s i α P₀

/-- Chart-locality-free twin of `rhsTerm6`. -/
private def rhsTerm6 : EuclN → ℝ :=
  fun y => (1 / densityOnEuclid (I := I) g α y) *
    (∑ l : Fin (Module.finrank ℝ E),
      weightedGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ l y)

/-- Chart-locality-free twin of `rhsTerm7`. -/
private def rhsTerm7 : EuclN → ℝ :=
  fun y => (1 / densityOnEuclid (I := I) g α y) *
    crossRightGradCoeffDivLimit (I := I) (M := M) g r s i α P₀ y

/-- Chart-locality-free twin of `rhsBracket`. -/
private def rhsBracket : EuclN → ℝ :=
  rhsTerm1 (I := I) (M := M) g r s i α P₀ -
      rhsTerm2 (I := I) (M := M) g r s i α P₀ +
      rhsTerm3 (I := I) (M := M) g r s i α P₀ -
      rhsTerm4 (I := I) (M := M) g r s i α P₀ -
      rhsTerm5 (I := I) (M := M) g r s i α P₀ +
      rhsTerm6 (I := I) (M := M) g r s i α P₀ -
      rhsTerm7 (I := I) (M := M) g r s i α P₀

set_option linter.unusedSectionVars false in
/-- Chart-locality-free twin of `eigenvectorChartRHS_eq_smul_bracket`. -/
private lemma eigenvectorChartRHS_eq_smul_bracket :
    eigenvectorChartRHS (I := I) (M := M) g r s i α P₀
      = fun y => (i.fst.val)⁻¹ *
          rhsBracket (I := I) (M := M) g r s i α P₀ y := by
  funext y
  simp only [eigenvectorChartRHS, rhsBracket,
    rhsTerm1, rhsTerm2, rhsTerm3,
    rhsTerm4, rhsTerm5, rhsTerm6,
    rhsTerm7, Pi.sub_apply, Pi.add_apply]

end BracketTermsUnconditional

section TermMemWkpUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)

/-- Chart-locality-free twin of `rhsTerm1_memWkp`. -/
private lemma rhsTerm1_memWkp
    (h_pou : PouRegularity (I := I) (M := M) g r s i K) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (rhsTerm1 (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold rhsTerm1
  exact eigenvectorChartRHS_summand1_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou

/-- Chart-locality-free twin of `rhsTerm2_memWkp`. -/
private lemma rhsTerm2_memWkp
    (h_pou : PouRegularity (I := I) (M := M) g r s i K) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (rhsTerm2 (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold rhsTerm2
  exact eigenvectorChartRHS_summand2_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou

/-- Chart-locality-free twin of `rhsTerm3_memWkp`. -/
private lemma rhsTerm3_memWkp
    (h_pou : PouRegularity (I := I) (M := M) g r s i K) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (rhsTerm3 (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold rhsTerm3
  exact eigenvectorChartRHS_summand3_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou

/-- Chart-locality-free twin of `rhsTerm4_memWkp`. -/
private lemma rhsTerm4_memWkp
    (h_pou : PouRegularity (I := I) (M := M) g r s i K) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (rhsTerm4 (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold rhsTerm4
  exact eigenvectorChartRHS_summand4_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou

/-- Chart-locality-free twin of `rhsTerm5_memWkp`. -/
private lemma rhsTerm5_memWkp
    (h_pou : PouRegularity (I := I) (M := M) g r s i K) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (rhsTerm5 (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold rhsTerm5
  exact eigenvectorChartRHS_summand5_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou

/-- Chart-locality-free twin of `rhsTerm6_memWkp`. -/
private lemma rhsTerm6_memWkp
    (h_pou : PouRegularity (I := I) (M := M) g r s i K) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (rhsTerm6 (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold rhsTerm6
  exact eigenvectorChartRHS_summand6_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou

/-- Chart-locality-free twin of `rhsTerm7_memWkp`. -/
private lemma rhsTerm7_memWkp
    (h_pou : PouRegularity (I := I) (M := M) g r s i K) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (rhsTerm7 (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold rhsTerm7
  exact eigenvectorChartRHS_summand7_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou

end TermMemWkpUnconditional

section AggregateUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)

/-- Chart-locality-free twin of `resInclNorm`. -/
private def resInclNorm (N : ℕ) (β : M)
    (Q : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  wkpNorm (d := Module.finrank ℝ E) N 2
    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i))
        β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
    (chartTargetEuclid (I := I) (M := M) β)

/-- Chart-locality-free twin of `aggrUchart`. -/
private def aggrUchart : ℝ≥0∞ :=
  wkpNorm (d := Module.finrank ℝ E) K 2
    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i) α P₀ :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
    (chartTargetEuclid (I := I) (M := M) α)

/-- Chart-locality-free twin of `aggrCrossLeft`. -/
private def aggrCrossLeft : ℝ≥0∞ :=
  ∑ β ∈ transportChartCenters (I := I) (M := M) α,
    ((∑ Q : TensorCompIdx (E := E) r s,
        resInclNorm (I := I) (M := M) g r s i (K + 1) β Q)
      + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
          ∑ Q : TensorCompIdx (E := E) r s,
            resInclNorm (I := I) (M := M) g r s i (K + 1) β' Q)

/-- Chart-locality-free twin of `aggrCrossRight`. -/
private def aggrCrossRight : ℝ≥0∞ :=
  ∑ β ∈ transportChartCenters (I := I) (M := M) α,
    ∑ Q : TensorCompIdx (E := E) r s,
      resInclNorm (I := I) (M := M) g r s i K β Q

/-- Chart-locality-free twin of `aggrPartial`. -/
private def aggrPartial : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r s,
    ∑ k : Fin (Module.finrank ℝ E),
      wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((partialLpLimit (I := I) (M := M)
            g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)

/-- Chart-locality-free twin of `aggrComponent`. -/
private def aggrComponent : ℝ≥0∞ :=
  ∑ p : TensorCompIdx (E := E) r s,
    wkpNorm (d := Module.finrank ℝ E) K 2
      (fun y => ((componentLpLimit (I := I) (M := M)
          g r s i α p :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α)

/-- Chart-locality-free twin of `aggrCrossRightLimit`. -/
private def aggrCrossRightLimit : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r s,
    wkpNorm (d := Module.finrank ℝ E) K 2
      (fun y => ((crossRightLimitComponent (I := I) (M := M)
          g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α)

/-- Chart-locality-free twin of `aggrCutoffPartial`. -/
private def aggrCutoffPartial : ℝ≥0∞ :=
  ∑ P : TensorCompIdx (E := E) r s,
    ∑ l : Fin (Module.finrank ℝ E),
      wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
            g r s i α P l :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)

/-- Chart-locality-free twin of `wkpRhsAggregate`. -/
private def wkpRhsAggregate : ℝ≥0∞ :=
  aggrUchart (I := I) (M := M) g r s i α P₀ K +
    aggrCrossLeft (I := I) (M := M) g r s i α K +
    aggrCrossRight (I := I) (M := M) g r s i α K +
    aggrPartial (I := I) (M := M) g r s i α K +
    aggrComponent (I := I) (M := M) g r s i α K +
    aggrCrossRightLimit (I := I) (M := M) g r s i α K +
    aggrCutoffPartial (I := I) (M := M) g r s i α K

end AggregateUnconditional

section DominationUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)

set_option linter.unusedSectionVars false in
/-- Chart-locality-free twin of `aggrUchart_le`. -/
private lemma aggrUchart_le :
    aggrUchart (I := I) (M := M) g r s i α P₀ K
      ≤ wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  rw [wkpRhsAggregate]; exact (le_sevenSum _ _ _ _ _ _ _).1

set_option linter.unusedSectionVars false in
/-- Chart-locality-free twin of `aggrCrossLeft_le`. -/
private lemma aggrCrossLeft_le :
    aggrCrossLeft (I := I) (M := M) g r s i α K
      ≤ wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  rw [wkpRhsAggregate]; exact (le_sevenSum _ _ _ _ _ _ _).2.1

set_option linter.unusedSectionVars false in
/-- Chart-locality-free twin of `aggrCrossRight_le`. -/
private lemma aggrCrossRight_le :
    aggrCrossRight (I := I) (M := M) g r s i α K
      ≤ wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  rw [wkpRhsAggregate]; exact (le_sevenSum _ _ _ _ _ _ _).2.2.1

set_option linter.unusedSectionVars false in
/-- Chart-locality-free twin of `aggrPartial_le`. -/
private lemma aggrPartial_le :
    aggrPartial (I := I) (M := M) g r s i α K
      ≤ wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  rw [wkpRhsAggregate]; exact (le_sevenSum _ _ _ _ _ _ _).2.2.2.1

set_option linter.unusedSectionVars false in
/-- Chart-locality-free twin of `aggrComponent_le`. -/
private lemma aggrComponent_le :
    aggrComponent (I := I) (M := M) g r s i α K
      ≤ wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  rw [wkpRhsAggregate]
  exact (le_sevenSum _ _ _ _ _ _ _).2.2.2.2.1

set_option linter.unusedSectionVars false in
/-- Chart-locality-free twin of `aggrCrossRightLimit_le`. -/
private lemma aggrCrossRightLimit_le :
    aggrCrossRightLimit (I := I) (M := M) g r s i α K
      ≤ wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  rw [wkpRhsAggregate]
  exact (le_sevenSum _ _ _ _ _ _ _).2.2.2.2.2.1

set_option linter.unusedSectionVars false in
/-- Chart-locality-free twin of `aggrCutoffPartial_le`. -/
private lemma aggrCutoffPartial_le :
    aggrCutoffPartial (I := I) (M := M) g r s i α K
      ≤ wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  rw [wkpRhsAggregate]
  exact (le_sevenSum _ _ _ _ _ _ _).2.2.2.2.2.2

end DominationUnconditional

section TermBoundsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)

set_option linter.unusedSectionVars false in
/-- Chart-locality-free twin of `rhsTerm1_wkpNorm_le`. -/
private lemma rhsTerm1_wkpNorm_le :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (rhsTerm1 (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  refine ⟨1, by norm_num, ?_⟩
  rw [ENNReal.ofReal_one, one_mul]
  exact le_trans (le_of_eq rfl)
    (aggrUchart_le (I := I) (M := M) g r s i α P₀ K)

/-- Chart-locality-free twin of `rhsTerm2_wkpNorm_le`. -/
private lemma rhsTerm2_wkpNorm_le
    (h_pou : PouRegularity (I := I) (M := M) g r s i K) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (rhsTerm2 (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set F : (TensorCompIdx (E := E) r (s + 1) ×
      TensorCompIdx (E := E) r (s + 1)) → EuclN → ℝ :=
    fun x y => (covChartMetricGram (I := I) (M := M) g r (s + 1) α x.1 x.2 y *
        crossLeftTestCoeff (I := I) (M := M) g r s α P₀ x.2 y) *
      ((crossLeftLimitComponent (I := I) (M := M) g r s i α x.1 :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  have h_data : ∀ x : TensorCompIdx (E := E) r (s + 1) ×
      TensorCompIdx (E := E) r (s + 1),
      MemWkp (d := Module.finrank ℝ E) K 2 (F x) Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧
          wkpNorm (d := Module.finrank ℝ E) K 2 (F x) Ω
            ≤ ENNReal.ofReal C *
              wkpRhsAggregate (I := I) (M := M)
                g r s i α P₀ K := by
    intro x
    have h_factor : MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((crossLeftLimitComponent (I := I) (M := M)
            g r s i α x.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      crossLeftLimitComponent_memWkp (I := I) (M := M)
        g r s i α x.1 K h_pou
    have hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => covChartMetricGram (I := I) (M := M) g r (s + 1) α x.1 x.2 y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ x.2 y) Ω :=
      (covChartMetricGram_contDiffOn (I := I) (M := M)
          g r (s + 1) α x.1 x.2).mul
        (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ x.2)
    have h_factor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α x.1 :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossLeftLimitComponent]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
        (I := I) (M := M) g r (s + 1)
        (tensorCovGradL2Compl (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) α x.1
    obtain ⟨h_summand_memWkp, C, hC_nn, hC_bd⟩ :=
      wkpNorm_smoothCoef_mul_aeZeroFactor_le
        (I := I) (M := M) α K
        (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
        (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
        hcoef_chart h_factor h_factor_ae_zero
    refine ⟨?_, ?_⟩
    · rw [hF_def]; exact h_summand_memWkp
    obtain ⟨C', hC'_nn, hC'_bd⟩ := wkpNorm_crossLeftLimitComponent_le
      (I := I) (M := M) g r s i K h_pou α x.1
    refine ⟨C * C', by positivity, ?_⟩
    rw [hF_def]
    have h_aggr_eq :
        (∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ((∑ Q : TensorCompIdx (E := E) r s,
                wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                        (eigenvectorResolvent (I := I) (M := M)
                          g r s i))
                      β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β))
              + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
                  ∑ Q : TensorCompIdx (E := E) r s,
                    wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                            (eigenvectorResolvent (I := I) (M := M)
                              g r s i))
                          β' Q :
                          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                          EuclN → ℝ) y)
                      (chartTargetEuclid (I := I) (M := M) β')))
          = aggrCrossLeft (I := I) (M := M) g r s i α K := by
      rw [aggrCrossLeft]; rfl
    calc
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => (covChartMetricGram (I := I) (M := M)
              g r (s + 1) α x.1 x.2 y *
            crossLeftTestCoeff (I := I) (M := M) g r s α P₀ x.2 y) *
          ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α x.1 :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω
          ≤ ENNReal.ofReal C *
              wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((crossLeftLimitComponent (I := I) (M := M)
                    g r s i α x.1 :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) Ω := hC_bd
      _ ≤ ENNReal.ofReal C *
            (ENNReal.ofReal C' *
              wkpRhsAggregate (I := I) (M := M)
                g r s i α P₀ K) := by
          gcongr
          rw [hΩ_def]
          refine hC'_bd.trans ?_
          rw [h_aggr_eq]
          gcongr
          exact aggrCrossLeft_le (I := I) (M := M)
            g r s i α P₀ K
      _ = ENNReal.ofReal (C * C') *
            wkpRhsAggregate (I := I) (M := M)
              g r s i α P₀ K := by
          rw [ENNReal.ofReal_mul hC_nn, mul_assoc]
  obtain ⟨C, hC_nn, hC_bd⟩ := wkpNorm_sum_le_const_mul_aggregate
    (Ω := Ω) hΩ_open F
    (wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K)
    (fun x => (h_data x).1) (fun x => (h_data x).2)
  refine ⟨C, hC_nn, ?_⟩
  have h_eq : rhsTerm2 (I := I) (M := M) g r s i α P₀
      = fun y => ∑ x : TensorCompIdx (E := E) r (s + 1) ×
          TensorCompIdx (E := E) r (s + 1), F x y := by
    funext y
    simp only [rhsTerm2, hF_def, Fintype.sum_prod_type]
  rw [h_eq, hΩ_def]
  exact hC_bd

/-- Chart-locality-free twin of `rhsTerm3_wkpNorm_le`. -/
private lemma rhsTerm3_wkpNorm_le
    (h_pou : PouRegularity (I := I) (M := M) g r s i K) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (rhsTerm3 (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set F : (TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun x y => (covChartMetricGram (I := I) (M := M) g r s α x.1 x.2 y *
        crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ x.2 y) *
      ((crossRightLimitComponent (I := I) (M := M) g r s i α x.1 :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  have h_data : ∀ x : TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s,
      MemWkp (d := Module.finrank ℝ E) K 2 (F x) Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧
          wkpNorm (d := Module.finrank ℝ E) K 2 (F x) Ω
            ≤ ENNReal.ofReal C *
              wkpRhsAggregate (I := I) (M := M)
                g r s i α P₀ K := by
    intro x
    have h_factor : MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((crossRightLimitComponent (I := I) (M := M)
            g r s i α x.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      crossRightLimitComponent_memWkp (I := I) (M := M)
        g r s i α x.1 K h_pou
    have hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => covChartMetricGram (I := I) (M := M) g r s α x.1 x.2 y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ x.2 y) Ω :=
      (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α x.1 x.2).mul
        (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ x.2)
    have h_factor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((crossRightLimitComponent (I := I) (M := M)
              g r s i α x.1 :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossRightLimitComponent]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
        (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) α x.1
    obtain ⟨h_summand_memWkp, C, hC_nn, hC_bd⟩ :=
      wkpNorm_smoothCoef_mul_aeZeroFactor_le
        (I := I) (M := M) α K
        (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
        (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
        hcoef_chart h_factor h_factor_ae_zero
    refine ⟨?_, ?_⟩
    · rw [hF_def]; exact h_summand_memWkp
    obtain ⟨C', hC'_nn, hC'_bd⟩ := wkpNorm_crossRightLimitComponent_le
      (I := I) (M := M) g r s i K
      (fun β Q => (h_pou β Q).le_of_le (Nat.le_succ K)) α x.1
    refine ⟨C * C', by positivity, ?_⟩
    rw [hF_def]
    have h_aggr_eq :
        (∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ∑ Q : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M)
                        g r s i))
                    β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β))
          = aggrCrossRight (I := I) (M := M) g r s i α K := by
      rw [aggrCrossRight]; rfl
    calc
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => (covChartMetricGram (I := I) (M := M) g r s α x.1 x.2 y *
            crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ x.2 y) *
          ((crossRightLimitComponent (I := I) (M := M)
              g r s i α x.1 :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω
          ≤ ENNReal.ofReal C *
              wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((crossRightLimitComponent (I := I) (M := M)
                    g r s i α x.1 :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) Ω := hC_bd
      _ ≤ ENNReal.ofReal C *
            (ENNReal.ofReal C' *
              wkpRhsAggregate (I := I) (M := M)
                g r s i α P₀ K) := by
          gcongr
          rw [hΩ_def]
          refine hC'_bd.trans ?_
          rw [h_aggr_eq]
          gcongr
          exact aggrCrossRight_le (I := I) (M := M)
            g r s i α P₀ K
      _ = ENNReal.ofReal (C * C') *
            wkpRhsAggregate (I := I) (M := M)
              g r s i α P₀ K := by
          rw [ENNReal.ofReal_mul hC_nn, mul_assoc]
  obtain ⟨C, hC_nn, hC_bd⟩ := wkpNorm_sum_le_const_mul_aggregate
    (Ω := Ω) hΩ_open F
    (wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K)
    (fun x => (h_data x).1) (fun x => (h_data x).2)
  refine ⟨C, hC_nn, ?_⟩
  have h_eq : rhsTerm3 (I := I) (M := M) g r s i α P₀
      = fun y => ∑ x : TensorCompIdx (E := E) r s ×
          TensorCompIdx (E := E) r s, F x y := by
    funext y
    simp only [rhsTerm3, hF_def, Fintype.sum_prod_type]
  rw [h_eq, hΩ_def]
  exact hC_bd

/-- Chart-locality-free twin of `rhsTerm4_wkpNorm_le`. -/
private lemma rhsTerm4_wkpNorm_le
    (h_pou : PouRegularity (I := I) (M := M) g r s i K) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (rhsTerm4 (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    wkpNorm_covPrincipalRotationCoeffLimit_le_unconditional
      (I := I) (M := M) g r s i K α P₀ (fun β Q => h_pou β Q)
  refine ⟨C, hC_nn, ?_⟩
  rw [rhsTerm4]
  refine le_trans hC_bd ?_
  gcongr
  exact aggrPartial_le (I := I) (M := M) g r s i α P₀ K

/-- Chart-locality-free twin of `rhsTerm5_wkpNorm_le`. -/
private lemma rhsTerm5_wkpNorm_le
    (h_pou : PouRegularity (I := I) (M := M) g r s i K) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (rhsTerm5 (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    wkpNorm_covLowerOrderRotationValueCoeffLimit_le_unconditional
      (I := I) (M := M) g r s i K α P₀ (fun β Q => h_pou β Q)
  refine ⟨2 * C, by positivity, ?_⟩
  rw [rhsTerm5]
  have h_sum_le :
      aggrPartial (I := I) (M := M) g r s i α K
          + aggrComponent (I := I) (M := M) g r s i α K
        ≤ 2 * wkpRhsAggregate (I := I) (M := M)
            g r s i α P₀ K := by
    rw [two_mul]
    exact add_le_add
      (aggrPartial_le (I := I) (M := M) g r s i α P₀ K)
      (aggrComponent_le (I := I) (M := M) g r s i α P₀ K)
  refine le_trans hC_bd ?_
  calc
    ENNReal.ofReal C *
        (aggrPartial (I := I) (M := M) g r s i α K
          + aggrComponent (I := I) (M := M) g r s i α K)
        ≤ ENNReal.ofReal C *
            (2 * wkpRhsAggregate (I := I) (M := M)
              g r s i α P₀ K) := by
          gcongr
    _ = ENNReal.ofReal (2 * C) *
          wkpRhsAggregate (I := I) (M := M)
            g r s i α P₀ K := by
        rw [← ofReal_two, ← mul_assoc, ← ENNReal.ofReal_mul hC_nn, mul_comm C 2]

/-- Chart-locality-free twin of `weightedGradCoeffDivLimit_sum_wkpNorm_le`. -/
private lemma weightedGradCoeffDivLimit_sum_wkpNorm_le
    (h_pou : PouRegularity (I := I) (M := M) g r s i K) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ l : Fin (Module.finrank ℝ E),
            weightedGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ l y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_data : ∀ l : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) K 2
          (weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l) Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧
          wkpNorm (d := Module.finrank ℝ E) K 2
              (weightedGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀ l) Ω
            ≤ ENNReal.ofReal C *
              wkpRhsAggregate (I := I) (M := M)
                g r s i α P₀ K := by
    intro l
    refine ⟨?_, ?_⟩
    · rw [hΩ_def]
      exact weightedGradCoeffDivLimit_memWkp (I := I) (M := M)
        g r s i α P₀ l K (fun β Q => h_pou β Q)
    obtain ⟨C, hC_nn, hC_bd⟩ := wkpNorm_weightedGradCoeffDivLimit_le_unconditional
      (I := I) (M := M) g r s i K α P₀ l (fun β Q => h_pou β Q)
    refine ⟨2 * C, by positivity, ?_⟩
    rw [hΩ_def]
    refine le_trans hC_bd ?_
    have h_sum_le :
        aggrComponent (I := I) (M := M) g r s i α K
            + aggrPartial (I := I) (M := M) g r s i α K
          ≤ 2 * wkpRhsAggregate (I := I) (M := M)
              g r s i α P₀ K := by
      rw [two_mul]
      exact add_le_add
        (aggrComponent_le (I := I) (M := M) g r s i α P₀ K)
        (aggrPartial_le (I := I) (M := M) g r s i α P₀ K)
    calc
      ENNReal.ofReal C *
          (aggrComponent (I := I) (M := M) g r s i α K
            + aggrPartial (I := I) (M := M) g r s i α K)
          ≤ ENNReal.ofReal C *
              (2 * wkpRhsAggregate (I := I) (M := M)
                g r s i α P₀ K) := by
            gcongr
      _ = ENNReal.ofReal (2 * C) *
            wkpRhsAggregate (I := I) (M := M)
              g r s i α P₀ K := by
          rw [← ofReal_two, ← mul_assoc, ← ENNReal.ofReal_mul hC_nn,
            mul_comm C 2]
  exact wkpNorm_sum_le_const_mul_aggregate (Ω := Ω) hΩ_open
    (fun l => weightedGradCoeffDivLimit (I := I) (M := M)
      g r s i α P₀ l)
    (wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K)
    (fun l => (h_data l).1) (fun l => (h_data l).2)

/-- Chart-locality-free twin of `rhsTerm6_wkpNorm_le`. -/
private lemma rhsTerm6_wkpNorm_le
    (h_pou : PouRegularity (I := I) (M := M) g r s i K) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (rhsTerm6 (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_sum_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
        weightedGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ l y) Ω :=
    memWkpFinsetSum hΩ_open
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l => weightedGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ l)
      (fun l _ => weightedGradCoeffDivLimit_memWkp (I := I) (M := M)
        g r s i α P₀ l K (fun β Q => h_pou β Q))
  have h_sum_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l y) = 0 :=
    Filter.Eventually.of_forall (fun _y hy =>
      Finset.sum_eq_zero (fun l _ =>
        weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel_unconditional
          (I := I) (M := M) g r s i α P₀ l hy))
  obtain ⟨_, C₁, hC₁_nn, hC₁_bd⟩ := wkpNorm_smoothCoef_mul_aeZeroFactor_le
    (I := I) (M := M) α K
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
    h_sum_memWkp h_sum_ae_zero
  obtain ⟨C₂, hC₂_nn, hC₂_bd⟩ :=
    weightedGradCoeffDivLimit_sum_wkpNorm_le
      (I := I) (M := M) g r s i α P₀ K h_pou
  refine ⟨C₁ * C₂, by positivity, ?_⟩
  have h_term6_eq : rhsTerm6 (I := I) (M := M) g r s i α P₀
      = fun y => (1 / densityOnEuclid (I := I) g α y) *
          (∑ l : Fin (Module.finrank ℝ E),
            weightedGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ l y) := rfl
  rw [h_term6_eq]
  calc
    wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => (1 / densityOnEuclid (I := I) g α y) *
          (∑ l : Fin (Module.finrank ℝ E),
            weightedGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ l y)) Ω
        ≤ ENNReal.ofReal C₁ *
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ l : Fin (Module.finrank ℝ E),
                weightedGradCoeffDivLimit (I := I) (M := M)
                  g r s i α P₀ l y) Ω := hC₁_bd
    _ ≤ ENNReal.ofReal C₁ *
          (ENNReal.ofReal C₂ *
            wkpRhsAggregate (I := I) (M := M)
              g r s i α P₀ K) := by
        gcongr
    _ = ENNReal.ofReal (C₁ * C₂) *
          wkpRhsAggregate (I := I) (M := M)
            g r s i α P₀ K := by
        rw [ENNReal.ofReal_mul hC₁_nn, mul_assoc]

/-- Chart-locality-free twin of `crossRightGradCoeffDivLimit_memWkp_local`. -/
private lemma crossRightGradCoeffDivLimit_memWkp_local
    (h_pou : PouRegularity (I := I) (M := M) g r s i K) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_term7_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (rhsTerm7 (I := I) (M := M) g r s i α P₀) Ω :=
    rhsTerm7_memWkp (I := I) (M := M) g r s i α P₀ K h_pou
  have h_term7_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        rhsTerm7 (I := I) (M := M) g r s i α P₀ y = 0 :=
    Filter.Eventually.of_forall (fun y hy_imp => by
      change (1 / densityOnEuclid (I := I) g α y) *
        crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ y = 0
      rw [crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ hy_imp, mul_zero])
  obtain ⟨h_prod_memWkp, _⟩ := wkpNorm_smoothCoef_mul_aeZeroFactor_le
    (I := I) (M := M) α K
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (densityOnEuclid_contDiffOn (I := I) g α)
    h_term7_memWkp h_term7_ae_zero
  have h_ae_eq : (fun y => densityOnEuclid (I := I) g α y *
        rhsTerm7 (I := I) (M := M) g r s i α P₀ y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ := by
    refine (ae_restrict_iff' hΩ_open.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall fun y hy => ?_
    have hy' : y ∈ chartTargetEuclid (I := I) (M := M) α := hy
    have h_pos : densityOnEuclid (I := I) g α y ≠ 0 :=
      (densityOnEuclid_pos (I := I) g α hy').ne'
    change densityOnEuclid (I := I) g α y *
        ((1 / densityOnEuclid (I := I) g α y) *
          crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ y)
      = crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ y
    rw [← mul_assoc, mul_one_div, div_self h_pos, one_mul]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).mp h_prod_memWkp

/-- Chart-locality-free twin of `rhsTerm7_wkpNorm_le`. -/
private lemma rhsTerm7_wkpNorm_le
    (h_pou : PouRegularity (I := I) (M := M) g r s i K) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (rhsTerm7 (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have h_div_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀) Ω :=
    crossRightGradCoeffDivLimit_memWkp_local (I := I) (M := M)
      g r s i α P₀ K h_pou
  have h_div_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ y = 0 :=
    Filter.Eventually.of_forall (fun y hy_imp =>
      crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ hy_imp)
  obtain ⟨_, C₁, hC₁_nn, hC₁_bd⟩ := wkpNorm_smoothCoef_mul_aeZeroFactor_le
    (I := I) (M := M) α K
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
    h_div_memWkp h_div_ae_zero
  obtain ⟨C₂, hC₂_nn, hC₂_bd⟩ :=
    wkpNorm_crossRightGradCoeffDivLimit_le
      (I := I) (M := M) g r s i α P₀ K (fun β Q => h_pou β Q)
  refine ⟨C₁ * (2 * C₂), by positivity, ?_⟩
  have h_term7_eq : rhsTerm7 (I := I) (M := M) g r s i α P₀
      = fun y => (1 / densityOnEuclid (I := I) g α y) *
          crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ y := rfl
  rw [h_term7_eq]
  have h_sum_le :
      aggrCrossRightLimit (I := I) (M := M) g r s i α K
          + aggrCutoffPartial (I := I) (M := M) g r s i α K
        ≤ 2 * wkpRhsAggregate (I := I) (M := M)
            g r s i α P₀ K := by
    rw [two_mul]
    exact add_le_add
      (aggrCrossRightLimit_le (I := I) (M := M) g r s i α P₀ K)
      (aggrCutoffPartial_le (I := I) (M := M) g r s i α P₀ K)
  calc
    wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => (1 / densityOnEuclid (I := I) g α y) *
          crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ y) Ω
        ≤ ENNReal.ofReal C₁ *
            wkpNorm (d := Module.finrank ℝ E) K 2
              (crossRightGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀) Ω := hC₁_bd
    _ ≤ ENNReal.ofReal C₁ *
          (ENNReal.ofReal C₂ *
            (2 * wkpRhsAggregate (I := I) (M := M)
              g r s i α P₀ K)) := by
        rw [hΩ_def]
        gcongr
        refine le_trans hC₂_bd ?_
        gcongr
        exact h_sum_le
    _ = ENNReal.ofReal (C₁ * (2 * C₂)) *
          wkpRhsAggregate (I := I) (M := M)
            g r s i α P₀ K := by
        rw [ENNReal.ofReal_mul hC₁_nn,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ofReal_two]
        ring

end TermBoundsUnconditional

section BracketBoundUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)

/-- Chart-locality-free twin of `rhsBracket_wkpNorm_le`. -/
private lemma rhsBracket_wkpNorm_le
    (h_pou : PouRegularity (I := I) (M := M) g r s i K) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (rhsBracket (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hM1 := rhsTerm1_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou
  have hM2 := rhsTerm2_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou
  have hM3 := rhsTerm3_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou
  have hM4 := rhsTerm4_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou
  have hM5 := rhsTerm5_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou
  have hM6 := rhsTerm6_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou
  have hM7 := rhsTerm7_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou
  rw [← hΩ_def] at hM1 hM2 hM3 hM4 hM5 hM6 hM7
  have hp2 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hB12 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => rhsTerm1 (I := I) (M := M) g r s i α P₀ y
        - rhsTerm2 (I := I) (M := M) g r s i α P₀ y) Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open hM1 hM2
  have hB123 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (rhsTerm1 (I := I) (M := M) g r s i α P₀ y
          - rhsTerm2 (I := I) (M := M) g r s i α P₀ y)
        + rhsTerm3 (I := I) (M := M) g r s i α P₀ y) Ω :=
    MemWkp.add (d := Module.finrank ℝ E) hp2 hΩ_open hB12 hM3
  have hB1234 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((rhsTerm1 (I := I) (M := M) g r s i α P₀ y
            - rhsTerm2 (I := I) (M := M) g r s i α P₀ y)
          + rhsTerm3 (I := I) (M := M) g r s i α P₀ y)
        - rhsTerm4 (I := I) (M := M) g r s i α P₀ y) Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open hB123 hM4
  have hB12345 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (((rhsTerm1 (I := I) (M := M) g r s i α P₀ y
              - rhsTerm2 (I := I) (M := M) g r s i α P₀ y)
            + rhsTerm3 (I := I) (M := M) g r s i α P₀ y)
          - rhsTerm4 (I := I) (M := M) g r s i α P₀ y)
        - rhsTerm5 (I := I) (M := M) g r s i α P₀ y) Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open hB1234 hM5
  have hB123456 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((((rhsTerm1 (I := I) (M := M) g r s i α P₀ y
                - rhsTerm2 (I := I) (M := M) g r s i α P₀ y)
              + rhsTerm3 (I := I) (M := M) g r s i α P₀ y)
            - rhsTerm4 (I := I) (M := M) g r s i α P₀ y)
          - rhsTerm5 (I := I) (M := M) g r s i α P₀ y)
        + rhsTerm6 (I := I) (M := M) g r s i α P₀ y) Ω :=
    MemWkp.add (d := Module.finrank ℝ E) hp2 hΩ_open hB12345 hM6
  obtain ⟨D1, hD1_nn, hD1⟩ := rhsTerm1_wkpNorm_le
    (I := I) (M := M) g r s i α P₀ K
  obtain ⟨D2, hD2_nn, hD2⟩ := rhsTerm2_wkpNorm_le
    (I := I) (M := M) g r s i α P₀ K h_pou
  obtain ⟨D3, hD3_nn, hD3⟩ := rhsTerm3_wkpNorm_le
    (I := I) (M := M) g r s i α P₀ K h_pou
  obtain ⟨D4, hD4_nn, hD4⟩ := rhsTerm4_wkpNorm_le
    (I := I) (M := M) g r s i α P₀ K h_pou
  obtain ⟨D5, hD5_nn, hD5⟩ := rhsTerm5_wkpNorm_le
    (I := I) (M := M) g r s i α P₀ K h_pou
  obtain ⟨D6, hD6_nn, hD6⟩ := rhsTerm6_wkpNorm_le
    (I := I) (M := M) g r s i α P₀ K h_pou
  obtain ⟨D7, hD7_nn, hD7⟩ := rhsTerm7_wkpNorm_le
    (I := I) (M := M) g r s i α P₀ K h_pou
  rw [← hΩ_def] at hD1 hD2 hD3 hD4 hD5 hD6 hD7
  refine ⟨D1 + D2 + D3 + D4 + D5 + D6 + D7, by positivity, ?_⟩
  have h_tri :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (rhsBracket (I := I) (M := M) g r s i α P₀) Ω
        ≤ wkpNorm (d := Module.finrank ℝ E) K 2
            (rhsTerm1 (I := I) (M := M) g r s i α P₀) Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2
              (rhsTerm2 (I := I) (M := M) g r s i α P₀) Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2
              (rhsTerm3 (I := I) (M := M) g r s i α P₀) Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2
              (rhsTerm4 (I := I) (M := M) g r s i α P₀) Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2
              (rhsTerm5 (I := I) (M := M) g r s i α P₀) Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2
              (rhsTerm6 (I := I) (M := M) g r s i α P₀) Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2
              (rhsTerm7 (I := I) (M := M) g r s i α P₀) Ω := by
    have h_bracket_eq :
        rhsBracket (I := I) (M := M) g r s i α P₀
        = fun y =>
            (((((rhsTerm1 (I := I) (M := M) g r s i α P₀ y
                  - rhsTerm2 (I := I) (M := M) g r s i α P₀ y)
                + rhsTerm3 (I := I) (M := M) g r s i α P₀ y)
              - rhsTerm4 (I := I) (M := M) g r s i α P₀ y)
            - rhsTerm5 (I := I) (M := M) g r s i α P₀ y)
          + rhsTerm6 (I := I) (M := M) g r s i α P₀ y)
          - rhsTerm7 (I := I) (M := M) g r s i α P₀ y := by
      funext y
      simp only [rhsBracket, Pi.sub_apply, Pi.add_apply]
    rw [h_bracket_eq]
    refine le_trans (wkpNorm_sub_le (K := K) hΩ_open hB123456 hM7) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (wkpNorm_add_le (d := Module.finrank ℝ E)
      (by norm_num) hΩ_open hB12345 hM6) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (wkpNorm_sub_le (K := K) hΩ_open hB1234 hM5) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (wkpNorm_sub_le (K := K) hΩ_open hB123 hM4) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (wkpNorm_add_le (d := Module.finrank ℝ E)
      (by norm_num) hΩ_open hB12 hM3) ?_
    refine add_le_add ?_ (le_refl _)
    exact wkpNorm_sub_le (K := K) hΩ_open hM1 hM2
  refine le_trans h_tri ?_
  have h_seven :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (rhsTerm1 (I := I) (M := M) g r s i α P₀) Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2
            (rhsTerm2 (I := I) (M := M) g r s i α P₀) Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2
            (rhsTerm3 (I := I) (M := M) g r s i α P₀) Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2
            (rhsTerm4 (I := I) (M := M) g r s i α P₀) Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2
            (rhsTerm5 (I := I) (M := M) g r s i α P₀) Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2
            (rhsTerm6 (I := I) (M := M) g r s i α P₀) Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2
            (rhsTerm7 (I := I) (M := M) g r s i α P₀) Ω
      ≤ ENNReal.ofReal D1 *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D2 *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D3 *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D4 *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D5 *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D6 *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D7 *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K :=
    add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (add_le_add hD1 hD2) hD3) hD4) hD5) hD6) hD7
  refine le_trans h_seven ?_
  rw [ENNReal.ofReal_add (by positivity) hD7_nn,
    ENNReal.ofReal_add (by positivity) hD6_nn,
    ENNReal.ofReal_add (by positivity) hD5_nn,
    ENNReal.ofReal_add (by positivity) hD4_nn,
    ENNReal.ofReal_add (by positivity) hD3_nn,
    ENNReal.ofReal_add hD1_nn hD2_nn]
  rw [add_mul, add_mul, add_mul, add_mul, add_mul, add_mul]

end BracketBoundUnconditional

section MainBoundUnconditional

/-- **Chart-locality-free twin of `eigenvectorChartRHS_wkpNorm_le`.** -/
theorem eigenvectorChartRHS_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartRHS (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          (wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (tensorResolventEigenbasisVec (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I)
                      (M := M) g r s) i) α P₀ :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α)
            + (∑ β ∈ transportChartCenters (I := I) (M := M) α,
                ((∑ Q : TensorCompIdx (E := E) r s,
                    wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                            (eigenvectorResolvent (I := I) (M := M)
                              g r s i))
                          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                          EuclN → ℝ) y)
                      (chartTargetEuclid (I := I) (M := M) β))
                  + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
                      ∑ Q : TensorCompIdx (E := E) r s,
                        wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                          (fun y => ((tensorL2ChartComponent (I := I) (M := M)
                              g r s
                              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                                (eigenvectorResolvent (I := I)
                                  (M := M) g r s i))
                              β' Q :
                              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                              EuclN → ℝ) y)
                          (chartTargetEuclid (I := I) (M := M) β')))
            + (∑ β ∈ transportChartCenters (I := I) (M := M) α,
                ∑ Q : TensorCompIdx (E := E) r s,
                  wkpNorm (d := Module.finrank ℝ E) K 2
                    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                          (eigenvectorResolvent (I := I) (M := M)
                            g r s i))
                        β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                        EuclN → ℝ) y)
                    (chartTargetEuclid (I := I) (M := M) β))
            + (∑ P : TensorCompIdx (E := E) r s,
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
                  (chartTargetEuclid (I := I) (M := M) α))
            + (∑ P : TensorCompIdx (E := E) r s,
                wkpNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((crossRightLimitComponent (I := I)
                      (M := M) g r s i α P :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) α))
            + (∑ P : TensorCompIdx (E := E) r s,
                ∑ l : Fin (Module.finrank ℝ E),
                  wkpNorm (d := Module.finrank ℝ E) K 2
                    (fun y => ((cutoffPartialLpLimit (I := I)
                        (M := M) g r s i α P l :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) y)
                    (chartTargetEuclid (I := I) (M := M) α))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hμ_pos : 0 < i.fst.val := eigenIdx_val_pos (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have h_bracket_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (rhsBracket (I := I) (M := M) g r s i α P₀) Ω := by
    have hM1 := rhsTerm1_memWkp (I := I) (M := M)
      g r s i α P₀ K h_pou
    have hM2 := rhsTerm2_memWkp (I := I) (M := M)
      g r s i α P₀ K h_pou
    have hM3 := rhsTerm3_memWkp (I := I) (M := M)
      g r s i α P₀ K h_pou
    have hM4 := rhsTerm4_memWkp (I := I) (M := M)
      g r s i α P₀ K h_pou
    have hM5 := rhsTerm5_memWkp (I := I) (M := M)
      g r s i α P₀ K h_pou
    have hM6 := rhsTerm6_memWkp (I := I) (M := M)
      g r s i α P₀ K h_pou
    have hM7 := rhsTerm7_memWkp (I := I) (M := M)
      g r s i α P₀ K h_pou
    rw [← hΩ_def] at hM1 hM2 hM3 hM4 hM5 hM6 hM7
    have hp2 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
    have h_bracket_eq :
        rhsBracket (I := I) (M := M) g r s i α P₀
        = fun y =>
            (((((rhsTerm1 (I := I) (M := M) g r s i α P₀ y
                  - rhsTerm2 (I := I) (M := M) g r s i α P₀ y)
                + rhsTerm3 (I := I) (M := M) g r s i α P₀ y)
              - rhsTerm4 (I := I) (M := M) g r s i α P₀ y)
            - rhsTerm5 (I := I) (M := M) g r s i α P₀ y)
          + rhsTerm6 (I := I) (M := M) g r s i α P₀ y)
          - rhsTerm7 (I := I) (M := M) g r s i α P₀ y := by
      funext y
      simp only [rhsBracket, Pi.sub_apply, Pi.add_apply]
    rw [h_bracket_eq]
    exact MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open
      (MemWkp.add (d := Module.finrank ℝ E) hp2 hΩ_open
        (MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open
          (MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open
            (MemWkp.add (d := Module.finrank ℝ E) hp2 hΩ_open
              (MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open hM1 hM2) hM3)
            hM4) hM5) hM6) hM7
  obtain ⟨C, hC_nn, hC_bd⟩ := rhsBracket_wkpNorm_le
    (I := I) (M := M) g r s i α P₀ K h_pou
  rw [← hΩ_def] at hC_bd
  refine ⟨C, hC_nn, ?_⟩
  have h_smul_eq :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartRHS (I := I) (M := M)
            g r s i α P₀) Ω
        = ENNReal.ofReal (i.fst.val)⁻¹ *
          wkpNorm (d := Module.finrank ℝ E) K 2
            (rhsBracket (I := I) (M := M) g r s i α P₀) Ω := by
    rw [eigenvectorChartRHS_eq_smul_bracket (I := I) (M := M)
      g r s i α P₀]
    have h := wkpNorm_const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_bracket_memWkp (i.fst.val)⁻¹
    rw [h, Real.enorm_of_nonneg hμ_inv_nn]
  rw [h_smul_eq]
  have h_step :
      ENNReal.ofReal (i.fst.val)⁻¹ *
          wkpNorm (d := Module.finrank ℝ E) K 2
            (rhsBracket (I := I) (M := M) g r s i α P₀) Ω
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
    rw [ENNReal.ofReal_mul hμ_inv_nn, mul_assoc]
    gcongr
  refine le_trans h_step (le_of_eq ?_)
  simp only [hΩ_def, wkpRhsAggregate, aggrUchart,
    aggrCrossLeft, aggrCrossRight,
    aggrPartial, aggrComponent,
    aggrCrossRightLimit, aggrCutoffPartial,
    resInclNorm]

end MainBoundUnconditional

section UniformTermBoundsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)

set_option linter.unusedSectionVars false in
/-- Chart-locality-free twin of `rhsTerm1_wkpNorm_le_uniform`. -/
private lemma rhsTerm1_wkpNorm_le_uniform :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
            (rhsTerm1 (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  refine ⟨1, by norm_num, fun i => ?_⟩
  rw [ENNReal.ofReal_one, one_mul]
  exact le_trans (le_of_eq rfl)
    (aggrUchart_le (I := I) (M := M) g r s i α P₀ K)

set_option linter.unusedSectionVars false in
/-- Chart-locality-free twin of `rhsTerm2_wkpNorm_le_uniform`. -/
private lemma rhsTerm2_wkpNorm_le_uniform
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
            (rhsTerm2 (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set F : (TensorCompIdx (E := E) r (s + 1) ×
        TensorCompIdx (E := E) r (s + 1)) →
      TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ :=
    fun x i y =>
      (covChartMetricGram (I := I) (M := M) g r (s + 1) α x.1 x.2 y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ x.2 y) *
        ((crossLeftLimitComponent (I := I) (M := M)
          g r s i α x.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  have h_data : ∀ x : TensorCompIdx (E := E) r (s + 1) ×
      TensorCompIdx (E := E) r (s + 1),
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) K 2 (F x i) Ω ∧
            wkpNorm (d := Module.finrank ℝ E) K 2 (F x i) Ω
              ≤ ENNReal.ofReal C *
                wkpRhsAggregate (I := I) (M := M)
                  g r s i α P₀ K := by
    intro x
    have hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => covChartMetricGram (I := I) (M := M) g r (s + 1) α x.1 x.2 y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ x.2 y) Ω :=
      (covChartMetricGram_contDiffOn (I := I) (M := M)
          g r (s + 1) α x.1 x.2).mul
        (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ x.2)
    obtain ⟨C, hC_nn, hC_bd⟩ := wkpNorm_smoothCoef_mul_aeZeroFactor_le_uniform
      (I := I) (M := M) α K
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      hcoef_chart
    obtain ⟨C', hC'_nn, hC'_bd⟩ :=
      wkpNorm_crossLeftLimitComponent_le_uniform
        (I := I) (M := M) g r s K h_pou α x.1
    refine ⟨C * C', by positivity, fun i => ?_⟩
    have h_factor : MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((crossLeftLimitComponent (I := I) (M := M)
            g r s i α x.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      crossLeftLimitComponent_memWkp (I := I) (M := M)
        g r s i α x.1 K (h_pou i)
    have h_factor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α x.1 :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossLeftLimitComponent]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
        (I := I) (M := M) g r (s + 1)
        (tensorCovGradL2Compl (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) α x.1
    obtain ⟨h_summand_memWkp, h_summand_bd⟩ := hC_bd
      (fun y => ((crossLeftLimitComponent (I := I) (M := M)
          g r s i α x.1 :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      h_factor h_factor_ae_zero
    refine ⟨h_summand_memWkp, ?_⟩
    have h_aggr_eq :
        (∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ((∑ Q : TensorCompIdx (E := E) r s,
                wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                        (eigenvectorResolvent (I := I) (M := M)
                          g r s i))
                      β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β))
              + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
                  ∑ Q : TensorCompIdx (E := E) r s,
                    wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                            (eigenvectorResolvent (I := I) (M := M)
                              g r s i))
                          β' Q :
                          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                          EuclN → ℝ) y)
                      (chartTargetEuclid (I := I) (M := M) β')))
          = aggrCrossLeft (I := I) (M := M) g r s i α K := by
      rw [aggrCrossLeft]; rfl
    calc
      wkpNorm (d := Module.finrank ℝ E) K 2 (F x i) Ω
          ≤ ENNReal.ofReal C *
              wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((crossLeftLimitComponent (I := I) (M := M)
                    g r s i α x.1 :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) Ω := h_summand_bd
      _ ≤ ENNReal.ofReal C *
            (ENNReal.ofReal C' *
              wkpRhsAggregate (I := I) (M := M)
                g r s i α P₀ K) := by
          gcongr
          rw [hΩ_def]
          refine (hC'_bd i).trans ?_
          rw [h_aggr_eq]
          gcongr
          exact aggrCrossLeft_le (I := I) (M := M)
            g r s i α P₀ K
      _ = ENNReal.ofReal (C * C') *
            wkpRhsAggregate (I := I) (M := M)
              g r s i α P₀ K := by
          rw [ENNReal.ofReal_mul hC_nn, mul_assoc]
  choose Cx hCx_nn hCx using h_data
  obtain ⟨C, hC_nn, hC_bd⟩ := wkpNorm_sum_le_const_mul_aggregate_uniform
    (Ω := Ω) hΩ_open F
    (fun i => wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K)
    (fun x i => (hCx x i).1)
    (fun x => ⟨Cx x, hCx_nn x, fun i => (hCx x i).2⟩)
  refine ⟨C, hC_nn, fun i => ?_⟩
  have h_eq : rhsTerm2 (I := I) (M := M) g r s i α P₀
      = fun y => ∑ x : TensorCompIdx (E := E) r (s + 1) ×
          TensorCompIdx (E := E) r (s + 1), F x i y := by
    funext y
    simp only [rhsTerm2, hF_def, Fintype.sum_prod_type]
  rw [h_eq, hΩ_def]
  exact hC_bd i

set_option linter.unusedSectionVars false in
/-- Chart-locality-free twin of `rhsTerm3_wkpNorm_le_uniform`. -/
private lemma rhsTerm3_wkpNorm_le_uniform
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
            (rhsTerm3 (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set F : (TensorCompIdx (E := E) r s ×
        TensorCompIdx (E := E) r s) →
      TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ :=
    fun x i y =>
      (covChartMetricGram (I := I) (M := M) g r s α x.1 x.2 y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ x.2 y) *
        ((crossRightLimitComponent (I := I) (M := M)
          g r s i α x.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  have h_pou_K : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β) :=
    fun i β Q => (h_pou i β Q).le_of_le (Nat.le_succ K)
  have h_data : ∀ x : TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) K 2 (F x i) Ω ∧
            wkpNorm (d := Module.finrank ℝ E) K 2 (F x i) Ω
              ≤ ENNReal.ofReal C *
                wkpRhsAggregate (I := I) (M := M)
                  g r s i α P₀ K := by
    intro x
    have hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => covChartMetricGram (I := I) (M := M) g r s α x.1 x.2 y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ x.2 y) Ω :=
      (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α x.1 x.2).mul
        (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ x.2)
    obtain ⟨C, hC_nn, hC_bd⟩ := wkpNorm_smoothCoef_mul_aeZeroFactor_le_uniform
      (I := I) (M := M) α K
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      hcoef_chart
    obtain ⟨C', hC'_nn, hC'_bd⟩ :=
      wkpNorm_crossRightLimitComponent_le_uniform
        (I := I) (M := M) g r s K h_pou_K α x.1
    refine ⟨C * C', by positivity, fun i => ?_⟩
    have h_factor : MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((crossRightLimitComponent (I := I) (M := M)
            g r s i α x.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      crossRightLimitComponent_memWkp (I := I) (M := M)
        g r s i α x.1 K (h_pou i)
    have h_factor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((crossRightLimitComponent (I := I) (M := M)
              g r s i α x.1 :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossRightLimitComponent]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
        (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) α x.1
    obtain ⟨h_summand_memWkp, h_summand_bd⟩ := hC_bd
      (fun y => ((crossRightLimitComponent (I := I) (M := M)
          g r s i α x.1 :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      h_factor h_factor_ae_zero
    refine ⟨h_summand_memWkp, ?_⟩
    have h_aggr_eq :
        (∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ∑ Q : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M)
                        g r s i))
                    β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β))
          = aggrCrossRight (I := I) (M := M) g r s i α K := by
      rw [aggrCrossRight]; rfl
    calc
      wkpNorm (d := Module.finrank ℝ E) K 2 (F x i) Ω
          ≤ ENNReal.ofReal C *
              wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((crossRightLimitComponent (I := I)
                    (M := M) g r s i α x.1 :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) Ω := h_summand_bd
      _ ≤ ENNReal.ofReal C *
            (ENNReal.ofReal C' *
              wkpRhsAggregate (I := I) (M := M)
                g r s i α P₀ K) := by
          gcongr
          rw [hΩ_def]
          refine (hC'_bd i).trans ?_
          rw [h_aggr_eq]
          gcongr
          exact aggrCrossRight_le (I := I) (M := M)
            g r s i α P₀ K
      _ = ENNReal.ofReal (C * C') *
            wkpRhsAggregate (I := I) (M := M)
              g r s i α P₀ K := by
          rw [ENNReal.ofReal_mul hC_nn, mul_assoc]
  choose Cx hCx_nn hCx using h_data
  obtain ⟨C, hC_nn, hC_bd⟩ := wkpNorm_sum_le_const_mul_aggregate_uniform
    (Ω := Ω) hΩ_open F
    (fun i => wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K)
    (fun x i => (hCx x i).1)
    (fun x => ⟨Cx x, hCx_nn x, fun i => (hCx x i).2⟩)
  refine ⟨C, hC_nn, fun i => ?_⟩
  have h_eq : rhsTerm3 (I := I) (M := M) g r s i α P₀
      = fun y => ∑ x : TensorCompIdx (E := E) r s ×
          TensorCompIdx (E := E) r s, F x i y := by
    funext y
    simp only [rhsTerm3, hF_def, Fintype.sum_prod_type]
  rw [h_eq, hΩ_def]
  exact hC_bd i

set_option linter.unusedSectionVars false in
/-- Chart-locality-free twin of `rhsTerm4_wkpNorm_le_uniform`. -/
private lemma rhsTerm4_wkpNorm_le_uniform
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
            (rhsTerm4 (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    wkpNorm_covPrincipalRotationCoeffLimit_le_uniform_unconditional
      (I := I) (M := M) g r s K α P₀ h_pou
  refine ⟨C, hC_nn, fun i => ?_⟩
  rw [rhsTerm4]
  refine le_trans (hC_bd i) ?_
  gcongr
  exact aggrPartial_le (I := I) (M := M) g r s i α P₀ K

set_option linter.unusedSectionVars false in
/-- Chart-locality-free twin of `rhsTerm5_wkpNorm_le_uniform`. -/
private lemma rhsTerm5_wkpNorm_le_uniform
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
            (rhsTerm5 (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    wkpNorm_covLowerOrderRotationValueCoeffLimit_le_uniform_unconditional
      (I := I) (M := M) g r s K α P₀ h_pou
  refine ⟨2 * C, by positivity, fun i => ?_⟩
  rw [rhsTerm5]
  have h_sum_le :
      aggrPartial (I := I) (M := M) g r s i α K
          + aggrComponent (I := I) (M := M) g r s i α K
        ≤ 2 * wkpRhsAggregate (I := I) (M := M)
            g r s i α P₀ K := by
    rw [two_mul]
    exact add_le_add
      (aggrPartial_le (I := I) (M := M) g r s i α P₀ K)
      (aggrComponent_le (I := I) (M := M) g r s i α P₀ K)
  refine le_trans (hC_bd i) ?_
  calc
    ENNReal.ofReal C *
        (aggrPartial (I := I) (M := M) g r s i α K
          + aggrComponent (I := I) (M := M) g r s i α K)
        ≤ ENNReal.ofReal C *
            (2 * wkpRhsAggregate (I := I) (M := M)
              g r s i α P₀ K) := by
          gcongr
    _ = ENNReal.ofReal (2 * C) *
          wkpRhsAggregate (I := I) (M := M)
            g r s i α P₀ K := by
        rw [← ofReal_two, ← mul_assoc, ← ENNReal.ofReal_mul hC_nn, mul_comm C 2]

set_option linter.unusedSectionVars false in
/-- Chart-locality-free twin of `weightedGradCoeffDivLimit_sum_wkpNorm_le_uniform`. -/
private lemma weightedGradCoeffDivLimit_sum_wkpNorm_le_uniform
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
            (fun y => ∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀ l y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_data : ∀ l : Fin (Module.finrank ℝ E),
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) K 2
              (weightedGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀ l) Ω ∧
            wkpNorm (d := Module.finrank ℝ E) K 2
                (weightedGradCoeffDivLimit (I := I) (M := M)
                  g r s i α P₀ l) Ω
              ≤ ENNReal.ofReal C *
                wkpRhsAggregate (I := I) (M := M)
                  g r s i α P₀ K := by
    intro l
    obtain ⟨C, hC_nn, hC_bd⟩ :=
      wkpNorm_weightedGradCoeffDivLimit_le_uniform_unconditional
        (I := I) (M := M) g r s K α P₀ l h_pou
    refine ⟨2 * C, by positivity, fun i => ?_⟩
    refine ⟨?_, ?_⟩
    · rw [hΩ_def]
      exact weightedGradCoeffDivLimit_memWkp (I := I) (M := M)
        g r s i α P₀ l K (fun β Q => h_pou i β Q)
    rw [hΩ_def]
    refine le_trans (hC_bd i) ?_
    have h_sum_le :
        aggrComponent (I := I) (M := M) g r s i α K
            + aggrPartial (I := I) (M := M) g r s i α K
          ≤ 2 * wkpRhsAggregate (I := I) (M := M)
              g r s i α P₀ K := by
      rw [two_mul]
      exact add_le_add
        (aggrComponent_le (I := I) (M := M) g r s i α P₀ K)
        (aggrPartial_le (I := I) (M := M) g r s i α P₀ K)
    calc
      ENNReal.ofReal C *
          (aggrComponent (I := I) (M := M) g r s i α K
            + aggrPartial (I := I) (M := M) g r s i α K)
          ≤ ENNReal.ofReal C *
              (2 * wkpRhsAggregate (I := I) (M := M)
                g r s i α P₀ K) := by
            gcongr
      _ = ENNReal.ofReal (2 * C) *
            wkpRhsAggregate (I := I) (M := M)
              g r s i α P₀ K := by
          rw [← ofReal_two, ← mul_assoc, ← ENNReal.ofReal_mul hC_nn,
            mul_comm C 2]
  choose Cl hCl_nn hCl using h_data
  obtain ⟨C, hC_nn, hC_bd⟩ := wkpNorm_sum_le_const_mul_aggregate_uniform
    (Ω := Ω) hΩ_open
    (fun l i => weightedGradCoeffDivLimit (I := I) (M := M)
      g r s i α P₀ l)
    (fun i => wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K)
    (fun l i => (hCl l i).1)
    (fun l => ⟨Cl l, hCl_nn l, fun i => (hCl l i).2⟩)
  exact ⟨C, hC_nn, fun i => hC_bd i⟩

set_option linter.unusedSectionVars false in
/-- Chart-locality-free twin of `rhsTerm6_wkpNorm_le_uniform`. -/
private lemma rhsTerm6_wkpNorm_le_uniform
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
            (rhsTerm6 (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨C₁, hC₁_nn, hC₁_bd⟩ := wkpNorm_smoothCoef_mul_aeZeroFactor_le_uniform
    (I := I) (M := M) α K
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
  obtain ⟨C₂, hC₂_nn, hC₂_bd⟩ :=
    weightedGradCoeffDivLimit_sum_wkpNorm_le_uniform
      (I := I) (M := M) g r s α P₀ K h_pou
  refine ⟨C₁ * C₂, by positivity, fun i => ?_⟩
  have h_sum_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
        weightedGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ l y) Ω :=
    memWkpFinsetSum hΩ_open
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l => weightedGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ l)
      (fun l _ => weightedGradCoeffDivLimit_memWkp (I := I) (M := M)
        g r s i α P₀ l K (fun β Q => h_pou i β Q))
  have h_sum_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l y) = 0 :=
    Filter.Eventually.of_forall (fun _y hy =>
      Finset.sum_eq_zero (fun l _ =>
        weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel_unconditional
          (I := I) (M := M) g r s i α P₀ l hy))
  obtain ⟨_, h_coef_bd⟩ := hC₁_bd
    (fun y => ∑ l : Fin (Module.finrank ℝ E),
      weightedGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ l y)
    h_sum_memWkp h_sum_ae_zero
  have h_term6_eq : rhsTerm6 (I := I) (M := M) g r s i α P₀
      = fun y => (1 / densityOnEuclid (I := I) g α y) *
          (∑ l : Fin (Module.finrank ℝ E),
            weightedGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ l y) := rfl
  rw [h_term6_eq]
  calc
    wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => (1 / densityOnEuclid (I := I) g α y) *
          (∑ l : Fin (Module.finrank ℝ E),
            weightedGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ l y)) Ω
        ≤ ENNReal.ofReal C₁ *
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ l : Fin (Module.finrank ℝ E),
                weightedGradCoeffDivLimit (I := I) (M := M)
                  g r s i α P₀ l y) Ω := h_coef_bd
    _ ≤ ENNReal.ofReal C₁ *
          (ENNReal.ofReal C₂ *
            wkpRhsAggregate (I := I) (M := M)
              g r s i α P₀ K) := by
        gcongr
        exact hC₂_bd i
    _ = ENNReal.ofReal (C₁ * C₂) *
          wkpRhsAggregate (I := I) (M := M)
            g r s i α P₀ K := by
        rw [ENNReal.ofReal_mul hC₁_nn, mul_assoc]

set_option linter.unusedSectionVars false in
/-- Chart-locality-free twin of `rhsTerm7_wkpNorm_le_uniform`. -/
private lemma rhsTerm7_wkpNorm_le_uniform
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
            (rhsTerm7 (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨C₁, hC₁_nn, hC₁_bd⟩ := wkpNorm_smoothCoef_mul_aeZeroFactor_le_uniform
    (I := I) (M := M) α K
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
  obtain ⟨C₂, hC₂_nn, hC₂_bd⟩ :=
    wkpNorm_crossRightGradCoeffDivLimit_le_uniform
      (I := I) (M := M) g r s α P₀ K h_pou
  refine ⟨C₁ * (2 * C₂), by positivity, fun i => ?_⟩
  have h_div_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀) Ω :=
    crossRightGradCoeffDivLimit_memWkp_local (I := I) (M := M)
      g r s i α P₀ K (fun β Q => h_pou i β Q)
  have h_div_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ y = 0 :=
    Filter.Eventually.of_forall (fun y hy_imp =>
      crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ hy_imp)
  obtain ⟨_, h_coef_bd⟩ := hC₁_bd
    (crossRightGradCoeffDivLimit (I := I) (M := M)
      g r s i α P₀)
    h_div_memWkp h_div_ae_zero
  have h_term7_eq : rhsTerm7 (I := I) (M := M) g r s i α P₀
      = fun y => (1 / densityOnEuclid (I := I) g α y) *
          crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ y := rfl
  rw [h_term7_eq]
  have h_sum_le :
      aggrCrossRightLimit (I := I) (M := M) g r s i α K
          + aggrCutoffPartial (I := I) (M := M) g r s i α K
        ≤ 2 * wkpRhsAggregate (I := I) (M := M)
            g r s i α P₀ K := by
    rw [two_mul]
    exact add_le_add
      (aggrCrossRightLimit_le (I := I) (M := M) g r s i α P₀ K)
      (aggrCutoffPartial_le (I := I) (M := M) g r s i α P₀ K)
  calc
    wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => (1 / densityOnEuclid (I := I) g α y) *
          crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ y) Ω
        ≤ ENNReal.ofReal C₁ *
            wkpNorm (d := Module.finrank ℝ E) K 2
              (crossRightGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀) Ω := h_coef_bd
    _ ≤ ENNReal.ofReal C₁ *
          (ENNReal.ofReal C₂ *
            (2 * wkpRhsAggregate (I := I) (M := M)
              g r s i α P₀ K)) := by
        gcongr
        refine le_trans (hC₂_bd i) ?_
        gcongr
        exact h_sum_le
    _ = ENNReal.ofReal (C₁ * (2 * C₂)) *
          wkpRhsAggregate (I := I) (M := M)
            g r s i α P₀ K := by
        rw [ENNReal.ofReal_mul hC₁_nn,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ofReal_two]
        ring

end UniformTermBoundsUnconditional

section UniformBracketBoundUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)

set_option linter.unusedSectionVars false in
/-- Chart-locality-free twin of `rhsBracket_wkpNorm_le_uniform`. -/
private lemma rhsBracket_wkpNorm_le_uniform
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
            (rhsBracket (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  classical
  obtain ⟨D1, hD1_nn, hD1⟩ := rhsTerm1_wkpNorm_le_uniform
    (I := I) (M := M) g r s α P₀ K
  obtain ⟨D2, hD2_nn, hD2⟩ := rhsTerm2_wkpNorm_le_uniform
    (I := I) (M := M) g r s α P₀ K h_pou
  obtain ⟨D3, hD3_nn, hD3⟩ := rhsTerm3_wkpNorm_le_uniform
    (I := I) (M := M) g r s α P₀ K h_pou
  obtain ⟨D4, hD4_nn, hD4⟩ := rhsTerm4_wkpNorm_le_uniform
    (I := I) (M := M) g r s α P₀ K h_pou
  obtain ⟨D5, hD5_nn, hD5⟩ := rhsTerm5_wkpNorm_le_uniform
    (I := I) (M := M) g r s α P₀ K h_pou
  obtain ⟨D6, hD6_nn, hD6⟩ := rhsTerm6_wkpNorm_le_uniform
    (I := I) (M := M) g r s α P₀ K h_pou
  obtain ⟨D7, hD7_nn, hD7⟩ := rhsTerm7_wkpNorm_le_uniform
    (I := I) (M := M) g r s α P₀ K h_pou
  refine ⟨D1 + D2 + D3 + D4 + D5 + D6 + D7, by positivity, fun i => ?_⟩
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hM1 := rhsTerm1_memWkp (I := I) (M := M)
    g r s i α P₀ K (h_pou i)
  have hM2 := rhsTerm2_memWkp (I := I) (M := M)
    g r s i α P₀ K (h_pou i)
  have hM3 := rhsTerm3_memWkp (I := I) (M := M)
    g r s i α P₀ K (h_pou i)
  have hM4 := rhsTerm4_memWkp (I := I) (M := M)
    g r s i α P₀ K (h_pou i)
  have hM5 := rhsTerm5_memWkp (I := I) (M := M)
    g r s i α P₀ K (h_pou i)
  have hM6 := rhsTerm6_memWkp (I := I) (M := M)
    g r s i α P₀ K (h_pou i)
  have hM7 := rhsTerm7_memWkp (I := I) (M := M)
    g r s i α P₀ K (h_pou i)
  rw [← hΩ_def] at hM1 hM2 hM3 hM4 hM5 hM6 hM7
  have hp2 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hB12 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => rhsTerm1 (I := I) (M := M) g r s i α P₀ y
        - rhsTerm2 (I := I) (M := M) g r s i α P₀ y) Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open hM1 hM2
  have hB123 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (rhsTerm1 (I := I) (M := M) g r s i α P₀ y
          - rhsTerm2 (I := I) (M := M) g r s i α P₀ y)
        + rhsTerm3 (I := I) (M := M) g r s i α P₀ y) Ω :=
    MemWkp.add (d := Module.finrank ℝ E) hp2 hΩ_open hB12 hM3
  have hB1234 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((rhsTerm1 (I := I) (M := M) g r s i α P₀ y
            - rhsTerm2 (I := I) (M := M) g r s i α P₀ y)
          + rhsTerm3 (I := I) (M := M) g r s i α P₀ y)
        - rhsTerm4 (I := I) (M := M) g r s i α P₀ y) Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open hB123 hM4
  have hB12345 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (((rhsTerm1 (I := I) (M := M) g r s i α P₀ y
              - rhsTerm2 (I := I) (M := M) g r s i α P₀ y)
            + rhsTerm3 (I := I) (M := M) g r s i α P₀ y)
          - rhsTerm4 (I := I) (M := M) g r s i α P₀ y)
        - rhsTerm5 (I := I) (M := M) g r s i α P₀ y) Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open hB1234 hM5
  have hB123456 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((((rhsTerm1 (I := I) (M := M) g r s i α P₀ y
                - rhsTerm2 (I := I) (M := M) g r s i α P₀ y)
              + rhsTerm3 (I := I) (M := M) g r s i α P₀ y)
            - rhsTerm4 (I := I) (M := M) g r s i α P₀ y)
          - rhsTerm5 (I := I) (M := M) g r s i α P₀ y)
        + rhsTerm6 (I := I) (M := M) g r s i α P₀ y) Ω :=
    MemWkp.add (d := Module.finrank ℝ E) hp2 hΩ_open hB12345 hM6
  have hD1i := hD1 i
  have hD2i := hD2 i
  have hD3i := hD3 i
  have hD4i := hD4 i
  have hD5i := hD5 i
  have hD6i := hD6 i
  have hD7i := hD7 i
  have h_tri :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (rhsBracket (I := I) (M := M) g r s i α P₀) Ω
        ≤ wkpNorm (d := Module.finrank ℝ E) K 2
            (rhsTerm1 (I := I) (M := M) g r s i α P₀) Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2
              (rhsTerm2 (I := I) (M := M) g r s i α P₀) Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2
              (rhsTerm3 (I := I) (M := M) g r s i α P₀) Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2
              (rhsTerm4 (I := I) (M := M) g r s i α P₀) Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2
              (rhsTerm5 (I := I) (M := M) g r s i α P₀) Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2
              (rhsTerm6 (I := I) (M := M) g r s i α P₀) Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2
              (rhsTerm7 (I := I) (M := M) g r s i α P₀) Ω := by
    have h_bracket_eq :
        rhsBracket (I := I) (M := M) g r s i α P₀
        = fun y =>
            (((((rhsTerm1 (I := I) (M := M) g r s i α P₀ y
                  - rhsTerm2 (I := I) (M := M) g r s i α P₀ y)
                + rhsTerm3 (I := I) (M := M) g r s i α P₀ y)
              - rhsTerm4 (I := I) (M := M) g r s i α P₀ y)
            - rhsTerm5 (I := I) (M := M) g r s i α P₀ y)
          + rhsTerm6 (I := I) (M := M) g r s i α P₀ y)
          - rhsTerm7 (I := I) (M := M) g r s i α P₀ y := by
      funext y
      simp only [rhsBracket, Pi.sub_apply, Pi.add_apply]
    rw [h_bracket_eq]
    refine le_trans (wkpNorm_sub_le (K := K) hΩ_open hB123456 hM7) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (wkpNorm_add_le (d := Module.finrank ℝ E)
      (by norm_num) hΩ_open hB12345 hM6) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (wkpNorm_sub_le (K := K) hΩ_open hB1234 hM5) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (wkpNorm_sub_le (K := K) hΩ_open hB123 hM4) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (wkpNorm_add_le (d := Module.finrank ℝ E)
      (by norm_num) hΩ_open hB12 hM3) ?_
    refine add_le_add ?_ (le_refl _)
    exact wkpNorm_sub_le (K := K) hΩ_open hM1 hM2
  refine le_trans h_tri ?_
  have h_seven :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (rhsTerm1 (I := I) (M := M) g r s i α P₀) Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2
            (rhsTerm2 (I := I) (M := M) g r s i α P₀) Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2
            (rhsTerm3 (I := I) (M := M) g r s i α P₀) Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2
            (rhsTerm4 (I := I) (M := M) g r s i α P₀) Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2
            (rhsTerm5 (I := I) (M := M) g r s i α P₀) Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2
            (rhsTerm6 (I := I) (M := M) g r s i α P₀) Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2
            (rhsTerm7 (I := I) (M := M) g r s i α P₀) Ω
      ≤ ENNReal.ofReal D1 *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D2 *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D3 *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D4 *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D5 *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D6 *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D7 *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K :=
    add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (add_le_add hD1i hD2i) hD3i) hD4i) hD5i) hD6i) hD7i
  refine le_trans h_seven ?_
  rw [ENNReal.ofReal_add (by positivity) hD7_nn,
    ENNReal.ofReal_add (by positivity) hD6_nn,
    ENNReal.ofReal_add (by positivity) hD5_nn,
    ENNReal.ofReal_add (by positivity) hD4_nn,
    ENNReal.ofReal_add (by positivity) hD3_nn,
    ENNReal.ofReal_add hD1_nn hD2_nn]
  rw [add_mul, add_mul, add_mul, add_mul, add_mul, add_mul]

end UniformBracketBoundUnconditional

section UniformMainBoundUnconditional

/-- **Chart-locality-free twin of `eigenvectorChartRHS_wkpNorm_le_uniform`.** -/
theorem eigenvectorChartRHS_wkpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
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
            (eigenvectorChartRHS (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
            (wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (tensorResolventEigenbasisVec (I := I) (M := M)
                      (tensorResolventL2_isCompactOperator (I := I)
                        (M := M) g r s) i) α P₀ :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) α)
              + (∑ β ∈ transportChartCenters (I := I) (M := M) α,
                  ((∑ Q : TensorCompIdx (E := E) r s,
                      wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                        (fun y => ((tensorL2ChartComponent (I := I) (M := M)
                            g r s
                            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                              (eigenvectorResolvent (I := I)
                                (M := M) g r s i))
                            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                            EuclN → ℝ) y)
                        (chartTargetEuclid (I := I) (M := M) β))
                    + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
                        ∑ Q : TensorCompIdx (E := E) r s,
                          wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                            (fun y => ((tensorL2ChartComponent (I := I) (M := M)
                                g r s
                                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                                  (eigenvectorResolvent (I := I)
                                    (M := M) g r s i))
                                β' Q :
                                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                                EuclN → ℝ) y)
                            (chartTargetEuclid (I := I) (M := M) β')))
              + (∑ β ∈ transportChartCenters (I := I) (M := M) α,
                  ∑ Q : TensorCompIdx (E := E) r s,
                    wkpNorm (d := Module.finrank ℝ E) K 2
                      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                            (eigenvectorResolvent (I := I) (M := M)
                              g r s i))
                          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                          EuclN → ℝ) y)
                      (chartTargetEuclid (I := I) (M := M) β))
              + (∑ P : TensorCompIdx (E := E) r s,
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
                    (chartTargetEuclid (I := I) (M := M) α))
              + (∑ P : TensorCompIdx (E := E) r s,
                  wkpNorm (d := Module.finrank ℝ E) K 2
                    (fun y => ((crossRightLimitComponent (I := I)
                        (M := M) g r s i α P :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) y)
                    (chartTargetEuclid (I := I) (M := M) α))
              + (∑ P : TensorCompIdx (E := E) r s,
                  ∑ l : Fin (Module.finrank ℝ E),
                    wkpNorm (d := Module.finrank ℝ E) K 2
                      (fun y => ((cutoffPartialLpLimit (I := I)
                          (M := M) g r s i α P l :
                        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                        EuclN → ℝ) y)
                      (chartTargetEuclid (I := I) (M := M) α))) := by
  classical
  obtain ⟨C, hC_nn, hC_bd⟩ := rhsBracket_wkpNorm_le_uniform
    (I := I) (M := M) g r s α P₀ K h_pou
  refine ⟨C, hC_nn, fun i => ?_⟩
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hμ_pos : 0 < i.fst.val := eigenIdx_val_pos (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have h_bracket_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (rhsBracket (I := I) (M := M) g r s i α P₀) Ω := by
    have hM1 := rhsTerm1_memWkp (I := I) (M := M)
      g r s i α P₀ K (h_pou i)
    have hM2 := rhsTerm2_memWkp (I := I) (M := M)
      g r s i α P₀ K (h_pou i)
    have hM3 := rhsTerm3_memWkp (I := I) (M := M)
      g r s i α P₀ K (h_pou i)
    have hM4 := rhsTerm4_memWkp (I := I) (M := M)
      g r s i α P₀ K (h_pou i)
    have hM5 := rhsTerm5_memWkp (I := I) (M := M)
      g r s i α P₀ K (h_pou i)
    have hM6 := rhsTerm6_memWkp (I := I) (M := M)
      g r s i α P₀ K (h_pou i)
    have hM7 := rhsTerm7_memWkp (I := I) (M := M)
      g r s i α P₀ K (h_pou i)
    rw [← hΩ_def] at hM1 hM2 hM3 hM4 hM5 hM6 hM7
    have hp2 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
    have h_bracket_eq :
        rhsBracket (I := I) (M := M) g r s i α P₀
        = fun y =>
            (((((rhsTerm1 (I := I) (M := M) g r s i α P₀ y
                  - rhsTerm2 (I := I) (M := M) g r s i α P₀ y)
                + rhsTerm3 (I := I) (M := M) g r s i α P₀ y)
              - rhsTerm4 (I := I) (M := M) g r s i α P₀ y)
            - rhsTerm5 (I := I) (M := M) g r s i α P₀ y)
          + rhsTerm6 (I := I) (M := M) g r s i α P₀ y)
          - rhsTerm7 (I := I) (M := M) g r s i α P₀ y := by
      funext y
      simp only [rhsBracket, Pi.sub_apply, Pi.add_apply]
    rw [h_bracket_eq]
    exact MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open
      (MemWkp.add (d := Module.finrank ℝ E) hp2 hΩ_open
        (MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open
          (MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open
            (MemWkp.add (d := Module.finrank ℝ E) hp2 hΩ_open
              (MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open hM1 hM2) hM3)
            hM4) hM5) hM6) hM7
  have hC_bd_i := hC_bd i
  have h_smul_eq :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartRHS (I := I) (M := M)
            g r s i α P₀) Ω
        = ENNReal.ofReal (i.fst.val)⁻¹ *
          wkpNorm (d := Module.finrank ℝ E) K 2
            (rhsBracket (I := I) (M := M) g r s i α P₀) Ω := by
    rw [eigenvectorChartRHS_eq_smul_bracket (I := I) (M := M)
      g r s i α P₀]
    have h := wkpNorm_const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_bracket_memWkp (i.fst.val)⁻¹
    rw [h, Real.enorm_of_nonneg hμ_inv_nn]
  rw [h_smul_eq]
  have h_step :
      ENNReal.ofReal (i.fst.val)⁻¹ *
          wkpNorm (d := Module.finrank ℝ E) K 2
            (rhsBracket (I := I) (M := M) g r s i α P₀) Ω
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
    rw [ENNReal.ofReal_mul hμ_inv_nn, mul_assoc]
    gcongr
  refine le_trans h_step (le_of_eq ?_)
  simp only [hΩ_def, wkpRhsAggregate, aggrUchart,
    aggrCrossLeft, aggrCrossRight,
    aggrPartial, aggrComponent,
    aggrCrossRightLimit, aggrCutoffPartial,
    resInclNorm]

end UniformMainBoundUnconditional

end Unconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
