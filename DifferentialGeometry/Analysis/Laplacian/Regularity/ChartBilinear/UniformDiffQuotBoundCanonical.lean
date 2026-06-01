import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartBilinear.UniformDiffQuotBound
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartBilinear.UniformDiffQuotGTotalBound
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionDischargeAssembly
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionNonSmooth

/-!
# Unconditional uniform-in-`h` `L²` bound on the difference quotient of the
chart-pulled weak partial derivatives — setup

This module is the entry point for the unconditional version of
`chartBilinearH1Compl_uniform_diffQuot_bound`. The original wrapper takes
three analytical hypotheses (`h_FK_diffQuot_u_bound`, `h_v_test_sq_bound`,
`h_master_nonsmooth`) and produces a uniform-in-`h` per-`(i, k)`
`L²(Ω'')` bound on `D_h^k (g_g i)` for a globally-`L²` extension
`g_g i` of `D.weak_partial i`. The unconditional version aims to
discharge those three hypotheses internally from the chart-bilinear
data structure `D` and the substitution identity supplied by
`chartBilinear_substitution_identity_holds`, and to relate the output
bound on `g_g i` back to `D.weak_partial i` on `Ω''`.

This module provides the import-level setup and the local cutoff
construction used to glue `D`'s chart-pulled data into globally-`L²`
extensions. Subsequent modules (named `…_of_data`-suffixed) thread
the three discharges through the existing substitution-identity
machinery and the principal-term ellipticity bound.

## Discharge plan

The discharge constructs, internally:

* a smooth cutoff `χ` equal to `1` on a `1`-thickening of `tsupport η`
  and compactly supported strictly inside the chart target;
* a smooth elliptic bilinear form `B` whose principal coefficient
  agrees with `weightedInvGramOnEuclid g α` on the thickened compact
  set, via `exists_smooth_metric_extension`;
* the globally-`L²` extensions
  - `u_g := χ · D.u_chart`,
  - `f_g := χ · D.f_chart`,
  - `g_g i := (∂_i χ) · D.u_chart + χ · D.weak_partial i`.

The three discharges:

1. **`h_FK_diffQuot_u_bound`** — apply
   `integral_sq_diffQuot_le_integral_sq_weakPartial` to `u_g` with
   weak `k`-partial `g_g k`. Bound the RHS `∫_{Ω'} (g_g k)²` by
   `∫_{Ω'} ∑_l (g_g l)²` since all summands are non-negative.

2. **`h_v_test_sq_bound`** — apply
   `hasWeakPartialDeriv_eta_sq_diffQuot` (chain rule for
   `D_h^k (η² · D_h^k u_g)`) to obtain the explicit weak
   `k`-partial of `η² · D_h^k u_g`. Apply
   `eLpNorm_diffQuot_le_eLpNorm_weakPartial` to `D_{-h}^k(·)` (FK
   for the outer difference quotient). The result is the explicit
   sum-form bound; pointwise `(a + b)² ≤ 2 a² + 2 b²` combined with
   `η² ≤ 1` (from `η ∈ [0, 1]`) and `‖∂_k η‖ ≤ N` yields the
   factor `8 N²` on the first term and `2` on the second.

3. **`h_master_nonsmooth`** — the chart-bilinear substitution
   identity `chartBilinear_substitution_identity_holds` gives
   `principal + cross_1 + cross_2 + cross_3 + f_term = c_term`,
   hence `principal = c_term − cross_1 − cross_2 − cross_3 − f_term`.
   The ellipticity bound `B.lam · ∫ η² ∑(D_h^k g_g_l)² ≤ principal`
   (from `principal_term_ge_lambda_norm_sq_nonsmooth`) and the
   triangle inequality on the resulting expression for `principal`
   produce the master inequality. The bridge from the chart-bilinear
   coefficients (`weightedInvGramOnEuclid`) to the
   `SmoothEllipticBilinearForm` coefficients (`B.a`) uses the
   agreement `B.a = weightedInvGramOnEuclid` on the thickened cutoff
   support and the support of `η` restricting integration to that
   region.

The output bound, in terms of `g_g i`, is converted to a bound on
`D.weak_partial i` via the agreement `g_g i = D.weak_partial i` on
`cthickening 1 (tsupport η) ⊇ cthickening 1 Ω''`. For `x ∈ Ω''` and
`|h| ≤ 1`, both `x` and `x + h e_k` lie in this region, so
`diffQuot k h (g_g i) x = diffQuot k h (D.weak_partial i) x`, and
the L² norm equality follows.

## Closure hypothesis

The chart-containment constraint `closure Ω' ⊆ chartTargetEuclid α`
(replacing the trivially-true `closure Ω' ⊆ Set.univ` of the
hypothesis-bearing version) is mathematically essential: `D`'s
data are only locally `L²` on compact subsets of the chart target.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartBilinearUniformDiffQuotBoundCanonical

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
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearUniformDiffQuotBound
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
open DifferentialGeometry.Analysis.Sobolev.NirenbergDiffQuotTestFunction
open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox
open DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly
open DifferentialGeometry.Analysis.Sobolev.SubstitutionNonSmoothChartBilinear
open DifferentialGeometry.Analysis.Sobolev.NirenbergSubstitutionNonSmooth
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- Existence of a smooth cutoff `χ` equal to `1` on
`cthickening 1 (tsupport η)` and compactly supported strictly inside
`chartTargetEuclid α`. -/
theorem exists_cutoff_around_tsupport
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {α : M} {η : EuclN → ℝ} (hη_supp : HasCompactSupport η)
    (h_cthick_1_in_chart : Metric.cthickening 1 (tsupport η) ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    ∃ χ : EuclN → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧
      HasCompactSupport χ ∧
      (∀ x : EuclN, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x ∈ Metric.cthickening 1 (tsupport η), χ x = 1) ∧
      tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α := by
  classical
  have hη_tsupp_compact : IsCompact (tsupport η) := hη_supp
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_cthick_1_compact : IsCompact (Metric.cthickening 1 (tsupport η)) :=
    hη_tsupp_compact.cthickening
  obtain ⟨δ, hδ_pos, hδ_in_chart⟩ :=
    h_cthick_1_compact.exists_cthickening_subset_open h_chart_open
      h_cthick_1_in_chart
  obtain ⟨χ, hχ_smooth, hχ_cs, hχ_range, hχ_one, hχ_tsupp⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff
      (d := Module.finrank ℝ E)
      h_cthick_1_compact
      (Metric.isOpen_thickening (δ := δ)
        (E := Metric.cthickening 1 (tsupport η)))
      (Metric.self_subset_thickening hδ_pos _)
  have hχ_tsupp_in_chart : tsupport χ ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    intro x hx
    have h1 : x ∈ Metric.thickening δ (Metric.cthickening 1 (tsupport η)) :=
      hχ_tsupp hx
    have h2 : x ∈ Metric.cthickening δ (Metric.cthickening 1 (tsupport η)) :=
      Metric.thickening_subset_cthickening δ _ h1
    exact hδ_in_chart h2
  have hχ_nn : ∀ x : EuclN, 0 ≤ χ x ∧ χ x ≤ 1 := by
    intro x
    have hx_range : χ x ∈ Set.range χ := Set.mem_range_self x
    have hx_mem := hχ_range hx_range
    exact ⟨hx_mem.1, hx_mem.2⟩
  exact ⟨χ, hχ_smooth, hχ_cs, hχ_nn, hχ_one, hχ_tsupp_in_chart⟩

/-- The global `L²` extension `f_g := χ · D.f_chart`. -/
theorem cutoff_fChart_memLp_two_univ
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {χ : EuclN → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_cs : HasCompactSupport χ)
    (hχ_supp_in : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (fun x => χ x * D.f_chart x) 2 (volume : Measure EuclN) := by
  classical
  have hχ_cont : Continuous χ := hχ_smooth.continuous
  obtain ⟨M_χ, hM_χ_nn, hM_χ_bd⟩ : ∃ M_χ : ℝ, 0 ≤ M_χ ∧ ∀ x, |χ x| ≤ M_χ := by
    by_cases hSupp_empty : (tsupport χ).Nonempty
    · obtain ⟨xMax, _hxMax_in, hxMax_max⟩ :=
        hχ_cs.exists_isMaxOn hSupp_empty hχ_cont.abs.continuousOn
      refine ⟨|χ xMax|, abs_nonneg _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport χ
      · exact hxMax_max hx
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hχx, abs_zero]; exact abs_nonneg _
    · refine ⟨0, le_refl _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport χ
      · exact absurd ⟨x, hx⟩ hSupp_empty
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hχx, abs_zero]
  have h_supp_compact : IsCompact (tsupport χ) := hχ_cs
  have h_supp_meas : MeasurableSet (tsupport χ) :=
    (isClosed_tsupport χ).measurableSet
  have hf_l2_supp : MemLp D.f_chart 2
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
      D.f_chart_memLp_weighted h_supp_compact h_supp_meas hχ_supp_in
  have h_f_aesm_restrict : AEStronglyMeasurable D.f_chart
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    hf_l2_supp.aestronglyMeasurable
  have h_pt_le : ∀ᵐ x ∂((volume : Measure EuclN).restrict (tsupport χ)),
      ‖χ x * D.f_chart x‖ ≤ ‖M_χ * D.f_chart x‖ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg hM_χ_nn]
    exact mul_le_mul_of_nonneg_right (hM_χ_bd x) (abs_nonneg _)
  have h_prod_aesm_restrict :
      AEStronglyMeasurable (fun x => χ x * D.f_chart x)
        ((volume : Measure EuclN).restrict (tsupport χ)) :=
    hχ_cont.aestronglyMeasurable.restrict.mul h_f_aesm_restrict
  have h_restrict_lp : MemLp (fun x => χ x * D.f_chart x) 2
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    MemLp.mono (hf_l2_supp.const_mul M_χ) h_prod_aesm_restrict h_pt_le
  have h_indicator_eq : (tsupport χ).indicator (fun x => χ x * D.f_chart x) =
      (fun x => χ x * D.f_chart x) := by
    funext x
    by_cases hx : x ∈ tsupport χ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hχx, zero_mul]
  have h_indicator_lp :
      MemLp ((tsupport χ).indicator (fun x => χ x * D.f_chart x)) 2
        (volume : Measure EuclN) :=
    (MeasureTheory.memLp_indicator_iff_restrict h_supp_meas).mpr h_restrict_lp
  rw [h_indicator_eq] at h_indicator_lp
  exact h_indicator_lp

set_option linter.unusedVariables false in
/-- Discharge of `h_FK_diffQuot_u_bound` from the chart-bilinear data `D`,
with `u_g := D.u_chart` and `g_g l := D.weak_partial l`. The proof internally
constructs a smooth cutoff `χ` equal to `1` on a closed thickening of
`tsupport η` strictly larger than `cthickening R₀ (tsupport η)` (possible by
the chart-containment slack `closure Ω' ⊆ chartTargetEuclid α`) and applies
the non-smooth Fréchet–Kolmogorov bound to the cutoff extensions
`χ · D.u_chart` and `(∂_l χ) · D.u_chart + χ · D.weak_partial l`. The
inequality survives the conversion back to `D.u_chart` and `D.weak_partial l`
because, on the relevant integration regions, the cutoff agrees with the
identity (where `χ = 1`) and the derivative term `(∂_l χ) · D.u_chart`
vanishes (where `∂_l χ = 0`). The bound `R₀ > 0` is the diff-quotient
radius parameter; the proof works uniformly in `R₀`. -/
theorem chartBilinearFK_diffQuot_u_discharge
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {η : EuclN → ℝ} (hη_supp : HasCompactSupport η)
    {Ω' : Set EuclN} (hΩ'_open : IsOpen Ω')
    (hΩ'_chart : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hΩ'_compact_closure : IsCompact (closure Ω'))
    (hη_in_Ω' : tsupport η ⊆ Ω')
    {R₀ : ℝ} (hR₀_pos : 0 < R₀)
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω') :
    ∀ (k : Fin (Module.finrank ℝ E)),
    ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x in tsupport η,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart x)^2
        ∂(volume : Measure EuclN) ≤
        ∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E),
          ((D.weak_partial l) x) ^ 2
        ∂(volume : Measure EuclN) := by
  classical
  have hη_tsupp_compact : IsCompact (tsupport η) := hη_supp
  have h_cthickR0_compact : IsCompact (Metric.cthickening R₀ (tsupport η)) :=
    hη_tsupp_compact.cthickening
  have h_cthickR0_in_Ω' : Metric.cthickening R₀ (tsupport η) ⊆ Ω' := by
    have h := hh_supp_in_Ω' (h := R₀) (by rw [abs_of_pos hR₀_pos])
    rw [abs_of_pos hR₀_pos] at h
    exact h
  have h_cthickR0_in_chart :
      Metric.cthickening R₀ (tsupport η) ⊆
        chartTargetEuclid (I := I) (M := M) α :=
    h_cthickR0_in_Ω'.trans (subset_closure.trans hΩ'_chart)
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨δ, hδ_pos, hδ_in_chart⟩ :=
    h_cthickR0_compact.exists_cthickening_subset_open h_chart_open
      h_cthickR0_in_chart
  set r : ℝ := R₀ + δ / 2 with hr_def
  have hr_pos : 0 < r := by rw [hr_def]; linarith
  have hr_le : r ≤ R₀ + δ := by rw [hr_def]; linarith
  have h_cthick_r_compact : IsCompact (Metric.cthickening r (tsupport η)) :=
    hη_tsupp_compact.cthickening
  have h_cthick_r_in_chart :
      Metric.cthickening r (tsupport η) ⊆
        chartTargetEuclid (I := I) (M := M) α := by
    intro x hx
    have hx' : x ∈ Metric.cthickening (R₀ + δ) (tsupport η) :=
      Metric.cthickening_mono hr_le _ hx
    have h_eq : Metric.cthickening (R₀ + δ) (tsupport η) =
        Metric.cthickening δ (Metric.cthickening R₀ (tsupport η)) := by
      have hδ_le : (0 : ℝ) ≤ δ := hδ_pos.le
      have hR0_le : (0 : ℝ) ≤ R₀ := hR₀_pos.le
      rw [show (R₀ + δ) = (δ + R₀) from by ring,
        ← cthickening_cthickening hδ_le hR0_le]
    rw [h_eq] at hx'
    exact hδ_in_chart hx'
  obtain ⟨χ, hχ_smooth, hχ_cs, hχ_range, hχ_one, hχ_tsupp⟩ :=
    DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff
      (d := Module.finrank ℝ E)
      (K := Metric.cthickening r (tsupport η))
      (Ω' := chartTargetEuclid (I := I) (M := M) α)
      h_cthick_r_compact h_chart_open h_cthick_r_in_chart
  have hχ_nn : ∀ x : EuclN, 0 ≤ χ x ∧ χ x ≤ 1 := by
    intro x
    have hx_range : χ x ∈ Set.range χ := Set.mem_range_self x
    exact ⟨(hχ_range hx_range).1, (hχ_range hx_range).2⟩
  set u_g : EuclN → ℝ := fun x => χ x * D.u_chart x with hu_g_def
  set G : Fin (Module.finrank ℝ E) → EuclN → ℝ := fun i x =>
    (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.u_chart x +
    χ x * D.weak_partial i x with hG_def
  have hu_g_l2 : MemLp u_g 2 (volume : Measure EuclN) :=
    cutoff_uChart_memLp_two_univ (I := I) (M := M) D hχ_smooth hχ_cs hχ_tsupp
  have hG_l2 : ∀ i, MemLp (G i) 2 (volume : Measure EuclN) := fun i =>
    cutoff_uChart_partial_memLp_two_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_tsupp i
  have hG_isWP : ∀ i, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (G i) u_g Set.univ := fun i =>
    cutoff_uChart_hasWeakPartialDeriv_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_tsupp i
  intro k h hh hh_le
  have hh_abs_pos : 0 < |h| := abs_pos.mpr hh
  have hh_abs_le : |h| ≤ R₀ := hh_le
  set Ω'_fk : Set EuclN := Metric.cthickening |h| (tsupport η) with hΩ'_fk_def
  set Ω''_fk : Set EuclN := tsupport η with hΩ''_fk_def
  have hΩ'_fk_meas : MeasurableSet Ω'_fk := by
    rw [hΩ'_fk_def]; exact (Metric.isClosed_cthickening).measurableSet
  have hΩ''_fk_meas : MeasurableSet Ω''_fk := by
    rw [hΩ''_fk_def]; exact (isClosed_tsupport η).measurableSet
  have h_closure_eq : closure Ω''_fk = tsupport η := by
    rw [hΩ''_fk_def]; exact (isClosed_tsupport η).closure_eq
  have hΩ''_compact_closure : IsCompact (closure Ω''_fk) := by
    rw [h_closure_eq]; exact hη_tsupp_compact
  have h_thick : Metric.cthickening |h| (closure Ω''_fk) ⊆ Ω'_fk := by
    rw [h_closure_eq, hΩ'_fk_def]
  have h_FK : ∫ x in Ω''_fk,
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g x)^2
        ∂(volume : Measure EuclN) ≤
      ∫ x in Ω'_fk, (G k x)^2 ∂(volume : Measure EuclN) := by
    exact
      DifferentialGeometry.Analysis.Sobolev.integral_sq_diffQuot_le_integral_sq_weakPartial_meas
        (d := Module.finrank ℝ E)
        hu_g_l2 (hG_l2 k) k (hG_isWP k)
        hΩ'_fk_meas hΩ''_fk_meas
        hΩ''_compact_closure hh_abs_pos h_thick hh (le_refl |h|)
  have hr_ge_R0 : R₀ ≤ r := by rw [hr_def]; linarith
  have h_cthick_h_subset_r :
      Metric.cthickening |h| (tsupport η) ⊆ Metric.cthickening r (tsupport η) :=
    Metric.cthickening_mono (hh_abs_le.trans hr_ge_R0) _
  have h_self_subset_cthick_h :
      tsupport η ⊆ Metric.cthickening |h| (tsupport η) :=
    Metric.self_subset_cthickening _
  have h_diffQuot_eq_on_tsupport : ∀ x ∈ tsupport η,
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_g x =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart x := by
    intro x hx
    have hx_in_r : x ∈ Metric.cthickening r (tsupport η) := by
      exact h_cthick_h_subset_r (h_self_subset_cthick_h hx)
    have hχx : χ x = 1 := hχ_one x hx_in_r
    have h_shift_in_cthick_h :
        x + h • EuclideanSpace.single k 1 ∈ Metric.cthickening |h| (tsupport η) := by
      refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η) hx ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
      rw [hsing, mul_one, Real.norm_eq_abs]
    have h_shift_in_r : x + h • EuclideanSpace.single k 1 ∈
        Metric.cthickening r (tsupport η) := h_cthick_h_subset_r h_shift_in_cthick_h
    have hχ_shift : χ (x + h • EuclideanSpace.single k 1) = 1 :=
      hχ_one _ h_shift_in_r
    change
      (if h = 0 then 0 else
        (u_g (x + h • EuclideanSpace.single k 1) - u_g x) / h) =
      (if h = 0 then 0 else
        (D.u_chart (x + h • EuclideanSpace.single k 1) - D.u_chart x) / h)
    rw [if_neg hh, if_neg hh, hu_g_def]
    simp only [hχ_shift, hχx, one_mul]
  have h_LHS_eq :
      ∫ x in tsupport η,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart x)^2
        ∂(volume : Measure EuclN) =
      ∫ x in tsupport η,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun (isClosed_tsupport η).measurableSet ?_
    intro x hx
    have h_eq := h_diffQuot_eq_on_tsupport x hx
    exact congrArg (· ^ 2) h_eq.symm
  have hh_abs_lt_r : |h| < r := by rw [hr_def]; linarith
  have h_cthick_h_subset_thick_r :
      Metric.cthickening |h| (tsupport η) ⊆ Metric.thickening r (tsupport η) := by
    intro x hx
    have h_inf : Metric.infEDist x (tsupport η) ≤ ENNReal.ofReal |h| :=
      (Metric.mem_cthickening_iff).mp hx
    have h_ofReal_lt : ENNReal.ofReal |h| < ENNReal.ofReal r :=
      ENNReal.ofReal_lt_ofReal_iff hr_pos |>.mpr hh_abs_lt_r
    have h_inf_lt : Metric.infEDist x (tsupport η) < ENNReal.ofReal r :=
      lt_of_le_of_lt h_inf h_ofReal_lt
    exact (Metric.mem_thickening_iff_infEDist_lt).mpr h_inf_lt
  have h_thick_r_open : IsOpen (Metric.thickening r (tsupport η)) :=
    Metric.isOpen_thickening
  have h_thick_r_subset_cthick_r :
      Metric.thickening r (tsupport η) ⊆ Metric.cthickening r (tsupport η) :=
    Metric.thickening_subset_cthickening _ _
  have h_fderiv_zero_on_thick_r : ∀ x ∈ Metric.thickening r (tsupport η),
      (fderiv ℝ χ x) (EuclideanSpace.single k 1) = 0 := by
    intro x hx
    have hχ_eq_one_nhds : (fun y => χ y) =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
      refine Filter.eventually_of_mem (h_thick_r_open.mem_nhds hx) ?_
      intro y hy
      exact hχ_one y (h_thick_r_subset_cthick_r hy)
    have h_fderiv_eq : fderiv ℝ χ x = fderiv ℝ (fun _ : EuclN => (1 : ℝ)) x :=
      Filter.EventuallyEq.fderiv_eq hχ_eq_one_nhds
    rw [h_fderiv_eq]
    simp
  have hG_eq_on_cthick_h : ∀ x ∈ Metric.cthickening |h| (tsupport η),
      G k x = D.weak_partial k x := by
    intro x hx
    have hx_in_r : x ∈ Metric.cthickening r (tsupport η) := h_cthick_h_subset_r hx
    have hx_in_thick_r : x ∈ Metric.thickening r (tsupport η) :=
      h_cthick_h_subset_thick_r hx
    have hχx : χ x = 1 := hχ_one x hx_in_r
    have hdχx : (fderiv ℝ χ x) (EuclideanSpace.single k 1) = 0 :=
      h_fderiv_zero_on_thick_r x hx_in_thick_r
    change (fderiv ℝ χ x) (EuclideanSpace.single k 1) * D.u_chart x +
      χ x * D.weak_partial k x = D.weak_partial k x
    rw [hdχx, hχx, zero_mul, one_mul, zero_add]
  have h_FK_RHS_eq :
      ∫ x in Ω'_fk, (G k x)^2 ∂(volume : Measure EuclN) =
      ∫ x in Ω'_fk, (D.weak_partial k x)^2 ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ'_fk_meas ?_
    intro x hx
    have h_eq := hG_eq_on_cthick_h x (by rw [hΩ'_fk_def] at hx; exact hx)
    exact congrArg (· ^ 2) h_eq
  have h_cthick_h_subset_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω' :=
    hh_supp_in_Ω' hh_le
  have h_closure_Ω'_meas : MeasurableSet (closure Ω') :=
    isClosed_closure.measurableSet
  have h_wp_k_l2_closure_Ω' : MemLp (D.weak_partial k) 2
      ((volume : Measure EuclN).restrict (closure Ω')) :=
    D.weak_partial_locally_memLp k (closure Ω') hΩ'_compact_closure hΩ'_chart
  have h_wp_k_l2_Ω' : MemLp (D.weak_partial k) 2
      ((volume : Measure EuclN).restrict Ω') :=
    h_wp_k_l2_closure_Ω'.mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  have h_wp_k_intOn_Ω' : IntegrableOn (fun x => (D.weak_partial k x) ^ 2)
      Ω' (volume : Measure EuclN) :=
    h_wp_k_l2_Ω'.integrable_sq
  have h_set_mono :
      ∫ x in Ω'_fk, (D.weak_partial k x)^2 ∂(volume : Measure EuclN) ≤
      ∫ x in Ω', (D.weak_partial k x)^2 ∂(volume : Measure EuclN) := by
    refine setIntegral_mono_set h_wp_k_intOn_Ω' ?_ ?_
    · exact Filter.Eventually.of_forall fun x => sq_nonneg _
    · refine Filter.Eventually.of_forall ?_
      intro x hx
      rw [hΩ'_fk_def] at hx
      exact h_cthick_h_subset_Ω' hx
  have h_per_l_intOn : ∀ l, IntegrableOn (fun x => (D.weak_partial l x) ^ 2)
      Ω' (volume : Measure EuclN) := by
    intro l
    have h_wp_l_l2_closure_Ω' : MemLp (D.weak_partial l) 2
        ((volume : Measure EuclN).restrict (closure Ω')) :=
      D.weak_partial_locally_memLp l (closure Ω') hΩ'_compact_closure hΩ'_chart
    have h_wp_l_l2_Ω' : MemLp (D.weak_partial l) 2
        ((volume : Measure EuclN).restrict Ω') :=
      h_wp_l_l2_closure_Ω'.mono_measure
        (Measure.restrict_mono subset_closure le_rfl)
    exact h_wp_l_l2_Ω'.integrable_sq
  have h_sum_intOn : IntegrableOn
      (fun x => ∑ l : Fin (Module.finrank ℝ E), (D.weak_partial l x) ^ 2)
      Ω' (volume : Measure EuclN) :=
    integrable_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (μ := (volume : Measure EuclN).restrict Ω')
      (f := fun l x => (D.weak_partial l x) ^ 2)
      (fun l _ => h_per_l_intOn l)
  have h_k_le_sum :
      ∫ x in Ω', (D.weak_partial k x)^2 ∂(volume : Measure EuclN) ≤
      ∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E), ((D.weak_partial l) x)^2
        ∂(volume : Measure EuclN) := by
    refine integral_mono_ae (h_per_l_intOn k) h_sum_intOn ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    exact Finset.single_le_sum (f := fun l => (D.weak_partial l x) ^ 2)
      (fun l _ => sq_nonneg _) (Finset.mem_univ k)
  calc ∫ x in tsupport η,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart x)^2
        ∂(volume : Measure EuclN)
      = ∫ x in tsupport η,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2
        ∂(volume : Measure EuclN) := h_LHS_eq
    _ ≤ ∫ x in Ω'_fk, (G k x)^2 ∂(volume : Measure EuclN) := h_FK
    _ = ∫ x in Ω'_fk, (D.weak_partial k x)^2 ∂(volume : Measure EuclN) := h_FK_RHS_eq
    _ ≤ ∫ x in Ω', (D.weak_partial k x)^2 ∂(volume : Measure EuclN) := h_set_mono
    _ ≤ ∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E), ((D.weak_partial l) x)^2
        ∂(volume : Measure EuclN) := h_k_le_sum

set_option maxHeartbeats 1200000 in
set_option linter.unusedVariables false in
/-- Discharge of `h_v_test_sq_bound` from the chart-bilinear data `D`, with
`u_g := D.u_chart` and `g_g k := D.weak_partial k`. The proof builds a smooth
cutoff `χ` equal to `1` on a closed thickening of `tsupport η` strictly larger
than `cthickening R₀ (tsupport η)` (possible by the chart-containment slack
`closure Ω' ⊆ chartTargetEuclid α`), applies the `Set.univ`-weak-partial
chain rule for `η² · D_h^k (χ · D.u_chart)` and the Fréchet–Kolmogorov
bound for the outer difference quotient `D_{-h}^k`, then converts the
bound back to `D.u_chart` and `D.weak_partial k` using the cutoff
agreements on the relevant integration regions. The radius `R₀ > 0` is
the diff-quotient bound; the proof works uniformly in `R₀`. -/
theorem chartBilinear_v_test_sq_discharge
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : EuclN, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' : Set EuclN} (hΩ'_open : IsOpen Ω')
    (hΩ'_chart : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hΩ'_compact_closure : IsCompact (closure Ω'))
    (hη_in_Ω' : tsupport η ⊆ Ω')
    {R₀ : ℝ} (hR₀_pos : 0 < R₀)
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω') :
    ∀ (k : Fin (Module.finrank ℝ E)), ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x,
          (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            (d := Module.finrank ℝ E) k h η D.u_chart x)^2
        ∂(volume : Measure EuclN) ≤
        8 * N^2 *
          ∫ x in tsupport η,
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.u_chart x)^2
          ∂(volume : Measure EuclN) +
        2 * ∫ x, (η x)^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial k) x)^2
          ∂(volume : Measure EuclN) := by
  classical
  have hη_tsupp_compact : IsCompact (tsupport η) := hη_supp
  have h_cthickR0_compact : IsCompact (Metric.cthickening R₀ (tsupport η)) :=
    hη_tsupp_compact.cthickening
  have h_cthickR0_in_Ω' : Metric.cthickening R₀ (tsupport η) ⊆ Ω' := by
    have h := hh_supp_in_Ω' (h := R₀) (by rw [abs_of_pos hR₀_pos])
    rw [abs_of_pos hR₀_pos] at h
    exact h
  have h_cthickR0_in_chart :
      Metric.cthickening R₀ (tsupport η) ⊆
        chartTargetEuclid (I := I) (M := M) α :=
    h_cthickR0_in_Ω'.trans (subset_closure.trans hΩ'_chart)
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨δ, hδ_pos, hδ_in_chart⟩ :=
    h_cthickR0_compact.exists_cthickening_subset_open h_chart_open
      h_cthickR0_in_chart
  set r : ℝ := R₀ + δ / 2 with hr_def
  have hr_pos : 0 < r := by rw [hr_def]; linarith
  have hr_gt_R0 : R₀ < r := by rw [hr_def]; linarith
  have hr_ge_R0 : R₀ ≤ r := hr_gt_R0.le
  have hr_le : r ≤ R₀ + δ := by rw [hr_def]; linarith
  have h_cthick_r_compact : IsCompact (Metric.cthickening r (tsupport η)) :=
    hη_tsupp_compact.cthickening
  have h_cthick_r_in_chart :
      Metric.cthickening r (tsupport η) ⊆
        chartTargetEuclid (I := I) (M := M) α := by
    intro x hx
    have hx' : x ∈ Metric.cthickening (R₀ + δ) (tsupport η) :=
      Metric.cthickening_mono hr_le _ hx
    have h_eq : Metric.cthickening (R₀ + δ) (tsupport η) =
        Metric.cthickening δ (Metric.cthickening R₀ (tsupport η)) := by
      have hδ_le : (0 : ℝ) ≤ δ := hδ_pos.le
      have hR0_le : (0 : ℝ) ≤ R₀ := hR₀_pos.le
      rw [show (R₀ + δ) = (δ + R₀) from by ring,
        ← cthickening_cthickening hδ_le hR0_le]
    rw [h_eq] at hx'
    exact hδ_in_chart hx'
  obtain ⟨χ, hχ_smooth, hχ_cs, hχ_range, hχ_one, hχ_tsupp⟩ :=
    DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff
      (d := Module.finrank ℝ E)
      (K := Metric.cthickening r (tsupport η))
      (Ω' := chartTargetEuclid (I := I) (M := M) α)
      h_cthick_r_compact h_chart_open h_cthick_r_in_chart
  have hχ_nn : ∀ x : EuclN, 0 ≤ χ x ∧ χ x ≤ 1 := by
    intro x
    have hx_range : χ x ∈ Set.range χ := Set.mem_range_self x
    exact ⟨(hχ_range hx_range).1, (hχ_range hx_range).2⟩
  set u_g : EuclN → ℝ := fun x => χ x * D.u_chart x with hu_g_def
  set G : Fin (Module.finrank ℝ E) → EuclN → ℝ := fun i x =>
    (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.u_chart x +
    χ x * D.weak_partial i x with hG_def
  have hu_g_l2 : MemLp u_g 2 (volume : Measure EuclN) :=
    cutoff_uChart_memLp_two_univ (I := I) (M := M) D hχ_smooth hχ_cs hχ_tsupp
  have hG_l2 : ∀ i, MemLp (G i) 2 (volume : Measure EuclN) := fun i =>
    cutoff_uChart_partial_memLp_two_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_tsupp i
  have hG_isWP : ∀ i, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (G i) u_g Set.univ := fun i =>
    cutoff_uChart_hasWeakPartialDeriv_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_tsupp i
  have hu_g_locInt :
      LocallyIntegrable u_g ((volume : Measure EuclN).restrict Set.univ) := by
    have : LocallyIntegrable u_g (volume : Measure EuclN) :=
      hu_g_l2.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    rw [Measure.restrict_univ]; exact this
  have hG_locInt : ∀ i,
      LocallyIntegrable (G i) ((volume : Measure EuclN).restrict Set.univ) :=
    fun i => by
      have : LocallyIntegrable (G i) (volume : Measure EuclN) :=
        (hG_l2 i).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      rw [Measure.restrict_univ]; exact this
  intro k h hh hh_le
  have hh_abs_pos : 0 < |h| := abs_pos.mpr hh
  have hh_abs_le : |h| ≤ R₀ := hh_le
  have hh_abs_lt_r : |h| < r := lt_of_le_of_lt hh_abs_le hr_gt_R0
  have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
  have h_abs_nh : |-h| = |h| := abs_neg h
  have h_inner_wp :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
        (fun y => (η y)^2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h (G k) y +
          ((fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single k 1)) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h u_g y)
        (fun y => (η y)^2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h u_g y)
        Set.univ :=
    DifferentialGeometry.Analysis.Sobolev.NirenbergDiffQuotTestFunction.hasWeakPartialDeriv_eta_sq_diffQuot
      (d := Module.finrank ℝ E) k k h hη hu_g_locInt (hG_locInt k) (hG_isWP k)
  have h_self_subset_cthick :
      tsupport η ⊆ Metric.cthickening |h| (tsupport η) :=
    Metric.self_subset_cthickening _
  have h_cthick_h_subset_R0 :
      Metric.cthickening |h| (tsupport η) ⊆
        Metric.cthickening R₀ (tsupport η) :=
    Metric.cthickening_mono hh_abs_le _
  have h_cthick_R0_subset_r :
      Metric.cthickening R₀ (tsupport η) ⊆ Metric.cthickening r (tsupport η) :=
    Metric.cthickening_mono hr_ge_R0 _
  have h_cthick_h_subset_r :
      Metric.cthickening |h| (tsupport η) ⊆ Metric.cthickening r (tsupport η) :=
    h_cthick_h_subset_R0.trans h_cthick_R0_subset_r
  have h_cthick_h_subset_thick_r :
      Metric.cthickening |h| (tsupport η) ⊆ Metric.thickening r (tsupport η) := by
    intro x hx
    have h_inf : Metric.infEDist x (tsupport η) ≤ ENNReal.ofReal |h| :=
      (Metric.mem_cthickening_iff).mp hx
    have h_ofReal_lt : ENNReal.ofReal |h| < ENNReal.ofReal r :=
      ENNReal.ofReal_lt_ofReal_iff hr_pos |>.mpr hh_abs_lt_r
    have h_inf_lt : Metric.infEDist x (tsupport η) < ENNReal.ofReal r :=
      lt_of_le_of_lt h_inf h_ofReal_lt
    exact (Metric.mem_thickening_iff_infEDist_lt).mpr h_inf_lt
  have h_tsupp_subset_thick_r : tsupport η ⊆ Metric.thickening r (tsupport η) :=
    Metric.self_subset_thickening hr_pos _
  have h_thick_r_open : IsOpen (Metric.thickening r (tsupport η)) :=
    Metric.isOpen_thickening
  have h_thick_r_subset_cthick_r :
      Metric.thickening r (tsupport η) ⊆ Metric.cthickening r (tsupport η) :=
    Metric.thickening_subset_cthickening _ _
  have hχ_one_on_r : ∀ x ∈ Metric.cthickening r (tsupport η), χ x = 1 :=
    fun x hx => hχ_one x hx
  have h_fderiv_zero_on_thick_r : ∀ x ∈ Metric.thickening r (tsupport η),
      (fderiv ℝ χ x) (EuclideanSpace.single k 1) = 0 := by
    intro x hx
    have hχ_eq_one_nhds : (fun y => χ y) =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
      refine Filter.eventually_of_mem (h_thick_r_open.mem_nhds hx) ?_
      intro y hy
      exact hχ_one y (h_thick_r_subset_cthick_r hy)
    have h_fderiv_eq : fderiv ℝ χ x = fderiv ℝ (fun _ : EuclN => (1 : ℝ)) x :=
      Filter.EventuallyEq.fderiv_eq hχ_eq_one_nhds
    rw [h_fderiv_eq]
    simp
  have h_u_g_eq_on_cthick_R0 : ∀ x ∈ Metric.cthickening R₀ (tsupport η),
      u_g x = D.u_chart x := by
    intro x hx
    have hx_in_r : x ∈ Metric.cthickening r (tsupport η) :=
      h_cthick_R0_subset_r hx
    have hχx : χ x = 1 := hχ_one_on_r x hx_in_r
    change χ x * D.u_chart x = D.u_chart x
    rw [hχx, one_mul]
  have h_G_eq_on_thick_r : ∀ x ∈ Metric.thickening r (tsupport η),
      G k x = D.weak_partial k x := by
    intro x hx
    have hx_in_cthick_r : x ∈ Metric.cthickening r (tsupport η) :=
      h_thick_r_subset_cthick_r hx
    have hχx : χ x = 1 := hχ_one_on_r x hx_in_cthick_r
    have hdχx : (fderiv ℝ χ x) (EuclideanSpace.single k 1) = 0 :=
      h_fderiv_zero_on_thick_r x hx
    change (fderiv ℝ χ x) (EuclideanSpace.single k 1) * D.u_chart x +
      χ x * D.weak_partial k x = D.weak_partial k x
    rw [hdχx, hχx, zero_mul, one_mul, zero_add]
  have h_diffQuot_u_eq_on_tsupport : ∀ x ∈ tsupport η,
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_g x =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart x := by
    intro x hx
    have hx_in_cthick_h : x ∈ Metric.cthickening |h| (tsupport η) :=
      h_self_subset_cthick hx
    have hx_in_cthick_R0 : x ∈ Metric.cthickening R₀ (tsupport η) :=
      h_cthick_h_subset_R0 hx_in_cthick_h
    have h_shift_in_cthick_h :
        x + h • EuclideanSpace.single k 1 ∈ Metric.cthickening |h| (tsupport η) := by
      refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η) hx ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
      rw [hsing, mul_one, Real.norm_eq_abs]
    have h_shift_in_cthick_R0 :
        x + h • EuclideanSpace.single k 1 ∈ Metric.cthickening R₀ (tsupport η) :=
      h_cthick_h_subset_R0 h_shift_in_cthick_h
    have hux : u_g x = D.u_chart x :=
      h_u_g_eq_on_cthick_R0 x hx_in_cthick_R0
    have hux_shift : u_g (x + h • EuclideanSpace.single k 1) =
        D.u_chart (x + h • EuclideanSpace.single k 1) :=
      h_u_g_eq_on_cthick_R0 _ h_shift_in_cthick_R0
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh,
      DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh,
      hux, hux_shift]
  have h_diffQuot_G_eq_on_tsupport : ∀ x ∈ tsupport η,
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (G k) x =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial k) x := by
    intro x hx
    have hx_in_thick_r : x ∈ Metric.thickening r (tsupport η) :=
      h_tsupp_subset_thick_r hx
    have hx_in_cthick_h : x ∈ Metric.cthickening |h| (tsupport η) :=
      h_self_subset_cthick hx
    have h_shift_in_cthick_h :
        x + h • EuclideanSpace.single k 1 ∈ Metric.cthickening |h| (tsupport η) := by
      refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η) hx ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
      rw [hsing, mul_one, Real.norm_eq_abs]
    have h_shift_in_thick_r :
        x + h • EuclideanSpace.single k 1 ∈ Metric.thickening r (tsupport η) :=
      h_cthick_h_subset_thick_r h_shift_in_cthick_h
    have hGx : G k x = D.weak_partial k x := h_G_eq_on_thick_r x hx_in_thick_r
    have hGx_shift : G k (x + h • EuclideanSpace.single k 1) =
        D.weak_partial k (x + h • EuclideanSpace.single k 1) :=
      h_G_eq_on_thick_r _ h_shift_in_thick_r
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh,
      DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh,
      hGx, hGx_shift]
  set F : EuclN → ℝ := fun y => (η y)^2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_g y with hF_def
  set G_F : EuclN → ℝ := fun y => (η y)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) y +
      ((fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single k 1)) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g y with hG_F_def
  have hF_wp : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k G_F F
      Set.univ := h_inner_wp
  have hη_sq_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN => (η y)^2) :=
    hη.pow 2
  have hη_sq_cont : Continuous (fun y : EuclN => (η y)^2) :=
    hη_sq_smooth.continuous
  have hη_pt : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1 := fun x =>
    hη_range (Set.mem_range_self x)
  have hη_nn : ∀ x, 0 ≤ η x := fun x => (hη_pt x).1
  have hη_le_one : ∀ x, η x ≤ 1 := fun x => (hη_pt x).2
  have hη_sq_nn : ∀ x, 0 ≤ (η x)^2 := fun x => sq_nonneg _
  have hη_sq_le_one : ∀ x, (η x)^2 ≤ 1 := fun x => by
    have h := hη_pt x
    nlinarith [h.1, h.2]
  have h_abs_eta_le_one : ∀ x, |η x| ≤ 1 := fun x =>
    abs_le.mpr ⟨by linarith [hη_nn x], hη_le_one x⟩
  have hη_sq_supp : HasCompactSupport (fun y : EuclN => (η y)^2) := by
    have heq : (fun y : EuclN => (η y)^2) = (fun y : EuclN => η y * η y) := by
      funext y; ring
    rw [heq]; exact hη_supp.mul_right
  have hF_cs : HasCompactSupport F := by
    rw [hF_def]; exact hη_sq_supp.mul_right
  have hF_supp_subset : tsupport F ⊆ tsupport η := by
    have h_supp_subset : Function.support F ⊆ Function.support η := by
      intro x hx
      change (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x ≠ 0 at hx
      have hη_x_ne : η x ≠ 0 := by
        intro hη_zero
        have hη_sq_zero : (η x)^2 = 0 := by rw [hη_zero]; ring
        apply hx; rw [hη_sq_zero, zero_mul]
      exact hη_x_ne
    exact (closure_mono h_supp_subset)
  have h_translate_u_g_l2 :
      MemLp
        (DifferentialGeometry.Analysis.Sobolev.translate
          (d := Module.finrank ℝ E) k h u_g) 2 (volume : Measure EuclN) :=
    DifferentialGeometry.Analysis.Sobolev.memLp_translate
      (d := Module.finrank ℝ E) k h hu_g_l2
  have h_diffQuot_u_g_l2 :
      MemLp
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g) 2 (volume : Measure EuclN) := by
    have h_eq :
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g =
        fun x : EuclN =>
          h⁻¹ * (DifferentialGeometry.Analysis.Sobolev.translate
              (d := Module.finrank ℝ E) k h u_g x) + (-h⁻¹) * u_g x := by
      funext x
      rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh]
      change (u_g (x + h • EuclideanSpace.single k 1) - u_g x) / h =
        h⁻¹ * u_g (x + h • EuclideanSpace.single k 1) + (-h⁻¹) * u_g x
      field_simp; ring
    rw [h_eq]
    have h1 : MemLp
        (fun x : EuclN => h⁻¹ *
          DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h u_g x) 2 (volume : Measure EuclN) := by
      have h_eq_smul : (fun x : EuclN => h⁻¹ *
          DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h u_g x) =
          h⁻¹ • (DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h u_g) := by
        funext x; rw [Pi.smul_apply, smul_eq_mul]
      rw [h_eq_smul]
      exact h_translate_u_g_l2.const_smul h⁻¹
    have h2 : MemLp (fun x : EuclN => (-h⁻¹) * u_g x) 2
        (volume : Measure EuclN) := by
      have h_eq_smul : (fun x : EuclN => (-h⁻¹) * u_g x) = (-h⁻¹) • u_g := by
        funext x; rw [Pi.smul_apply, smul_eq_mul]
      rw [h_eq_smul]
      exact hu_g_l2.const_smul (-h⁻¹)
    exact h1.add h2
  have h_translate_G_l2 :
      MemLp
        (DifferentialGeometry.Analysis.Sobolev.translate
          (d := Module.finrank ℝ E) k h (G k)) 2 (volume : Measure EuclN) :=
    DifferentialGeometry.Analysis.Sobolev.memLp_translate
      (d := Module.finrank ℝ E) k h (hG_l2 k)
  have h_diffQuot_G_l2 :
      MemLp
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k)) 2 (volume : Measure EuclN) := by
    have h_eq :
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) =
        fun x : EuclN =>
          h⁻¹ * (DifferentialGeometry.Analysis.Sobolev.translate
              (d := Module.finrank ℝ E) k h (G k) x) + (-h⁻¹) * (G k) x := by
      funext x
      rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh]
      change ((G k) (x + h • EuclideanSpace.single k 1) - (G k) x) / h =
        h⁻¹ * (G k) (x + h • EuclideanSpace.single k 1) + (-h⁻¹) * (G k) x
      field_simp; ring
    rw [h_eq]
    have h1 : MemLp
        (fun x : EuclN => h⁻¹ *
          DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h (G k) x) 2
        (volume : Measure EuclN) := by
      have h_eq_smul : (fun x : EuclN => h⁻¹ *
          DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h (G k) x) =
          h⁻¹ • (DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h (G k)) := by
        funext x; rw [Pi.smul_apply, smul_eq_mul]
      rw [h_eq_smul]
      exact h_translate_G_l2.const_smul h⁻¹
    have h2 : MemLp (fun x : EuclN => (-h⁻¹) * (G k) x) 2
        (volume : Measure EuclN) := by
      have h_eq_smul : (fun x : EuclN => (-h⁻¹) * (G k) x) = (-h⁻¹) • (G k) := by
        funext x; rw [Pi.smul_apply, smul_eq_mul]
      rw [h_eq_smul]
      exact (hG_l2 k).const_smul (-h⁻¹)
    exact h1.add h2
  have hF_l2 : MemLp F 2 (volume : Measure EuclN) := by
    have h_aesm_F : AEStronglyMeasurable F (volume : Measure EuclN) := by
      have h_eta_sq_aesm :
          AEStronglyMeasurable (fun y : EuclN => (η y)^2)
            (volume : Measure EuclN) := hη_sq_cont.aestronglyMeasurable
      have h_diffQuot_aesm :
          AEStronglyMeasurable
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g) (volume : Measure EuclN) :=
        h_diffQuot_u_g_l2.aestronglyMeasurable
      exact h_eta_sq_aesm.mul h_diffQuot_aesm
    have h_pt_le : ∀ᵐ x ∂(volume : Measure EuclN),
        ‖F x‖ ≤ ‖DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g x‖ := by
      refine Filter.Eventually.of_forall ?_
      intro x
      change ‖(η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x‖ ≤ _
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (hη_sq_nn x)]
      have h_le1 : (η x)^2 ≤ 1 := hη_sq_le_one x
      nlinarith [abs_nonneg
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g x), hη_sq_nn x]
    exact MemLp.mono h_diffQuot_u_g_l2 h_aesm_F h_pt_le
  have h_eta_sq_fderiv_cont :
      Continuous (fun y : EuclN =>
        (fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single k 1)) := by
    have h_top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by decide
    exact (hη_sq_smooth.continuous_fderiv h_top_ne_zero).clm_apply continuous_const
  have h_eta_sq_fderiv_cs : HasCompactSupport
      (fun y : EuclN =>
        (fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single k 1)) :=
    hη_sq_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k 1)
  have h_eta_sq_fderiv_bound : ∀ y : EuclN,
      |(fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single k 1)| ≤ 2 * N := by
    intro y
    have h_eq : (fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single k 1) =
        2 * η y * (fderiv ℝ η y) (EuclideanSpace.single k 1) := by
      have hη_diff : Differentiable ℝ η := hη.differentiable (by simp)
      rw [fderiv_fun_pow 2 (hη_diff y)]
      rw [ContinuousLinearMap.smul_apply]
      have h1 : (η y) ^ ((2 : ℕ) - 1) = η y := by norm_num
      rw [h1]
      have h_two : ((2 : ℕ) • η y) = 2 * η y := by rw [two_smul]; ring
      rw [h_two, smul_eq_mul]
    rw [h_eq, abs_mul, abs_mul]
    have h_eta_abs : |η y| ≤ 1 := h_abs_eta_le_one y
    have h_eta_partial_abs :
        |(fderiv ℝ η y) (EuclideanSpace.single k 1)| ≤ N := by
      have h_apply_le :
          ‖(fderiv ℝ η y) (EuclideanSpace.single k 1)‖ ≤
            ‖fderiv ℝ η y‖ * ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ :=
        (fderiv ℝ η y).le_opNorm (EuclideanSpace.single k 1)
      have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
      rw [hsing, mul_one, Real.norm_eq_abs] at h_apply_le
      exact h_apply_le.trans (h_fderiv_eta y)
    have h_2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h_2]
    have h_step1 : 2 * |η y| ≤ 2 := by linarith
    have h_step2 : 0 ≤ |(fderiv ℝ η y) (EuclideanSpace.single k 1)| :=
      abs_nonneg _
    nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg (η y))]
  have hG_F_l2 : MemLp G_F 2 (volume : Measure EuclN) := by
    have h_T1_l2 : MemLp (fun y : EuclN => (η y)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) y) 2 (volume : Measure EuclN) := by
      have h_aesm : AEStronglyMeasurable (fun y : EuclN => (η y)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) y)
          (volume : Measure EuclN) :=
        hη_sq_cont.aestronglyMeasurable.mul
          h_diffQuot_G_l2.aestronglyMeasurable
      have h_pt_le : ∀ᵐ x ∂(volume : Measure EuclN),
          ‖(η x)^2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (G k) x‖ ≤
            ‖DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (G k) x‖ := by
        refine Filter.Eventually.of_forall ?_
        intro x
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (hη_sq_nn x)]
        have h_le1 : (η x)^2 ≤ 1 := hη_sq_le_one x
        nlinarith [abs_nonneg
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x), hη_sq_nn x]
      exact MemLp.mono h_diffQuot_G_l2 h_aesm h_pt_le
    have h_T2_l2 : MemLp (fun y : EuclN =>
        ((fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single k 1)) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g y) 2 (volume : Measure EuclN) := by
      have h_aesm : AEStronglyMeasurable (fun y : EuclN =>
          ((fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single k 1)) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g y)
          (volume : Measure EuclN) :=
        h_eta_sq_fderiv_cont.aestronglyMeasurable.mul
          h_diffQuot_u_g_l2.aestronglyMeasurable
      have h_pt_le : ∀ᵐ x ∂(volume : Measure EuclN),
          ‖((fderiv ℝ (fun z => (η z)^2) x) (EuclideanSpace.single k 1)) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g x‖ ≤
            ‖(2 * N) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h u_g x‖ := by
        refine Filter.Eventually.of_forall ?_
        intro x
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
        have h_2N_nn : 0 ≤ 2 * N := by linarith
        rw [abs_of_nonneg h_2N_nn]
        exact mul_le_mul_of_nonneg_right (h_eta_sq_fderiv_bound x) (abs_nonneg _)
      exact MemLp.mono (h_diffQuot_u_g_l2.const_mul (2 * N)) h_aesm h_pt_le
    exact h_T1_l2.add h_T2_l2
  set Ω''_fk : Set EuclN := Metric.thickening (R₀ + 1) (tsupport η) with hΩ''_fk_def
  have hΩ''_fk_open : IsOpen Ω''_fk := Metric.isOpen_thickening
  have hΩ''_fk_meas : MeasurableSet Ω''_fk := hΩ''_fk_open.measurableSet
  have h_closure_Ω''_fk_compact : IsCompact (closure Ω''_fk) := by
    have h_le : closure Ω''_fk ⊆ Metric.cthickening (R₀ + 1) (tsupport η) := by
      rw [hΩ''_fk_def]
      exact Metric.closure_thickening_subset_cthickening _ _
    exact (hη_tsupp_compact.cthickening).of_isClosed_subset
      isClosed_closure h_le
  have hR0_plus_one_pos : 0 < R₀ + 1 := by linarith
  have hh_abs_le_R0_plus_one : |-h| ≤ R₀ + 1 := by
    rw [h_abs_nh]; linarith
  have hh_abs_pos_nh : 0 < |-h| := by rw [h_abs_nh]; exact hh_abs_pos
  have h_thick_outer :
      Metric.cthickening |-h| (closure Ω''_fk) ⊆ (Set.univ : Set EuclN) :=
    fun _ _ => trivial
  have h_FK_F : ∫ x in Ω''_fk,
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h) F x)^2
        ∂(volume : Measure EuclN) ≤
      ∫ x in (Set.univ : Set EuclN), (G_F x)^2 ∂(volume : Measure EuclN) :=
    DifferentialGeometry.Analysis.Sobolev.integral_sq_diffQuot_le_integral_sq_weakPartial_meas
      (d := Module.finrank ℝ E)
      hF_l2 hG_F_l2 k hF_wp MeasurableSet.univ hΩ''_fk_meas
      h_closure_Ω''_fk_compact hh_abs_pos_nh h_thick_outer hnh (le_refl _)
  have h_v_eq_diffQuot : ∀ x,
      DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
        (d := Module.finrank ℝ E) k h η u_g x =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h) F x := by
    intro x
    rfl
  have h_support_diffQuot_F_subset_Ω''_fk : ∀ x,
      x ∉ Ω''_fk →
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h) F x = 0 := by
    intro x hx_notin
    have hx_far : Metric.infEDist x (tsupport η) ≥ ENNReal.ofReal (R₀ + 1) := by
      have : ¬ Metric.infEDist x (tsupport η) < ENNReal.ofReal (R₀ + 1) := by
        intro h_lt
        apply hx_notin
        rw [hΩ''_fk_def]
        exact (Metric.mem_thickening_iff_infEDist_lt).mpr h_lt
      exact not_lt.mp this
    have hx_notin_tsupp : x ∉ tsupport η := by
      intro hx_in
      have h_zero : Metric.infEDist x (tsupport η) = 0 :=
        Metric.infEDist_zero_of_mem hx_in
      rw [h_zero] at hx_far
      have h_pos : (0 : ℝ≥0∞) < ENNReal.ofReal (R₀ + 1) :=
        ENNReal.ofReal_pos.mpr hR0_plus_one_pos
      exact absurd hx_far (not_le.mpr h_pos)
    have hF_x_zero : F x = 0 := by
      have hη_x_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx_notin_tsupp
      change (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x = 0
      rw [hη_x_zero]; ring
    have h_shift_notin_tsupp :
        x + (-h) • EuclideanSpace.single k 1 ∉ tsupport η := by
      intro h_in
      have h_dist_shift_x :
          dist (x + (-h) • EuclideanSpace.single k 1) x = |h| := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
        have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
        rw [hsing, mul_one, Real.norm_eq_abs, abs_neg]
      have h_inf_le : Metric.infEDist x (tsupport η) ≤
          edist x (x + (-h) • EuclideanSpace.single k 1) :=
        Metric.infEDist_le_edist_of_mem h_in
      have h_edist_eq : edist x (x + (-h) • EuclideanSpace.single k 1) =
          ENNReal.ofReal |h| := by
        rw [edist_dist]
        have : dist x (x + (-h) • EuclideanSpace.single k 1) = |h| := by
          rw [dist_comm]; exact h_dist_shift_x
        rw [this]
      rw [h_edist_eq] at h_inf_le
      have h_h_lt_R0_plus_one : ENNReal.ofReal |h| < ENNReal.ofReal (R₀ + 1) :=
        (ENNReal.ofReal_lt_ofReal_iff hR0_plus_one_pos).mpr (by linarith)
      have h_inf_lt : Metric.infEDist x (tsupport η) < ENNReal.ofReal (R₀ + 1) :=
        lt_of_le_of_lt h_inf_le h_h_lt_R0_plus_one
      have h_inf_not_lt : ¬ Metric.infEDist x (tsupport η) < ENNReal.ofReal (R₀ + 1) :=
        not_lt.mpr hx_far
      exact absurd h_inf_lt h_inf_not_lt
    have hF_shift_zero : F (x + (-h) • EuclideanSpace.single k 1) = 0 := by
      have hη_shift_zero : η (x + (-h) • EuclideanSpace.single k 1) = 0 :=
        image_eq_zero_of_notMem_tsupport h_shift_notin_tsupp
      change (η (x + (-h) • EuclideanSpace.single k 1))^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g
            (x + (-h) • EuclideanSpace.single k 1) = 0
      rw [hη_shift_zero]; ring
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := Module.finrank ℝ E) k hnh,
      hF_shift_zero, hF_x_zero, sub_zero, zero_div]
  have h_int_univ_F :
      ∫ x, (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h) F x)^2
          ∂(volume : Measure EuclN) =
      ∫ x in Ω''_fk,
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h) F x)^2
        ∂(volume : Measure EuclN) := by
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Ω''_fk) (μ := (volume : Measure EuclN)) ?_).symm
    intro x hx_notin
    have h_zero := h_support_diffQuot_F_subset_Ω''_fk x hx_notin
    rw [h_zero]; ring
  have h_F_eq_D : F = fun y => (η y)^2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart y := by
    funext y
    by_cases hη_y : η y = 0
    · change (η y)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g y =
        (η y)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart y
      rw [hη_y]; ring
    · have hy_in : y ∈ tsupport η := subset_tsupport η hη_y
      rw [hF_def]
      change (η y)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g y =
        (η y)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart y
      rw [h_diffQuot_u_eq_on_tsupport y hy_in]
  have h_nb_test_eq : ∀ x,
      DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
        (d := Module.finrank ℝ E) k h η D.u_chart x =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h) F x := by
    intro x
    change DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h) (fun y => (η y)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart y) x = _
    rw [← h_F_eq_D]
  have h_LHS_eq_FK :
      ∫ x, (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            (d := Module.finrank ℝ E) k h η D.u_chart x)^2
          ∂(volume : Measure EuclN) =
      ∫ x in Ω''_fk,
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h) F x)^2
        ∂(volume : Measure EuclN) := by
    have h_eq :
        (fun x => (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              (d := Module.finrank ℝ E) k h η D.u_chart x)^2) =
        (fun x =>
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h) F x)^2) := by
      funext x; rw [h_nb_test_eq x]
    rw [h_eq, h_int_univ_F]
  have h_pointwise_G_F_sq : ∀ x : EuclN,
      (G_F x)^2 ≤
        8 * N^2 *
          (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2 +
        2 * (η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x)^2 := by
    intro x
    set T1 : ℝ := (η x)^2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (G k) x with hT1_def
    set T2 : ℝ := ((fderiv ℝ (fun z => (η z)^2) x) (EuclideanSpace.single k 1)) *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_g x with hT2_def
    have hG_F_x : G_F x = T1 + T2 := rfl
    rw [hG_F_x]
    have h_sq_sum_le : (T1 + T2)^2 ≤ 2 * T1^2 + 2 * T2^2 := by
      have h_nn_diff : 0 ≤ (T1 - T2)^2 := sq_nonneg _
      nlinarith
    refine h_sq_sum_le.trans ?_
    have h_T1_sq_bound : 2 * T1^2 ≤ 2 * (η x)^2 *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) x)^2 := by
      rw [hT1_def]
      have h_sq : ((η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x)^2 =
          (η x)^4 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x)^2 := by ring
      rw [h_sq]
      have h_eta_4_le_2 : (η x)^4 ≤ (η x)^2 := by
        have h1 : (η x)^4 = (η x)^2 * (η x)^2 := by ring
        rw [h1]
        have h_eta_sq_nn : 0 ≤ (η x)^2 := sq_nonneg _
        have h_eta_sq_le_one : (η x)^2 ≤ 1 := hη_sq_le_one x
        nlinarith
      have h_dq_sq_nn : 0 ≤ (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) x)^2 := sq_nonneg _
      nlinarith
    have h_T2_sq_bound : 2 * T2^2 ≤ 8 * N^2 *
        (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g x)^2 := by
      rw [hT2_def]
      by_cases hx_in : x ∈ tsupport η
      · rw [Set.indicator_of_mem hx_in]
        have h_bound := h_eta_sq_fderiv_bound x
        have h_sq_eq : (((fderiv ℝ (fun z => (η z)^2) x) (EuclideanSpace.single k 1)) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g x)^2 =
            ((fderiv ℝ (fun z => (η z)^2) x) (EuclideanSpace.single k 1))^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g x)^2 := by ring
        rw [h_sq_eq]
        have h_partial_sq_le_4N2 :
            ((fderiv ℝ (fun z => (η z)^2) x) (EuclideanSpace.single k 1))^2 ≤
              4 * N^2 := by
          have h_abs_le : |(fderiv ℝ (fun z => (η z)^2) x) (EuclideanSpace.single k 1)|
              ≤ 2 * N := h_bound
          have h_abs_nn : 0 ≤
              |(fderiv ℝ (fun z => (η z)^2) x) (EuclideanSpace.single k 1)| :=
            abs_nonneg _
          have h_2N_nn : 0 ≤ 2 * N := by linarith
          have h_sq_le : |(fderiv ℝ (fun z => (η z)^2) x) (EuclideanSpace.single k 1)|^2 ≤
              (2 * N)^2 := by
            exact sq_le_sq' (by linarith) h_abs_le
          have h_sq_abs : |(fderiv ℝ (fun z => (η z)^2) x)
              (EuclideanSpace.single k 1)|^2 =
              ((fderiv ℝ (fun z => (η z)^2) x) (EuclideanSpace.single k 1))^2 := by
            rw [sq_abs]
          rw [← h_sq_abs]
          have : (2 * N)^2 = 4 * N^2 := by ring
          rw [this] at h_sq_le
          exact h_sq_le
        have h_dq_sq_nn : 0 ≤ (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2 := sq_nonneg _
        nlinarith
      · rw [Set.indicator_of_notMem hx_in]
        have h_η_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx_in
        have h_tsupp_compl_open : IsOpen (tsupport η)ᶜ :=
          (isClosed_tsupport η).isOpen_compl
        have hx_in_compl : x ∈ (tsupport η)ᶜ := hx_in
        have h_eta_sq_eq_zero_nhds :
            (fun y : EuclN => (η y)^2) =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
          refine Filter.eventually_of_mem (h_tsupp_compl_open.mem_nhds hx_in_compl) ?_
          intro y hy
          have hη_y_zero : η y = 0 := image_eq_zero_of_notMem_tsupport hy
          change (η y)^2 = 0
          rw [hη_y_zero]; ring
        have h_fderiv_eq : fderiv ℝ (fun y : EuclN => (η y)^2) x =
            fderiv ℝ (fun _ : EuclN => (0 : ℝ)) x :=
          Filter.EventuallyEq.fderiv_eq h_eta_sq_eq_zero_nhds
        have h_partial_zero :
            (fderiv ℝ (fun y : EuclN => (η y)^2) x)
              (EuclideanSpace.single k 1) = 0 := by
          rw [h_fderiv_eq]; simp
        rw [h_partial_zero, zero_mul]
        have h_dq_sq_nn : 0 ≤ (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2 := sq_nonneg _
        nlinarith
    linarith
  have h_eta_sq_dq_G_sq_integrable :
      Integrable (fun x : EuclN => (η x)^2 *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) x)^2) (volume : Measure EuclN) := by
    have h_dq_G_sq_int : Integrable (fun x : EuclN =>
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) x)^2) (volume : Measure EuclN) :=
      h_diffQuot_G_l2.integrable_sq
    have h_aesm : AEStronglyMeasurable (fun x : EuclN => (η x)^2 *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) x)^2) (volume : Measure EuclN) := by
      have h1 : AEStronglyMeasurable (fun x : EuclN => (η x)^2)
          (volume : Measure EuclN) := hη_sq_cont.aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun x : EuclN =>
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x)^2) (volume : Measure EuclN) :=
        h_dq_G_sq_int.aestronglyMeasurable
      exact h1.mul h2
    have h_pt_le : ∀ᵐ x ∂(volume : Measure EuclN),
        ‖(η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x)^2‖ ≤
          ‖(DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x)^2‖ := by
      refine Filter.Eventually.of_forall ?_
      intro x
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hη_sq_nn x)]
      have h_le1 : (η x)^2 ≤ 1 := hη_sq_le_one x
      nlinarith [abs_nonneg
        ((DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) x)^2), hη_sq_nn x]
    exact h_dq_G_sq_int.mono h_aesm h_pt_le
  have h_dq_u_g_sq_int : Integrable (fun x : EuclN =>
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_g x)^2) (volume : Measure EuclN) :=
    h_diffQuot_u_g_l2.integrable_sq
  have h_indicator_dq_u_g_sq_int : Integrable (fun x : EuclN =>
      8 * N^2 *
      (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_g x)^2) (volume : Measure EuclN) := by
    have h_aesm : AEStronglyMeasurable (fun x : EuclN =>
        8 * N^2 *
        (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g x)^2) (volume : Measure EuclN) := by
      have h1 : AEStronglyMeasurable
          (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)))
          (volume : Measure EuclN) :=
        (aestronglyMeasurable_const).indicator
          (isClosed_tsupport η).measurableSet
      have h2 : AEStronglyMeasurable (fun x : EuclN =>
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2)
          (volume : Measure EuclN) := h_dq_u_g_sq_int.aestronglyMeasurable
      exact ((aestronglyMeasurable_const.mul h1).mul h2)
    have h_pt_le : ∀ᵐ x ∂(volume : Measure EuclN),
        ‖8 * N^2 *
          (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2‖ ≤
          ‖8 * N^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g x)^2‖ := by
      refine Filter.Eventually.of_forall ?_
      intro x
      have h_8N2_nn : 0 ≤ 8 * N^2 := by nlinarith
      have h_indicator_le : |Set.indicator (tsupport η)
          (fun _ : EuclN => (1 : ℝ)) x| ≤ 1 := by
        by_cases hx : x ∈ tsupport η
        · rw [Set.indicator_of_mem hx]; simp
        · rw [Set.indicator_of_notMem hx]; simp
      have h_indicator_nn : 0 ≤ Set.indicator (tsupport η)
          (fun _ : EuclN => (1 : ℝ)) x := by
        by_cases hx : x ∈ tsupport η
        · rw [Set.indicator_of_mem hx]; norm_num
        · rw [Set.indicator_of_notMem hx]
      have h_dq_sq_nn : 0 ≤ (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g x)^2 := sq_nonneg _
      have h_LHS_nn : 0 ≤ 8 * N^2 *
          (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2 := by
        have : 0 ≤ 8 * N^2 * (Set.indicator (tsupport η)
            (fun _ : EuclN => (1 : ℝ)) x) :=
          mul_nonneg h_8N2_nn h_indicator_nn
        exact mul_nonneg this h_dq_sq_nn
      have h_RHS_nn : 0 ≤ 8 * N^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2 :=
        mul_nonneg h_8N2_nn h_dq_sq_nn
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h_LHS_nn,
        abs_of_nonneg h_RHS_nn]
      have h_ind_le_1 : Set.indicator (tsupport η)
          (fun _ : EuclN => (1 : ℝ)) x ≤ 1 := by
        by_cases hx : x ∈ tsupport η
        · rw [Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx]; norm_num
      have h_step : 8 * N^2 * (Set.indicator (tsupport η)
          (fun _ : EuclN => (1 : ℝ)) x) *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2 ≤
          8 * N^2 * 1 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g x)^2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_ind_le_1 h_8N2_nn)
          h_dq_sq_nn
      linarith
    exact (h_dq_u_g_sq_int.const_mul (8 * N^2)).mono h_aesm h_pt_le
  have hG_F_sq_int : Integrable (fun x : EuclN => (G_F x)^2)
      (volume : Measure EuclN) := hG_F_l2.integrable_sq
  have h_two_eta_sq_dq_int : Integrable (fun x : EuclN =>
      2 * (η x)^2 *
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (G k) x)^2) (volume : Measure EuclN) := by
    have h_const_mul := h_eta_sq_dq_G_sq_integrable.const_mul 2
    have heq : (fun x : EuclN => 2 *
        ((η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x)^2)) =
        (fun x : EuclN => 2 * (η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x)^2) := by
      funext x; ring
    rw [heq] at h_const_mul
    exact h_const_mul
  have h_RHS_int : Integrable (fun x : EuclN =>
      8 * N^2 *
        (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g x)^2 +
      2 * (η x)^2 *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) x)^2) (volume : Measure EuclN) :=
    h_indicator_dq_u_g_sq_int.add h_two_eta_sq_dq_int
  have h_integral_G_F_le :
      ∫ x, (G_F x)^2 ∂(volume : Measure EuclN) ≤
        ∫ x, 8 * N^2 *
            (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g x)^2 +
          2 * (η x)^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (G k) x)^2
          ∂(volume : Measure EuclN) := by
    exact integral_mono hG_F_sq_int h_RHS_int h_pointwise_G_F_sq
  have h_integral_split :
      ∫ x, 8 * N^2 *
          (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2 +
        2 * (η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x)^2
        ∂(volume : Measure EuclN) =
      (∫ x, 8 * N^2 *
          (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2
        ∂(volume : Measure EuclN)) +
      (∫ x, 2 * (η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x)^2
        ∂(volume : Measure EuclN)) :=
    integral_add h_indicator_dq_u_g_sq_int h_two_eta_sq_dq_int
  have h_t1_eq : ∫ x, 8 * N^2 *
        (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g x)^2
      ∂(volume : Measure EuclN) =
      8 * N^2 *
        ∫ x in tsupport η,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2
        ∂(volume : Measure EuclN) := by
    have h_eq : (fun x : EuclN => 8 * N^2 *
        (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g x)^2) =
        (fun x : EuclN => (8 * N^2) *
          (Set.indicator (tsupport η)
            (fun y => (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g y)^2) x)) := by
      funext x
      by_cases hx : x ∈ tsupport η
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; ring
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; ring
    rw [h_eq, integral_const_mul]
    congr 1
    exact (MeasureTheory.integral_indicator (isClosed_tsupport η).measurableSet)
  have h_t2_eq : ∫ x, 2 * (η x)^2 *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) x)^2
      ∂(volume : Measure EuclN) =
      2 * ∫ x, (η x)^2 *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) x)^2
      ∂(volume : Measure EuclN) := by
    have heq : (fun x : EuclN => 2 * (η x)^2 *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) x)^2) =
        (fun x : EuclN => 2 * ((η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x)^2)) := by
      funext x; ring
    rw [heq, integral_const_mul]
  have h_FK_combined :
      ∫ x in Ω''_fk,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h) F x)^2
        ∂(volume : Measure EuclN) ≤
        ∫ x in (Set.univ : Set EuclN), (G_F x)^2 ∂(volume : Measure EuclN) :=
    h_FK_F
  have h_int_univ_G_F :
      ∫ x in (Set.univ : Set EuclN), (G_F x)^2 ∂(volume : Measure EuclN) =
      ∫ x, (G_F x)^2 ∂(volume : Measure EuclN) :=
    MeasureTheory.setIntegral_univ
  have h_int_dq_u_g_eq : ∫ x in tsupport η,
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g x)^2
      ∂(volume : Measure EuclN) =
      ∫ x in tsupport η,
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h D.u_chart x)^2
      ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun (isClosed_tsupport η).measurableSet ?_
    intro x hx
    have h_eq := h_diffQuot_u_eq_on_tsupport x hx
    change (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_g x)^2 =
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart x)^2
    rw [h_eq]
  have h_int_eta_sq_dq_G_eq :
      ∫ x, (η x)^2 *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) x)^2
      ∂(volume : Measure EuclN) =
      ∫ x, (η x)^2 *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weak_partial k) x)^2
      ∂(volume : Measure EuclN) := by
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    change (η x)^2 * (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (G k) x)^2 =
      (η x)^2 * (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial k) x)^2
    by_cases hx : x ∈ tsupport η
    · have h_eq := h_diffQuot_G_eq_on_tsupport x hx
      rw [h_eq]
    · have hη_x_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hη_x_zero]; ring
  calc ∫ x,
          (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            (d := Module.finrank ℝ E) k h η D.u_chart x)^2
        ∂(volume : Measure EuclN)
      = ∫ x in Ω''_fk,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h) F x)^2
        ∂(volume : Measure EuclN) := h_LHS_eq_FK
    _ ≤ ∫ x in (Set.univ : Set EuclN), (G_F x)^2 ∂(volume : Measure EuclN) :=
        h_FK_combined
    _ = ∫ x, (G_F x)^2 ∂(volume : Measure EuclN) := h_int_univ_G_F
    _ ≤ ∫ x, 8 * N^2 *
            (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g x)^2 +
          2 * (η x)^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (G k) x)^2
          ∂(volume : Measure EuclN) := h_integral_G_F_le
    _ = (∫ x, 8 * N^2 *
            (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g x)^2
          ∂(volume : Measure EuclN)) +
        (∫ x, 2 * (η x)^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (G k) x)^2
          ∂(volume : Measure EuclN)) := h_integral_split
    _ = 8 * N^2 *
          (∫ x in tsupport η,
              (DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h u_g x)^2
            ∂(volume : Measure EuclN)) +
        2 * (∫ x, (η x)^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (G k) x)^2
          ∂(volume : Measure EuclN)) := by rw [h_t1_eq, h_t2_eq]
    _ = 8 * N^2 *
          (∫ x in tsupport η,
              (DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart x)^2
            ∂(volume : Measure EuclN)) +
        2 * (∫ x, (η x)^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial k) x)^2
          ∂(volume : Measure EuclN)) := by
          rw [h_int_dq_u_g_eq, h_int_eta_sq_dq_G_eq]

set_option maxHeartbeats 4000000 in
set_option linter.unusedVariables false in
/-- Discharge of `h_master_nonsmooth` from the chart-bilinear data `D` with an
externally supplied elliptic bilinear form `B`. The hypotheses
`h_B_a_match` and `h_B_c_match` connect `B` to the chart data on
`cthickening R₀ (tsupport η)`. The output instantiates the conditional
wrapper's `h_master_nonsmooth` shape with `u_g := D.u_chart`,
`f_g := densityOnEuclid g α · D.f_chart`, and `g_g i := D.weak_partial i`.
The radius `R₀ > 0` is the diff-quotient bound; the proof works uniformly
in `R₀`. -/
theorem chartBilinear_master_nonsmooth_discharge
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (B : SmoothEllipticBilinearForm
      (Module.finrank ℝ E) (Set.univ : Set EuclN))
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {Ω' : Set EuclN} (hΩ'_open : IsOpen Ω')
    (hΩ'_chart : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hΩ'_compact_closure : IsCompact (closure Ω'))
    (hη_in_Ω' : tsupport η ⊆ Ω')
    {R₀ : ℝ} (hR₀_pos : 0 < R₀)
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (h_B_a_match : ∀ y ∈ Metric.cthickening R₀ (tsupport η),
      ∀ i j : Fin (Module.finrank ℝ E),
        B.a y i j = weightedInvGramOnEuclid (I := I) g α i j y)
    (h_B_c_match : ∀ y ∈ Metric.cthickening R₀ (tsupport η),
      B.c y = densityOnEuclid (I := I) g α y) :
    ∀ (k : Fin (Module.finrank ℝ E)),
    ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      B.lam * ∫ x, (η x)^2 *
          ∑ l : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial l) x ^ 2
        ∂(volume : Measure EuclN) ≤
        |∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              2 * DifferentialGeometry.Analysis.Sobolev.translate
                (d := Module.finrank ℝ E) k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weak_partial i) x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart x
            ∂(volume : Measure EuclN)| +
        |∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun y : EuclN => B.a y i j) x * (η x)^2 *
              ((D.weak_partial i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weak_partial j) x
            ∂(volume : Measure EuclN)| +
        |∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              2 * DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((D.weak_partial i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart x
            ∂(volume : Measure EuclN)| +
        |∫ x in (Set.univ : Set EuclN),
            (densityOnEuclid (I := I) g α x * D.f_chart x) *
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              (d := Module.finrank ℝ E) k h η D.u_chart x| +
        |∫ x in (Set.univ : Set EuclN), B.c x * D.u_chart x *
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              (d := Module.finrank ℝ E) k h η D.u_chart x
              ∂(volume : Measure EuclN)| := by
  classical
  intro k h hh hh_le
  have hh_abs_pos : 0 < |h| := abs_pos.mpr hh
  have hη_tsupp_compact : IsCompact (tsupport η) := hη_supp
  have h_cthickR0_compact : IsCompact (Metric.cthickening R₀ (tsupport η)) :=
    hη_tsupp_compact.cthickening
  have h_cthickR0_in_Ω' : Metric.cthickening R₀ (tsupport η) ⊆ Ω' := by
    have h := hh_supp_in_Ω' (h := R₀) (by rw [abs_of_pos hR₀_pos])
    rw [abs_of_pos hR₀_pos] at h
    exact h
  have h_cthickR0_in_chart :
      Metric.cthickening R₀ (tsupport η) ⊆
        chartTargetEuclid (I := I) (M := M) α :=
    h_cthickR0_in_Ω'.trans (subset_closure.trans hΩ'_chart)
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨δ, hδ_pos, hδ_in_chart⟩ :=
    h_cthickR0_compact.exists_cthickening_subset_open h_chart_open
      h_cthickR0_in_chart
  set r : ℝ := R₀ + δ / 2 with hr_def
  have hr_pos : 0 < r := by rw [hr_def]; linarith
  have hr_gt_R0 : R₀ < r := by rw [hr_def]; linarith
  have hr_ge_R0 : R₀ ≤ r := hr_gt_R0.le
  have hr_le : r ≤ R₀ + δ := by rw [hr_def]; linarith
  have h_cthick_r_compact : IsCompact (Metric.cthickening r (tsupport η)) :=
    hη_tsupp_compact.cthickening
  have h_cthick_r_in_chart :
      Metric.cthickening r (tsupport η) ⊆
        chartTargetEuclid (I := I) (M := M) α := by
    intro x hx
    have hx' : x ∈ Metric.cthickening (R₀ + δ) (tsupport η) :=
      Metric.cthickening_mono hr_le _ hx
    have h_eq : Metric.cthickening (R₀ + δ) (tsupport η) =
        Metric.cthickening δ (Metric.cthickening R₀ (tsupport η)) := by
      have hδ_le : (0 : ℝ) ≤ δ := hδ_pos.le
      have hR0_le : (0 : ℝ) ≤ R₀ := hR₀_pos.le
      rw [show (R₀ + δ) = (δ + R₀) from by ring,
        ← cthickening_cthickening hδ_le hR0_le]
    rw [h_eq] at hx'
    exact hδ_in_chart hx'
  obtain ⟨χ, hχ_smooth, hχ_cs, hχ_range, hχ_one, hχ_tsupp⟩ :=
    DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff
      (d := Module.finrank ℝ E)
      (K := Metric.cthickening r (tsupport η))
      (Ω' := chartTargetEuclid (I := I) (M := M) α)
      h_cthick_r_compact h_chart_open h_cthick_r_in_chart
  have hχ_nn : ∀ x : EuclN, 0 ≤ χ x ∧ χ x ≤ 1 := by
    intro x
    have hx_range : χ x ∈ Set.range χ := Set.mem_range_self x
    exact ⟨(hχ_range hx_range).1, (hχ_range hx_range).2⟩
  set u_g : EuclN → ℝ := fun x => χ x * D.u_chart x with hu_g_def
  set G : Fin (Module.finrank ℝ E) → EuclN → ℝ := fun i x =>
    (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.u_chart x +
    χ x * D.weak_partial i x with hG_def
  have hu_g_l2 : MemLp u_g 2 (volume : Measure EuclN) :=
    cutoff_uChart_memLp_two_univ (I := I) (M := M) D hχ_smooth hχ_cs hχ_tsupp
  have hG_l2 : ∀ i, MemLp (G i) 2 (volume : Measure EuclN) := fun i =>
    cutoff_uChart_partial_memLp_two_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_tsupp i
  have hG_isWP : ∀ i, DeGiorgi.HasWeakPartialDeriv
      (d := Module.finrank ℝ E) i (G i) u_g Set.univ := fun i =>
    cutoff_uChart_hasWeakPartialDeriv_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_tsupp i
  set Ω_principal : Set EuclN := Metric.thickening δ
    (Metric.cthickening R₀ (tsupport η)) with hΩ_principal_def
  have hΩ_principal_open : IsOpen Ω_principal := Metric.isOpen_thickening
  have hΩ_principal_compact_closure :
      IsCompact (closure Ω_principal) := by
    have h_subset : closure Ω_principal ⊆
        Metric.cthickening δ (Metric.cthickening R₀ (tsupport η)) :=
      Metric.closure_thickening_subset_cthickening _ _
    refine (h_cthickR0_compact.cthickening (r := δ)).of_isClosed_subset
      isClosed_closure h_subset
  have hΩ_principal_in_univ : closure Ω_principal ⊆ (Set.univ : Set EuclN) := by
    intro x _; exact Set.mem_univ _
  have hh_supp_in_Ω_principal :
      ∀ {h' : ℝ}, |h'| ≤ R₀ →
        Metric.cthickening |h'| (tsupport η) ⊆ Ω_principal := by
    intro h' hh'_le x hx
    have h_subset_cthickR0 :
        Metric.cthickening |h'| (tsupport η) ⊆
          Metric.cthickening R₀ (tsupport η) :=
      Metric.cthickening_mono hh'_le _
    have hx_in_cthickR0 :
        x ∈ Metric.cthickening R₀ (tsupport η) := h_subset_cthickR0 hx
    have h_self : Metric.cthickening R₀ (tsupport η) ⊆ Ω_principal := by
      rw [hΩ_principal_def]
      exact Metric.self_subset_thickening hδ_pos _
    exact h_self hx_in_cthickR0
  have h_principal_le :
      B.lam *
        ∫ x, (η x)^2 *
          ∑ l : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (G l) x)^2
          ∂(volume : Measure EuclN) ≤
      ∫ x, ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Analysis.Sobolev.translate
          (d := Module.finrank ℝ E) k h
          (fun y : EuclN => B.a y i j)) x *
        (η x)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G i) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G j) x
        ∂(volume : Measure EuclN) := by
    exact principal_term_ge_lambda_norm_sq_nonsmooth
      (d := Module.finrank ℝ E) B hu_g_l2 hG_l2 hG_isWP
      hη hη_supp hη_range hΩ_principal_open
      hΩ_principal_compact_closure hΩ_principal_in_univ
      hh_supp_in_Ω_principal k hh hh_le
  have h_cthick_h_subset_r :
      Metric.cthickening |h| (tsupport η) ⊆ Metric.cthickening r (tsupport η) :=
    Metric.cthickening_mono (hh_le.trans hr_ge_R0) _
  have h_cthick_h_subset_cthickR0 :
      Metric.cthickening |h| (tsupport η) ⊆
        Metric.cthickening R₀ (tsupport η) :=
    Metric.cthickening_mono hh_le _
  have h_cthickR0_subset_r :
      Metric.cthickening R₀ (tsupport η) ⊆ Metric.cthickening r (tsupport η) :=
    Metric.cthickening_mono hr_ge_R0 _
  have h_self_subset_cthick_h :
      tsupport η ⊆ Metric.cthickening |h| (tsupport η) :=
    Metric.self_subset_cthickening _
  have hh_abs_lt_r : |h| < r := by rw [hr_def]; linarith
  have h_cthick_h_subset_thick_r :
      Metric.cthickening |h| (tsupport η) ⊆ Metric.thickening r (tsupport η) := by
    intro x hx
    have h_inf : Metric.infEDist x (tsupport η) ≤ ENNReal.ofReal |h| :=
      (Metric.mem_cthickening_iff).mp hx
    have h_ofReal_lt : ENNReal.ofReal |h| < ENNReal.ofReal r :=
      ENNReal.ofReal_lt_ofReal_iff hr_pos |>.mpr hh_abs_lt_r
    have h_inf_lt : Metric.infEDist x (tsupport η) < ENNReal.ofReal r :=
      lt_of_le_of_lt h_inf h_ofReal_lt
    exact (Metric.mem_thickening_iff_infEDist_lt).mpr h_inf_lt
  have h_thick_r_open : IsOpen (Metric.thickening r (tsupport η)) :=
    Metric.isOpen_thickening
  have h_thick_r_subset_cthick_r :
      Metric.thickening r (tsupport η) ⊆ Metric.cthickening r (tsupport η) :=
    Metric.thickening_subset_cthickening _ _
  have h_fderiv_zero_on_thick_r : ∀ x ∈ Metric.thickening r (tsupport η),
      ∀ l : Fin (Module.finrank ℝ E),
      (fderiv ℝ χ x) (EuclideanSpace.single l 1) = 0 := by
    intro x hx l
    have hχ_eq_one_nhds : (fun y => χ y) =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
      refine Filter.eventually_of_mem (h_thick_r_open.mem_nhds hx) ?_
      intro y hy
      exact hχ_one y (h_thick_r_subset_cthick_r hy)
    have h_fderiv_eq : fderiv ℝ χ x = fderiv ℝ (fun _ : EuclN => (1 : ℝ)) x :=
      Filter.EventuallyEq.fderiv_eq hχ_eq_one_nhds
    rw [h_fderiv_eq]
    simp
  have hG_eq_on_cthick_h : ∀ l : Fin (Module.finrank ℝ E),
      ∀ x ∈ Metric.cthickening |h| (tsupport η),
        G l x = D.weak_partial l x := by
    intro l x hx
    have hx_in_r : x ∈ Metric.cthickening r (tsupport η) :=
      h_cthick_h_subset_r hx
    have hx_in_thick_r : x ∈ Metric.thickening r (tsupport η) :=
      h_cthick_h_subset_thick_r hx
    have hχx : χ x = 1 := hχ_one x hx_in_r
    have hdχx : (fderiv ℝ χ x) (EuclideanSpace.single l 1) = 0 :=
      h_fderiv_zero_on_thick_r x hx_in_thick_r l
    change (fderiv ℝ χ x) (EuclideanSpace.single l 1) * D.u_chart x +
      χ x * D.weak_partial l x = D.weak_partial l x
    rw [hdχx, hχx, zero_mul, one_mul, zero_add]
  have hu_g_eq_on_cthick_h : ∀ x ∈ Metric.cthickening |h| (tsupport η),
      u_g x = D.u_chart x := by
    intro x hx
    have hx_in_r : x ∈ Metric.cthickening r (tsupport η) :=
      h_cthick_h_subset_r hx
    have hχx : χ x = 1 := hχ_one x hx_in_r
    change χ x * D.u_chart x = D.u_chart x
    rw [hχx, one_mul]
  have h_diffQuot_G_eq_on_tsupport : ∀ l : Fin (Module.finrank ℝ E),
      ∀ x ∈ tsupport η,
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G l) x =
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weak_partial l) x := by
    intro l x hx
    have hx_in_cthick_h : x ∈ Metric.cthickening |h| (tsupport η) :=
      h_self_subset_cthick_h hx
    have h_shift_in_cthick_h :
        x + h • EuclideanSpace.single k 1 ∈
          Metric.cthickening |h| (tsupport η) := by
      refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η) hx ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
      rw [hsing, mul_one, Real.norm_eq_abs]
    have hG_at : G l x = D.weak_partial l x :=
      hG_eq_on_cthick_h l x hx_in_cthick_h
    have hG_shift : G l (x + h • EuclideanSpace.single k 1) =
        D.weak_partial l (x + h • EuclideanSpace.single k 1) :=
      hG_eq_on_cthick_h l _ h_shift_in_cthick_h
    change
      (if h = 0 then 0 else
        (G l (x + h • EuclideanSpace.single k 1) - G l x) / h) =
      (if h = 0 then 0 else
        (D.weak_partial l (x + h • EuclideanSpace.single k 1) -
          D.weak_partial l x) / h)
    rw [if_neg hh, if_neg hh, hG_at, hG_shift]
  have h_diffQuot_u_g_eq_on_tsupport : ∀ x ∈ tsupport η,
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_g x =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart x := by
    intro x hx
    have hx_in_cthick_h : x ∈ Metric.cthickening |h| (tsupport η) :=
      h_self_subset_cthick_h hx
    have h_shift_in_cthick_h :
        x + h • EuclideanSpace.single k 1 ∈
          Metric.cthickening |h| (tsupport η) := by
      refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η) hx ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
      rw [hsing, mul_one, Real.norm_eq_abs]
    have hu_at : u_g x = D.u_chart x :=
      hu_g_eq_on_cthick_h x hx_in_cthick_h
    have hu_shift : u_g (x + h • EuclideanSpace.single k 1) =
        D.u_chart (x + h • EuclideanSpace.single k 1) :=
      hu_g_eq_on_cthick_h _ h_shift_in_cthick_h
    change
      (if h = 0 then 0 else
        (u_g (x + h • EuclideanSpace.single k 1) - u_g x) / h) =
      (if h = 0 then 0 else
        (D.u_chart (x + h • EuclideanSpace.single k 1) - D.u_chart x) / h)
    rw [if_neg hh, if_neg hh, hu_at, hu_shift]
  have h_LHS_pointwise :
      (fun x => (η x)^2 *
        ∑ l : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G l) x)^2) =
      (fun x => (η x)^2 *
        ∑ l : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weak_partial l) x)^2) := by
    funext x
    by_cases hx : x ∈ tsupport η
    · refine congrArg _ ?_
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [h_diffQuot_G_eq_on_tsupport l x hx]
    · have hη_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hη_zero]; ring
  set K_0 : Set EuclN := tsupport η with hK_0_def
  have hK_0_compact : IsCompact K_0 := hη_tsupp_compact
  have hK_0_in_chart : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α := by
    rw [hK_0_def]
    exact hη_in_Ω'.trans (subset_closure.trans hΩ'_chart)
  have h_thick_K_0_in_chart :
      Metric.cthickening |h| K_0 ⊆
        chartTargetEuclid (I := I) (M := M) α := by
    rw [hK_0_def]
    exact h_cthick_h_subset_cthickR0.trans h_cthickR0_in_chart
  have h_translate_Ba_eq_on_tsupport : ∀ i j : Fin (Module.finrank ℝ E),
      ∀ x ∈ tsupport η,
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun y : EuclN => B.a y i j) x =
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun y : EuclN => weightedInvGramOnEuclid (I := I) g α i j y) x := by
    intro i j x hx
    have h_shift_in_cthick_h :
        x + h • EuclideanSpace.single k 1 ∈
          Metric.cthickening |h| (tsupport η) := by
      refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η) hx ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
      rw [hsing, mul_one, Real.norm_eq_abs]
    have h_shift_in_cthickR0 :
        x + h • EuclideanSpace.single k 1 ∈
          Metric.cthickening R₀ (tsupport η) :=
      h_cthick_h_subset_cthickR0 h_shift_in_cthick_h
    change B.a (x + h • EuclideanSpace.single k 1) i j =
      weightedInvGramOnEuclid (I := I) g α i j
        (x + h • EuclideanSpace.single k 1)
    exact h_B_a_match _ h_shift_in_cthickR0 i j
  have h_diffQuot_Ba_eq_on_tsupport : ∀ i j : Fin (Module.finrank ℝ E),
      ∀ x ∈ tsupport η,
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun y : EuclN => B.a y i j) x =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun y : EuclN => weightedInvGramOnEuclid (I := I) g α i j y) x := by
    intro i j x hx
    have h_shift_in_cthick_h :
        x + h • EuclideanSpace.single k 1 ∈
          Metric.cthickening |h| (tsupport η) := by
      refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η) hx ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
      rw [hsing, mul_one, Real.norm_eq_abs]
    have h_shift_in_cthickR0 :
        x + h • EuclideanSpace.single k 1 ∈
          Metric.cthickening R₀ (tsupport η) :=
      h_cthick_h_subset_cthickR0 h_shift_in_cthick_h
    have hx_in_cthickR0 : x ∈ Metric.cthickening R₀ (tsupport η) :=
      h_cthick_h_subset_cthickR0 (h_self_subset_cthick_h hx)
    have hBa_x : B.a x i j = weightedInvGramOnEuclid (I := I) g α i j x :=
      h_B_a_match x hx_in_cthickR0 i j
    have hBa_shift :
        B.a (x + h • EuclideanSpace.single k 1) i j =
          weightedInvGramOnEuclid (I := I) g α i j
            (x + h • EuclideanSpace.single k 1) :=
      h_B_a_match _ h_shift_in_cthickR0 i j
    change
      (if h = 0 then 0 else
        (B.a (x + h • EuclideanSpace.single k 1) i j - B.a x i j) / h) =
      (if h = 0 then 0 else
        (weightedInvGramOnEuclid (I := I) g α i j
            (x + h • EuclideanSpace.single k 1) -
          weightedInvGramOnEuclid (I := I) g α i j x) / h)
    rw [if_neg hh, if_neg hh, hBa_x, hBa_shift]
  have h_RHS_principal_eq :
      ∫ x, ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h
            (fun y : EuclN => B.a y i j)) x *
          (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G i) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G j) x
          ∂(volume : Measure EuclN) =
      principalTerm_chartBilinear (I := I) (M := M) D K_0 η k h := by
    unfold principalTerm_chartBilinear
    have h_eq_on_tsupport : ∀ x ∈ tsupport η,
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h
            (fun y : EuclN => B.a y i j)) x *
          (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G i) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G j) x) =
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h
            (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
          (η x) ^ 2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weak_partial i) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weak_partial j) x) := by
      intro x hx
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [h_translate_Ba_eq_on_tsupport i j x hx,
          h_diffQuot_G_eq_on_tsupport i x hx,
          h_diffQuot_G_eq_on_tsupport j x hx]
    have h_eq_zero_off : ∀ x ∉ tsupport η,
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h
            (fun y : EuclN => B.a y i j)) x *
          (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G i) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G j) x) = 0 := by
      intro x hx
      have hη_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      refine Finset.sum_eq_zero ?_
      intro i _
      refine Finset.sum_eq_zero ?_
      intro j _
      rw [hη_zero]; ring
    have h_eq_zero_off_chartBilinear : ∀ x ∉ tsupport η,
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h
            (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
          (η x) ^ 2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weak_partial i) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weak_partial j) x) = 0 := by
      intro x hx
      have hη_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      refine Finset.sum_eq_zero ?_
      intro i _
      refine Finset.sum_eq_zero ?_
      intro j _
      rw [hη_zero]; ring
    have h_compl_zero_LHS : ∀ x ∉ K_0,
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h
            (fun y : EuclN => B.a y i j)) x *
          (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G i) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G j) x) = 0 := by
      intro x hx
      rw [hK_0_def] at hx
      exact h_eq_zero_off x hx
    have hK_0_meas : MeasurableSet K_0 := by
      rw [hK_0_def]
      exact (isClosed_tsupport η).measurableSet
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h_compl_zero_LHS]
    refine setIntegral_congr_fun hK_0_meas ?_
    intro x hx
    rw [hK_0_def] at hx
    exact h_eq_on_tsupport x hx
  have h_LHS_principal_eq :
      B.lam *
        ∫ x, (η x)^2 *
          ∑ l : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (G l) x)^2
          ∂(volume : Measure EuclN) =
      B.lam *
        ∫ x, (η x)^2 *
          ∑ l : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial l) x ^ 2
          ∂(volume : Measure EuclN) := by
    have h_inner_eq :
        (fun x => (η x)^2 *
          ∑ l : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (G l) x)^2) =
        (fun x => (η x)^2 *
          ∑ l : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial l) x ^ 2) :=
      h_LHS_pointwise
    rw [h_inner_eq]
  have h_subst : chartBilinear_LHS (I := I) (M := M) D K_0 η k h =
      chartBilinear_RHS (I := I) (M := M) D K_0 η k h :=
    chartBilinear_substitution_identity_holds (I := I) (M := M) D
      hK_0_compact hK_0_in_chart hη hη_supp (le_refl _) k hh hh_le
      h_thick_K_0_in_chart
  unfold chartBilinear_LHS chartBilinear_RHS at h_subst
  have h_principal_eq :
      principalTerm_chartBilinear (I := I) (M := M) D K_0 η k h =
        c_term_chartBilinear (I := I) (M := M) D K_0 η k h
          - cross_1_term_chartBilinear (I := I) (M := M) D K_0 η k h
          - cross_2_term_chartBilinear (I := I) (M := M) D K_0 η k h
          - cross_3_term_chartBilinear (I := I) (M := M) D K_0 η k h
          - f_term_chartBilinear (I := I) (M := M) D K_0 η k h := by
    linarith

  have h_test_supp_in_cthick_h :
      Function.support
        (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
          (d := Module.finrank ℝ E) k h η D.u_chart) ⊆
      Metric.cthickening |h| (tsupport η) := by
    intro x hx
    rw [Function.mem_support] at hx
    have h_unfold :
        DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
          (d := Module.finrank ℝ E) k h η D.u_chart x =
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h)
          (fun y : EuclN => η y ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.u_chart y) x := rfl
    rw [h_unfold] at hx
    have hh_neg : (-h) ≠ 0 := neg_ne_zero.mpr hh
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh_neg
        (fun y : EuclN => η y ^ 2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart y) x] at hx
    have h_num_ne : (η (x + (-h) • EuclideanSpace.single k 1))^2 *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h D.u_chart
            (x + (-h) • EuclideanSpace.single k 1)) -
        (η x)^2 * (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h D.u_chart x) ≠ 0 := by
      intro h_zero
      apply hx
      rw [h_zero, zero_div]
    by_cases hηx : η x = 0
    · have hFx_zero : (η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart x) = 0 := by
        rw [show (η x)^2 = 0 from by rw [hηx]; ring, zero_mul]
      rw [hFx_zero, sub_zero] at h_num_ne
      have hηy_ne : η (x + (-h) • EuclideanSpace.single k 1) ≠ 0 := by
        intro h_zero
        apply h_num_ne
        rw [show (η (x + (-h) • EuclideanSpace.single k 1))^2 = 0 from by
          rw [h_zero]; ring, zero_mul]
      have hy_in_supp :
          x + (-h) • EuclideanSpace.single k 1 ∈ tsupport η :=
        subset_tsupport η (Function.mem_support.mpr hηy_ne)
      refine Metric.mem_cthickening_of_dist_le _
        (x + (-h) • EuclideanSpace.single k 1) |h| (tsupport η) hy_in_supp ?_
      rw [dist_eq_norm]
      have h_diff_eq : x - (x + (-h) • EuclideanSpace.single k 1) =
          h • EuclideanSpace.single k 1 := by
        rw [sub_add_eq_sub_sub]
        rw [sub_self, zero_sub, neg_smul, neg_neg]
      rw [h_diff_eq]
      rw [norm_smul]
      have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
      rw [hsing, mul_one, Real.norm_eq_abs]
    · have hx_in_supp : x ∈ tsupport η :=
        subset_tsupport η (Function.mem_support.mpr hηx)
      exact h_self_subset_cthick_h hx_in_supp
  have h_c_term_eq :
      c_term_chartBilinear (I := I) (M := M) D K_0 η k h =
      ∫ x in (Set.univ : Set EuclN), B.c x * D.u_chart x *
        DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
          (d := Module.finrank ℝ E) k h η D.u_chart x
        ∂(volume : Measure EuclN) := by
    unfold c_term_chartBilinear
    have h_supp_in_cthick_h_K_0 :
        Function.support
          (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            (d := Module.finrank ℝ E) k h η D.u_chart) ⊆
        Metric.cthickening |h| K_0 := by
      rw [hK_0_def]; exact h_test_supp_in_cthick_h
    have h_test_eq :
        (DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
          (d := Module.finrank ℝ E) k h η D.u_chart) =
        (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
          (d := Module.finrank ℝ E) k h η D.u_chart) := rfl
    have h_cthick_h_K_0_subset_cthick1 :
        Metric.cthickening |h| K_0 ⊆ Metric.cthickening R₀ (tsupport η) := by
      rw [hK_0_def]; exact h_cthick_h_subset_cthickR0
    have h_Bc_match_on_supp : ∀ x ∈ Metric.cthickening |h| K_0,
        B.c x = densityOnEuclid (I := I) g α x := fun x hx =>
      h_B_c_match x (h_cthick_h_K_0_subset_cthick1 hx)
    have h_cthick_h_K_0_meas : MeasurableSet (Metric.cthickening |h| K_0) :=
      Metric.isClosed_cthickening.measurableSet
    have h_F_zero_off : ∀ x ∉ Metric.cthickening |h| K_0,
        B.c x * D.u_chart x *
          (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            (d := Module.finrank ℝ E) k h η D.u_chart x) = 0 := by
      intro x hx
      have h_test_zero :
          DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            (d := Module.finrank ℝ E) k h η D.u_chart x = 0 := by
        by_contra h_ne
        exact hx (h_supp_in_cthick_h_K_0 h_ne)
      rw [h_test_zero, mul_zero]
    have h_step_a :
        (∫ x in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α x * D.u_chart x *
            DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
              (d := Module.finrank ℝ E) k h η D.u_chart x
            ∂(volume : Measure EuclN)) =
        (∫ x in Metric.cthickening |h| K_0,
          B.c x * D.u_chart x *
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              (d := Module.finrank ℝ E) k h η D.u_chart x
          ∂(volume : Measure EuclN)) := by
      refine setIntegral_congr_fun h_cthick_h_K_0_meas ?_
      intro x hx
      simp only
      rw [← h_Bc_match_on_supp x hx, h_test_eq]
    rw [h_step_a]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero h_F_zero_off,
        ← MeasureTheory.setIntegral_univ]
  have h_f_term_eq :
      f_term_chartBilinear (I := I) (M := M) D K_0 η k h =
      ∫ x in (Set.univ : Set EuclN),
        (densityOnEuclid (I := I) g α x * D.f_chart x) *
        DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
          (d := Module.finrank ℝ E) k h η D.u_chart x
        ∂(volume : Measure EuclN) := by
    unfold f_term_chartBilinear
    have h_supp_in_cthick_h_K_0 :
        Function.support
          (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            (d := Module.finrank ℝ E) k h η D.u_chart) ⊆
        Metric.cthickening |h| K_0 := by
      rw [hK_0_def]; exact h_test_supp_in_cthick_h
    have h_test_eq :
        (DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
          (d := Module.finrank ℝ E) k h η D.u_chart) =
        (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
          (d := Module.finrank ℝ E) k h η D.u_chart) := rfl
    have h_cthick_h_K_0_meas : MeasurableSet (Metric.cthickening |h| K_0) :=
      Metric.isClosed_cthickening.measurableSet
    have h_F_zero_off : ∀ x ∉ Metric.cthickening |h| K_0,
        (densityOnEuclid (I := I) g α x * D.f_chart x) *
          (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            (d := Module.finrank ℝ E) k h η D.u_chart x) = 0 := by
      intro x hx
      have h_test_zero :
          DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            (d := Module.finrank ℝ E) k h η D.u_chart x = 0 := by
        by_contra h_ne
        exact hx (h_supp_in_cthick_h_K_0 h_ne)
      rw [h_test_zero, mul_zero]
    have h_step_a :
        (∫ x in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α x * D.f_chart x *
            DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
              (d := Module.finrank ℝ E) k h η D.u_chart x
          ∂(volume : Measure EuclN)) =
        (∫ x in Metric.cthickening |h| K_0,
          (densityOnEuclid (I := I) g α x * D.f_chart x) *
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              (d := Module.finrank ℝ E) k h η D.u_chart x
          ∂(volume : Measure EuclN)) := by
      refine setIntegral_congr_fun h_cthick_h_K_0_meas ?_
      intro x _hx
      simp only
      rw [h_test_eq]
    rw [h_step_a]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero h_F_zero_off,
        ← MeasureTheory.setIntegral_univ]
  have h_cross_1_eq :
      cross_1_term_chartBilinear (I := I) (M := M) D K_0 η k h =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), ∫ x,
            2 * DifferentialGeometry.Analysis.Sobolev.translate
              (d := Module.finrank ℝ E) k h
              (fun y : EuclN => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial i) x *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.u_chart x
          ∂(volume : Measure EuclN) := by
    unfold cross_1_term_chartBilinear
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    have h_compl_zero : ∀ x ∉ K_0,
        2 * DifferentialGeometry.Analysis.Sobolev.translate
          (d := Module.finrank ℝ E) k h
          (fun y : EuclN => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weak_partial i) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h D.u_chart x = 0 := by
      intro x hx
      rw [hK_0_def] at hx
      have hη_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hη_zero]; ring
    have hK_0_meas : MeasurableSet K_0 := by
      rw [hK_0_def]; exact (isClosed_tsupport η).measurableSet
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h_compl_zero]
    refine setIntegral_congr_fun hK_0_meas ?_
    intro x hx
    rw [hK_0_def] at hx
    simp only
    rw [h_translate_Ba_eq_on_tsupport i j x hx]
  have h_cross_2_eq :
      cross_2_term_chartBilinear (I := I) (M := M) D K_0 η k h =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), ∫ x,
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (fun y : EuclN => B.a y i j) x * (η x)^2 *
            ((D.weak_partial i) x) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial j) x
          ∂(volume : Measure EuclN) := by
    unfold cross_2_term_chartBilinear
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    have h_compl_zero : ∀ x ∉ K_0,
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun y : EuclN => B.a y i j) x * (η x)^2 *
        (D.weak_partial i x) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weak_partial j) x = 0 := by
      intro x hx
      rw [hK_0_def] at hx
      have hη_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hη_zero]; ring
    have hK_0_meas : MeasurableSet K_0 := by
      rw [hK_0_def]; exact (isClosed_tsupport η).measurableSet
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h_compl_zero]
    refine setIntegral_congr_fun hK_0_meas ?_
    intro x hx
    rw [hK_0_def] at hx
    simp only
    rw [h_diffQuot_Ba_eq_on_tsupport i j x hx]
  have h_cross_3_eq :
      cross_3_term_chartBilinear (I := I) (M := M) D K_0 η k h =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), ∫ x,
            2 * DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (fun y : EuclN => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            ((D.weak_partial i) x) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.u_chart x
          ∂(volume : Measure EuclN) := by
    unfold cross_3_term_chartBilinear
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    have h_compl_zero : ∀ x ∉ K_0,
        2 * DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun y : EuclN => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        (D.weak_partial i x) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h D.u_chart x = 0 := by
      intro x hx
      rw [hK_0_def] at hx
      have hη_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hη_zero]; ring
    have hK_0_meas : MeasurableSet K_0 := by
      rw [hK_0_def]; exact (isClosed_tsupport η).measurableSet
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h_compl_zero]
    refine setIntegral_congr_fun hK_0_meas ?_
    intro x hx
    rw [hK_0_def] at hx
    simp only
    rw [h_diffQuot_Ba_eq_on_tsupport i j x hx]
  set A_1 : ℝ :=
    ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E), ∫ x,
          2 * DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h
            (fun y : EuclN => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weak_partial i) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart x
        ∂(volume : Measure EuclN) with hA_1_def
  set A_2 : ℝ :=
    ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E), ∫ x,
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h
            (fun y : EuclN => B.a y i j) x * (η x)^2 *
          ((D.weak_partial i) x) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weak_partial j) x
        ∂(volume : Measure EuclN) with hA_2_def
  set A_3 : ℝ :=
    ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E), ∫ x,
          2 * DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h
            (fun y : EuclN => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          ((D.weak_partial i) x) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart x
        ∂(volume : Measure EuclN) with hA_3_def
  set A_f : ℝ :=
    ∫ x in (Set.univ : Set EuclN),
      (densityOnEuclid (I := I) g α x * D.f_chart x) *
      DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
        (d := Module.finrank ℝ E) k h η D.u_chart x
      ∂(volume : Measure EuclN) with hA_f_def
  set A_c : ℝ :=
    ∫ x in (Set.univ : Set EuclN), B.c x * D.u_chart x *
      DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
        (d := Module.finrank ℝ E) k h η D.u_chart x
      ∂(volume : Measure EuclN) with hA_c_def
  have h_principal_in_A :
      principalTerm_chartBilinear (I := I) (M := M) D K_0 η k h =
        A_c - A_1 - A_2 - A_3 - A_f := by
    rw [h_principal_eq, h_c_term_eq, h_cross_1_eq, h_cross_2_eq, h_cross_3_eq,
        h_f_term_eq]
  have h_LHS_le_principal_A :
      B.lam *
        ∫ x, (η x)^2 *
          ∑ l : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial l) x ^ 2
          ∂(volume : Measure EuclN) ≤
      A_c - A_1 - A_2 - A_3 - A_f := by
    rw [← h_LHS_principal_eq, ← h_principal_in_A, ← h_RHS_principal_eq]
    exact h_principal_le
  have h_triangle :
      A_c - A_1 - A_2 - A_3 - A_f ≤
        |A_1| + |A_2| + |A_3| + |A_f| + |A_c| := by
    calc A_c - A_1 - A_2 - A_3 - A_f
        ≤ |A_c - A_1 - A_2 - A_3 - A_f| := le_abs_self _
      _ = |(- A_1) + (-A_2) + (-A_3) + (-A_f) + A_c| := by ring_nf
      _ ≤ |-A_1| + |-A_2| + |-A_3| + |-A_f| + |A_c| := by
          have h1 := abs_add_le ((- A_1) + (-A_2) + (-A_3) + (-A_f)) A_c
          have h2 := abs_add_le ((- A_1) + (-A_2) + (-A_3)) (-A_f)
          have h3 := abs_add_le ((- A_1) + (-A_2)) (-A_3)
          have h4 := abs_add_le (-A_1) (-A_2)
          linarith
      _ = |A_1| + |A_2| + |A_3| + |A_f| + |A_c| := by
          rw [abs_neg, abs_neg, abs_neg, abs_neg]
  exact h_LHS_le_principal_A.trans h_triangle

/-- The smooth extension of `densityOnEuclid` paired with the unit constant.

On `tsupport χ`, this is `χ · densityOnEuclid g α`. Off `tsupport χ` it is
the constant `1`. Smooth globally, positive, and equal to `densityOnEuclid`
exactly where `χ y = 1`. -/
private def extendedDensity
    (g : SmoothRiemannianMetric I M) (α : M) (χ : EuclN → ℝ) (y : EuclN) : ℝ :=
  χ y * densityOnEuclid (I := I) g α y + (1 - χ y) * 1

private lemma extendedDensity_contDiff
    (g : SmoothRiemannianMetric I M) (α : M) [I.Boundaryless]
    {χ : EuclN → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_supp : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ContDiff ℝ (⊤ : ℕ∞) (extendedDensity (I := I) g α χ) := by
  set f : EuclN → ℝ := extendedDensity (I := I) g α χ with hf_def
  set s : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hs_def
  set t : Set EuclN := (tsupport χ)ᶜ with ht_def
  have hs_open : IsOpen s := chartTargetEuclid_isOpen (I := I) (M := M) α
  have ht_open : IsOpen t := isClosed_tsupport _ |>.isOpen_compl
  have hcov : s ∪ t = Set.univ := by
    refine Set.eq_univ_of_forall ?_
    intro y
    by_cases hy : y ∈ tsupport χ
    · exact Or.inl (hχ_supp hy)
    · exact Or.inr hy
  have hf_on_s : ContDiffOn ℝ (⊤ : ℕ∞) f s := by
    change ContDiffOn ℝ (⊤ : ℕ∞) (fun y =>
      χ y * densityOnEuclid (I := I) g α y + (1 - χ y) * 1) s
    refine ContDiffOn.add ?_ ?_
    · exact hχ_smooth.contDiffOn.mul (densityOnEuclid_contDiffOn (I := I) g α)
    · exact (contDiffOn_const.sub hχ_smooth.contDiffOn).mul contDiffOn_const
  have hf_on_t : ContDiffOn ℝ (⊤ : ℕ∞) f t := by
    have hf_eq_const : ∀ y ∈ t, f y = 1 := by
      intro y hy
      have hχ_zero : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
      change extendedDensity (I := I) g α χ y = 1
      unfold extendedDensity
      rw [hχ_zero]; ring
    exact contDiffOn_const.congr (fun y hy => hf_eq_const y hy)
  exact contDiff_of_contDiffOn_union_of_isOpen hf_on_s hf_on_t hcov hs_open ht_open

private lemma extendedDensity_eq_density_of_chi_one
    (g : SmoothRiemannianMetric I M) (α : M) {χ : EuclN → ℝ} {y : EuclN}
    (hχ_one : χ y = 1) :
    extendedDensity (I := I) g α χ y = densityOnEuclid (I := I) g α y := by
  unfold extendedDensity
  rw [hχ_one]; ring

/-- Internal helper: build a `SmoothEllipticBilinearForm` whose principal
coefficient agrees with `weightedInvGramOnEuclid` on a chosen compact
`K ⊆ chartTargetEuclid α` AND whose zeroth-order coefficient agrees with
`densityOnEuclid` on `K`. -/
private theorem exists_smooth_metric_extension_with_density
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN}
    (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN),
      (∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
        B.a y i j = weightedInvGramOnEuclid (I := I) g α i j y) ∧
      (∀ y ∈ K, B.c y = densityOnEuclid (I := I) g α y) := by
  classical
  have hO : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨δ, δ_pos, hδ_subset⟩ := hK.exists_cthickening_subset_open hO hK_target
  set Ω' : Set EuclN := Metric.thickening δ K with hΩ'_def
  set K' : Set EuclN := Metric.cthickening δ K with hK'_def
  have hΩ'_open : IsOpen Ω' := Metric.isOpen_thickening
  have hK'_compact : IsCompact K' := hK.cthickening (r := δ)
  have h_K_in_Ω' : K ⊆ Ω' := Metric.self_subset_thickening δ_pos K
  have h_Ω'_in_K' : Ω' ⊆ K' := Metric.thickening_subset_cthickening δ K
  have h_K'_in_chart : K' ⊆ chartTargetEuclid (I := I) (M := M) α := hδ_subset
  obtain ⟨χ, hχ_smooth, hχ_supp, hχ_range, hχ_one, hχ_tsupp⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff
      (d := Module.finrank ℝ E)
      (K := K) (Ω' := Ω') hK hΩ'_open h_K_in_Ω'
  have hχ_tsupp_chart : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α := by
    intro y hy
    have h1 : y ∈ Ω' := hχ_tsupp hy
    exact (h_Ω'_in_K'.trans h_K'_in_chart) h1
  have hχ_tsupp_compact : IsCompact (tsupport χ) := hχ_supp
  obtain ⟨lamK0, hlamK0_pos, hlamK0_bound⟩ :=
    exists_unif_lower_bound_on_compact (I := I) g α hχ_tsupp_compact hχ_tsupp_chart
  set lamK : ℝ := min 1 lamK0 with hlamK_def
  have hlamK_pos : 0 < lamK := lt_min one_pos hlamK0_pos
  have hlamK_le_one : lamK ≤ 1 := min_le_left _ _
  have hlamK_le_lamK0 : lamK ≤ lamK0 := min_le_right _ _
  have hlamK0_bound_for_lamK : ∀ y ∈ tsupport χ, ∀ ξ : EuclN,
      lamK * ‖ξ‖ ^ 2 ≤
        ⟪ξ, DeGiorgi.matMulE
          (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
            weightedInvGramOnEuclid (I := I) g α i j y)) ξ⟫_ℝ := by
    intro y hy ξ
    have h0 := hlamK0_bound y hy ξ
    have h_norm_sq_nn : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
    have h_le : lamK * ‖ξ‖ ^ 2 ≤ lamK0 * ‖ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hlamK_le_lamK0 h_norm_sq_nn
    linarith
  let aFun : EuclN → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun y => Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      extendedMatrix (I := I) g α χ i j y)
  have h_a_smooth : ∀ i j : Fin (Module.finrank ℝ E),
      ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN => aFun y i j) := by
    intro i j
    change ContDiff ℝ (⊤ : ℕ∞) (extendedMatrix (I := I) g α χ i j)
    exact extendedMatrix_contDiff (I := I) g α
      (χ := χ) hχ_smooth hχ_tsupp_chart i j
  have h_a_symm : ∀ y i j, aFun y i j = aFun y j i := by
    intro y i j
    change extendedMatrix (I := I) g α χ i j y =
      extendedMatrix (I := I) g α χ j i y
    exact extendedMatrix_symm (I := I) g α
      (χ := χ) hχ_tsupp_chart i j y
  have h_a_coercive : ∀ y ∈ (Set.univ : Set EuclN), ∀ ξ : EuclN,
      lamK * ‖ξ‖ ^ 2 ≤ ⟪ξ, DeGiorgi.matMulE (aFun y) ξ⟫_ℝ := by
    intro y _ ξ
    change lamK * ‖ξ‖ ^ 2 ≤
      ⟪ξ, DeGiorgi.matMulE
        (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
          extendedMatrix (I := I) g α χ i j y)) ξ⟫_ℝ
    exact extendedMatrix_coercive (I := I) g α
      (χ := χ) hχ_range hχ_tsupp_chart hlamK_pos hlamK_le_one
      hlamK0_bound_for_lamK y ξ
  let cFun : EuclN → ℝ := extendedDensity (I := I) g α χ
  have h_c_smooth : ContDiff ℝ (⊤ : ℕ∞) cFun :=
    extendedDensity_contDiff (I := I) g α hχ_smooth hχ_tsupp_chart
  let B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN) :=
    { a := aFun
      c := cFun
      symm := h_a_symm
      smooth_a := h_a_smooth
      smooth_c := h_c_smooth
      lam := lamK
      capLam := max lamK 1
      hlam_pos := hlamK_pos
      hlam_le_capLam := le_max_left _ _
      coercive := h_a_coercive }
  have h_agree_a : ∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
      B.a y i j = weightedInvGramOnEuclid (I := I) g α i j y := by
    intro y hy i j
    change extendedMatrix (I := I) g α χ i j y =
      weightedInvGramOnEuclid (I := I) g α i j y
    have hχ_y : χ y = 1 := hχ_one y hy
    unfold extendedMatrix
    rw [hχ_y]; ring
  have h_agree_c : ∀ y ∈ K, B.c y = densityOnEuclid (I := I) g α y := by
    intro y hy
    change extendedDensity (I := I) g α χ y = densityOnEuclid (I := I) g α y
    exact extendedDensity_eq_density_of_chi_one (I := I) g α (hχ_one y hy)
  exact ⟨B, h_agree_a, h_agree_c⟩

set_option maxHeartbeats 8000000 in
set_option linter.unusedVariables false in
/-- **Quantitative final assembly**: the unconditional uniform-in-`h`
per-`(i, k)` `L²(Ω'')` bound on the difference quotient of the
chart-bilinear data's weak partial derivatives, with an *explicit
chart-geometric constant* `C_geom` that is **uniform over the bilinear
data `D`**.

Given a standard Nirenberg cutoff `η` on the Euclidean chart space with a
precompact target `Ω'` inside the chart target and `Ω'' ⊆ Ω'` on which
`η ≡ 1`, there is a constant `C_geom i k ≥ 0` — built purely from the
chart geometry (a smooth elliptic extension `B` of the metric and a
master cutoff `χ`, neither depending on `D`) — such that **for every**
`ChartBilinearH1ComplData D` and every `0 < |h| ≤ R₀`:

  `‖D_h^k (D.weak_partial i)‖_{L²(Ω'')} ≤`
  `  ENNReal.ofReal (C_geom i k · √(∑_l ‖D.weak_partial l‖²_{L²(closure Ω')}`
  `    + ‖D.u_chart‖²_{L²(closure Ω')} + ‖D.f_chart‖²_{L²(closure Ω')}))`.

Because `C_geom` is quantified **before** `D`, the statement asserts the
constant is uniform over all bilinear data — which is the whole point: the
chart-localising cutoff `χ` and the smooth elliptic extension `B` depend
only on `g`, `α`, `Ω'`, `η`, never on `D`.

The radius `R₀ > 0` is the diff-quotient bound; the proof works uniformly
in `R₀`. The existential headline `chartBilinearH1Compl_uniform_diffQuot_bound_of_data`
is a thin wrapper around this theorem. -/
theorem chartBilinearH1Compl_uniform_diffQuot_bound_of_data_quantitative
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_supp : HasCompactSupport η)
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
    (hΩ''_meas : MeasurableSet Ω'') :
    ∃ C_geom : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ,
      (∀ i k, 0 ≤ C_geom i k) ∧
      ∀ (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
        ⦃i k : Fin (Module.finrank ℝ E)⦄ ⦃h : ℝ⦄,
        0 < |h| → |h| ≤ R₀ →
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial i)) 2
            ((volume : Measure EuclN).restrict Ω'')
          ≤ ENNReal.ofReal (C_geom i k * Real.sqrt (
              (∑ l : Fin (Module.finrank ℝ E),
                (eLpNorm (D.weak_partial l) 2
                  ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
              + (eLpNorm D.u_chart 2
                  ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2
              + (eLpNorm D.f_chart 2
                  ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)) := by
  classical
  have hη_tsupp_compact : IsCompact (tsupport η) := hη_supp
  have h_cthickR0_compact : IsCompact (Metric.cthickening R₀ (tsupport η)) :=
    hη_tsupp_compact.cthickening
  have h_cthickR0_in_Ω' : Metric.cthickening R₀ (tsupport η) ⊆ Ω' := by
    have h := hh_supp_in_Ω' (h := R₀) (by rw [abs_of_pos hR₀_pos])
    rw [abs_of_pos hR₀_pos] at h
    exact h
  have h_cthickR0_in_chart :
      Metric.cthickening R₀ (tsupport η) ⊆
        chartTargetEuclid (I := I) (M := M) α :=
    h_cthickR0_in_Ω'.trans (subset_closure.trans hΩ'_chart)
  obtain ⟨B, hB_a_match, hB_c_match⟩ :=
    exists_smooth_metric_extension_with_density (I := I) (M := M) g α
      h_cthickR0_compact h_cthickR0_in_chart
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨δ, hδ_pos, hδ_in_chart⟩ :=
    hΩ'_compact.exists_cthickening_subset_open h_chart_open hΩ'_chart
  set K_χ : Set EuclN := Metric.cthickening (δ / 2) (closure Ω') with hK_χ_def
  have hδ_half_pos : 0 < δ / 2 := by linarith
  have hδ_half_lt_δ : δ / 2 < δ := by linarith
  have hK_χ_compact : IsCompact K_χ := hΩ'_compact.cthickening
  have hK_χ_in_thick_δ : K_χ ⊆ Metric.thickening δ (closure Ω') := by
    intro x hx
    rw [hK_χ_def] at hx
    have h_inf : Metric.infEDist x (closure Ω') ≤ ENNReal.ofReal (δ / 2) :=
      Metric.mem_cthickening_iff.mp hx
    have h_ofReal_lt : ENNReal.ofReal (δ / 2) < ENNReal.ofReal δ :=
      ENNReal.ofReal_lt_ofReal_iff hδ_pos |>.mpr hδ_half_lt_δ
    have h_inf_lt : Metric.infEDist x (closure Ω') < ENNReal.ofReal δ :=
      lt_of_le_of_lt h_inf h_ofReal_lt
    exact Metric.mem_thickening_iff_infEDist_lt.mpr h_inf_lt
  have h_thick_δ_in_chart :
      Metric.thickening δ (closure Ω') ⊆ chartTargetEuclid (I := I) (M := M) α := by
    intro x hx
    exact hδ_in_chart (Metric.thickening_subset_cthickening _ _ hx)
  obtain ⟨χ, hχ_smooth, hχ_cs, hχ_range, hχ_one, hχ_tsupp⟩ :=
    DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff
      (d := Module.finrank ℝ E)
      (K := K_χ)
      (Ω' := Metric.thickening δ (closure Ω'))
      hK_χ_compact Metric.isOpen_thickening hK_χ_in_thick_δ
  have hχ_tsupp_in_chart :
      tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α := by
    intro x hx
    exact h_thick_δ_in_chart (hχ_tsupp hx)
  have hχ_nn : ∀ x : EuclN, 0 ≤ χ x ∧ χ x ≤ 1 := by
    intro x
    have hx_range : χ x ∈ Set.range χ := Set.mem_range_self x
    exact ⟨(hχ_range hx_range).1, (hχ_range hx_range).2⟩
  have hχ_cont : Continuous χ := hχ_smooth.continuous
  obtain ⟨M_χ, hM_χ_nn, hM_χ_bd⟩ : ∃ M_χ : ℝ, 0 ≤ M_χ ∧ ∀ x, |χ x| ≤ M_χ := by
    by_cases hSupp_empty : (tsupport χ).Nonempty
    · obtain ⟨xMax, _, hxMax_max⟩ :=
        hχ_cs.exists_isMaxOn hSupp_empty hχ_cont.abs.continuousOn
      refine ⟨|χ xMax|, abs_nonneg _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport χ
      · exact hxMax_max hx
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hχx, abs_zero]; exact abs_nonneg _
    · refine ⟨0, le_refl _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport χ
      · exact absurd ⟨x, hx⟩ hSupp_empty
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hχx, abs_zero]
  have hχ_fderiv_cont : Continuous (fderiv ℝ χ) :=
    hχ_smooth.continuous_fderiv (by decide : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  have hχ_partial_cont : ∀ l : Fin (Module.finrank ℝ E), Continuous
      (fun x => (fderiv ℝ χ x) (EuclideanSpace.single l 1)) := fun l =>
    hχ_fderiv_cont.clm_apply continuous_const
  obtain ⟨M_dχ, hM_dχ_nn, hM_dχ_bd⟩ :
      ∃ M_dχ : ℝ, 0 ≤ M_dχ ∧ ∀ (l : Fin (Module.finrank ℝ E)) (x : EuclN),
        |(fderiv ℝ χ x) (EuclideanSpace.single l 1)| ≤ M_dχ := by
    have h_per_l : ∀ l : Fin (Module.finrank ℝ E),
        ∃ M : ℝ, 0 ≤ M ∧ ∀ x : EuclN,
          |(fderiv ℝ χ x) (EuclideanSpace.single l 1)| ≤ M := by
      intro l
      have h_cs_l : HasCompactSupport
          (fun x => (fderiv ℝ χ x) (EuclideanSpace.single l 1)) :=
        hχ_cs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single l 1)
      have h_cont_abs : Continuous
          (fun x => |(fderiv ℝ χ x) (EuclideanSpace.single l 1)|) :=
        (hχ_partial_cont l).abs
      by_cases hSupp_empty :
          (tsupport (fun x => (fderiv ℝ χ x) (EuclideanSpace.single l 1))).Nonempty
      · obtain ⟨xMax, _, hxMax_max⟩ :=
          h_cs_l.exists_isMaxOn hSupp_empty h_cont_abs.continuousOn
        refine ⟨|(fderiv ℝ χ xMax) (EuclideanSpace.single l 1)|,
          abs_nonneg _, fun x => ?_⟩
        by_cases hx : x ∈ tsupport
            (fun x => (fderiv ℝ χ x) (EuclideanSpace.single l 1))
        · exact hxMax_max hx
        · have hχx : (fderiv ℝ χ x) (EuclideanSpace.single l 1) = 0 :=
            image_eq_zero_of_notMem_tsupport
              (f := fun x => (fderiv ℝ χ x) (EuclideanSpace.single l 1)) hx
          rw [hχx, abs_zero]; exact abs_nonneg _
      · refine ⟨0, le_refl _, fun x => ?_⟩
        by_cases hx : x ∈ tsupport
            (fun x => (fderiv ℝ χ x) (EuclideanSpace.single l 1))
        · exact absurd ⟨x, hx⟩ hSupp_empty
        · have hχx : (fderiv ℝ χ x) (EuclideanSpace.single l 1) = 0 :=
            image_eq_zero_of_notMem_tsupport
              (f := fun x => (fderiv ℝ χ x) (EuclideanSpace.single l 1)) hx
          rw [hχx, abs_zero]
    choose Mfun hMfun_nn hMfun_bd using h_per_l
    set M_dχ : ℝ :=
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sup' Finset.univ_nonempty
        Mfun with hM_dχ_def
    have hM_dχ_nn : 0 ≤ M_dχ := by
      obtain ⟨l₀⟩ : Nonempty (Fin (Module.finrank ℝ E)) :=
        ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
      exact le_trans (hMfun_nn l₀)
        (Finset.le_sup' Mfun (Finset.mem_univ l₀))
    refine ⟨M_dχ, hM_dχ_nn, ?_⟩
    intro l x
    exact le_trans (hMfun_bd l x)
      (Finset.le_sup' Mfun (Finset.mem_univ l))
  set C_geom : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i k => Real.sqrt ((2 / B.lam) *
      nirenbergMasterYoungConstant B N hΩ'_compact k *
      (2 * ((Module.finrank ℝ E : ℝ) + 1) * (M_χ ^ 2 + M_dχ ^ 2 + 1)) *
      max 1 ((chartDensitySup (I := I) (M := M) g α Ω') ^ 2))
    with hC_geom_def
  refine ⟨C_geom, fun i k => Real.sqrt_nonneg _, ?_⟩
  intro D i k h hh_pos hh_le
  have h_FK_diffQuot_u_bound :=
    chartBilinearFK_diffQuot_u_discharge (I := I) (M := M) D hη_supp
      hΩ' hΩ'_chart hΩ'_compact hη_in_Ω' hR₀_pos hh_supp_in_Ω'
  have h_v_test_sq_bound :=
    chartBilinear_v_test_sq_discharge (I := I) (M := M) D hη hη_supp hη_range
      hN h_fderiv_eta hΩ' hΩ'_chart hΩ'_compact hη_in_Ω' hR₀_pos hh_supp_in_Ω'
  have h_master_nonsmooth :=
    chartBilinear_master_nonsmooth_discharge (I := I) (M := M) D B hη hη_supp
      hη_range hΩ' hΩ'_chart hΩ'_compact hη_in_Ω' hR₀_pos hh_supp_in_Ω'
      hB_a_match hB_c_match
  set u_g : EuclN → ℝ := fun x => χ x * D.u_chart x with hu_g_def
  set g_g : Fin (Module.finrank ℝ E) → EuclN → ℝ := fun i x =>
    (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.u_chart x +
    χ x * D.weak_partial i x with hg_g_def
  set f_g : EuclN → ℝ :=
    fun x => χ x * (densityOnEuclid (I := I) g α x * D.f_chart x) with hf_g_def
  have hu_g_l2 : MemLp u_g 2 (volume : Measure EuclN) :=
    cutoff_uChart_memLp_two_univ (I := I) (M := M) D hχ_smooth hχ_cs hχ_tsupp_in_chart
  have hg_g_l2 : ∀ i, MemLp (g_g i) 2 (volume : Measure EuclN) := fun i =>
    cutoff_uChart_partial_memLp_two_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_tsupp_in_chart i
  have hg_g_isWP : ∀ i, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (g_g i) u_g Set.univ := fun i =>
    cutoff_uChart_hasWeakPartialDeriv_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_tsupp_in_chart i
  have hf_g_l2_global : MemLp f_g 2 (volume : Measure EuclN) := by
    classical
    have hχ_cont : Continuous χ := hχ_smooth.continuous
    obtain ⟨M_χ, hM_χ_nn, hM_χ_bd⟩ : ∃ M_χ : ℝ, 0 ≤ M_χ ∧ ∀ x, |χ x| ≤ M_χ := by
      by_cases hSupp_empty : (tsupport χ).Nonempty
      · obtain ⟨xMax, _, hxMax_max⟩ :=
          hχ_cs.exists_isMaxOn hSupp_empty hχ_cont.abs.continuousOn
        refine ⟨|χ xMax|, abs_nonneg _, ?_⟩
        intro x
        by_cases hx : x ∈ tsupport χ
        · exact hxMax_max hx
        · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
          rw [hχx, abs_zero]; exact abs_nonneg _
      · refine ⟨0, le_refl _, ?_⟩
        intro x
        by_cases hx : x ∈ tsupport χ
        · exact absurd ⟨x, hx⟩ hSupp_empty
        · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
          rw [hχx, abs_zero]
    have h_supp_compact : IsCompact (tsupport χ) := hχ_cs
    have h_supp_meas : MeasurableSet (tsupport χ) :=
      (isClosed_tsupport χ).measurableSet
    have h_density_contOn : ContinuousOn (densityOnEuclid (I := I) g α)
        (tsupport χ) :=
      ((densityOnEuclid_contDiffOn (I := I) g α).continuousOn).mono
        hχ_tsupp_in_chart
    obtain ⟨M_d, hM_d_nn, hM_d_bd⟩ :
        ∃ M_d : ℝ, 0 ≤ M_d ∧ ∀ x ∈ tsupport χ,
          |densityOnEuclid (I := I) g α x| ≤ M_d := by
      by_cases hSupp_empty : (tsupport χ).Nonempty
      · obtain ⟨xMax, _, hxMax_max⟩ :=
          h_supp_compact.exists_isMaxOn hSupp_empty h_density_contOn.abs
        refine ⟨|densityOnEuclid (I := I) g α xMax|, abs_nonneg _, ?_⟩
        intro x hx; exact hxMax_max hx
      · refine ⟨0, le_refl _, ?_⟩
        intro x hx; exact absurd ⟨x, hx⟩ hSupp_empty
    have hf_l2_supp : MemLp D.f_chart 2
        ((volume : Measure EuclN).restrict (tsupport χ)) :=
      memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
        D.f_chart_memLp_weighted h_supp_compact h_supp_meas hχ_tsupp_in_chart
    have h_f_aesm : AEStronglyMeasurable D.f_chart
        ((volume : Measure EuclN).restrict (tsupport χ)) :=
      hf_l2_supp.aestronglyMeasurable
    have h_density_aesm_supp : AEStronglyMeasurable
        (densityOnEuclid (I := I) g α)
        ((volume : Measure EuclN).restrict (tsupport χ)) :=
      h_density_contOn.aestronglyMeasurable h_supp_meas
    have h_prod_aesm : AEStronglyMeasurable f_g
        ((volume : Measure EuclN).restrict (tsupport χ)) := by
      refine (hχ_cont.aestronglyMeasurable.restrict).mul ?_
      exact h_density_aesm_supp.mul h_f_aesm
    have h_pt_le : ∀ᵐ x ∂((volume : Measure EuclN).restrict (tsupport χ)),
        ‖f_g x‖ ≤ ‖(M_χ * M_d) * D.f_chart x‖ := by
      refine ae_restrict_of_forall_mem h_supp_meas ?_
      intro x hx
      change ‖χ x * (densityOnEuclid (I := I) g α x * D.f_chart x)‖ ≤ _
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      rw [show |M_χ * M_d| = M_χ * M_d from abs_of_nonneg (mul_nonneg hM_χ_nn hM_d_nn)]
      have h1 : |χ x| ≤ M_χ := hM_χ_bd x
      have h2 : |densityOnEuclid (I := I) g α x| ≤ M_d := hM_d_bd x hx
      have h3 : 0 ≤ |D.f_chart x| := abs_nonneg _
      nlinarith [abs_nonneg (χ x), abs_nonneg (densityOnEuclid (I := I) g α x),
        mul_le_mul h1 h2 (abs_nonneg _) hM_χ_nn]
    have h_const_lp : MemLp (fun x => (M_χ * M_d) * D.f_chart x) 2
        ((volume : Measure EuclN).restrict (tsupport χ)) :=
      hf_l2_supp.const_mul (M_χ * M_d)
    have h_restrict_lp : MemLp f_g 2
        ((volume : Measure EuclN).restrict (tsupport χ)) :=
      MemLp.mono h_const_lp h_prod_aesm h_pt_le
    have h_indicator_eq : (tsupport χ).indicator f_g = f_g := by
      funext x
      by_cases hx : x ∈ tsupport χ
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        have : f_g x = χ x * (densityOnEuclid (I := I) g α x * D.f_chart x) := rfl
        rw [this, hχx, zero_mul]
    have h_indicator_lp :
        MemLp ((tsupport χ).indicator f_g) 2 (volume : Measure EuclN) :=
      (MeasureTheory.memLp_indicator_iff_restrict h_supp_meas).mpr h_restrict_lp
    rw [h_indicator_eq] at h_indicator_lp
    exact h_indicator_lp
  have hf_g_l2_loc : ∀ {Ω'_in : Set EuclN}, IsCompact (closure Ω'_in) →
      MemLp f_g 2 ((volume : Measure EuclN).restrict Ω'_in) := fun _ =>
    hf_g_l2_global.restrict _
  have h_closure_subset_thick_half_δ :
      closure Ω' ⊆ Metric.thickening (δ / 2) (closure Ω') :=
    Metric.self_subset_thickening hδ_half_pos _
  have h_thick_half_subset_K_χ :
      Metric.thickening (δ / 2) (closure Ω') ⊆ K_χ := by
    rw [hK_χ_def]
    exact Metric.thickening_subset_cthickening _ _
  have h_closure_subset_K_χ : closure Ω' ⊆ K_χ :=
    h_closure_subset_thick_half_δ.trans h_thick_half_subset_K_χ
  have hχ_one_on_closure : ∀ x ∈ closure Ω', χ x = 1 := fun x hx =>
    hχ_one x (h_closure_subset_K_χ hx)
  have h_thick_half_open : IsOpen (Metric.thickening (δ / 2) (closure Ω')) :=
    Metric.isOpen_thickening
  have h_fderiv_χ_zero_on_thick :
      ∀ x ∈ Metric.thickening (δ / 2) (closure Ω'),
        ∀ k : Fin (Module.finrank ℝ E),
          (fderiv ℝ χ x) (EuclideanSpace.single k 1) = 0 := by
    intro x hx k
    have hχ_eq_one_nhds : (fun y => χ y) =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
      refine Filter.eventually_of_mem (h_thick_half_open.mem_nhds hx) ?_
      intro y hy
      exact hχ_one y (h_thick_half_subset_K_χ hy)
    have h_fderiv_eq : fderiv ℝ χ x = fderiv ℝ (fun _ : EuclN => (1 : ℝ)) x :=
      Filter.EventuallyEq.fderiv_eq hχ_eq_one_nhds
    rw [h_fderiv_eq]; simp
  have hu_g_eq_on_closure : ∀ x ∈ closure Ω', u_g x = D.u_chart x := by
    intro x hx
    have hχx : χ x = 1 := hχ_one_on_closure x hx
    change χ x * D.u_chart x = D.u_chart x
    rw [hχx, one_mul]
  have hg_g_eq_on_closure : ∀ x ∈ closure Ω',
      ∀ i : Fin (Module.finrank ℝ E), g_g i x = D.weak_partial i x := by
    intro x hx i
    have hχx : χ x = 1 := hχ_one_on_closure x hx
    have hx_in_thick : x ∈ Metric.thickening (δ / 2) (closure Ω') :=
      h_closure_subset_thick_half_δ hx
    have hdχx : (fderiv ℝ χ x) (EuclideanSpace.single i 1) = 0 :=
      h_fderiv_χ_zero_on_thick x hx_in_thick i
    change (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.u_chart x +
      χ x * D.weak_partial i x = D.weak_partial i x
    rw [hdχx, hχx, zero_mul, one_mul, zero_add]
  have h_cthick_h_subset_closure : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ closure Ω' := fun {h} hh_le =>
    (hh_supp_in_Ω' hh_le).trans subset_closure
  have h_tsupp_subset_closure : tsupport η ⊆ closure Ω' :=
    hη_in_Ω'.trans subset_closure
  have h_diffQuot_u_g_eq_on_tsupport :
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∀ (k : Fin (Module.finrank ℝ E)),
        ∀ x ∈ tsupport η,
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x =
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart x := by
    intro h hh hh_le k x hx
    have hx_in_closure : x ∈ closure Ω' := h_tsupp_subset_closure hx
    have h_shift_in_cthick : x + h • EuclideanSpace.single k 1 ∈
        Metric.cthickening |h| (tsupport η) := by
      refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η) hx ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
      rw [hsing, mul_one, Real.norm_eq_abs]
    have h_shift_in_closure :
        x + h • EuclideanSpace.single k 1 ∈ closure Ω' :=
      h_cthick_h_subset_closure hh_le h_shift_in_cthick
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh,
      DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh,
      hu_g_eq_on_closure x hx_in_closure,
      hu_g_eq_on_closure _ h_shift_in_closure]
  have h_diffQuot_g_g_eq_on_tsupport :
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∀ (k : Fin (Module.finrank ℝ E)) (i : Fin (Module.finrank ℝ E)),
        ∀ x ∈ tsupport η,
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (g_g i) x =
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weak_partial i) x := by
    intro h hh hh_le k i x hx
    have hx_in_closure : x ∈ closure Ω' := h_tsupp_subset_closure hx
    have h_shift_in_cthick : x + h • EuclideanSpace.single k 1 ∈
        Metric.cthickening |h| (tsupport η) := by
      refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η) hx ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
      rw [hsing, mul_one, Real.norm_eq_abs]
    have h_shift_in_closure :
        x + h • EuclideanSpace.single k 1 ∈ closure Ω' :=
      h_cthick_h_subset_closure hh_le h_shift_in_cthick
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh,
      DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh,
      hg_g_eq_on_closure x hx_in_closure i,
      hg_g_eq_on_closure _ h_shift_in_closure i]
  have hΩ'_meas : MeasurableSet Ω' := hΩ'.measurableSet
  have h_tsupp_meas : MeasurableSet (tsupport η) :=
    (isClosed_tsupport η).measurableSet
  have h_FK :
      ∀ (k : Fin (Module.finrank ℝ E)),
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
        ∫ x in tsupport η,
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g x)^2
          ∂(volume : Measure EuclN) ≤
          ∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E), ((g_g l) x) ^ 2
            ∂(volume : Measure EuclN) := by
    intro k h hh hh_le
    have h_LHS_eq :
        ∫ x in tsupport η,
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g x)^2
          ∂(volume : Measure EuclN) =
        ∫ x in tsupport η,
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.u_chart x)^2
          ∂(volume : Measure EuclN) := by
      refine setIntegral_congr_fun h_tsupp_meas ?_
      intro x hx
      have h_eq := h_diffQuot_u_g_eq_on_tsupport hh hh_le k x hx
      exact congrArg (· ^ 2) h_eq
    have hΩ'_subset_closure : Ω' ⊆ closure Ω' := subset_closure
    have h_RHS_eq :
        ∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E), ((g_g l) x) ^ 2
          ∂(volume : Measure EuclN) =
        ∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E), ((D.weak_partial l) x) ^ 2
          ∂(volume : Measure EuclN) := by
      refine setIntegral_congr_fun hΩ'_meas ?_
      intro x hx
      have hx_in_closure : x ∈ closure Ω' := hΩ'_subset_closure hx
      refine congrArg (fun s => s) ?_
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [hg_g_eq_on_closure x hx_in_closure l]
    rw [h_LHS_eq, h_RHS_eq]
    exact h_FK_diffQuot_u_bound k hh hh_le
  have h_nirenberg_eq :
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∀ (k : Fin (Module.finrank ℝ E)),
        ∀ x : EuclN,
          DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            (d := Module.finrank ℝ E) k h η u_g x =
          DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            (d := Module.finrank ℝ E) k h η D.u_chart x := by
    intro h hh hh_le k x
    have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
    have h_pt_inner : ∀ y : EuclN,
        (η y)^2 * DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g y =
        (η y)^2 * DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h D.u_chart y := by
      intro y
      by_cases hη_y : η y = 0
      · rw [hη_y]; ring
      · have hy_in_supp : y ∈ tsupport η :=
          subset_tsupport η (Function.mem_support.mpr hη_y)
        rw [h_diffQuot_u_g_eq_on_tsupport hh hh_le k y hy_in_supp]
    change DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h)
        (fun y => (η y)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g y) x =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h)
        (fun y => (η y)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart y) x
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hnh,
      DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hnh]
    rw [h_pt_inner (x + (-h) • EuclideanSpace.single k 1), h_pt_inner x]
  have h_v_test_sq :
      ∀ (k : Fin (Module.finrank ℝ E)),
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
        ∫ x, (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g x)^2 ∂(volume : Measure EuclN) ≤
          8 * N^2 *
            ∫ x in tsupport η,
                (DifferentialGeometry.Analysis.Sobolev.diffQuot k h u_g x)^2
              ∂(volume : Measure EuclN) +
          2 * ∫ x, (η x)^2 *
              (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g_g k) x)^2
            ∂(volume : Measure EuclN) := by
    intro k h hh hh_le
    have h_LHS_eq :
        ∫ x, (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g x)^2 ∂(volume : Measure EuclN) =
        ∫ x, (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η D.u_chart x)^2 ∂(volume : Measure EuclN) := by
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      change (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g x)^2 =
        (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η D.u_chart x)^2
      rw [h_nirenberg_eq hh hh_le k x]
    have h_RHS_1_eq :
        ∫ x in tsupport η,
            (DifferentialGeometry.Analysis.Sobolev.diffQuot k h u_g x)^2
          ∂(volume : Measure EuclN) =
        ∫ x in tsupport η,
            (DifferentialGeometry.Analysis.Sobolev.diffQuot k h D.u_chart x)^2
          ∂(volume : Measure EuclN) := by
      refine setIntegral_congr_fun h_tsupp_meas ?_
      intro x hx
      exact congrArg (· ^ 2) (h_diffQuot_u_g_eq_on_tsupport hh hh_le k x hx)
    have h_RHS_2_eq :
        ∫ x, (η x)^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g_g k) x)^2
          ∂(volume : Measure EuclN) =
        ∫ x, (η x)^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (D.weak_partial k) x)^2
          ∂(volume : Measure EuclN) := by
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      change (η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g_g k) x)^2 =
        (η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (D.weak_partial k) x)^2
      by_cases hη_x : η x = 0
      · rw [hη_x]; ring
      · have hx_in_supp : x ∈ tsupport η :=
          subset_tsupport η (Function.mem_support.mpr hη_x)
        rw [h_diffQuot_g_g_eq_on_tsupport hh hh_le k k x hx_in_supp]
    rw [h_LHS_eq, h_RHS_1_eq, h_RHS_2_eq]
    exact h_v_test_sq_bound k hh hh_le
  have h_master :
      ∀ (k : Fin (Module.finrank ℝ E)),
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      B.lam * ∫ x, (η x)^2 *
          ∑ l : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g_g l) x ^ 2
        ∂(volume : Measure EuclN) ≤
        |∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              2 * DifferentialGeometry.Analysis.Sobolev.translate k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g_g i) x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u_g x
            ∂(volume : Measure EuclN)| +
        |∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : EuclN => B.a y i j) x * (η x)^2 *
              ((g_g i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g_g j) x
            ∂(volume : Measure EuclN)| +
        |∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((g_g i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u_g x
            ∂(volume : Measure EuclN)| +
        |∫ x in (Set.univ : Set EuclN), f_g x *
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g x| +
        |∫ x in (Set.univ : Set EuclN), B.c x * u_g x *
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g x ∂(volume : Measure EuclN)| := by
    intro k h hh hh_le
    have h_LHS_eq :
        ∫ x, (η x)^2 *
            ∑ l : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g_g l) x ^ 2
          ∂(volume : Measure EuclN) =
        ∫ x, (η x)^2 *
            ∑ l : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (D.weak_partial l) x ^ 2
          ∂(volume : Measure EuclN) := by
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      change (η x)^2 *
            ∑ l : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g_g l) x ^ 2 =
        (η x)^2 *
            ∑ l : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (D.weak_partial l) x ^ 2
      by_cases hη_x : η x = 0
      · rw [hη_x]; ring
      · have hx_in_supp : x ∈ tsupport η :=
          subset_tsupport η (Function.mem_support.mpr hη_x)
        congr 1
        refine Finset.sum_congr rfl ?_
        intro l _
        rw [h_diffQuot_g_g_eq_on_tsupport hh hh_le k l x hx_in_supp]
    have h_A1_eq :
        ∀ i j : Fin (Module.finrank ℝ E),
        ∫ x, 2 * DifferentialGeometry.Analysis.Sobolev.translate k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g_g i) x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u_g x
            ∂(volume : Measure EuclN) =
        ∫ x, 2 * DifferentialGeometry.Analysis.Sobolev.translate k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (D.weak_partial i) x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h D.u_chart x
            ∂(volume : Measure EuclN) := by
      intro i j
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      change 2 * DifferentialGeometry.Analysis.Sobolev.translate k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g_g i) x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u_g x =
        2 * DifferentialGeometry.Analysis.Sobolev.translate k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (D.weak_partial i) x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h D.u_chart x
      by_cases hη_x : η x = 0
      · rw [hη_x]; ring
      · have hx_in_supp : x ∈ tsupport η :=
          subset_tsupport η (Function.mem_support.mpr hη_x)
        rw [h_diffQuot_g_g_eq_on_tsupport hh hh_le k i x hx_in_supp,
            h_diffQuot_u_g_eq_on_tsupport hh hh_le k x hx_in_supp]
    have h_A2_eq :
        ∀ i j : Fin (Module.finrank ℝ E),
        ∫ x, DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : EuclN => B.a y i j) x * (η x)^2 *
              ((g_g i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g_g j) x
            ∂(volume : Measure EuclN) =
        ∫ x, DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : EuclN => B.a y i j) x * (η x)^2 *
              ((D.weak_partial i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (D.weak_partial j) x
            ∂(volume : Measure EuclN) := by
      intro i j
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      change DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : EuclN => B.a y i j) x * (η x)^2 *
            ((g_g i) x) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g_g j) x =
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : EuclN => B.a y i j) x * (η x)^2 *
            ((D.weak_partial i) x) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h (D.weak_partial j) x
      by_cases hη_x : η x = 0
      · rw [hη_x]; ring
      · have hx_in_supp : x ∈ tsupport η :=
          subset_tsupport η (Function.mem_support.mpr hη_x)
        have hx_in_closure : x ∈ closure Ω' := h_tsupp_subset_closure hx_in_supp
        rw [hg_g_eq_on_closure x hx_in_closure i,
            h_diffQuot_g_g_eq_on_tsupport hh hh_le k j x hx_in_supp]
    have h_A3_eq :
        ∀ i j : Fin (Module.finrank ℝ E),
        ∫ x, 2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((g_g i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u_g x
            ∂(volume : Measure EuclN) =
        ∫ x, 2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((D.weak_partial i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h D.u_chart x
            ∂(volume : Measure EuclN) := by
      intro i j
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      change 2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : EuclN => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            ((g_g i) x) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h u_g x =
        2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun y : EuclN => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            ((D.weak_partial i) x) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h D.u_chart x
      by_cases hη_x : η x = 0
      · rw [hη_x]; ring
      · have hx_in_supp : x ∈ tsupport η :=
          subset_tsupport η (Function.mem_support.mpr hη_x)
        have hx_in_closure : x ∈ closure Ω' := h_tsupp_subset_closure hx_in_supp
        rw [hg_g_eq_on_closure x hx_in_closure i,
            h_diffQuot_u_g_eq_on_tsupport hh hh_le k x hx_in_supp]
    have h_f_term_eq :
        ∫ x in (Set.univ : Set EuclN), f_g x *
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g x =
        ∫ x in (Set.univ : Set EuclN),
            (densityOnEuclid (I := I) g α x * D.f_chart x) *
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η D.u_chart x := by
      refine setIntegral_congr_ae MeasurableSet.univ ?_
      refine Filter.Eventually.of_forall ?_
      intro x _
      have h_supp_subset :
          Function.support
            (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η D.u_chart) ⊆
            Metric.cthickening |h| (tsupport η) := by
        intro y hy
        rw [Function.mem_support] at hy
        have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
        change DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun y₁ => (η y₁)^2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart y₁) y ≠ 0 at hy
        rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
            (d := Module.finrank ℝ E) k hnh] at hy
        have h_num_ne :
            (η (y + (-h) • EuclideanSpace.single k 1))^2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart
                  (y + (-h) • EuclideanSpace.single k 1) -
            (η y)^2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart y ≠ 0 := by
          intro h_zero
          apply hy
          rw [h_zero, zero_div]
        by_cases hη_y : η y = 0
        · have h_first_zero : (η y)^2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart y = 0 := by
            rw [hη_y]; ring
          rw [h_first_zero, sub_zero] at h_num_ne
          have h_eta_shift_ne : η (y + (-h) • EuclideanSpace.single k 1) ≠ 0 := by
            intro h_zero
            apply h_num_ne
            rw [show (η (y + (-h) • EuclideanSpace.single k 1))^2 = 0 from by
              rw [h_zero]; ring, zero_mul]
          have h_shift_in_supp :
              y + (-h) • EuclideanSpace.single k 1 ∈ tsupport η :=
            subset_tsupport η (Function.mem_support.mpr h_eta_shift_ne)
          refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η)
            h_shift_in_supp ?_
          rw [dist_eq_norm]
          have h_diff_eq : y - (y + (-h) • EuclideanSpace.single k 1) =
              h • EuclideanSpace.single k 1 := by
            rw [sub_add_eq_sub_sub, sub_self, zero_sub, neg_smul, neg_neg]
          rw [h_diff_eq, norm_smul]
          have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
          rw [hsing, mul_one, Real.norm_eq_abs]
        · exact Metric.self_subset_cthickening _
            (subset_tsupport η (Function.mem_support.mpr hη_y))
      have h_supp_subset_u_g :
          Function.support
            (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g) ⊆
            Metric.cthickening |h| (tsupport η) := by
        intro y hy
        rw [Function.mem_support] at hy
        have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
        change DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun y₁ => (η y₁)^2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h u_g y₁) y ≠ 0 at hy
        rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
            (d := Module.finrank ℝ E) k hnh] at hy
        have h_num_ne :
            (η (y + (-h) • EuclideanSpace.single k 1))^2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h u_g
                  (y + (-h) • EuclideanSpace.single k 1) -
            (η y)^2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h u_g y ≠ 0 := by
          intro h_zero
          apply hy
          rw [h_zero, zero_div]
        by_cases hη_y : η y = 0
        · have h_first_zero : (η y)^2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h u_g y = 0 := by
            rw [hη_y]; ring
          rw [h_first_zero, sub_zero] at h_num_ne
          have h_eta_shift_ne : η (y + (-h) • EuclideanSpace.single k 1) ≠ 0 := by
            intro h_zero
            apply h_num_ne
            rw [show (η (y + (-h) • EuclideanSpace.single k 1))^2 = 0 from by
              rw [h_zero]; ring, zero_mul]
          have h_shift_in_supp :
              y + (-h) • EuclideanSpace.single k 1 ∈ tsupport η :=
            subset_tsupport η (Function.mem_support.mpr h_eta_shift_ne)
          refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η)
            h_shift_in_supp ?_
          rw [dist_eq_norm]
          have h_diff_eq : y - (y + (-h) • EuclideanSpace.single k 1) =
              h • EuclideanSpace.single k 1 := by
            rw [sub_add_eq_sub_sub, sub_self, zero_sub, neg_smul, neg_neg]
          rw [h_diff_eq, norm_smul]
          have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
          rw [hsing, mul_one, Real.norm_eq_abs]
        · exact Metric.self_subset_cthickening _
            (subset_tsupport η (Function.mem_support.mpr hη_y))
      by_cases hx_in : x ∈ Metric.cthickening |h| (tsupport η)
      · have hx_in_closure : x ∈ closure Ω' :=
          h_cthick_h_subset_closure hh_le hx_in
        have hχx : χ x = 1 := hχ_one_on_closure x hx_in_closure
        have hf_g_eq : f_g x = densityOnEuclid (I := I) g α x * D.f_chart x := by
          change χ x * (densityOnEuclid (I := I) g α x * D.f_chart x) =
            densityOnEuclid (I := I) g α x * D.f_chart x
          rw [hχx, one_mul]
        rw [hf_g_eq, h_nirenberg_eq hh hh_le k x]
      · have h_test_u_g_zero :
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g x = 0 := by
          by_contra h_ne
          exact hx_in (h_supp_subset_u_g (Function.mem_support.mpr h_ne))
        have h_test_D_zero :
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η D.u_chart x = 0 := by
          by_contra h_ne
          exact hx_in (h_supp_subset (Function.mem_support.mpr h_ne))
        rw [h_test_u_g_zero, h_test_D_zero, mul_zero, mul_zero]
    have h_c_term_eq :
        ∫ x in (Set.univ : Set EuclN), B.c x * u_g x *
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g x ∂(volume : Measure EuclN) =
        ∫ x in (Set.univ : Set EuclN), B.c x * D.u_chart x *
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η D.u_chart x ∂(volume : Measure EuclN) := by
      refine setIntegral_congr_ae MeasurableSet.univ ?_
      refine Filter.Eventually.of_forall ?_
      intro x _
      have h_supp_subset_D :
          Function.support
            (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η D.u_chart) ⊆
            Metric.cthickening |h| (tsupport η) := by
        intro y hy
        rw [Function.mem_support] at hy
        have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
        change DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun y₁ => (η y₁)^2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart y₁) y ≠ 0 at hy
        rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
            (d := Module.finrank ℝ E) k hnh] at hy
        have h_num_ne :
            (η (y + (-h) • EuclideanSpace.single k 1))^2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart
                  (y + (-h) • EuclideanSpace.single k 1) -
            (η y)^2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart y ≠ 0 := by
          intro h_zero; apply hy; rw [h_zero, zero_div]
        by_cases hη_y : η y = 0
        · have h_first_zero : (η y)^2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart y = 0 := by
            rw [hη_y]; ring
          rw [h_first_zero, sub_zero] at h_num_ne
          have h_eta_shift_ne : η (y + (-h) • EuclideanSpace.single k 1) ≠ 0 := by
            intro h_zero
            apply h_num_ne
            rw [show (η (y + (-h) • EuclideanSpace.single k 1))^2 = 0 from by
              rw [h_zero]; ring, zero_mul]
          have h_shift_in_supp :
              y + (-h) • EuclideanSpace.single k 1 ∈ tsupport η :=
            subset_tsupport η (Function.mem_support.mpr h_eta_shift_ne)
          refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η)
            h_shift_in_supp ?_
          rw [dist_eq_norm]
          have h_diff_eq : y - (y + (-h) • EuclideanSpace.single k 1) =
              h • EuclideanSpace.single k 1 := by
            rw [sub_add_eq_sub_sub, sub_self, zero_sub, neg_smul, neg_neg]
          rw [h_diff_eq, norm_smul]
          have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
          rw [hsing, mul_one, Real.norm_eq_abs]
        · exact Metric.self_subset_cthickening _
            (subset_tsupport η (Function.mem_support.mpr hη_y))
      have h_supp_subset_u :
          Function.support
            (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g) ⊆
            Metric.cthickening |h| (tsupport η) := by
        intro y hy
        rw [Function.mem_support] at hy
        have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
        change DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun y₁ => (η y₁)^2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h u_g y₁) y ≠ 0 at hy
        rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
            (d := Module.finrank ℝ E) k hnh] at hy
        have h_num_ne :
            (η (y + (-h) • EuclideanSpace.single k 1))^2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h u_g
                  (y + (-h) • EuclideanSpace.single k 1) -
            (η y)^2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h u_g y ≠ 0 := by
          intro h_zero; apply hy; rw [h_zero, zero_div]
        by_cases hη_y : η y = 0
        · have h_first_zero : (η y)^2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h u_g y = 0 := by
            rw [hη_y]; ring
          rw [h_first_zero, sub_zero] at h_num_ne
          have h_eta_shift_ne : η (y + (-h) • EuclideanSpace.single k 1) ≠ 0 := by
            intro h_zero
            apply h_num_ne
            rw [show (η (y + (-h) • EuclideanSpace.single k 1))^2 = 0 from by
              rw [h_zero]; ring, zero_mul]
          have h_shift_in_supp :
              y + (-h) • EuclideanSpace.single k 1 ∈ tsupport η :=
            subset_tsupport η (Function.mem_support.mpr h_eta_shift_ne)
          refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η)
            h_shift_in_supp ?_
          rw [dist_eq_norm]
          have h_diff_eq : y - (y + (-h) • EuclideanSpace.single k 1) =
              h • EuclideanSpace.single k 1 := by
            rw [sub_add_eq_sub_sub, sub_self, zero_sub, neg_smul, neg_neg]
          rw [h_diff_eq, norm_smul]
          have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
          rw [hsing, mul_one, Real.norm_eq_abs]
        · exact Metric.self_subset_cthickening _
            (subset_tsupport η (Function.mem_support.mpr hη_y))
      by_cases hx_in : x ∈ Metric.cthickening |h| (tsupport η)
      · have hx_in_closure : x ∈ closure Ω' :=
          h_cthick_h_subset_closure hh_le hx_in
        have hu_eq : u_g x = D.u_chart x := hu_g_eq_on_closure x hx_in_closure
        rw [hu_eq, h_nirenberg_eq hh hh_le k x]
      · have h_test_u_g_zero :
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g x = 0 := by
          by_contra h_ne
          exact hx_in (h_supp_subset_u (Function.mem_support.mpr h_ne))
        have h_test_D_zero :
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η D.u_chart x = 0 := by
          by_contra h_ne
          exact hx_in (h_supp_subset_D (Function.mem_support.mpr h_ne))
        rw [h_test_u_g_zero, h_test_D_zero, mul_zero, mul_zero]
    rw [h_LHS_eq]
    have h_A1_sum_eq :
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              2 * DifferentialGeometry.Analysis.Sobolev.translate k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g_g i) x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u_g x
            ∂(volume : Measure EuclN) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              2 * DifferentialGeometry.Analysis.Sobolev.translate k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (D.weak_partial i) x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h D.u_chart x
            ∂(volume : Measure EuclN) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      exact h_A1_eq i j
    have h_A2_sum_eq :
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : EuclN => B.a y i j) x * (η x)^2 *
              ((g_g i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g_g j) x
            ∂(volume : Measure EuclN) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : EuclN => B.a y i j) x * (η x)^2 *
              ((D.weak_partial i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (D.weak_partial j) x
            ∂(volume : Measure EuclN) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      exact h_A2_eq i j
    have h_A3_sum_eq :
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((g_g i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h u_g x
            ∂(volume : Measure EuclN) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((D.weak_partial i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h D.u_chart x
            ∂(volume : Measure EuclN) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      exact h_A3_eq i j
    rw [h_A1_sum_eq, h_A2_sum_eq, h_A3_sum_eq, h_f_term_eq, h_c_term_eq]
    exact h_master_nonsmooth k hh hh_le
  have h_g_g_quant :
      eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (g_g i)) 2
        ((volume : Measure EuclN).restrict Ω'')
      ≤ ENNReal.ofReal (Real.sqrt ((2 / B.lam) *
          nirenbergMasterYoungConstant B N hΩ'_compact k *
          (∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E), ((g_g l) x) ^ 2
              ∂(volume : Measure EuclN) +
            ∫ x in Ω', (u_g x)^2 ∂(volume : Measure EuclN) +
            ∫ x in Ω', (f_g x)^2 ∂(volume : Measure EuclN)))) :=
    chartBilinearH1Compl_uniform_diffQuot_bound_quantitative
      (I := I) (M := M) (E := E) (H := H) (g := g) (α := α)
      D B hu_g_l2 hf_g_l2_loc hg_g_l2 hg_g_isWP hη hη_supp hη_range hN
      h_fderiv_eta hΩ' (by intro x _; exact Set.mem_univ _) hΩ'_compact
      hη_in_Ω' hh_supp_in_Ω' hη_one_on_Ω'' hΩ''_meas
      h_FK h_v_test_sq h_master hh_pos hh_le
  have hΩ'_closure_meas : MeasurableSet (closure Ω') :=
    isClosed_closure.measurableSet
  have hf_chart_l2_closure : MemLp D.f_chart 2
      ((volume : Measure EuclN).restrict (closure Ω')) :=
    memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
      D.f_chart_memLp_weighted hΩ'_compact hΩ'_closure_meas hΩ'_chart
  set fSrc : EuclN → ℝ := fun x => densityOnEuclid (I := I) g α x * D.f_chart x
    with hfSrc_def
  have hfSrc_l2_closure : MemLp fSrc 2
      ((volume : Measure EuclN).restrict (closure Ω')) :=
    densityWeightedSource_memLp (I := I) (M := M) (g := g) (α := α)
      hΩ'_compact hΩ'_chart hf_chart_l2_closure
  set Sw : ℝ := ∑ l : Fin (Module.finrank ℝ E),
      (eLpNorm (D.weak_partial l) 2
        ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2 with hSw_def
  set Su : ℝ := (eLpNorm D.u_chart 2
      ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2 with hSu_def
  set Sf : ℝ := (eLpNorm D.f_chart 2
      ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2 with hSf_def
  have hSw_nn : 0 ≤ Sw := by
    rw [hSw_def]; exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hSu_nn : 0 ≤ Su := by rw [hSu_def]; exact sq_nonneg _
  have hSf_nn : 0 ≤ Sf := by rw [hSf_def]; exact sq_nonneg _
  set G_total : ℝ :=
    (∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E), ((g_g l) x) ^ 2
        ∂(volume : Measure EuclN) +
      ∫ x in Ω', (u_g x)^2 ∂(volume : Measure EuclN) +
      ∫ x in Ω', (f_g x)^2 ∂(volume : Measure EuclN)) with hG_total_def
  have hG_total_nn : 0 ≤ G_total := by
    rw [hG_total_def]
    refine add_nonneg (add_nonneg ?_ ?_) ?_
    · exact integral_nonneg (fun x => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    · exact integral_nonneg (fun x => sq_nonneg _)
    · exact integral_nonneg (fun x => sq_nonneg _)
  set Cχ : ℝ :=
    2 * ((Module.finrank ℝ E : ℝ) + 1) * (M_χ ^ 2 + M_dχ ^ 2 + 1) with hCχ_def
  have hCχ_nn : 0 ≤ Cχ := by
    rw [hCχ_def]
    have hn_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    positivity
  have h_Sf'_le :
      (eLpNorm fSrc 2
        ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2 ≤
        (chartDensitySup (I := I) (M := M) g α Ω') ^ 2 * Sf := by
    have h := densityWeightedSource_eLpNorm_sq_le (I := I) (M := M)
      (g := g) (α := α) hΩ'_compact hΩ'_chart hf_chart_l2_closure
    rw [hfSrc_def, hSf_def]
    exact h
  have h_gTotal_data : G_total ≤
      Cχ * (Sw + Su +
        (eLpNorm fSrc 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2) := by
    have h := gTotal_le_data_eLpNorm (I := I) (M := M) (g := g) (α := α)
      hχ_smooth hM_χ_bd hM_dχ_bd hΩ'_compact hΩ'_chart hfSrc_l2_closure D
    rw [hG_total_def, hCχ_def, hSw_def, hSu_def]
    simp only [hg_g_def, hu_g_def, hf_g_def, hfSrc_def] at h ⊢
    convert h using 2
  set Mden2 : ℝ := max 1 ((chartDensitySup (I := I) (M := M) g α Ω') ^ 2)
    with hMden2_def
  have hMden2_one_le : (1 : ℝ) ≤ Mden2 := le_max_left _ _
  have hMden2_dens_le : (chartDensitySup (I := I) (M := M) g α Ω') ^ 2 ≤ Mden2 :=
    le_max_right _ _
  have hMden2_nn : 0 ≤ Mden2 := le_trans zero_le_one hMden2_one_le
  have h_gTotal_max : G_total ≤ Cχ * Mden2 * (Sw + Su + Sf) := by
    refine le_trans h_gTotal_data ?_
    have h_inner :
        Sw + Su +
          (eLpNorm fSrc 2
            ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2 ≤
          Mden2 * (Sw + Su + Sf) := by
      have h_w : Sw ≤ Mden2 * Sw :=
        le_mul_of_one_le_left hSw_nn hMden2_one_le
      have h_u : Su ≤ Mden2 * Su :=
        le_mul_of_one_le_left hSu_nn hMden2_one_le
      have h_f :
          (eLpNorm fSrc 2
            ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2 ≤
            Mden2 * Sf := by
        refine le_trans h_Sf'_le ?_
        exact mul_le_mul_of_nonneg_right hMden2_dens_le hSf_nn
      have h_expand : Mden2 * (Sw + Su + Sf) =
          Mden2 * Sw + Mden2 * Su + Mden2 * Sf := by ring
      linarith [h_w, h_u, h_f, h_expand]
    calc Cχ * (Sw + Su +
            (eLpNorm fSrc 2
              ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
        ≤ Cχ * (Mden2 * (Sw + Su + Sf)) :=
          mul_le_mul_of_nonneg_left h_inner hCχ_nn
      _ = Cχ * Mden2 * (Sw + Su + Sf) := by ring
  have hlam_pos : 0 < B.lam := B.hlam_pos
  have h_two_lam_nn : (0 : ℝ) ≤ 2 / B.lam := by positivity
  have hC_young_nn : 0 ≤ nirenbergMasterYoungConstant B N hΩ'_compact k :=
    nirenbergMasterYoungConstant_nonneg B hN hΩ'_compact k
  have h_coeff_nn : 0 ≤ (2 / B.lam) *
      nirenbergMasterYoungConstant B N hΩ'_compact k * Cχ * Mden2 :=
    mul_nonneg (mul_nonneg (mul_nonneg h_two_lam_nn hC_young_nn) hCχ_nn) hMden2_nn
  have h_sqrt_arg_le :
      (2 / B.lam) * nirenbergMasterYoungConstant B N hΩ'_compact k * G_total ≤
        ((2 / B.lam) * nirenbergMasterYoungConstant B N hΩ'_compact k *
          Cχ * Mden2) * (Sw + Su + Sf) := by
    have h_pre_nn : 0 ≤ (2 / B.lam) *
        nirenbergMasterYoungConstant B N hΩ'_compact k :=
      mul_nonneg h_two_lam_nn hC_young_nn
    calc (2 / B.lam) * nirenbergMasterYoungConstant B N hΩ'_compact k * G_total
        ≤ (2 / B.lam) * nirenbergMasterYoungConstant B N hΩ'_compact k *
            (Cχ * Mden2 * (Sw + Su + Sf)) :=
          mul_le_mul_of_nonneg_left h_gTotal_max h_pre_nn
      _ = ((2 / B.lam) * nirenbergMasterYoungConstant B N hΩ'_compact k *
            Cχ * Mden2) * (Sw + Su + Sf) := by ring
  have hC_geom_eq : C_geom i k =
      Real.sqrt ((2 / B.lam) *
        nirenbergMasterYoungConstant B N hΩ'_compact k * Cχ * Mden2) := by
    simp only [hC_geom_def, hCχ_def, hMden2_def]
  have h_sqrt_le :
      Real.sqrt ((2 / B.lam) *
        nirenbergMasterYoungConstant B N hΩ'_compact k * G_total) ≤
        C_geom i k * Real.sqrt (Sw + Su + Sf) := by
    have h_mono := Real.sqrt_le_sqrt h_sqrt_arg_le
    have h_split :
        Real.sqrt (((2 / B.lam) *
          nirenbergMasterYoungConstant B N hΩ'_compact k * Cχ * Mden2) *
            (Sw + Su + Sf)) =
          C_geom i k * Real.sqrt (Sw + Su + Sf) := by
      rw [Real.sqrt_mul h_coeff_nn, hC_geom_eq]
    calc Real.sqrt ((2 / B.lam) *
            nirenbergMasterYoungConstant B N hΩ'_compact k * G_total)
        ≤ Real.sqrt (((2 / B.lam) *
            nirenbergMasterYoungConstant B N hΩ'_compact k * Cχ * Mden2) *
              (Sw + Su + Sf)) := h_mono
      _ = C_geom i k * Real.sqrt (Sw + Su + Sf) := h_split
  have h_g_g_bd :
      eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (g_g i)) 2
        ((volume : Measure EuclN).restrict Ω'')
      ≤ ENNReal.ofReal (C_geom i k * Real.sqrt (Sw + Su + Sf)) := by
    refine le_trans h_g_g_quant ?_
    exact ENNReal.ofReal_le_ofReal h_sqrt_le
  have hh_ne : h ≠ 0 := abs_ne_zero.mp (ne_of_gt hh_pos)
  have hΩ''_subset_tsupp : Ω'' ⊆ tsupport η := by
    intro x hx
    have hη_x_eq_one : η x = 1 := hη_one_on_Ω'' x hx
    have hη_x_ne : η x ≠ 0 := by rw [hη_x_eq_one]; norm_num
    exact subset_tsupport η (Function.mem_support.mpr hη_x_ne)
  have h_eq_on_Ω'' : ∀ x ∈ Ω'',
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (g_g i) x =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial i) x := by
    intro x hx
    exact h_diffQuot_g_g_eq_on_tsupport hh_ne hh_le k i x (hΩ''_subset_tsupp hx)
  have h_eLp_eq :
      eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weak_partial i)) 2
        ((volume : Measure EuclN).restrict Ω'') =
      eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (g_g i)) 2
        ((volume : Measure EuclN).restrict Ω'') := by
    refine eLpNorm_congr_ae ?_
    refine (ae_restrict_iff' hΩ''_meas).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    exact (h_eq_on_Ω'' x hx).symm
  rw [h_eLp_eq]
  rw [show (∑ l : Fin (Module.finrank ℝ E),
        (eLpNorm (D.weak_partial l) 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
      + (eLpNorm D.u_chart 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2
      + (eLpNorm D.f_chart 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2
      = Sw + Su + Sf from by rw [hSw_def, hSu_def, hSf_def]]
  exact h_g_g_bd

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
/-- **Final assembly**: the unconditional uniform-in-`h` per-`(i, k)`
`L²(Ω'')` bound on the difference quotient of the chart-bilinear data's
weak partial derivatives.

Given a chart-bilinear data structure `D`, a standard Nirenberg cutoff `η`
on the Euclidean chart space with a precompact target Ω' inside the chart
target and Ω'' ⊆ Ω' on which `η ≡ 1`, the wrapper produces a constant
`M_bound i k ≥ 0` such that for every `0 < |h| ≤ R₀`:

  `‖D_h^k (D.weak_partial i)‖_{L²(Ω'')} ≤ ENNReal.ofReal (M_bound i k)`.

The conclusion is the uniform-in-`h` bound consumed by
`h2_chart_loc_of_uniform_bound` to extract `H²` regularity. The radius
`R₀ > 0` is the diff-quotient bound; the proof works uniformly in `R₀`.

This is a thin wrapper around the quantitative theorem
`chartBilinearH1Compl_uniform_diffQuot_bound_of_data_quantitative`: the
existential witness `M_bound i k` is the quantitative theorem's explicit
chart-geometric constant `C_geom i k` multiplied by the (data-dependent)
square root of the `L²` energy of `D`. -/
theorem chartBilinearH1Compl_uniform_diffQuot_bound_of_data
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_supp : HasCompactSupport η)
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
    (hΩ''_meas : MeasurableSet Ω'') :
    ∃ M_bound : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ,
      (∀ i k, 0 ≤ M_bound i k) ∧
      (∀ (i k : Fin (Module.finrank ℝ E)) (h : ℝ),
        0 < |h| → |h| ≤ R₀ →
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial i)) 2
            ((volume : Measure EuclN).restrict Ω'')
          ≤ ENNReal.ofReal (M_bound i k)) := by
  classical
  obtain ⟨C_geom, hC_geom_nn, hC_geom⟩ :=
    chartBilinearH1Compl_uniform_diffQuot_bound_of_data_quantitative
      (I := I) (M := M) (E := E) (H := H) (g := g) (α := α)
      hη hη_supp hη_range hN h_fderiv_eta hΩ' hΩ'_chart hΩ'_compact
      hη_in_Ω' hR₀_pos hh_supp_in_Ω' hη_one_on_Ω'' hΩ''_meas
  refine ⟨fun i k => C_geom i k * Real.sqrt (
      (∑ l : Fin (Module.finrank ℝ E),
        (eLpNorm (D.weak_partial l) 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
      + (eLpNorm D.u_chart 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2
      + (eLpNorm D.f_chart 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2),
    fun i k => mul_nonneg (hC_geom_nn i k) (Real.sqrt_nonneg _),
    fun i k h hpos hle => hC_geom D hpos hle⟩

end ChartBilinearUniformDiffQuotBoundCanonical

end Laplacian
end Analysis
end DifferentialGeometry
