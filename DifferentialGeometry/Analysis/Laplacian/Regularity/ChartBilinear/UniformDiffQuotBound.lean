import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartBilinear.H1Compl_H1_0
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartHk.H2NonSmooth
import DifferentialGeometry.Analysis.Laplacian.MetricExtension
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.CrossBoundsNonSmooth_Master
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.StandardNirenbergTest
import DifferentialGeometry.Analysis.Sobolev.Tools.DiffQuotFKNonSmooth

/-!
# Uniform-in-`h` `L²` bound on the difference quotient of the chart-pulled
weak partial derivatives, packaged for `h2_chart_loc_of_uniform_bound`

For a non-smooth chart-bilinear data structure `D` and a precompact
`Ω''` whose `h₀`-thickening lies inside the chart-target image, this
module produces the uniform-in-`h` `L²(Ω'')` bound

  `‖D_h^k (g_g i)‖_{L²(Ω'')} ≤ M_bound i k`

for `0 < |h| ≤ 1`, where `g_g i` is a globally `L²` representative of
`D.weak_partial i` (agreeing on a neighbourhood of `closure Ω''`).
This bound is exactly the input shape consumed by
`h2_chart_loc_of_uniform_bound` to extract weak second partial
derivatives.

## Strategy

The wrapper packages the localised non-smooth absorbing inequality
`nirenberg_diffQuot_g_localL2_bound`. The key conversion is from the
sum-form bound

  `(λ/2) · ∫_{Ω''} ∑_i (D_h^k g_i)² ≤ C · (G + U + F)`

to per-`(i, k)` `eLpNorm` bounds. Since each summand
`(D_h^k g_i)² ≥ 0`, the sum dominates each term. Using the equivalence
`(eLpNorm w 2 μ)² = ∫⁻ ‖w‖² ∂μ` and the relation
`(ENNReal.ofReal S)^(1/2) = ENNReal.ofReal (Real.sqrt S)` for
`S ≥ 0`, the per-`(i, k)` `eLpNorm` bound follows.

## Inputs

The headline accepts the master inequality, the per-component
Fréchet–Kolmogorov bound on the difference quotient of the explicit
weak partials, the FK bound on `u`, and the L² bound on the standard
Nirenberg test function as additional hypotheses, alongside the chart-
bilinear data structure `D` and a smooth elliptic bilinear form `B`.
These hypotheses bundle the non-smooth analogues of the absorbing-
master ingredients required by `nirenberg_diffQuot_g_localL2_bound`.
Downstream callers in possession of the substitution identity for
non-smooth weak solutions discharge these hypotheses by mollification.

## Main results

* `chartBilinearH1Compl_uniform_diffQuot_bound`: the uniform-in-`h`
  per-`(i, k)` `eLpNorm` bound on `D_h^k (g_g i)` over `Ω''`, with an
  existential bound `M_bound i k`.
* `chartBilinearH1Compl_uniform_diffQuot_bound_quantitative`: the
  explicit-constant sibling, whose bound is the literal closed-form
  `√((2 / λ) · C · G_total)` with `C` the explicit master constant
  `nirenbergMasterYoungConstant B N hΩ'_compact k`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartBilinearUniformDiffQuotBound

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
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- Pointwise: `f i x ^ 2 ≤ ∑_l f l x ^ 2`. -/
private lemma sq_le_finset_sum_sq
    {n : ℕ} {α : Type*} (f : Fin n → α → ℝ) (i : Fin n) (x : α) :
    (f i x)^2 ≤ ∑ l : Fin n, (f l x)^2 :=
  Finset.single_le_sum (f := fun l => (f l x)^2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

/-- The square of `eLpNorm f 2 μ` equals `∫⁻ ‖f x‖² ∂μ`. Mirrors a
private helper of the same name in `DiffQuotFKNonSmooth`. -/
private lemma sq_eLpNorm_two_eq_lintegral_enorm_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
  classical
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) h2_ne_zero h2_ne_top]
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  rw [h2_toReal]
  have h_inner_eq : ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
      ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards with x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rw [h_inner_eq]
  rw [← ENNReal.rpow_natCast _ 2]
  rw [← ENNReal.rpow_mul]
  norm_num

/-- For a nonnegative integrable real-valued function `g`, the lintegral
of `ENNReal.ofReal g` equals `ENNReal.ofReal (∫ g)`. -/
private lemma lintegral_ofReal_eq_ofReal_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℝ} (hg_int : Integrable g μ) (hg_nn : 0 ≤ᵐ[μ] g) :
    ∫⁻ x, ENNReal.ofReal (g x) ∂μ = ENNReal.ofReal (∫ x, g x ∂μ) := by
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg_int hg_nn]

/-- Conversion: if `∫ ∑_l (f l x)² ∂μ ≤ S` (with the sum integrable),
then for each fixed `i`, `(eLpNorm (f i) 2 μ)² ≤ ENNReal.ofReal S`. -/
private lemma sq_eLpNorm_two_le_of_integral_sum_sq_le
    {n : ℕ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Fin n → α → ℝ)
    (h_sum_int : Integrable (fun x => ∑ l : Fin n, (f l x)^2) μ)
    (i : Fin n) {S : ℝ}
    (h_sum_le : ∫ x, ∑ l : Fin n, (f l x)^2 ∂μ ≤ S) :
    (eLpNorm (f i) 2 μ)^ 2 ≤ ENNReal.ofReal S := by
  classical
  have h_sum_nn : 0 ≤ᵐ[μ] (fun x => ∑ l : Fin n, (f l x)^2) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    exact Finset.sum_nonneg (fun l _ => sq_nonneg _)
  have h_pt : ∀ x : α,
      (‖f i x‖ₑ : ℝ≥0∞)^ 2 ≤
        ENNReal.ofReal (∑ l : Fin n, (f l x)^2) := by
    intro x
    have h_lhs_eq :
        (‖f i x‖ₑ : ℝ≥0∞)^ 2 = ENNReal.ofReal ((f i x)^2) := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]
    rw [h_lhs_eq]
    exact ENNReal.ofReal_le_ofReal (sq_le_finset_sum_sq f i x)
  have h_lint_le :
      ∫⁻ x, (‖f i x‖ₑ : ℝ≥0∞)^ 2 ∂μ ≤
        ∫⁻ x, ENNReal.ofReal (∑ l : Fin n, (f l x)^2) ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards with x using h_pt x
  have h_sum_int_eq :
      ∫⁻ x, ENNReal.ofReal (∑ l : Fin n, (f l x)^2) ∂μ =
        ENNReal.ofReal (∫ x, ∑ l : Fin n, (f l x)^2 ∂μ) :=
    lintegral_ofReal_eq_ofReal_integral h_sum_int h_sum_nn
  rw [sq_eLpNorm_two_eq_lintegral_enorm_sq μ (f i)]
  refine h_lint_le.trans ?_
  rw [h_sum_int_eq]
  exact ENNReal.ofReal_le_ofReal h_sum_le

/-- If `x^2 ≤ y` in `ℝ≥0∞`, then `x ≤ y^(1/2)`. -/
private lemma le_sqrt_of_sq_le {x y : ℝ≥0∞} (h : x^ 2 ≤ y) :
    x ≤ y ^ ((1 : ℝ) / 2) := by
  have h_xpow : x = (x^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← ENNReal.rpow_natCast x 2]
    rw [← ENNReal.rpow_mul]
    norm_num
  conv_lhs => rw [h_xpow]
  exact ENNReal.rpow_le_rpow h (by norm_num)

/-- For `S ≥ 0`, `(ENNReal.ofReal S)^(1/2) = ENNReal.ofReal (Real.sqrt S)`. -/
private lemma sqrt_ofReal_eq_ofReal_sqrt {S : ℝ} (hS : 0 ≤ S) :
    (ENNReal.ofReal S) ^ ((1 : ℝ) / 2) = ENNReal.ofReal (Real.sqrt S) := by
  rw [show S = Real.sqrt S * Real.sqrt S from (Real.mul_self_sqrt hS).symm]
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  rw [show (ENNReal.ofReal (Real.sqrt S)) * (ENNReal.ofReal (Real.sqrt S)) =
    (ENNReal.ofReal (Real.sqrt S))^ 2 from by ring]
  rw [← ENNReal.rpow_natCast _ 2]
  rw [← ENNReal.rpow_mul]
  norm_num

/-- From `(eLpNorm f 2 μ)^2 ≤ ENNReal.ofReal S` (with `S ≥ 0`), deduce
`eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt S)`. -/
private lemma eLpNorm_two_le_ofReal_sqrt
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    {S : ℝ} (hS : 0 ≤ S)
    (h_sq : (eLpNorm f 2 μ)^ 2 ≤ ENNReal.ofReal S) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt S) := by
  have h_pow := le_sqrt_of_sq_le h_sq
  rw [sqrt_ofReal_eq_ofReal_sqrt hS] at h_pow
  exact h_pow

/-- **Uniform-in-`h` per-`(i, k)` `L²(Ω'')` bound on the difference
quotient of the chart-pulled weak partial derivatives.**

The headline integrates the localised non-smooth absorbing inequality
`nirenberg_diffQuot_g_localL2_bound` with a sum-to-component shape
conversion. The output is exactly the uniform-in-`h` bound consumed
by `h2_chart_loc_of_uniform_bound` to extract weak second partial
derivatives.

### Inputs

* `D` — the chart-bilinear data structure.
* `Ω'', η, Ω', N, B, u_g, f_g, g_g` — the standard non-smooth
  Nirenberg setup: the precompact target, the smooth bump (≡ 1 on
  `Ω''`), the slightly larger precompact `Ω'` containing
  `tsupport η`, the bump-derivative bound `N`, the smooth elliptic
  bilinear form `B` (whose principal coefficient agrees with the
  chart-pulled `weightedInvGramOnEuclid g α` on a neighbourhood of
  `closure Ω''`, taken on the global Euclidean space via the
  metric-extension construction), and the global `L²` extensions
  `u_g, f_g, g_g i` of `D.u_chart, D.f_chart, D.weak_partial i`.
* `h_FK_diffQuot_u_bound, h_v_test_sq_bound, h_master_nonsmooth` — the
  three non-smooth analogues of the smooth ingredients of the master
  inequality. These are discharged downstream by mollification + the
  substitution identity for weak solutions.

### Output

A constant `M_bound i k ≥ 0` such that, for every `0 < |h| ≤ 1` and
every `(i, k)`:

  `‖D_h^k (g_g i)‖_{L²(Ω'')} ≤ ENNReal.ofReal (M_bound i k)`.

The bound is uniform in `h`. -/
theorem chartBilinearH1Compl_uniform_diffQuot_bound
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (_D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (B : SmoothEllipticBilinearForm
      (Module.finrank ℝ E) (Set.univ : Set EuclN))
    {u_g f_g : EuclN → ℝ}
    (hu_g_l2 : MemLp u_g 2 (volume : Measure EuclN))
    (hf_g_l2_loc : ∀ {Ω' : Set EuclN}, IsCompact (closure Ω') →
      MemLp f_g 2 ((volume : Measure EuclN).restrict Ω'))
    {g_g : Fin (Module.finrank ℝ E) → EuclN → ℝ}
    (hg_g_l2 : ∀ i, MemLp (g_g i) 2 (volume : Measure EuclN))
    (h_weakPartial_g_g :
      ∀ i, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (g_g i) u_g Set.univ)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : EuclN, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' Ω'' : Set EuclN} (hΩ' : IsOpen Ω')
    (hΩ'_closure : closure Ω' ⊆ (Set.univ : Set EuclN))
    (hΩ'_compact : IsCompact (closure Ω'))
    (hη_in_Ω' : tsupport η ⊆ Ω')
    {R₀ : ℝ}
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (hη_one_on_Ω'' : ∀ x ∈ Ω'', η x = 1)
    (hΩ''_meas : MeasurableSet Ω'')
    (h_FK_diffQuot_u_bound :
      ∀ (k : Fin (Module.finrank ℝ E)),
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
        ∫ x in tsupport η,
            (DifferentialGeometry.Analysis.Sobolev.diffQuot k h u_g x)^2
          ∂(volume : Measure EuclN) ≤
          ∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E), ((g_g l) x) ^ 2
            ∂(volume : Measure EuclN))
    (h_v_test_sq_bound :
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
            ∂(volume : Measure EuclN))
    (h_master_nonsmooth :
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
              k h η u_g x ∂(volume : Measure EuclN)|) :
    ∃ M_bound : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ,
      (∀ i k, 0 ≤ M_bound i k) ∧
      (∀ (i k : Fin (Module.finrank ℝ E)) (h : ℝ),
        0 < |h| → |h| ≤ R₀ →
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (g_g i)) 2
            ((volume : Measure EuclN).restrict Ω'')
          ≤ ENNReal.ofReal (M_bound i k)) := by
  classical
  have h_per_k :
      ∀ (k : Fin (Module.finrank ℝ E)),
      ∃ C_k : ℝ, 0 ≤ C_k ∧ ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
        (B.lam / 2) * ∫ x in Ω'',
            ∑ l : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g_g l) x ^ 2
          ∂(volume : Measure EuclN) ≤
          C_k * (∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E), ((g_g l) x) ^ 2
                  ∂(volume : Measure EuclN) +
              ∫ x in Ω', (u_g x)^2 ∂(volume : Measure EuclN) +
              ∫ x in Ω', (f_g x)^2 ∂(volume : Measure EuclN)) := by
    intro k
    exact nirenberg_diffQuot_g_localL2_bound (d := Module.finrank ℝ E)
      B hu_g_l2 hf_g_l2_loc hg_g_l2 h_weakPartial_g_g
      hη hη_supp hη_range hN h_fderiv_eta hΩ' hΩ'_closure hΩ'_compact
      hη_in_Ω' hh_supp_in_Ω' hη_one_on_Ω'' hΩ''_meas k
      (h_FK_diffQuot_u_bound k)
      (h_v_test_sq_bound k)
      (h_master_nonsmooth k)
  set G_total : ℝ :=
    (∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E), ((g_g l) x) ^ 2
      ∂(volume : Measure EuclN) +
      ∫ x in Ω', (u_g x)^2 ∂(volume : Measure EuclN) +
      ∫ x in Ω', (f_g x)^2 ∂(volume : Measure EuclN)) with hG_total_def
  have hG_total_nn : 0 ≤ G_total := by
    rw [hG_total_def]
    refine add_nonneg (add_nonneg ?_ ?_) ?_
    · refine integral_nonneg ?_
      intro x
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    · refine integral_nonneg ?_
      intro x; exact sq_nonneg _
    · refine integral_nonneg ?_
      intro x; exact sq_nonneg _
  have hlam_pos : 0 < B.lam := B.hlam_pos
  have hlam_half_pos : 0 < B.lam / 2 := by linarith
  let CkChoice : Fin (Module.finrank ℝ E) → ℝ := fun k => Classical.choose (h_per_k k)
  have CkChoice_spec : ∀ k, 0 ≤ CkChoice k ∧
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
        (B.lam / 2) * ∫ x in Ω'',
            ∑ l : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g_g l) x ^ 2
          ∂(volume : Measure EuclN) ≤
          CkChoice k * G_total := fun k => Classical.choose_spec (h_per_k k)
  set M_bound : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun _ k => Real.sqrt ((2 / B.lam) * CkChoice k * G_total) with hM_bound_def
  refine ⟨M_bound, ?_, ?_⟩
  · intro i k
    rw [hM_bound_def]
    exact Real.sqrt_nonneg _
  · intro i k h hh hh_le
    have habs_pos : 0 < |h| := hh
    have hh_ne : h ≠ 0 := abs_ne_zero.mp (ne_of_gt habs_pos)
    have hk_spec := (CkChoice_spec k).2 hh_ne hh_le
    set sumInt : ℝ :=
      ∫ x in Ω'',
        ∑ l : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g_g l) x ^ 2
        ∂(volume : Measure EuclN) with hsumInt_def
    set S : ℝ := (2 / B.lam) * CkChoice k * G_total with hS_def
    have hS_nn : 0 ≤ S := by
      rw [hS_def]
      refine mul_nonneg (mul_nonneg ?_ (CkChoice_spec k).1) hG_total_nn
      have : (0 : ℝ) ≤ 2 := by norm_num
      exact div_nonneg this hlam_pos.le
    have h_sumInt_le_S : sumInt ≤ S := by
      have h_factor : (2 / B.lam) > 0 := by positivity
      have h_step2 : sumInt = (2 / B.lam) * ((B.lam / 2) * sumInt) := by
        rw [← mul_assoc]
        rw [show (2 / B.lam) * (B.lam / 2) = 1 from by field_simp]
        rw [one_mul]
      rw [h_step2, hS_def]
      have h_rhs_eq : (2 / B.lam) * CkChoice k * G_total =
          (2 / B.lam) * (CkChoice k * G_total) := by ring
      rw [h_rhs_eq]
      exact mul_le_mul_of_nonneg_left hk_spec h_factor.le
    have h_per_l_int :
        ∀ l : Fin (Module.finrank ℝ E),
          Integrable
            (fun x => (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (g_g l) x)^2)
            ((volume : Measure EuclN).restrict Ω'') := by
      intro l
      have h_dq_l2_global :
          MemLp
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (g_g l)) 2
            (volume : Measure EuclN) :=
        memLp_diffQuot_two (d := Module.finrank ℝ E) k h (hg_g_l2 l)
      have h_dq_l2_restrict :
          MemLp
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (g_g l)) 2
            ((volume : Measure EuclN).restrict Ω'') :=
        h_dq_l2_global.restrict _
      exact h_dq_l2_restrict.integrable_sq
    have h_sum_int :
        Integrable
          (fun x => ∑ l : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (g_g l) x)^2)
          ((volume : Measure EuclN).restrict Ω'') := by
      have h_aux := integrable_finset_sum
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l _ => h_per_l_int l)
      have h_eq :
          (fun x : EuclN => ∑ l : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (g_g l) x)^2) =
          (fun x : EuclN => ∑ l ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
            (fun y => (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (g_g l) y)^2) x) := by
        funext x; rfl
      rw [h_eq]; exact h_aux
    have h_per_i_sq :
        (eLpNorm (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (g_g i)) 2
          ((volume : Measure EuclN).restrict Ω''))^ 2 ≤
          ENNReal.ofReal S := by
      refine sq_eLpNorm_two_le_of_integral_sum_sq_le
        (n := Module.finrank ℝ E)
        (μ := (volume : Measure EuclN).restrict Ω'')
        (fun l => DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (g_g l)) h_sum_int i ?_
      exact h_sumInt_le_S
    have h_concl :
        eLpNorm (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (g_g i)) 2
          ((volume : Measure EuclN).restrict Ω'') ≤
          ENNReal.ofReal (Real.sqrt S) :=
      eLpNorm_two_le_ofReal_sqrt hS_nn h_per_i_sq
    have hM_eq : M_bound i k = Real.sqrt S := by rw [hM_bound_def, hS_def]
    rw [hM_eq]
    exact h_concl

/-- **Quantitative uniform-in-`h` per-`(i, k)` `L²(Ω'')` bound on the
difference quotient of the chart-pulled weak partial derivatives.**

The explicit-constant form of `chartBilinearH1Compl_uniform_diffQuot_bound`.
It integrates the *quantitative* localised non-smooth absorbing inequality
`nirenberg_diffQuot_g_localL2_bound_quantitative` with the same
sum-to-component shape conversion. In contrast with the existential
sibling, the bound is exposed as the literal closed-form expression

  `‖D_h^k (g_g i)‖_{L²(Ω'')} ≤
    ENNReal.ofReal (√((2 / B.lam) · C · G_total))`,

with `C = nirenbergMasterYoungConstant B N hΩ'_compact k` the explicit
master constant and `G_total = ∫_{Ω'} ∑_l g_l² + ∫_{Ω'} u² + ∫_{Ω'} f²`
the energy quantity. The bound is uniform in `h` (for `0 < |h| ≤ R₀`).

### Inputs

Byte-identical to `chartBilinearH1Compl_uniform_diffQuot_bound`.

### Output

For every `0 < |h| ≤ R₀` and every `(i, k)`, the per-component `eLpNorm`
bound on `D_h^k (g_g i)` over `Ω''` with the explicit constant in place. -/
theorem chartBilinearH1Compl_uniform_diffQuot_bound_quantitative
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (_D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (B : SmoothEllipticBilinearForm
      (Module.finrank ℝ E) (Set.univ : Set EuclN))
    {u_g f_g : EuclN → ℝ}
    (hu_g_l2 : MemLp u_g 2 (volume : Measure EuclN))
    (hf_g_l2_loc : ∀ {Ω' : Set EuclN}, IsCompact (closure Ω') →
      MemLp f_g 2 ((volume : Measure EuclN).restrict Ω'))
    {g_g : Fin (Module.finrank ℝ E) → EuclN → ℝ}
    (hg_g_l2 : ∀ i, MemLp (g_g i) 2 (volume : Measure EuclN))
    (h_weakPartial_g_g :
      ∀ i, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (g_g i) u_g Set.univ)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : EuclN, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' Ω'' : Set EuclN} (hΩ' : IsOpen Ω')
    (hΩ'_closure : closure Ω' ⊆ (Set.univ : Set EuclN))
    (hΩ'_compact : IsCompact (closure Ω'))
    (hη_in_Ω' : tsupport η ⊆ Ω')
    {R₀ : ℝ}
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (hη_one_on_Ω'' : ∀ x ∈ Ω'', η x = 1)
    (hΩ''_meas : MeasurableSet Ω'')
    (h_FK_diffQuot_u_bound :
      ∀ (k : Fin (Module.finrank ℝ E)),
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
        ∫ x in tsupport η,
            (DifferentialGeometry.Analysis.Sobolev.diffQuot k h u_g x)^2
          ∂(volume : Measure EuclN) ≤
          ∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E), ((g_g l) x) ^ 2
            ∂(volume : Measure EuclN))
    (h_v_test_sq_bound :
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
            ∂(volume : Measure EuclN))
    (h_master_nonsmooth :
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
              k h η u_g x ∂(volume : Measure EuclN)|) :
    ∀ ⦃i k : Fin (Module.finrank ℝ E)⦄ ⦃h : ℝ⦄,
      0 < |h| → |h| ≤ R₀ →
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (g_g i)) 2
          ((volume : Measure EuclN).restrict Ω'')
        ≤ ENNReal.ofReal (Real.sqrt ((2 / B.lam) *
            nirenbergMasterYoungConstant B N hΩ'_compact k *
            (∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E), ((g_g l) x) ^ 2
                ∂(volume : Measure EuclN) +
              ∫ x in Ω', (u_g x)^2 ∂(volume : Measure EuclN) +
              ∫ x in Ω', (f_g x)^2 ∂(volume : Measure EuclN)))) := by
  classical
  intro i k h hh hh_le
  have habs_pos : 0 < |h| := hh
  have hh_ne : h ≠ 0 := abs_ne_zero.mp (ne_of_gt habs_pos)
  have hk_spec :
      (B.lam / 2) * ∫ x in Ω'',
          ∑ l : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g_g l) x ^ 2
        ∂(volume : Measure EuclN) ≤
        nirenbergMasterYoungConstant B N hΩ'_compact k *
          (∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E), ((g_g l) x) ^ 2
                  ∂(volume : Measure EuclN) +
              ∫ x in Ω', (u_g x)^2 ∂(volume : Measure EuclN) +
              ∫ x in Ω', (f_g x)^2 ∂(volume : Measure EuclN)) :=
    nirenberg_diffQuot_g_localL2_bound_quantitative (d := Module.finrank ℝ E)
      B hu_g_l2 hf_g_l2_loc hg_g_l2 h_weakPartial_g_g
      hη hη_supp hη_range hN h_fderiv_eta hΩ' hΩ'_closure hΩ'_compact
      hη_in_Ω' hh_supp_in_Ω' hη_one_on_Ω'' hΩ''_meas k
      (h_FK_diffQuot_u_bound k)
      (h_v_test_sq_bound k)
      (h_master_nonsmooth k) hh_ne hh_le
  set G_total : ℝ :=
    (∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E), ((g_g l) x) ^ 2
      ∂(volume : Measure EuclN) +
      ∫ x in Ω', (u_g x)^2 ∂(volume : Measure EuclN) +
      ∫ x in Ω', (f_g x)^2 ∂(volume : Measure EuclN)) with hG_total_def
  have hG_total_nn : 0 ≤ G_total := by
    rw [hG_total_def]
    refine add_nonneg (add_nonneg ?_ ?_) ?_
    · refine integral_nonneg ?_
      intro x
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    · refine integral_nonneg ?_
      intro x; exact sq_nonneg _
    · refine integral_nonneg ?_
      intro x; exact sq_nonneg _
  have hlam_pos : 0 < B.lam := B.hlam_pos
  have hlam_half_pos : 0 < B.lam / 2 := by linarith
  have hC_nn : 0 ≤ nirenbergMasterYoungConstant B N hΩ'_compact k :=
    nirenbergMasterYoungConstant_nonneg B hN hΩ'_compact k
  set sumInt : ℝ :=
    ∫ x in Ω'',
      ∑ l : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g_g l) x ^ 2
      ∂(volume : Measure EuclN) with hsumInt_def
  set S : ℝ :=
    (2 / B.lam) * nirenbergMasterYoungConstant B N hΩ'_compact k * G_total
    with hS_def
  have hS_nn : 0 ≤ S := by
    rw [hS_def]
    refine mul_nonneg (mul_nonneg ?_ hC_nn) hG_total_nn
    have : (0 : ℝ) ≤ 2 := by norm_num
    exact div_nonneg this hlam_pos.le
  have h_sumInt_le_S : sumInt ≤ S := by
    have h_factor : (2 / B.lam) > 0 := by positivity
    have h_step2 : sumInt = (2 / B.lam) * ((B.lam / 2) * sumInt) := by
      rw [← mul_assoc]
      rw [show (2 / B.lam) * (B.lam / 2) = 1 from by field_simp]
      rw [one_mul]
    rw [h_step2, hS_def]
    have h_rhs_eq :
        (2 / B.lam) * nirenbergMasterYoungConstant B N hΩ'_compact k * G_total =
          (2 / B.lam) *
            (nirenbergMasterYoungConstant B N hΩ'_compact k * G_total) := by
      ring
    rw [h_rhs_eq]
    exact mul_le_mul_of_nonneg_left hk_spec h_factor.le
  have h_per_l_int :
      ∀ l : Fin (Module.finrank ℝ E),
        Integrable
          (fun x => (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (g_g l) x)^2)
          ((volume : Measure EuclN).restrict Ω'') := by
    intro l
    have h_dq_l2_global :
        MemLp
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (g_g l)) 2
          (volume : Measure EuclN) :=
      memLp_diffQuot_two (d := Module.finrank ℝ E) k h (hg_g_l2 l)
    have h_dq_l2_restrict :
        MemLp
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (g_g l)) 2
          ((volume : Measure EuclN).restrict Ω'') :=
      h_dq_l2_global.restrict _
    exact h_dq_l2_restrict.integrable_sq
  have h_sum_int :
      Integrable
        (fun x => ∑ l : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (g_g l) x)^2)
        ((volume : Measure EuclN).restrict Ω'') := by
    have h_aux := integrable_finset_sum
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l _ => h_per_l_int l)
    have h_eq :
        (fun x : EuclN => ∑ l : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (g_g l) x)^2) =
        (fun x : EuclN => ∑ l ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
          (fun y => (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (g_g l) y)^2) x) := by
      funext x; rfl
    rw [h_eq]; exact h_aux
  have h_per_i_sq :
      (eLpNorm (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (g_g i)) 2
        ((volume : Measure EuclN).restrict Ω''))^ 2 ≤
        ENNReal.ofReal S := by
    refine sq_eLpNorm_two_le_of_integral_sum_sq_le
      (n := Module.finrank ℝ E)
      (μ := (volume : Measure EuclN).restrict Ω'')
      (fun l => DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (g_g l)) h_sum_int i ?_
    exact h_sumInt_le_S
  exact eLpNorm_two_le_ofReal_sqrt hS_nn h_per_i_sq

end ChartBilinearUniformDiffQuotBound

end Laplacian
end Analysis
end DifferentialGeometry
