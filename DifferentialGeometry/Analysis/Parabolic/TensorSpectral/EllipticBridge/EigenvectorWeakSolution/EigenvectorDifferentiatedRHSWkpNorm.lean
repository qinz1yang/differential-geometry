import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorDifferentiatedRHSEpNorm
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorIteratedData
import DifferentialGeometry.Analysis.Sobolev.Euclidean.MultiplyQuantK
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevQuant

/-!
# `K`-graded explicit-norm `wkpNorm` bound for the differentiated chart-RHS numerator

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, and a component multi-index `P₀`, the level-`(m+1)`
differentiated chart-RHS numerator `eigenvectorChartRHSDiffNumerator` is the
explicit five-layer Leibniz combination `A + B − C + D + E` produced by one more
integration by parts in the new direction `lₙ := l (Fin.last m)`.

The order-`0` companion `eigenvectorChartRHSDiffNumerator_eLpNorm_le` records the
quantitative `eLpNorm`-bound — the `wkpNorm`-bound at Sobolev order `0` — for the
numerator against `volume.restrict (chartPouKernel α)`. This file records its
order-`K` generalisation: there is a nonnegative constant `C` with

```
wkpNorm K 2 (eigenvectorChartRHSDiffNumerator … m l fChartEffPrev)
    (chartTargetEuclid α)
  ≤ ENNReal.ofReal C * <AGGREGATE_K>,
```

where `<AGGREGATE_K>` is `diffNumeratorAggregateK`, the order-`K` analogue of the
order-`0` `diffNumeratorAggregate`: the honest finite sum

* `∑ₐ wkpNorm (2 + K) 2 (eigenvectorChartIteratedPartial … (m+1) (Fin.cons a
  (Fin.init l))) (chartTargetEuclid α)` — the iterated weak partials feeding
  layers `A`, `B`;
* `wkpNorm (2 + K) 2 (eigenvectorChartIteratedPartial … m (Fin.init l))
  (chartTargetEuclid α)` — the iterated weak partial feeding layer `C`;
* `wkpNorm (K + 1) 2 fChartEffPrev (chartTargetEuclid α)` — controlling layer
  `E` via the chosen weak partial;
* `wkpNorm K 2 fChartEffPrev (chartTargetEuclid α)` — controlling layer `D`.

## Strategy

`eigenvectorChartRHSDiffNumerator` is a five-layer `+`/`-` combination; iterated
Minkowski for `wkpNorm` bounds its order-`K` norm by the sum of the five layer
norms. Each layer is a finite sum of `(smooth coefficient) · atom` summands,
aggregated via `wkpNorm_sum_le`. Per summand the order-`K` smooth-coefficient
bound `wkpNorm_coef_mul_factor_le` — the quantitative companion of the
qualitative `memWkp_coef_mul_factor` — gives `wkpNorm K 2 (coef · atom) Ω ≤
ENNReal.ofReal Cᵢ * wkpNorm K 2 atom Ω`; it cuts the chart-target-smooth
coefficient off into a globally smooth compactly supported representative,
uniformly bounds its iterated derivatives up to order `K`, applies the
global-smoothness Leibniz bound `wkpNorm_smul_smooth_bounded_le`, and transfers
back through the ae-vanishing of the atom off the kernel. The atom norm is then
bounded by the aggregate: an iterated weak partial directly (`wkpNorm K 2 ≤
wkpNorm (2 + K) 2`); a chosen weak partial of one by
`wkpNorm_chosenWeakPartial_le` (dropping one order, `wkpNorm (K + 1) 2 ≤ wkpNorm
(2 + K) 2`); `fChartEffPrev` directly; and its chosen weak partial via
`wkpNorm_chosenWeakPartial_le` (`wkpNorm (K + 1) 2 fChartEffPrev`). All
per-summand constants and finite-sum multiplicities fold into a single
nonnegative `C`.

## Main result

* `eigenvectorChartRHSDiffNumerator_wkpNorm_le` — the `K`-graded explicit-norm
  `wkpNorm` bound for the differentiated chart-RHS numerator.

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

/-! ## The order-`K` differentiated-numerator aggregate

`diffNumeratorAggregateK` packages the honest finite sum of order-`K` source
norms controlling the differentiated chart-RHS numerator. It is the order-`K`
analogue of the order-`0` `diffNumeratorAggregate`: it aggregates the
`wkpNorm (2 + K) 2` of the `(m+1)`-fold iterated weak partials feeding layers
`A`, `B`; the `wkpNorm (2 + K) 2` of the `m`-fold iterated weak partial feeding
layer `C`; the `wkpNorm (K + 1) 2` of `fChartEffPrev` controlling layer `E`; and
the `wkpNorm K 2` of `fChartEffPrev` controlling layer `D`. -/

/-- The finite aggregate of order-`K` source norms controlling the differentiated
chart-RHS numerator: the `wkpNorm (2 + K) 2` of the iterated weak partials
feeding layers `A`, `B`, `C`, together with the `wkpNorm (K + 1) 2` and the
`wkpNorm K 2` of the previous-level right-hand side `fChartEffPrev`, all on the
open chart target.

This is the order-`K` analogue of the order-`0` `diffNumeratorAggregate`; it is
**data** — an `ℝ≥0∞`-valued quantity, not a `Prop`. -/
def diffNumeratorAggregateK
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ) : ℝ≥0∞ :=
  (∑ a : Fin (Module.finrank ℝ E),
      wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α))
    + wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ m (Fin.init l))
        (chartTargetEuclid (I := I) (M := M) α)
    + wkpNorm (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
        (chartTargetEuclid (I := I) (M := M) α)
    + wkpNorm (d := Module.finrank ℝ E) K 2 fChartEffPrev
        (chartTargetEuclid (I := I) (M := M) α)

/-! ## The quantitative smooth-coefficient `wkpNorm` bound with ae-vanishing

The workhorse. Given a coefficient smooth on the open chart target, a factor in
`MemWkp K 2` on the chart target that ae-vanishes off the compact
partition-of-unity kernel, the product `coef · factor` lies in `MemWkp K 2` on
the chart target and its order-`K` Sobolev norm is bounded by an explicit
constant times the order-`K` norm of the factor.

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

/-! ## Finite-sum closure for `MemWkp K 2`

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

/-! ## A finite-sum aggregation lemma

A finite indexed family of `MemWkp K 2` summands, each `wkpNorm`-bounded by
`ENNReal.ofReal Cⱼ` times one *fixed* aggregate quantity `A`, has its summed
`wkpNorm` bounded by `ENNReal.ofReal` of an explicit nonnegative constant times
`A`. The explicit constant is the sum of the per-summand constants times the
cardinality of the index type; the triangle inequality `wkpNorm_sum_le` and the
monotonicity of `ENNReal.ofReal` assemble it. -/

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma wkpNorm_sum_le_const_mul_aggregate
    {α : M} {K : ℕ} {ι : Type*} [Fintype ι] (F : ι → EuclN → ℝ)
    (A : ℝ≥0∞)
    (hF : ∀ j : ι, MemWkp (d := Module.finrank ℝ E) K 2 (F j)
      (chartTargetEuclid (I := I) (M := M) α))
    (hbd : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2 (F j)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C * A) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ j : ι, F j y) (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C * A := by
  classical
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  choose Cf hCf_nn hCf using hbd
  refine ⟨(∑ j : ι, Cf j) * (Fintype.card ι : ℝ),
    mul_nonneg (Finset.sum_nonneg (fun j _ => hCf_nn j)) (by positivity), ?_⟩
  -- Triangle inequality over the finite sum.
  have h_tri : wkpNorm (d := Module.finrank ℝ E) K 2
      (fun y => ∑ j : ι, F j y) (chartTargetEuclid (I := I) (M := M) α)
      ≤ ∑ j : ι, wkpNorm (d := Module.finrank ℝ E) K 2 (F j)
          (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_sum_le (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open Finset.univ F
      (fun j _ => hF j)
  -- Each summand norm is `≤ ENNReal.ofReal (∑ Cf) * A`.
  have h_step : ∑ j : ι, wkpNorm (d := Module.finrank ℝ E) K 2 (F j)
        (chartTargetEuclid (I := I) (M := M) α)
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
    wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ j : ι, F j y) (chartTargetEuclid (I := I) (M := M) α)
        ≤ ∑ j : ι, wkpNorm (d := Module.finrank ℝ E) K 2 (F j)
            (chartTargetEuclid (I := I) (M := M) α) := h_tri
    _ ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A := h_step
    _ = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A) := h_const
    _ = ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)) * A := by
        rw [mul_assoc]
    _ = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) * A := by
        rw [h_cast]

/-! ## The triangle inequality for `wkpNorm` under subtraction

The iterated-Sobolev API ships the triangle inequality `wkpNorm_add_le` for
addition; the subtraction analogue is recorded here. The order-`K` norm is
invariant under negation (`wkpNorm_const_smul` with `c = -1`, whose `ℝ≥0∞`-norm
is `1`), so `u − v = u + (−v)` and `wkpNorm_add_le` deliver it. -/

private lemma wkpNorm_sub_le
    {d : ℕ} [NeZero d] {k : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) {u v : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemWkp (d := d) k 2 u Ω) (hv : MemWkp (d := d) k 2 v Ω) :
    wkpNorm (d := d) k 2 (fun y => u y - v y) Ω ≤
      wkpNorm (d := d) k 2 u Ω + wkpNorm (d := d) k 2 v Ω := by
  classical
  -- `u − v = u + (−v)`.
  have h_fun : (fun y => u y - v y) = (fun y => u y + (fun y => - v y) y) := by
    funext y; ring
  rw [h_fun]
  have hv_neg : MemWkp (d := d) k 2 (fun y => - v y) Ω :=
    MemWkp.neg (d := d) (by norm_num) hΩ hv
  refine le_trans (wkpNorm_add_le (d := d) (by norm_num) hΩ hu hv_neg) ?_
  -- `wkpNorm k 2 (−v) Ω = wkpNorm k 2 v Ω` via `wkpNorm_const_smul` at `c = -1`.
  have h_neg_eq : wkpNorm (d := d) k 2 (fun y => - v y) Ω =
      wkpNorm (d := d) k 2 v Ω := by
    have h_smul : (fun y => - v y) = (fun y => (-1 : ℝ) * v y) := by
      funext y; ring
    rw [h_smul, wkpNorm_const_smul (d := d) (by norm_num) hΩ hv (-1)]
    simp
  rw [h_neg_eq]

/-! ## Per-atom `wkpNorm` bounds

The iterated weak partials and their chosen weak partials feeding the five layers
have their order-`K` Sobolev norms bounded by sub-aggregates of
`diffNumeratorAggregateK`. Each sub-aggregate is `≤ diffNumeratorAggregateK` (all
summands are nonnegative `ℝ≥0∞` quantities). -/

section AtomBounds

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
  (l : Fin (m + 1) → Fin (Module.finrank ℝ E))

omit [CompleteSpace E] in
/-- The `(m+1)`-fold iterated weak partial atom (feeding layers `A`, `B`) has its
order-`K` Sobolev norm bounded by its order-`(2 + K)` norm — the order-`K` norm
sums over a sub-range of the order-`(2 + K)` norm's orders. -/
private lemma wkpNorm_iteratedPartial_succ_le
    (a : Fin (Module.finrank ℝ E)) :
    wkpNorm (d := Module.finrank ℝ E) K 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) :=
  wkpNorm_mono_order (d := Module.finrank ℝ E) (by omega) _ _

omit [CompleteSpace E] in
/-- The `m`-fold iterated weak partial atom (feeding layer `C`) has its order-`K`
Sobolev norm bounded by its order-`(2 + K)` norm. -/
private lemma wkpNorm_iteratedPartial_le :
    wkpNorm (d := Module.finrank ℝ E) K 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ m (Fin.init l))
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ m (Fin.init l))
          (chartTargetEuclid (I := I) (M := M) α) :=
  wkpNorm_mono_order (d := Module.finrank ℝ E) (by omega) _ _

omit [CompleteSpace E] in
/-- The chosen weak `b`-partial of the `(m+1)`-fold iterated weak partial atom
(feeding layer `B`) has its order-`K` Sobolev norm bounded by the order-`(2 + K)`
norm of the `(m+1)`-fold iterated weak partial. A chosen weak partial drops one
Sobolev order (`wkpNorm_chosenWeakPartial_le`), giving `wkpNorm (K + 1) 2`; the
order monotonicity `wkpNorm (K + 1) 2 ≤ wkpNorm (2 + K) 2` finishes. -/
private lemma wkpNorm_chosenWeakPartial_iteratedPartial_succ_le
    (a b : Fin (Module.finrank ℝ E)) :
    wkpNorm (d := Module.finrank ℝ E) K 2
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) := by
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  refine le_trans (wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E)
    K hΩ_open _ b) ?_
  exact wkpNorm_mono_order (d := Module.finrank ℝ E) (by omega) _ _

end AtomBounds

/-! ## Per-layer `wkpNorm` bounds

Each of the five layers of `eigenvectorChartRHSDiffNumerator` is a finite sum of
`(C^∞ coefficient) · atom` summands; this section bounds the order-`K` Sobolev
norm of every layer — and records its `MemWkp K 2` membership — by an explicit
constant times `diffNumeratorAggregateK`. -/

section LayerBounds

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
  (l : Fin (m + 1) → Fin (Module.finrank ℝ E))

/-! ### The smooth chart-target coefficient feeding layers `A`

Layer `A`'s coefficient is the `∂_b`-evaluation of `weightedInvGramDerivOnEuclid`,
which is `C^∞` on the open chart target. -/

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
/-- The layer-`A` coefficient `∂_b (weightedInvGramDerivOnEuclid g α a b lₙ)` is
`C^∞` on the open chart target. -/
private lemma layerA_coeff_contDiffOn
    (a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_diffOn : ContDiffOn ℝ (⊤ : ℕ∞)
      (weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)))
      (chartTargetEuclid (I := I) (M := M) α) :=
    weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m))
  have h_fderiv : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
          (l (Fin.last m))) y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_diffOn).2
  have h_eval : ContDiff ℝ (⊤ : ℕ∞)
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single b 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single b (1 : ℝ))).contDiff
  exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)

/-! ### Layer A

`A = ∑ₐ ∑_b (∂_b weightedInvGramDerivOnEuclid g α a b lₙ) ·
(eigenvectorChartIteratedPartial … (m+1) (Fin.cons a (Fin.init l)))`. -/

omit [CompleteSpace E] in
/-- **`wkpNorm` bound for layer `A`.** Each summand is the `C^∞` coefficient
`∂_b (weightedInvGramDerivOnEuclid · · ·)` times the `(m+1)`-fold iterated weak
partial; the smooth-coefficient bound `wkpNorm_coef_mul_factor_le` and the
iterated-weak-partial atom bound combine, and the double sum aggregates via
`wkpNorm_sum_le_const_mul_aggregate`. The layer is `MemWkp K 2` on the chart
target. -/
private lemma eigenvectorChartRHSDiffNumerator_layerA_wkpNorm_le
    (fChartEffPrev : EuclN → ℝ)
    (h_iter : ∀ a : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                  (l (Fin.last m))) y)
                (EuclideanSpace.single b 1) *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
        (chartTargetEuclid (I := I) (M := M) α) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E),
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                      (l (Fin.last m))) y)
                    (EuclideanSpace.single b 1) *
                  eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK (I := I) (M := M)
              g r s h_atlas i α P₀ m K l fChartEffPrev := by
  classical
  set A := diffNumeratorAggregateK (I := I) (M := M)
    g r s h_atlas i α P₀ m K l fChartEffPrev with hA_def
  -- Each `(a, b)`-summand: a smooth coefficient times the `(m+1)`-fold iterated
  -- weak partial, which ae-vanishes off the kernel.
  have h_pair : ∀ a b : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) K 2
          (fun y =>
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                  (l (Fin.last m))) y)
                (EuclideanSpace.single b 1) *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
          (chartTargetEuclid (I := I) (M := M) α) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y =>
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                      (l (Fin.last m))) y)
                    (EuclideanSpace.single b 1) *
                  eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C * A := by
    intro a b
    have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α) :=
      (h_iter a).le_of_le (by omega)
    have h_factor_ae_zero :=
      eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))
    obtain ⟨h_mem, C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le
      (I := I) (M := M) α K (layerA_coeff_contDiffOn (I := I) (M := M)
        g α m l a b) h_factor_memWkp h_factor_ae_zero
    refine ⟨h_mem, C₀, hC₀_nn, le_trans hC₀ ?_⟩
    gcongr
    refine le_trans (wkpNorm_iteratedPartial_succ_le
      (I := I) (M := M) g r s h_atlas i α P₀ m K l a) ?_
    rw [hA_def, diffNumeratorAggregateK]
    refine le_trans (Finset.single_le_sum (f := fun a =>
      wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α))
      (fun k _ => zero_le _) (Finset.mem_univ a)) ?_
    exact le_trans le_self_add (le_trans le_self_add le_self_add)
  -- Inner sum over `b`: `MemWkp K 2` of the inner sum, and its `wkpNorm` bound.
  have h_inner : ∀ a : Fin (Module.finrank ℝ E),
      (MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => ∑ b : Fin (Module.finrank ℝ E),
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                  (l (Fin.last m))) y)
                (EuclideanSpace.single b 1) *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
          (chartTargetEuclid (I := I) (M := M) α)) ∧
        _ := fun a =>
    ⟨memWkp_finset_sum (I := I) (M := M)
      (α := α) (K := K) (s := Finset.univ)
      (f := fun b y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      (fun b _ => (h_pair a b).1),
    wkpNorm_sum_le_const_mul_aggregate (I := I) (M := M)
      (α := α) (K := K)
      (fun b y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      A (fun b => (h_pair a b).1) (fun b => (h_pair a b).2)⟩
  exact ⟨memWkp_finset_sum (I := I) (M := M)
    (α := α) (K := K) (s := Finset.univ)
    (f := fun a y => ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
    (fun a _ => (h_inner a).1),
  wkpNorm_sum_le_const_mul_aggregate (I := I) (M := M)
    (α := α) (K := K)
    (fun a y => ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
    A (fun a => (h_inner a).1) (fun a => (h_inner a).2)⟩

/-! ### Layer B

`B = ∑ₐ ∑_b weightedInvGramDerivOnEuclid g α a b lₙ ·
(∂_b-weak-partial of eigenvectorChartIteratedPartial … (m+1) (Fin.cons a
(Fin.init l)))`. -/

omit [CompleteSpace E] in
/-- **`wkpNorm` bound for layer `B`.** Each summand is the `C^∞` coefficient
`weightedInvGramDerivOnEuclid` times the chosen weak `b`-partial of the
`(m+1)`-fold iterated weak partial; the smooth-coefficient bound and the
chosen-weak-partial atom bound combine. The layer is `MemWkp K 2` on the chart
target. -/
private lemma eigenvectorChartRHSDiffNumerator_layerB_wkpNorm_le
    (fChartEffPrev : EuclN → ℝ)
    (h_iter : ∀ a : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α) y)
        (chartTargetEuclid (I := I) (M := M) α) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E),
                weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m)) y *
                  chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                    (eigenvectorChartIteratedPartial (I := I) (M := M)
                      g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                    (chartTargetEuclid (I := I) (M := M) α) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK (I := I) (M := M)
              g r s h_atlas i α P₀ m K l fChartEffPrev := by
  classical
  set A := diffNumeratorAggregateK (I := I) (M := M)
    g r s h_atlas i α P₀ m K l fChartEffPrev with hA_def
  -- Each `(a, b)`-summand: a smooth coefficient times the chosen weak
  -- `b`-partial of the `(m+1)`-fold iterated weak partial.
  have h_pair : ∀ a b : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) K 2
          (fun y =>
            weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α) y)
          (chartTargetEuclid (I := I) (M := M) α) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y =>
                weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m)) y *
                  chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                    (eigenvectorChartIteratedPartial (I := I) (M := M)
                      g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                    (chartTargetEuclid (I := I) (M := M) α) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C * A := by
    intro a b
    -- The level-`(m+1)` mixed partial is `MemWkp (K + 1) 2`.
    have h_inner_memWkp_succ : MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α) :=
      (h_iter a).le_of_le (by omega)
    -- Its chosen weak `b`-partial is `MemWkp K 2`.
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
        (I := I) (M := M) g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l))
    have h_factor_ae_zero :=
      chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
        (I := I) (M := M) α h_inner_ae b
    obtain ⟨h_mem, C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le
      (I := I) (M := M) α K
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m)))
      h_factor_memWkp h_factor_ae_zero
    refine ⟨h_mem, C₀, hC₀_nn, le_trans hC₀ ?_⟩
    gcongr
    refine le_trans (wkpNorm_chosenWeakPartial_iteratedPartial_succ_le
      (I := I) (M := M) g r s h_atlas i α P₀ m K l a b) ?_
    rw [hA_def, diffNumeratorAggregateK]
    refine le_trans (Finset.single_le_sum (f := fun a =>
      wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α))
      (fun k _ => zero_le _) (Finset.mem_univ a)) ?_
    exact le_trans le_self_add (le_trans le_self_add le_self_add)
  -- Inner sum over `b`: `MemWkp K 2` of the inner sum, and its `wkpNorm` bound.
  have h_inner : ∀ a : Fin (Module.finrank ℝ E),
      (MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => ∑ b : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α) y)
          (chartTargetEuclid (I := I) (M := M) α)) ∧
        _ := fun a =>
    ⟨memWkp_finset_sum (I := I) (M := M)
      (α := α) (K := K) (s := Finset.univ)
      (f := fun b y =>
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y)
      (fun b _ => (h_pair a b).1),
    wkpNorm_sum_le_const_mul_aggregate (I := I) (M := M)
      (α := α) (K := K)
      (fun b y =>
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y)
      A (fun b => (h_pair a b).1) (fun b => (h_pair a b).2)⟩
  exact ⟨memWkp_finset_sum (I := I) (M := M)
    (α := α) (K := K) (s := Finset.univ)
    (f := fun a y => ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y)
    (fun a _ => (h_inner a).1),
  wkpNorm_sum_le_const_mul_aggregate (I := I) (M := M)
    (α := α) (K := K)
    (fun a y => ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y)
    A (fun a => (h_inner a).1) (fun a => (h_inner a).2)⟩

/-! ### Layer C

`C = densityDerivOnEuclid g α lₙ · (eigenvectorChartIteratedPartial … m
(Fin.init l))`. -/

omit [CompleteSpace E] in
/-- **`wkpNorm` bound for layer `C`.** The single summand is the `C^∞`
coefficient `densityDerivOnEuclid` times the `m`-fold iterated weak partial; the
smooth-coefficient bound and the iterated-weak-partial atom bound combine. The
layer is `MemWkp K 2` on the chart target. -/
private lemma eigenvectorChartRHSDiffNumerator_layerC_wkpNorm_le
    (fChartEffPrev : EuclN → ℝ)
    (h_iter_m : MemWkp (d := Module.finrank ℝ E) (2 + K) 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ m (Fin.init l))
      (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (fun y =>
          densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ m (Fin.init l) y)
        (chartTargetEuclid (I := I) (M := M) α) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y =>
              densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
                eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s h_atlas i α P₀ m (Fin.init l) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK (I := I) (M := M)
              g r s h_atlas i α P₀ m K l fChartEffPrev := by
  classical
  set A := diffNumeratorAggregateK (I := I) (M := M)
    g r s h_atlas i α P₀ m K l fChartEffPrev with hA_def
  have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ m (Fin.init l))
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_iter_m.le_of_le (by omega)
  have h_factor_ae_zero :=
    eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s h_atlas i α P₀ m (Fin.init l)
  obtain ⟨h_mem, C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le
    (I := I) (M := M) α K
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
    h_factor_memWkp h_factor_ae_zero
  refine ⟨h_mem, C₀, hC₀_nn, le_trans hC₀ ?_⟩
  gcongr
  refine le_trans (wkpNorm_iteratedPartial_le
    (I := I) (M := M) g r s h_atlas i α P₀ m K l) ?_
  rw [hA_def, diffNumeratorAggregateK]
  exact le_trans le_add_self (le_trans le_self_add le_self_add)

/-! ### Layer D

`D = densityDerivOnEuclid g α lₙ · fChartEffPrev`. -/

omit [CompleteSpace E] in
/-- **`wkpNorm` bound for layer `D`.** The single summand is the `C^∞`
coefficient `densityDerivOnEuclid` times `fChartEffPrev`; the smooth-coefficient
bound applies, and `wkpNorm K 2 fChartEffPrev` is a summand of the aggregate. The
layer is `MemWkp K 2` on the chart target. -/
private lemma eigenvectorChartRHSDiffNumerator_layerD_wkpNorm_le
    {fChartEffPrev : EuclN → ℝ}
    (h_prev : MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (fun y =>
          densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
            fChartEffPrev y)
        (chartTargetEuclid (I := I) (M := M) α) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y =>
              densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
                fChartEffPrev y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK (I := I) (M := M)
              g r s h_atlas i α P₀ m K l fChartEffPrev := by
  classical
  set A := diffNumeratorAggregateK (I := I) (M := M)
    g r s h_atlas i α P₀ m K l fChartEffPrev with hA_def
  have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 fChartEffPrev
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_prev.le_of_le (by omega)
  obtain ⟨h_mem, C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le
    (I := I) (M := M) α K
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
    h_factor_memWkp h_prev_zero
  refine ⟨h_mem, C₀, hC₀_nn, le_trans hC₀ ?_⟩
  gcongr
  rw [hA_def, diffNumeratorAggregateK]
  exact le_add_self

/-! ### Layer E

`E = densityOnEuclid g α · (∂_{lₙ}-weak-partial of fChartEffPrev)`. -/

omit [CompleteSpace E] in
/-- **`wkpNorm` bound for layer `E`.** The single summand is the `C^∞`
coefficient `densityOnEuclid` times the chosen weak `lₙ`-partial of
`fChartEffPrev`; the smooth-coefficient bound applies, and the chosen-weak-partial
atom is bounded — `wkpNorm K 2` of a chosen weak partial drops to `wkpNorm
(K + 1) 2 fChartEffPrev`, a summand of the aggregate. The layer is `MemWkp K 2`
on the chart target. -/
private lemma eigenvectorChartRHSDiffNumerator_layerE_wkpNorm_le
    {fChartEffPrev : EuclN → ℝ}
    (h_prev : MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (fun y =>
          densityOnEuclid (I := I) g α y *
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
              fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y)
        (chartTargetEuclid (I := I) (M := M) α) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y =>
              densityOnEuclid (I := I) g α y *
                chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
                  fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK (I := I) (M := M)
              g r s h_atlas i α P₀ m K l fChartEffPrev := by
  classical
  set A := diffNumeratorAggregateK (I := I) (M := M)
    g r s h_atlas i α P₀ m K l fChartEffPrev with hA_def
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The chosen weak `lₙ`-partial of `fChartEffPrev` is `MemWkp K 2`.
  have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        fChartEffPrev (chartTargetEuclid (I := I) (M := M) α))
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_prev.chosenWeakPartial_mem (l (Fin.last m))
  -- The chosen weak `lₙ`-partial ae-vanishes off the kernel.
  have h_factor_ae_zero :=
    chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
      (I := I) (M := M) α h_prev_zero (l (Fin.last m))
  obtain ⟨h_mem, C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le
    (I := I) (M := M) α K
    (densityOnEuclid_contDiffOn (I := I) g α)
    h_factor_memWkp h_factor_ae_zero
  refine ⟨h_mem, C₀, hC₀_nn, le_trans hC₀ ?_⟩
  gcongr
  -- `wkpNorm K 2 (∂_{lₙ} fChartEffPrev) ≤ wkpNorm (K + 1) 2 fChartEffPrev`.
  refine le_trans (wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E)
    K hΩ_open _ (l (Fin.last m))) ?_
  rw [hA_def, diffNumeratorAggregateK]
  exact le_trans le_add_self le_self_add

end LayerBounds

/-! ## The headline `K`-graded explicit-norm `wkpNorm` bound -/

section MainBound

omit [CompleteSpace E] in
/-- **The `K`-graded explicit-norm `wkpNorm` bound for the differentiated
chart-RHS numerator.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, a component multi-index `P₀`, a level `m`, a
regularity order `K`, a direction multi-index `l : Fin (m+1) → Fin n`, and a
previous-level right-hand side `fChartEffPrev : EuclN → ℝ`, there is a
nonnegative constant `C` such that the order-`K` Sobolev norm of the
level-`(m+1)` differentiated chart-RHS numerator
`eigenvectorChartRHSDiffNumerator g r s h_atlas i α P₀ m l fChartEffPrev` on the
open Euclidean chart target `chartTargetEuclid α` is bounded by `ENNReal.ofReal
C` times the finite aggregate `diffNumeratorAggregateK` of the order-`K` source
norms:

* `∑ₐ wkpNorm (2 + K) 2 (eigenvectorChartIteratedPartial … (m+1) (Fin.cons a
  (Fin.init l))) (chartTargetEuclid α)` — the iterated weak partials feeding
  layers `A`, `B`;
* `wkpNorm (2 + K) 2 (eigenvectorChartIteratedPartial … m (Fin.init l))
  (chartTargetEuclid α)` — the iterated weak partial feeding layer `C`;
* `wkpNorm (K + 1) 2 fChartEffPrev (chartTargetEuclid α)` — controlling layer
  `E`;
* `wkpNorm K 2 fChartEffPrev (chartTargetEuclid α)` — controlling layer `D`.

The hypotheses are: every `(m+1)`-fold and `m`-fold iterated weak partial of the
eigenvector chart component appearing in the numerator lies in
`W^{2 + K, 2}(chartTargetEuclid α)` (passed as the genuine regularity hypothesis
`h_iter`); and the previous-level right-hand side `fChartEffPrev` lies in
`W^{K + 1, 2}(chartTargetEuclid α)` (the genuine hypothesis `h_prev`) and
vanishes almost everywhere off the partition-of-unity kernel `chartPouKernel α`
(the genuine support hypothesis `h_prev_zero`).

This is the order-`K` generalisation of the order-`0` `eLpNorm`-bound
`eigenvectorChartRHSDiffNumerator_eLpNorm_le`. `eigenvectorChartRHSDiffNumerator`
is the five-layer `+`/`-` combination `A + B − C + D + E`; iterated Minkowski for
`wkpNorm` (`wkpNorm_add_le` / `wkpNorm_sub_le`) bounds its order-`K` norm by the
sum of the five layer norms. The per-layer bounds — each layer being a finite sum
of a `C^∞`-coefficient product whose atom is an iterated weak partial, a chosen
weak partial thereof, or `fChartEffPrev` (directly or via a chosen weak
partial) — control every layer by an explicit constant times the aggregate; the
five per-layer constants fold into the single nonnegative `C`. -/
theorem eigenvectorChartRHSDiffNumerator_wkpNorm_le
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
          (eigenvectorChartRHSDiffNumerator (I := I) (M := M)
            g r s h_atlas i α P₀ m l fChartEffPrev)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregateK (I := I) (M := M)
            g r s h_atlas i α P₀ m K l fChartEffPrev := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set A := diffNumeratorAggregateK (I := I) (M := M)
    g r s h_atlas i α P₀ m K l fChartEffPrev with hA_def
  -- The five layers, as functions `EuclN → ℝ`.
  set layerA : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M) g r s h_atlas i α P₀
          (m + 1) (Fin.cons a (Fin.init l)) y with hlayerA_def
  set layerB : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y with hlayerB_def
  set layerC : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      eigenvectorChartIteratedPartial (I := I) (M := M) g r s h_atlas i α P₀
        m (Fin.init l) y with hlayerC_def
  set layerD : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      fChartEffPrev y with hlayerD_def
  set layerE : EuclN → ℝ := fun y =>
    densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y
    with hlayerE_def
  -- The numerator is, pointwise, `layerA + layerB - layerC + layerD + layerE`.
  have h_num_eq : eigenvectorChartRHSDiffNumerator (I := I) (M := M)
      g r s h_atlas i α P₀ m l fChartEffPrev =
      fun y => layerA y + layerB y - layerC y + layerD y + layerE y := by
    funext y
    rw [eigenvectorChartRHSDiffNumerator]
  -- The five per-layer `MemWkp K 2` memberships and `wkpNorm` bounds.
  obtain ⟨hA_mem, CA, hCA_nn, hCA⟩ :=
    eigenvectorChartRHSDiffNumerator_layerA_wkpNorm_le
      (I := I) (M := M) g r s h_atlas i α P₀ m K l fChartEffPrev
      (fun a => h_iter (m + 1) (Fin.cons a (Fin.init l)))
  obtain ⟨hB_mem, CB, hCB_nn, hCB⟩ :=
    eigenvectorChartRHSDiffNumerator_layerB_wkpNorm_le
      (I := I) (M := M) g r s h_atlas i α P₀ m K l fChartEffPrev
      (fun a => h_iter (m + 1) (Fin.cons a (Fin.init l)))
  obtain ⟨hC_mem, CC, hCC_nn, hCC⟩ :=
    eigenvectorChartRHSDiffNumerator_layerC_wkpNorm_le
      (I := I) (M := M) g r s h_atlas i α P₀ m K l fChartEffPrev
      (h_iter m (Fin.init l))
  obtain ⟨hD_mem, CD, hCD_nn, hCD⟩ :=
    eigenvectorChartRHSDiffNumerator_layerD_wkpNorm_le
      (I := I) (M := M) g r s h_atlas i α P₀ m K l h_prev h_prev_zero
  obtain ⟨hE_mem, CE, hCE_nn, hCE⟩ :=
    eigenvectorChartRHSDiffNumerator_layerE_wkpNorm_le
      (I := I) (M := M) g r s h_atlas i α P₀ m K l h_prev h_prev_zero
  rw [← hΩ_def, ← hA_def] at hCA hCB hCC hCD hCE
  rw [← hΩ_def] at hA_mem hB_mem hC_mem hD_mem hE_mem
  -- The headline constant: the sum of the five per-layer constants.
  refine ⟨CA + CB + CC + CD + CE, by positivity, ?_⟩
  rw [h_num_eq]
  -- Intermediate partial sums of the five layers `A + B - C + D + E`.
  set sAB : EuclN → ℝ := fun y => layerA y + layerB y with hsAB_def
  set sABC : EuclN → ℝ := fun y => sAB y - layerC y with hsABC_def
  set sABCD : EuclN → ℝ := fun y => sABC y + layerD y with hsABCD_def
  have hAB_mem : MemWkp (d := Module.finrank ℝ E) K 2 sAB Ω :=
    MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open hA_mem hB_mem
  have hABC_mem : MemWkp (d := Module.finrank ℝ E) K 2 sABC Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) (by norm_num) hΩ_open hAB_mem hC_mem
  have hABCD_mem : MemWkp (d := Module.finrank ℝ E) K 2 sABCD Ω :=
    MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open hABC_mem hD_mem
  -- Per-partial-sum triangle bounds.
  have h_sAB_le : wkpNorm (d := Module.finrank ℝ E) K 2 sAB Ω ≤
      wkpNorm (d := Module.finrank ℝ E) K 2 layerA Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerB Ω :=
    wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open hA_mem hB_mem
  have h_sABC_le : wkpNorm (d := Module.finrank ℝ E) K 2 sABC Ω ≤
      wkpNorm (d := Module.finrank ℝ E) K 2 sAB Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerC Ω :=
    wkpNorm_sub_le (d := Module.finrank ℝ E) hΩ_open hAB_mem hC_mem
  have h_sABCD_le : wkpNorm (d := Module.finrank ℝ E) K 2 sABCD Ω ≤
      wkpNorm (d := Module.finrank ℝ E) K 2 sABC Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerD Ω :=
    wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open hABC_mem hD_mem
  -- The numerator, as a function, is `sABCD + layerE`.
  have h_split : (fun y => layerA y + layerB y - layerC y + layerD y
        + layerE y) = (fun y => sABCD y + layerE y) := by
    funext y
    rw [hsABCD_def, hsABC_def, hsAB_def]
  -- Iterated Minkowski: the numerator is `sABCD + layerE`.
  have h_tri :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => layerA y + layerB y - layerC y + layerD y + layerE y) Ω
        ≤ wkpNorm (d := Module.finrank ℝ E) K 2 layerA Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2 layerB Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2 layerC Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2 layerD Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2 layerE Ω := by
    rw [h_split]
    have h_outer : wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => sABCD y + layerE y) Ω ≤
        wkpNorm (d := Module.finrank ℝ E) K 2 sABCD Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2 layerE Ω :=
      wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        hABCD_mem hE_mem
    refine le_trans h_outer ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans h_sABCD_le ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans h_sABC_le ?_
    refine add_le_add ?_ (le_refl _)
    exact h_sAB_le
  refine le_trans h_tri ?_
  -- Each of the five per-layer norms is `≤ ofReal Cⱼ * A`.
  have h_five :
      wkpNorm (d := Module.finrank ℝ E) K 2 layerA Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerB Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerC Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerD Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerE Ω
      ≤ ENNReal.ofReal CA * A + ENNReal.ofReal CB * A + ENNReal.ofReal CC * A
        + ENNReal.ofReal CD * A + ENNReal.ofReal CE * A :=
    add_le_add (add_le_add (add_le_add (add_le_add hCA hCB) hCC) hCD) hCE
  refine le_trans h_five ?_
  -- Collect the five `ofReal Cⱼ * A` terms into `ofReal (∑ Cⱼ) * A`.
  rw [ENNReal.ofReal_add (by positivity) hCE_nn,
    ENNReal.ofReal_add (by positivity) hCD_nn,
    ENNReal.ofReal_add (by positivity) hCC_nn,
    ENNReal.ofReal_add hCA_nn hCB_nn]
  rw [add_mul, add_mul, add_mul, add_mul]

end MainBound

/-! ## The uniform-constant `K`-graded explicit-norm `wkpNorm` bound

The headline `eigenvectorChartRHSDiffNumerator_wkpNorm_le` produces, per
eigenbasis index `i`, a nonnegative constant `C`. A downstream bounded-operator
argument over the whole eigenbasis needs the constant *uniform* — one `C`
serving every `i`. The five per-layer constants are geometric — Leibniz
constants of the `C^∞` chart-target coefficients (`weightedInvGramDerivOnEuclid`
and its `fderiv`, `densityDerivOnEuclid`, `densityOnEuclid`), cut off to globally
smooth compactly supported representatives — and do not depend on `i`. The
eigenbasis index enters only through the iterated-weak-partial *atoms* and the
regularity hypotheses, never the constant.

The eigenvector index `i` is **not** a section variable here, so each restatement
carries its own `∀ i`. A `_uniform` statement cannot be derived from its per-`i`
original (one cannot get `∃ C, ∀ i` from `∀ i, ∃ C`); each carries its own proof
— the per-`i` proof with the constant hoisted before the `∀ i`. The genuine
regularity hypotheses `h_iter`, `h_prev`, `h_prev_zero` move to top-level
`∀ i`-uniform hypotheses. -/

section MainBoundUniform

/-! ## The uniform-constant smooth-coefficient `wkpNorm` bound

The constant-uniform twin of `wkpNorm_coef_mul_factor_le`. The cutoff
representative `χ · coef`, its uniform iterated-derivative bound `C₀`, and the
Leibniz constant `Kc` depend only on the coefficient and the order `K`, not on
the factor being multiplied — `wkpNorm_smul_smooth_bounded_le` already produces a
factor-uniform `Kc`. Only the factor-membership, factor-ae-vanishing, and the
resulting ae-equality vary with the factor, so the bound uniformizes over the
factor with a single geometric constant `C`. -/

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
  -- `χ · coef` is globally smooth.
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

/-! ## Uniform-constant finite-sum aggregation for `wkpNorm`

The constant-uniform twin of `wkpNorm_sum_le_const_mul_aggregate`: a finite
indexed family of summands `F j n`, each `MemWkp K 2` and each — *with an
`n`-uniform constant* — having its order-`K` Sobolev norm bounded by
`ENNReal.ofReal Cⱼ` times an aggregate `A n`, has its summed `wkpNorm` bounded by
a single `n`-uniform nonnegative constant times `A n`. -/

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma wkpNorm_sum_le_const_mul_aggregate_uniform
    {α : M} {K : ℕ} {ι : Type*} [Fintype ι] {ν : Type*} (F : ι → ν → EuclN → ℝ)
    (A : ν → ℝ≥0∞)
    (hF : ∀ (j : ι) (n : ν), MemWkp (d := Module.finrank ℝ E) K 2 (F j n)
      (chartTargetEuclid (I := I) (M := M) α))
    (hbd : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ν, wkpNorm (d := Module.finrank ℝ E) K 2 (F j n)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C * A n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ν, wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ j : ι, F j n y) (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C * A n := by
  classical
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  choose Cf hCf_nn hCf using hbd
  refine ⟨(∑ j : ι, Cf j) * (Fintype.card ι : ℝ),
    mul_nonneg (Finset.sum_nonneg (fun j _ => hCf_nn j)) (by positivity),
    fun n => ?_⟩
  have h_tri : wkpNorm (d := Module.finrank ℝ E) K 2
      (fun y => ∑ j : ι, F j n y) (chartTargetEuclid (I := I) (M := M) α)
      ≤ ∑ j : ι, wkpNorm (d := Module.finrank ℝ E) K 2 (F j n)
          (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_sum_le (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open Finset.univ (fun j => F j n)
      (fun j _ => hF j n)
  have h_step : ∑ j : ι, wkpNorm (d := Module.finrank ℝ E) K 2 (F j n)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A n := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine (hCf j n).trans ?_
    gcongr
    exact Finset.single_le_sum (fun k _ => hCf_nn k) (Finset.mem_univ j)
  have h_const : ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A n
      = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A n) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_cast : (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)
      = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) := by
    rw [mul_comm (∑ j : ι, Cf j), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast]
  calc
    wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ j : ι, F j n y) (chartTargetEuclid (I := I) (M := M) α)
        ≤ ∑ j : ι, wkpNorm (d := Module.finrank ℝ E) K 2 (F j n)
            (chartTargetEuclid (I := I) (M := M) α) := h_tri
    _ ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A n := h_step
    _ = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A n) := h_const
    _ = ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)) * A n := by
        rw [mul_assoc]
    _ = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) * A n := by
        rw [h_cast]

/-! ## Uniform-constant per-layer `wkpNorm` bounds

The constant-uniform twins of the five per-layer bounds. Each carries its
genuine regularity hypothesis as a top-level `∀ i`-uniform hypothesis, exhibits
the `∀ i` form of the `MemWkp K 2` membership of the layer, and concludes
`∃ C, 0 ≤ C ∧ ∀ i, <layer bound>`; the geometric constant is hoisted before the
`∀ i`. -/

omit [CompleteSpace E] in
/-- **Uniform-constant `wkpNorm` bound for layer `A`.** -/
private lemma eigenvectorChartRHSDiffNumerator_layerA_wkpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_iter : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a : Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) :
    (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => ∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m))) y)
                  (EuclideanSpace.single b 1) *
                eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
          (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ a : Fin (Module.finrank ℝ E),
                ∑ b : Fin (Module.finrank ℝ E),
                  (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                        (l (Fin.last m))) y)
                      (EuclideanSpace.single b 1) *
                    eigenvectorChartIteratedPartial (I := I) (M := M)
                      g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C *
              diffNumeratorAggregateK (I := I) (M := M)
                g r s h_atlas i α P₀ m K l (fChartEffPrev i) := by
  classical
  -- Each `(a, b)`-summand: a smooth coefficient times the `(m+1)`-fold iterated
  -- weak partial. The geometric constant is hoisted over `i`.
  have h_pair : ∀ a b : Fin (Module.finrank ℝ E),
      (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) K 2
            (fun y =>
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m))) y)
                  (EuclideanSpace.single b 1) *
                eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
            (chartTargetEuclid (I := I) (M := M) α)) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
            wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y =>
                  (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                        (l (Fin.last m))) y)
                      (EuclideanSpace.single b 1) *
                    eigenvectorChartIteratedPartial (I := I) (M := M)
                      g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
                (chartTargetEuclid (I := I) (M := M) α)
              ≤ ENNReal.ofReal C *
                diffNumeratorAggregateK (I := I) (M := M)
                  g r s h_atlas i α P₀ m K l (fChartEffPrev i) := by
    intro a b
    obtain ⟨C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le_uniform
      (I := I) (M := M) α K
      (layerA_coeff_contDiffOn (I := I) (M := M) g α m l a b)
    refine ⟨fun i => ?_, C₀, hC₀_nn, fun i => ?_⟩
    · exact (hC₀ _
        ((h_iter i a).le_of_le (by omega))
        (eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s h_atlas i α P₀ (m + 1)
          (Fin.cons a (Fin.init l)))).1
    · refine le_trans ((hC₀ _
        ((h_iter i a).le_of_le (by omega))
        (eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s h_atlas i α P₀ (m + 1)
          (Fin.cons a (Fin.init l)))).2) ?_
      gcongr
      refine le_trans (wkpNorm_iteratedPartial_succ_le
        (I := I) (M := M) g r s h_atlas i α P₀ m K l a) ?_
      rw [diffNumeratorAggregateK]
      refine le_trans (Finset.single_le_sum (f := fun a =>
        wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α))
        (fun k _ => zero_le _) (Finset.mem_univ a)) ?_
      exact le_trans le_self_add (le_trans le_self_add le_self_add)
  -- Inner sum over `b`: `MemWkp K 2` and the `i`-uniform `wkpNorm` bound.
  have h_inner : ∀ a : Fin (Module.finrank ℝ E),
      (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) K 2
            (fun y => ∑ b : Fin (Module.finrank ℝ E),
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m))) y)
                  (EuclideanSpace.single b 1) *
                eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
            (chartTargetEuclid (I := I) (M := M) α)) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ b : Fin (Module.finrank ℝ E),
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                      (l (Fin.last m))) y)
                    (EuclideanSpace.single b 1) *
                  eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C *
              diffNumeratorAggregateK (I := I) (M := M)
                g r s h_atlas i α P₀ m K l (fChartEffPrev i) := fun a =>
    ⟨fun i => memWkp_finset_sum (I := I) (M := M)
      (α := α) (K := K) (s := Finset.univ)
      (f := fun b y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      (fun b _ => (h_pair a b).1 i),
    wkpNorm_sum_le_const_mul_aggregate_uniform (I := I) (M := M)
      (α := α) (K := K) (ι := Fin (Module.finrank ℝ E))
      (ν := TensorEigenIdx (I := I) (M := M) g r s)
      (fun b => fun i => fun y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      (fun i => diffNumeratorAggregateK (I := I) (M := M)
        g r s h_atlas i α P₀ m K l (fChartEffPrev i))
      (fun b i => (h_pair a b).1 i) (fun b => (h_pair a b).2)⟩
  exact ⟨fun i => memWkp_finset_sum (I := I) (M := M)
    (α := α) (K := K) (s := Finset.univ)
    (f := fun a y => ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
    (fun a _ => (h_inner a).1 i),
  wkpNorm_sum_le_const_mul_aggregate_uniform (I := I) (M := M)
    (α := α) (K := K) (ι := Fin (Module.finrank ℝ E))
    (ν := TensorEigenIdx (I := I) (M := M) g r s)
    (fun a => fun i => fun y => ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
    (fun i => diffNumeratorAggregateK (I := I) (M := M)
      g r s h_atlas i α P₀ m K l (fChartEffPrev i))
    (fun a i => (h_inner a).1 i) (fun a => (h_inner a).2)⟩

omit [CompleteSpace E] in
/-- **Uniform-constant `wkpNorm` bound for layer `B`.** -/
private lemma eigenvectorChartRHSDiffNumerator_layerB_wkpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_iter : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a : Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) :
    (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => ∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
                chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                  (eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                  (chartTargetEuclid (I := I) (M := M) α) y)
          (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ a : Fin (Module.finrank ℝ E),
                ∑ b : Fin (Module.finrank ℝ E),
                  weightedInvGramDerivOnEuclid (I := I) g α a b
                      (l (Fin.last m)) y *
                    chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                      (eigenvectorChartIteratedPartial (I := I) (M := M)
                        g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                      (chartTargetEuclid (I := I) (M := M) α) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C *
              diffNumeratorAggregateK (I := I) (M := M)
                g r s h_atlas i α P₀ m K l (fChartEffPrev i) := by
  classical
  -- Each `(a, b)`-summand: a smooth coefficient times the chosen weak
  -- `b`-partial of the `(m+1)`-fold iterated weak partial.
  have h_pair : ∀ a b : Fin (Module.finrank ℝ E),
      (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) K 2
            (fun y =>
              weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
                chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                  (eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                  (chartTargetEuclid (I := I) (M := M) α) y)
            (chartTargetEuclid (I := I) (M := M) α)) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
            wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y =>
                  weightedInvGramDerivOnEuclid (I := I) g α a b
                      (l (Fin.last m)) y *
                    chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                      (eigenvectorChartIteratedPartial (I := I) (M := M)
                        g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                      (chartTargetEuclid (I := I) (M := M) α) y)
                (chartTargetEuclid (I := I) (M := M) α)
              ≤ ENNReal.ofReal C *
                diffNumeratorAggregateK (I := I) (M := M)
                  g r s h_atlas i α P₀ m K l (fChartEffPrev i) := by
    intro a b
    obtain ⟨C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le_uniform
      (I := I) (M := M) α K
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m)))
    -- The chosen weak `b`-partial of the level-`(m+1)` mixed partial.
    have h_factor : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        MemWkp (d := Module.finrank ℝ E) K 2
            (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
              (chartTargetEuclid (I := I) (M := M) α))
            (chartTargetEuclid (I := I) (M := M) α) ∧
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
              (chartTargetEuclid (I := I) (M := M) α)
            =ᵐ[(volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α \
                chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)) := by
      intro i
      refine ⟨((h_iter i a).le_of_le (by omega)).chosenWeakPartial_mem b, ?_⟩
      exact chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
        (I := I) (M := M) α
        (eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s h_atlas i α P₀ (m + 1)
          (Fin.cons a (Fin.init l))) b
    refine ⟨fun i => (hC₀ _ (h_factor i).1 (h_factor i).2).1,
      C₀, hC₀_nn, fun i => ?_⟩
    refine le_trans ((hC₀ _ (h_factor i).1 (h_factor i).2).2) ?_
    gcongr
    refine le_trans (wkpNorm_chosenWeakPartial_iteratedPartial_succ_le
      (I := I) (M := M) g r s h_atlas i α P₀ m K l a b) ?_
    rw [diffNumeratorAggregateK]
    refine le_trans (Finset.single_le_sum (f := fun a =>
      wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α))
      (fun k _ => zero_le _) (Finset.mem_univ a)) ?_
    exact le_trans le_self_add (le_trans le_self_add le_self_add)
  -- Inner sum over `b`.
  have h_inner : ∀ a : Fin (Module.finrank ℝ E),
      (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) K 2
            (fun y => ∑ b : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
                chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                  (eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                  (chartTargetEuclid (I := I) (M := M) α) y)
            (chartTargetEuclid (I := I) (M := M) α)) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ b : Fin (Module.finrank ℝ E),
                weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m)) y *
                  chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                    (eigenvectorChartIteratedPartial (I := I) (M := M)
                      g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                    (chartTargetEuclid (I := I) (M := M) α) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C *
              diffNumeratorAggregateK (I := I) (M := M)
                g r s h_atlas i α P₀ m K l (fChartEffPrev i) := fun a =>
    ⟨fun i => memWkp_finset_sum (I := I) (M := M)
      (α := α) (K := K) (s := Finset.univ)
      (f := fun b y =>
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y)
      (fun b _ => (h_pair a b).1 i),
    wkpNorm_sum_le_const_mul_aggregate_uniform (I := I) (M := M)
      (α := α) (K := K) (ι := Fin (Module.finrank ℝ E))
      (ν := TensorEigenIdx (I := I) (M := M) g r s)
      (fun b => fun i => fun y =>
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y)
      (fun i => diffNumeratorAggregateK (I := I) (M := M)
        g r s h_atlas i α P₀ m K l (fChartEffPrev i))
      (fun b i => (h_pair a b).1 i) (fun b => (h_pair a b).2)⟩
  exact ⟨fun i => memWkp_finset_sum (I := I) (M := M)
    (α := α) (K := K) (s := Finset.univ)
    (f := fun a y => ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y)
    (fun a _ => (h_inner a).1 i),
  wkpNorm_sum_le_const_mul_aggregate_uniform (I := I) (M := M)
    (α := α) (K := K) (ι := Fin (Module.finrank ℝ E))
    (ν := TensorEigenIdx (I := I) (M := M) g r s)
    (fun a => fun i => fun y => ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y)
    (fun i => diffNumeratorAggregateK (I := I) (M := M)
      g r s h_atlas i α P₀ m K l (fChartEffPrev i))
    (fun a i => (h_inner a).1 i) (fun a => (h_inner a).2)⟩

omit [CompleteSpace E] in
/-- **Uniform-constant `wkpNorm` bound for layer `C`.** -/
private lemma eigenvectorChartRHSDiffNumerator_layerC_wkpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_iter_m : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ m (Fin.init l))
        (chartTargetEuclid (I := I) (M := M) α)) :
    (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y =>
            densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ m (Fin.init l) y)
          (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y =>
                densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
                  eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s h_atlas i α P₀ m (Fin.init l) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C *
              diffNumeratorAggregateK (I := I) (M := M)
                g r s h_atlas i α P₀ m K l (fChartEffPrev i) := by
  classical
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le_uniform
    (I := I) (M := M) α K
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
  -- The `m`-fold iterated weak partial atom and its ae-vanishing off the kernel.
  have h_factor : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) K 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ m (Fin.init l))
          (chartTargetEuclid (I := I) (M := M) α) ∧
        eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ m (Fin.init l)
          =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α \
              chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)) := by
    intro i
    exact ⟨(h_iter_m i).le_of_le (by omega),
      eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s h_atlas i α P₀ m (Fin.init l)⟩
  refine ⟨fun i => (hC₀ _ (h_factor i).1 (h_factor i).2).1,
    C₀, hC₀_nn, fun i => ?_⟩
  refine le_trans ((hC₀ _ (h_factor i).1 (h_factor i).2).2) ?_
  gcongr
  refine le_trans (wkpNorm_iteratedPartial_le
    (I := I) (M := M) g r s h_atlas i α P₀ m K l) ?_
  rw [diffNumeratorAggregateK]
  exact le_trans le_add_self (le_trans le_self_add le_self_add)

omit [CompleteSpace E] in
/-- **Uniform-constant `wkpNorm` bound for layer `D`.** -/
private lemma eigenvectorChartRHSDiffNumerator_layerD_wkpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_prev : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      (fChartEffPrev i) =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y =>
            densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
              fChartEffPrev i y)
          (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y =>
                densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
                  fChartEffPrev i y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C *
              diffNumeratorAggregateK (I := I) (M := M)
                g r s h_atlas i α P₀ m K l (fChartEffPrev i) := by
  classical
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le_uniform
    (I := I) (M := M) α K
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
  have h_factor : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) K 2 (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α) := fun i =>
    (h_prev i).le_of_le (by omega)
  refine ⟨fun i => (hC₀ _ (h_factor i) (h_prev_zero i)).1,
    C₀, hC₀_nn, fun i => ?_⟩
  refine le_trans ((hC₀ _ (h_factor i) (h_prev_zero i)).2) ?_
  gcongr
  rw [diffNumeratorAggregateK]
  exact le_add_self

omit [CompleteSpace E] in
/-- **Uniform-constant `wkpNorm` bound for layer `E`.** -/
private lemma eigenvectorChartRHSDiffNumerator_layerE_wkpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_prev : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      (fChartEffPrev i) =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y =>
            densityOnEuclid (I := I) g α y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
                (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α) y)
          (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y =>
                densityOnEuclid (I := I) g α y *
                  chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
                    (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C *
              diffNumeratorAggregateK (I := I) (M := M)
                g r s h_atlas i α P₀ m K l (fChartEffPrev i) := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le_uniform
    (I := I) (M := M) α K
    (densityOnEuclid_contDiffOn (I := I) g α)
  -- The chosen weak `lₙ`-partial of `fChartEffPrev i` and its ae-vanishing.
  have h_factor : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) K 2
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
            (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α))
          (chartTargetEuclid (I := I) (M := M) α) ∧
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
            (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α)
          =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α \
              chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)) := by
    intro i
    refine ⟨(h_prev i).chosenWeakPartial_mem (l (Fin.last m)), ?_⟩
    exact chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
      (I := I) (M := M) α (h_prev_zero i) (l (Fin.last m))
  refine ⟨fun i => (hC₀ _ (h_factor i).1 (h_factor i).2).1,
    C₀, hC₀_nn, fun i => ?_⟩
  refine le_trans ((hC₀ _ (h_factor i).1 (h_factor i).2).2) ?_
  gcongr
  -- `wkpNorm K 2 (∂_{lₙ} fChartEffPrev) ≤ wkpNorm (K + 1) 2 fChartEffPrev`.
  refine le_trans (wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E)
    K hΩ_open _ (l (Fin.last m))) ?_
  rw [diffNumeratorAggregateK]
  exact le_trans le_add_self le_self_add

omit [CompleteSpace E] in
/-- **The uniform-constant `K`-graded explicit-norm `wkpNorm` bound for the
differentiated chart-RHS numerator.**

The constant-uniform form of `eigenvectorChartRHSDiffNumerator_wkpNorm_le`: a
single nonnegative constant `C` — geometric, the combined Leibniz constants of
the `C^∞` chart-target coefficients, independent of the eigenbasis index —
serves *every* eigenbasis index `i`. For each `i`, the order-`K` Sobolev norm of
the level-`(m+1)` differentiated chart-RHS numerator on the open Euclidean chart
target `chartTargetEuclid α` is bounded by `ENNReal.ofReal C` times the finite
aggregate `diffNumeratorAggregateK` of the order-`K` source norms of that `i`.

The genuine regularity hypotheses are uniform over `i`: every `(m+1)`-fold and
`m`-fold iterated weak partial of every eigenvector chart component lies in
`W^{2 + K, 2}(chartTargetEuclid α)` (`h_iter`); each previous-level right-hand
side `fChartEffPrev i` lies in `W^{K + 1, 2}(chartTargetEuclid α)` (`h_prev`) and
vanishes almost everywhere off the partition-of-unity kernel (`h_prev_zero`).

A `_uniform` statement cannot be derived from its per-`i` original; this carries
its own proof — the per-`i` proof of `eigenvectorChartRHSDiffNumerator_wkpNorm_le`
with the five per-layer geometric constants hoisted before the `∀ i` via the
constant-uniform per-layer bounds. -/
theorem eigenvectorChartRHSDiffNumerator_wkpNorm_le_uniform
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
            (eigenvectorChartRHSDiffNumerator (I := I) (M := M)
              g r s h_atlas i α P₀ m l (fChartEffPrev i))
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK (I := I) (M := M)
              g r s h_atlas i α P₀ m K l (fChartEffPrev i) := by
  classical
  -- The five `i`-uniform per-layer memberships and constants — the constants
  -- are hoisted before the `∀ i`.
  obtain ⟨hA_mem, CA, hCA_nn, hCA⟩ :=
    eigenvectorChartRHSDiffNumerator_layerA_wkpNorm_le_uniform
      (I := I) (M := M) g r s h_atlas α P₀ m K l fChartEffPrev
      (fun i a => h_iter i (m + 1) (Fin.cons a (Fin.init l)))
  obtain ⟨hB_mem, CB, hCB_nn, hCB⟩ :=
    eigenvectorChartRHSDiffNumerator_layerB_wkpNorm_le_uniform
      (I := I) (M := M) g r s h_atlas α P₀ m K l fChartEffPrev
      (fun i a => h_iter i (m + 1) (Fin.cons a (Fin.init l)))
  obtain ⟨hC_mem, CC, hCC_nn, hCC⟩ :=
    eigenvectorChartRHSDiffNumerator_layerC_wkpNorm_le_uniform
      (I := I) (M := M) g r s h_atlas α P₀ m K l fChartEffPrev
      (fun i => h_iter i m (Fin.init l))
  obtain ⟨hD_mem, CD, hCD_nn, hCD⟩ :=
    eigenvectorChartRHSDiffNumerator_layerD_wkpNorm_le_uniform
      (I := I) (M := M) g r s h_atlas α P₀ m K l fChartEffPrev h_prev h_prev_zero
  obtain ⟨hE_mem, CE, hCE_nn, hCE⟩ :=
    eigenvectorChartRHSDiffNumerator_layerE_wkpNorm_le_uniform
      (I := I) (M := M) g r s h_atlas α P₀ m K l fChartEffPrev h_prev h_prev_zero
  -- The headline constant: the sum of the five per-layer constants.
  refine ⟨CA + CB + CC + CD + CE, by positivity, fun i => ?_⟩
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set A := diffNumeratorAggregateK (I := I) (M := M)
    g r s h_atlas i α P₀ m K l (fChartEffPrev i) with hA_def
  -- The five layers, as functions `EuclN → ℝ`.
  set layerA : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M) g r s h_atlas i α P₀
          (m + 1) (Fin.cons a (Fin.init l)) y with hlayerA_def
  set layerB : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y with hlayerB_def
  set layerC : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      eigenvectorChartIteratedPartial (I := I) (M := M) g r s h_atlas i α P₀
        m (Fin.init l) y with hlayerC_def
  set layerD : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      fChartEffPrev i y with hlayerD_def
  set layerE : EuclN → ℝ := fun y =>
    densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α) y
    with hlayerE_def
  -- The numerator is, pointwise, `layerA + layerB - layerC + layerD + layerE`.
  have h_num_eq : eigenvectorChartRHSDiffNumerator (I := I) (M := M)
      g r s h_atlas i α P₀ m l (fChartEffPrev i) =
      fun y => layerA y + layerB y - layerC y + layerD y + layerE y := by
    funext y
    rw [eigenvectorChartRHSDiffNumerator]
  -- The five per-layer memberships and bounds, specialised to this `i`.
  have hA_mem_i := hA_mem i
  have hB_mem_i := hB_mem i
  have hC_mem_i := hC_mem i
  have hD_mem_i := hD_mem i
  have hE_mem_i := hE_mem i
  have hCA_i := hCA i
  have hCB_i := hCB i
  have hCC_i := hCC i
  have hCD_i := hCD i
  have hCE_i := hCE i
  rw [← hA_def] at hCA_i hCB_i hCC_i hCD_i hCE_i
  rw [← hlayerA_def] at hA_mem_i hCA_i
  rw [← hlayerB_def] at hB_mem_i hCB_i
  rw [← hlayerC_def] at hC_mem_i hCC_i
  rw [← hlayerD_def] at hD_mem_i hCD_i
  rw [← hlayerE_def] at hE_mem_i hCE_i
  rw [h_num_eq]
  -- Intermediate partial sums of the five layers `A + B - C + D + E`.
  set sAB : EuclN → ℝ := fun y => layerA y + layerB y with hsAB_def
  set sABC : EuclN → ℝ := fun y => sAB y - layerC y with hsABC_def
  set sABCD : EuclN → ℝ := fun y => sABC y + layerD y with hsABCD_def
  have hAB_mem : MemWkp (d := Module.finrank ℝ E) K 2 sAB Ω :=
    MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open hA_mem_i hB_mem_i
  have hABC_mem : MemWkp (d := Module.finrank ℝ E) K 2 sABC Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) (by norm_num) hΩ_open hAB_mem hC_mem_i
  have hABCD_mem : MemWkp (d := Module.finrank ℝ E) K 2 sABCD Ω :=
    MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open hABC_mem hD_mem_i
  -- Per-partial-sum triangle bounds.
  have h_sAB_le : wkpNorm (d := Module.finrank ℝ E) K 2 sAB Ω ≤
      wkpNorm (d := Module.finrank ℝ E) K 2 layerA Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerB Ω :=
    wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      hA_mem_i hB_mem_i
  have h_sABC_le : wkpNorm (d := Module.finrank ℝ E) K 2 sABC Ω ≤
      wkpNorm (d := Module.finrank ℝ E) K 2 sAB Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerC Ω :=
    wkpNorm_sub_le (d := Module.finrank ℝ E) hΩ_open hAB_mem hC_mem_i
  have h_sABCD_le : wkpNorm (d := Module.finrank ℝ E) K 2 sABCD Ω ≤
      wkpNorm (d := Module.finrank ℝ E) K 2 sABC Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerD Ω :=
    wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      hABC_mem hD_mem_i
  -- The numerator, as a function, is `sABCD + layerE`.
  have h_split : (fun y => layerA y + layerB y - layerC y + layerD y
        + layerE y) = (fun y => sABCD y + layerE y) := by
    funext y
    rw [hsABCD_def, hsABC_def, hsAB_def]
  -- Iterated Minkowski: the numerator is `sABCD + layerE`.
  have h_tri :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => layerA y + layerB y - layerC y + layerD y + layerE y) Ω
        ≤ wkpNorm (d := Module.finrank ℝ E) K 2 layerA Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2 layerB Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2 layerC Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2 layerD Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2 layerE Ω := by
    rw [h_split]
    have h_outer : wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => sABCD y + layerE y) Ω ≤
        wkpNorm (d := Module.finrank ℝ E) K 2 sABCD Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2 layerE Ω :=
      wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        hABCD_mem hE_mem_i
    refine le_trans h_outer ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans h_sABCD_le ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans h_sABC_le ?_
    refine add_le_add ?_ (le_refl _)
    exact h_sAB_le
  refine le_trans h_tri ?_
  -- Each of the five per-layer norms is `≤ ofReal Cⱼ * A`.
  have h_five :
      wkpNorm (d := Module.finrank ℝ E) K 2 layerA Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerB Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerC Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerD Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerE Ω
      ≤ ENNReal.ofReal CA * A + ENNReal.ofReal CB * A + ENNReal.ofReal CC * A
        + ENNReal.ofReal CD * A + ENNReal.ofReal CE * A :=
    add_le_add (add_le_add (add_le_add (add_le_add hCA_i hCB_i) hCC_i) hCD_i)
      hCE_i
  refine le_trans h_five ?_
  -- Collect the five `ofReal Cⱼ * A` terms into `ofReal (∑ Cⱼ) * A`.
  rw [ENNReal.ofReal_add (by positivity) hCE_nn,
    ENNReal.ofReal_add (by positivity) hCD_nn,
    ENNReal.ofReal_add (by positivity) hCC_nn,
    ENNReal.ofReal_add hCA_nn hCB_nn]
  rw [add_mul, add_mul, add_mul, add_mul]

end MainBoundUniform

/-! ## Sanity test -/

section ElaborationTest

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
          (eigenvectorChartRHSDiffNumerator (I := I) (M := M)
            g r s h_atlas i α P₀ m l fChartEffPrev)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregateK (I := I) (M := M)
            g r s h_atlas i α P₀ m K l fChartEffPrev :=
  eigenvectorChartRHSDiffNumerator_wkpNorm_le (I := I) (M := M)
    g r s h_atlas i α P₀ m K l fChartEffPrev h_iter h_prev h_prev_zero

end ElaborationTest

/-! ## Chart-locality-free twins

The chart-locality-free `_unconditional` companions of the declarations above.
Each statement and proof transfers verbatim, with the `m`-fold mixed weak
partials re-keyed onto `eigenvectorChartIteratedPartial_unconditional` (built on
the intrinsic-compactness eigenvector
`tensorResolventEigenbasisVec_ofCompact (tensorResolventL2_isCompactOperator_intrinsic g r s) i`),
the five-layer numerator onto `eigenvectorChartRHSDiffNumerator_unconditional`,
the aggregate onto `diffNumeratorAggregateK_unconditional`, and the
ae-vanishing-off-the-kernel hypothesis onto
`eigenvectorChartIteratedPartial_unconditional_ae_zero_off_chartPouKernel`. -/

/-- Chart-locality-free twin of `diffNumeratorAggregateK`. -/
def diffNumeratorAggregateK_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ) : ℝ≥0∞ :=
  (∑ a : Fin (Module.finrank ℝ E),
      wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α))
    + wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ m (Fin.init l))
        (chartTargetEuclid (I := I) (M := M) α)
    + wkpNorm (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
        (chartTargetEuclid (I := I) (M := M) α)
    + wkpNorm (d := Module.finrank ℝ E) K 2 fChartEffPrev
        (chartTargetEuclid (I := I) (M := M) α)

/-! ### Chart-locality-free per-atom `wkpNorm` bounds -/

section AtomBoundsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
  (l : Fin (m + 1) → Fin (Module.finrank ℝ E))

/-- Chart-locality-free twin of `wkpNorm_iteratedPartial_succ_le`. -/
private lemma wkpNorm_iteratedPartial_succ_le_unconditional
    (a : Fin (Module.finrank ℝ E)) :
    wkpNorm (d := Module.finrank ℝ E) K 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) :=
  wkpNorm_mono_order (d := Module.finrank ℝ E) (by omega) _ _

/-- Chart-locality-free twin of `wkpNorm_iteratedPartial_le`. -/
private lemma wkpNorm_iteratedPartial_le_unconditional :
    wkpNorm (d := Module.finrank ℝ E) K 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ m (Fin.init l))
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ m (Fin.init l))
          (chartTargetEuclid (I := I) (M := M) α) :=
  wkpNorm_mono_order (d := Module.finrank ℝ E) (by omega) _ _

/-- Chart-locality-free twin of
`wkpNorm_chosenWeakPartial_iteratedPartial_succ_le`. -/
private lemma wkpNorm_chosenWeakPartial_iteratedPartial_succ_le_unconditional
    (a b : Fin (Module.finrank ℝ E)) :
    wkpNorm (d := Module.finrank ℝ E) K 2
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) := by
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  refine le_trans (wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E)
    K hΩ_open _ b) ?_
  exact wkpNorm_mono_order (d := Module.finrank ℝ E) (by omega) _ _

end AtomBoundsUnconditional

/-! ### Chart-locality-free per-layer `wkpNorm` bounds -/

section LayerBoundsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
  (l : Fin (m + 1) → Fin (Module.finrank ℝ E))

/-- Chart-locality-free twin of
`eigenvectorChartRHSDiffNumerator_layerA_wkpNorm_le`. -/
private lemma eigenvectorChartRHSDiffNumerator_layerA_wkpNorm_le_unconditional
    (fChartEffPrev : EuclN → ℝ)
    (h_iter : ∀ a : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                  (l (Fin.last m))) y)
                (EuclideanSpace.single b 1) *
              eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
        (chartTargetEuclid (I := I) (M := M) α) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E),
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                      (l (Fin.last m))) y)
                    (EuclideanSpace.single b 1) *
                  eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                    g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK_unconditional (I := I) (M := M)
              g r s i α P₀ m K l fChartEffPrev := by
  classical
  set A := diffNumeratorAggregateK_unconditional (I := I) (M := M)
    g r s i α P₀ m K l fChartEffPrev with hA_def
  have h_pair : ∀ a b : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) K 2
          (fun y =>
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                  (l (Fin.last m))) y)
                (EuclideanSpace.single b 1) *
              eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
          (chartTargetEuclid (I := I) (M := M) α) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y =>
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                      (l (Fin.last m))) y)
                    (EuclideanSpace.single b 1) *
                  eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                    g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C * A := by
    intro a b
    have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α) :=
      (h_iter a).le_of_le (by omega)
    have h_factor_ae_zero :=
      eigenvectorChartIteratedPartial_unconditional_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))
    obtain ⟨h_mem, C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le
      (I := I) (M := M) α K (layerA_coeff_contDiffOn (I := I) (M := M)
        g α m l a b) h_factor_memWkp h_factor_ae_zero
    refine ⟨h_mem, C₀, hC₀_nn, le_trans hC₀ ?_⟩
    gcongr
    refine le_trans (wkpNorm_iteratedPartial_succ_le_unconditional
      (I := I) (M := M) g r s i α P₀ m K l a) ?_
    rw [hA_def, diffNumeratorAggregateK_unconditional]
    refine le_trans (Finset.single_le_sum (f := fun a =>
      wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α))
      (fun k _ => zero_le _) (Finset.mem_univ a)) ?_
    exact le_trans le_self_add (le_trans le_self_add le_self_add)
  have h_inner : ∀ a : Fin (Module.finrank ℝ E),
      (MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => ∑ b : Fin (Module.finrank ℝ E),
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                  (l (Fin.last m))) y)
                (EuclideanSpace.single b 1) *
              eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
          (chartTargetEuclid (I := I) (M := M) α)) ∧
        _ := fun a =>
    ⟨memWkp_finset_sum (I := I) (M := M)
      (α := α) (K := K) (s := Finset.univ)
      (f := fun b y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      (fun b _ => (h_pair a b).1),
    wkpNorm_sum_le_const_mul_aggregate (I := I) (M := M)
      (α := α) (K := K)
      (fun b y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      A (fun b => (h_pair a b).1) (fun b => (h_pair a b).2)⟩
  exact ⟨memWkp_finset_sum (I := I) (M := M)
    (α := α) (K := K) (s := Finset.univ)
    (f := fun a y => ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
    (fun a _ => (h_inner a).1),
  wkpNorm_sum_le_const_mul_aggregate (I := I) (M := M)
    (α := α) (K := K)
    (fun a y => ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
    A (fun a => (h_inner a).1) (fun a => (h_inner a).2)⟩

/-- Chart-locality-free twin of
`eigenvectorChartRHSDiffNumerator_layerB_wkpNorm_le`. -/
private lemma eigenvectorChartRHSDiffNumerator_layerB_wkpNorm_le_unconditional
    (fChartEffPrev : EuclN → ℝ)
    (h_iter : ∀ a : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α) y)
        (chartTargetEuclid (I := I) (M := M) α) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E),
                weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m)) y *
                  chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                    (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                      g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                    (chartTargetEuclid (I := I) (M := M) α) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK_unconditional (I := I) (M := M)
              g r s i α P₀ m K l fChartEffPrev := by
  classical
  set A := diffNumeratorAggregateK_unconditional (I := I) (M := M)
    g r s i α P₀ m K l fChartEffPrev with hA_def
  have h_pair : ∀ a b : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) K 2
          (fun y =>
            weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α) y)
          (chartTargetEuclid (I := I) (M := M) α) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y =>
                weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m)) y *
                  chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                    (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                      g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                    (chartTargetEuclid (I := I) (M := M) α) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C * A := by
    intro a b
    have h_inner_memWkp_succ : MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α) :=
      (h_iter a).le_of_le (by omega)
    have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
      h_inner_memWkp_succ.chosenWeakPartial_mem b
    have h_inner_ae :=
      eigenvectorChartIteratedPartial_unconditional_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))
    have h_factor_ae_zero :=
      chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
        (I := I) (M := M) α h_inner_ae b
    obtain ⟨h_mem, C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le
      (I := I) (M := M) α K
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m)))
      h_factor_memWkp h_factor_ae_zero
    refine ⟨h_mem, C₀, hC₀_nn, le_trans hC₀ ?_⟩
    gcongr
    refine le_trans (wkpNorm_chosenWeakPartial_iteratedPartial_succ_le_unconditional
      (I := I) (M := M) g r s i α P₀ m K l a b) ?_
    rw [hA_def, diffNumeratorAggregateK_unconditional]
    refine le_trans (Finset.single_le_sum (f := fun a =>
      wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α))
      (fun k _ => zero_le _) (Finset.mem_univ a)) ?_
    exact le_trans le_self_add (le_trans le_self_add le_self_add)
  have h_inner : ∀ a : Fin (Module.finrank ℝ E),
      (MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => ∑ b : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α) y)
          (chartTargetEuclid (I := I) (M := M) α)) ∧
        _ := fun a =>
    ⟨memWkp_finset_sum (I := I) (M := M)
      (α := α) (K := K) (s := Finset.univ)
      (f := fun b y =>
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y)
      (fun b _ => (h_pair a b).1),
    wkpNorm_sum_le_const_mul_aggregate (I := I) (M := M)
      (α := α) (K := K)
      (fun b y =>
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y)
      A (fun b => (h_pair a b).1) (fun b => (h_pair a b).2)⟩
  exact ⟨memWkp_finset_sum (I := I) (M := M)
    (α := α) (K := K) (s := Finset.univ)
    (f := fun a y => ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y)
    (fun a _ => (h_inner a).1),
  wkpNorm_sum_le_const_mul_aggregate (I := I) (M := M)
    (α := α) (K := K)
    (fun a y => ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y)
    A (fun a => (h_inner a).1) (fun a => (h_inner a).2)⟩

/-- Chart-locality-free twin of
`eigenvectorChartRHSDiffNumerator_layerC_wkpNorm_le`. -/
private lemma eigenvectorChartRHSDiffNumerator_layerC_wkpNorm_le_unconditional
    (fChartEffPrev : EuclN → ℝ)
    (h_iter_m : MemWkp (d := Module.finrank ℝ E) (2 + K) 2
      (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
        g r s i α P₀ m (Fin.init l))
      (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (fun y =>
          densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
            eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ m (Fin.init l) y)
        (chartTargetEuclid (I := I) (M := M) α) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y =>
              densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
                eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                  g r s i α P₀ m (Fin.init l) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK_unconditional (I := I) (M := M)
              g r s i α P₀ m K l fChartEffPrev := by
  classical
  set A := diffNumeratorAggregateK_unconditional (I := I) (M := M)
    g r s i α P₀ m K l fChartEffPrev with hA_def
  have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
        g r s i α P₀ m (Fin.init l))
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_iter_m.le_of_le (by omega)
  have h_factor_ae_zero :=
    eigenvectorChartIteratedPartial_unconditional_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P₀ m (Fin.init l)
  obtain ⟨h_mem, C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le
    (I := I) (M := M) α K
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
    h_factor_memWkp h_factor_ae_zero
  refine ⟨h_mem, C₀, hC₀_nn, le_trans hC₀ ?_⟩
  gcongr
  refine le_trans (wkpNorm_iteratedPartial_le_unconditional
    (I := I) (M := M) g r s i α P₀ m K l) ?_
  rw [hA_def, diffNumeratorAggregateK_unconditional]
  exact le_trans le_add_self (le_trans le_self_add le_self_add)

/-- Chart-locality-free twin of
`eigenvectorChartRHSDiffNumerator_layerD_wkpNorm_le`. -/
private lemma eigenvectorChartRHSDiffNumerator_layerD_wkpNorm_le_unconditional
    {fChartEffPrev : EuclN → ℝ}
    (h_prev : MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (fun y =>
          densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
            fChartEffPrev y)
        (chartTargetEuclid (I := I) (M := M) α) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y =>
              densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
                fChartEffPrev y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK_unconditional (I := I) (M := M)
              g r s i α P₀ m K l fChartEffPrev := by
  classical
  set A := diffNumeratorAggregateK_unconditional (I := I) (M := M)
    g r s i α P₀ m K l fChartEffPrev with hA_def
  have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 fChartEffPrev
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_prev.le_of_le (by omega)
  obtain ⟨h_mem, C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le
    (I := I) (M := M) α K
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
    h_factor_memWkp h_prev_zero
  refine ⟨h_mem, C₀, hC₀_nn, le_trans hC₀ ?_⟩
  gcongr
  rw [hA_def, diffNumeratorAggregateK_unconditional]
  exact le_add_self

/-- Chart-locality-free twin of
`eigenvectorChartRHSDiffNumerator_layerE_wkpNorm_le`. -/
private lemma eigenvectorChartRHSDiffNumerator_layerE_wkpNorm_le_unconditional
    {fChartEffPrev : EuclN → ℝ}
    (h_prev : MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (fun y =>
          densityOnEuclid (I := I) g α y *
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
              fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y)
        (chartTargetEuclid (I := I) (M := M) α) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y =>
              densityOnEuclid (I := I) g α y *
                chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
                  fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK_unconditional (I := I) (M := M)
              g r s i α P₀ m K l fChartEffPrev := by
  classical
  set A := diffNumeratorAggregateK_unconditional (I := I) (M := M)
    g r s i α P₀ m K l fChartEffPrev with hA_def
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        fChartEffPrev (chartTargetEuclid (I := I) (M := M) α))
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_prev.chosenWeakPartial_mem (l (Fin.last m))
  have h_factor_ae_zero :=
    chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
      (I := I) (M := M) α h_prev_zero (l (Fin.last m))
  obtain ⟨h_mem, C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le
    (I := I) (M := M) α K
    (densityOnEuclid_contDiffOn (I := I) g α)
    h_factor_memWkp h_factor_ae_zero
  refine ⟨h_mem, C₀, hC₀_nn, le_trans hC₀ ?_⟩
  gcongr
  refine le_trans (wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E)
    K hΩ_open _ (l (Fin.last m))) ?_
  rw [hA_def, diffNumeratorAggregateK_unconditional]
  exact le_trans le_add_self le_self_add

end LayerBoundsUnconditional

/-! ### The chart-locality-free headline `K`-graded explicit-norm `wkpNorm`
bound -/

section MainBoundUnconditional

/-- Chart-locality-free twin of `eigenvectorChartRHSDiffNumerator_wkpNorm_le`. -/
theorem eigenvectorChartRHSDiffNumerator_wkpNorm_le_unconditional
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
          (eigenvectorChartRHSDiffNumerator_unconditional (I := I) (M := M)
            g r s i α P₀ m l fChartEffPrev)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregateK_unconditional (I := I) (M := M)
            g r s i α P₀ m K l fChartEffPrev := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set A := diffNumeratorAggregateK_unconditional (I := I) (M := M)
    g r s i α P₀ m K l fChartEffPrev with hA_def
  set layerA : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y with hlayerA_def
  set layerB : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y with hlayerB_def
  set layerC : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
        g r s i α P₀ m (Fin.init l) y with hlayerC_def
  set layerD : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      fChartEffPrev y with hlayerD_def
  set layerE : EuclN → ℝ := fun y =>
    densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y
    with hlayerE_def
  have h_num_eq : eigenvectorChartRHSDiffNumerator_unconditional (I := I) (M := M)
      g r s i α P₀ m l fChartEffPrev =
      fun y => layerA y + layerB y - layerC y + layerD y + layerE y := by
    funext y
    rw [eigenvectorChartRHSDiffNumerator_unconditional]
  obtain ⟨hA_mem, CA, hCA_nn, hCA⟩ :=
    eigenvectorChartRHSDiffNumerator_layerA_wkpNorm_le_unconditional
      (I := I) (M := M) g r s i α P₀ m K l fChartEffPrev
      (fun a => h_iter (m + 1) (Fin.cons a (Fin.init l)))
  obtain ⟨hB_mem, CB, hCB_nn, hCB⟩ :=
    eigenvectorChartRHSDiffNumerator_layerB_wkpNorm_le_unconditional
      (I := I) (M := M) g r s i α P₀ m K l fChartEffPrev
      (fun a => h_iter (m + 1) (Fin.cons a (Fin.init l)))
  obtain ⟨hC_mem, CC, hCC_nn, hCC⟩ :=
    eigenvectorChartRHSDiffNumerator_layerC_wkpNorm_le_unconditional
      (I := I) (M := M) g r s i α P₀ m K l fChartEffPrev
      (h_iter m (Fin.init l))
  obtain ⟨hD_mem, CD, hCD_nn, hCD⟩ :=
    eigenvectorChartRHSDiffNumerator_layerD_wkpNorm_le_unconditional
      (I := I) (M := M) g r s i α P₀ m K l h_prev h_prev_zero
  obtain ⟨hE_mem, CE, hCE_nn, hCE⟩ :=
    eigenvectorChartRHSDiffNumerator_layerE_wkpNorm_le_unconditional
      (I := I) (M := M) g r s i α P₀ m K l h_prev h_prev_zero
  rw [← hΩ_def, ← hA_def] at hCA hCB hCC hCD hCE
  rw [← hΩ_def] at hA_mem hB_mem hC_mem hD_mem hE_mem
  refine ⟨CA + CB + CC + CD + CE, by positivity, ?_⟩
  rw [h_num_eq]
  set sAB : EuclN → ℝ := fun y => layerA y + layerB y with hsAB_def
  set sABC : EuclN → ℝ := fun y => sAB y - layerC y with hsABC_def
  set sABCD : EuclN → ℝ := fun y => sABC y + layerD y with hsABCD_def
  have hAB_mem : MemWkp (d := Module.finrank ℝ E) K 2 sAB Ω :=
    MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open hA_mem hB_mem
  have hABC_mem : MemWkp (d := Module.finrank ℝ E) K 2 sABC Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) (by norm_num) hΩ_open hAB_mem hC_mem
  have hABCD_mem : MemWkp (d := Module.finrank ℝ E) K 2 sABCD Ω :=
    MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open hABC_mem hD_mem
  have h_sAB_le : wkpNorm (d := Module.finrank ℝ E) K 2 sAB Ω ≤
      wkpNorm (d := Module.finrank ℝ E) K 2 layerA Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerB Ω :=
    wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open hA_mem hB_mem
  have h_sABC_le : wkpNorm (d := Module.finrank ℝ E) K 2 sABC Ω ≤
      wkpNorm (d := Module.finrank ℝ E) K 2 sAB Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerC Ω :=
    wkpNorm_sub_le (d := Module.finrank ℝ E) hΩ_open hAB_mem hC_mem
  have h_sABCD_le : wkpNorm (d := Module.finrank ℝ E) K 2 sABCD Ω ≤
      wkpNorm (d := Module.finrank ℝ E) K 2 sABC Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerD Ω :=
    wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open hABC_mem hD_mem
  have h_split : (fun y => layerA y + layerB y - layerC y + layerD y
        + layerE y) = (fun y => sABCD y + layerE y) := by
    funext y
    rw [hsABCD_def, hsABC_def, hsAB_def]
  have h_tri :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => layerA y + layerB y - layerC y + layerD y + layerE y) Ω
        ≤ wkpNorm (d := Module.finrank ℝ E) K 2 layerA Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2 layerB Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2 layerC Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2 layerD Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2 layerE Ω := by
    rw [h_split]
    have h_outer : wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => sABCD y + layerE y) Ω ≤
        wkpNorm (d := Module.finrank ℝ E) K 2 sABCD Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2 layerE Ω :=
      wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        hABCD_mem hE_mem
    refine le_trans h_outer ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans h_sABCD_le ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans h_sABC_le ?_
    refine add_le_add ?_ (le_refl _)
    exact h_sAB_le
  refine le_trans h_tri ?_
  have h_five :
      wkpNorm (d := Module.finrank ℝ E) K 2 layerA Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerB Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerC Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerD Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerE Ω
      ≤ ENNReal.ofReal CA * A + ENNReal.ofReal CB * A + ENNReal.ofReal CC * A
        + ENNReal.ofReal CD * A + ENNReal.ofReal CE * A :=
    add_le_add (add_le_add (add_le_add (add_le_add hCA hCB) hCC) hCD) hCE
  refine le_trans h_five ?_
  rw [ENNReal.ofReal_add (by positivity) hCE_nn,
    ENNReal.ofReal_add (by positivity) hCD_nn,
    ENNReal.ofReal_add (by positivity) hCC_nn,
    ENNReal.ofReal_add hCA_nn hCB_nn]
  rw [add_mul, add_mul, add_mul, add_mul]

end MainBoundUnconditional

/-! ### The chart-locality-free uniform-constant per-layer `wkpNorm` bounds -/

section MainBoundUniformUnconditional

/-- Chart-locality-free twin of
`eigenvectorChartRHSDiffNumerator_layerA_wkpNorm_le_uniform`. -/
private lemma eigenvectorChartRHSDiffNumerator_layerA_wkpNorm_le_uniform_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_iter : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a : Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) :
    (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => ∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m))) y)
                  (EuclideanSpace.single b 1) *
                eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
          (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ a : Fin (Module.finrank ℝ E),
                ∑ b : Fin (Module.finrank ℝ E),
                  (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                        (l (Fin.last m))) y)
                      (EuclideanSpace.single b 1) *
                    eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                      g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C *
              diffNumeratorAggregateK_unconditional (I := I) (M := M)
                g r s i α P₀ m K l (fChartEffPrev i) := by
  classical
  have h_pair : ∀ a b : Fin (Module.finrank ℝ E),
      (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) K 2
            (fun y =>
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m))) y)
                  (EuclideanSpace.single b 1) *
                eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
            (chartTargetEuclid (I := I) (M := M) α)) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
            wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y =>
                  (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                        (l (Fin.last m))) y)
                      (EuclideanSpace.single b 1) *
                    eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                      g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
                (chartTargetEuclid (I := I) (M := M) α)
              ≤ ENNReal.ofReal C *
                diffNumeratorAggregateK_unconditional (I := I) (M := M)
                  g r s i α P₀ m K l (fChartEffPrev i) := by
    intro a b
    obtain ⟨C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le_uniform
      (I := I) (M := M) α K
      (layerA_coeff_contDiffOn (I := I) (M := M) g α m l a b)
    refine ⟨fun i => ?_, C₀, hC₀_nn, fun i => ?_⟩
    · exact (hC₀ _
        ((h_iter i a).le_of_le (by omega))
        (eigenvectorChartIteratedPartial_unconditional_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ (m + 1)
          (Fin.cons a (Fin.init l)))).1
    · refine le_trans ((hC₀ _
        ((h_iter i a).le_of_le (by omega))
        (eigenvectorChartIteratedPartial_unconditional_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ (m + 1)
          (Fin.cons a (Fin.init l)))).2) ?_
      gcongr
      refine le_trans (wkpNorm_iteratedPartial_succ_le_unconditional
        (I := I) (M := M) g r s i α P₀ m K l a) ?_
      rw [diffNumeratorAggregateK_unconditional]
      refine le_trans (Finset.single_le_sum (f := fun a =>
        wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α))
        (fun k _ => zero_le _) (Finset.mem_univ a)) ?_
      exact le_trans le_self_add (le_trans le_self_add le_self_add)
  have h_inner : ∀ a : Fin (Module.finrank ℝ E),
      (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) K 2
            (fun y => ∑ b : Fin (Module.finrank ℝ E),
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m))) y)
                  (EuclideanSpace.single b 1) *
                eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
            (chartTargetEuclid (I := I) (M := M) α)) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ b : Fin (Module.finrank ℝ E),
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                      (l (Fin.last m))) y)
                    (EuclideanSpace.single b 1) *
                  eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                    g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C *
              diffNumeratorAggregateK_unconditional (I := I) (M := M)
                g r s i α P₀ m K l (fChartEffPrev i) := fun a =>
    ⟨fun i => memWkp_finset_sum (I := I) (M := M)
      (α := α) (K := K) (s := Finset.univ)
      (f := fun b y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      (fun b _ => (h_pair a b).1 i),
    wkpNorm_sum_le_const_mul_aggregate_uniform (I := I) (M := M)
      (α := α) (K := K) (ι := Fin (Module.finrank ℝ E))
      (ν := TensorEigenIdx (I := I) (M := M) g r s)
      (fun b => fun i => fun y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      (fun i => diffNumeratorAggregateK_unconditional (I := I) (M := M)
        g r s i α P₀ m K l (fChartEffPrev i))
      (fun b i => (h_pair a b).1 i) (fun b => (h_pair a b).2)⟩
  exact ⟨fun i => memWkp_finset_sum (I := I) (M := M)
    (α := α) (K := K) (s := Finset.univ)
    (f := fun a y => ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
    (fun a _ => (h_inner a).1 i),
  wkpNorm_sum_le_const_mul_aggregate_uniform (I := I) (M := M)
    (α := α) (K := K) (ι := Fin (Module.finrank ℝ E))
    (ν := TensorEigenIdx (I := I) (M := M) g r s)
    (fun a => fun i => fun y => ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
    (fun i => diffNumeratorAggregateK_unconditional (I := I) (M := M)
      g r s i α P₀ m K l (fChartEffPrev i))
    (fun a i => (h_inner a).1 i) (fun a => (h_inner a).2)⟩

/-- Chart-locality-free twin of
`eigenvectorChartRHSDiffNumerator_layerB_wkpNorm_le_uniform`. -/
private lemma eigenvectorChartRHSDiffNumerator_layerB_wkpNorm_le_uniform_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_iter : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a : Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) :
    (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => ∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
                chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                  (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                    g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                  (chartTargetEuclid (I := I) (M := M) α) y)
          (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ a : Fin (Module.finrank ℝ E),
                ∑ b : Fin (Module.finrank ℝ E),
                  weightedInvGramDerivOnEuclid (I := I) g α a b
                      (l (Fin.last m)) y *
                    chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                      (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                        g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                      (chartTargetEuclid (I := I) (M := M) α) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C *
              diffNumeratorAggregateK_unconditional (I := I) (M := M)
                g r s i α P₀ m K l (fChartEffPrev i) := by
  classical
  have h_pair : ∀ a b : Fin (Module.finrank ℝ E),
      (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) K 2
            (fun y =>
              weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
                chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                  (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                    g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                  (chartTargetEuclid (I := I) (M := M) α) y)
            (chartTargetEuclid (I := I) (M := M) α)) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
            wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y =>
                  weightedInvGramDerivOnEuclid (I := I) g α a b
                      (l (Fin.last m)) y *
                    chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                      (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                        g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                      (chartTargetEuclid (I := I) (M := M) α) y)
                (chartTargetEuclid (I := I) (M := M) α)
              ≤ ENNReal.ofReal C *
                diffNumeratorAggregateK_unconditional (I := I) (M := M)
                  g r s i α P₀ m K l (fChartEffPrev i) := by
    intro a b
    obtain ⟨C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le_uniform
      (I := I) (M := M) α K
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m)))
    have h_factor : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        MemWkp (d := Module.finrank ℝ E) K 2
            (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
              (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
              (chartTargetEuclid (I := I) (M := M) α))
            (chartTargetEuclid (I := I) (M := M) α) ∧
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
              (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
              (chartTargetEuclid (I := I) (M := M) α)
            =ᵐ[(volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α \
                chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)) := by
      intro i
      refine ⟨((h_iter i a).le_of_le (by omega)).chosenWeakPartial_mem b, ?_⟩
      exact chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
        (I := I) (M := M) α
        (eigenvectorChartIteratedPartial_unconditional_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ (m + 1)
          (Fin.cons a (Fin.init l))) b
    refine ⟨fun i => (hC₀ _ (h_factor i).1 (h_factor i).2).1,
      C₀, hC₀_nn, fun i => ?_⟩
    refine le_trans ((hC₀ _ (h_factor i).1 (h_factor i).2).2) ?_
    gcongr
    refine le_trans (wkpNorm_chosenWeakPartial_iteratedPartial_succ_le_unconditional
      (I := I) (M := M) g r s i α P₀ m K l a b) ?_
    rw [diffNumeratorAggregateK_unconditional]
    refine le_trans (Finset.single_le_sum (f := fun a =>
      wkpNorm (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α))
      (fun k _ => zero_le _) (Finset.mem_univ a)) ?_
    exact le_trans le_self_add (le_trans le_self_add le_self_add)
  have h_inner : ∀ a : Fin (Module.finrank ℝ E),
      (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) K 2
            (fun y => ∑ b : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
                chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                  (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                    g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                  (chartTargetEuclid (I := I) (M := M) α) y)
            (chartTargetEuclid (I := I) (M := M) α)) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ b : Fin (Module.finrank ℝ E),
                weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m)) y *
                  chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                    (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                      g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                    (chartTargetEuclid (I := I) (M := M) α) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C *
              diffNumeratorAggregateK_unconditional (I := I) (M := M)
                g r s i α P₀ m K l (fChartEffPrev i) := fun a =>
    ⟨fun i => memWkp_finset_sum (I := I) (M := M)
      (α := α) (K := K) (s := Finset.univ)
      (f := fun b y =>
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y)
      (fun b _ => (h_pair a b).1 i),
    wkpNorm_sum_le_const_mul_aggregate_uniform (I := I) (M := M)
      (α := α) (K := K) (ι := Fin (Module.finrank ℝ E))
      (ν := TensorEigenIdx (I := I) (M := M) g r s)
      (fun b => fun i => fun y =>
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y)
      (fun i => diffNumeratorAggregateK_unconditional (I := I) (M := M)
        g r s i α P₀ m K l (fChartEffPrev i))
      (fun b i => (h_pair a b).1 i) (fun b => (h_pair a b).2)⟩
  exact ⟨fun i => memWkp_finset_sum (I := I) (M := M)
    (α := α) (K := K) (s := Finset.univ)
    (f := fun a y => ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y)
    (fun a _ => (h_inner a).1 i),
  wkpNorm_sum_le_const_mul_aggregate_uniform (I := I) (M := M)
    (α := α) (K := K) (ι := Fin (Module.finrank ℝ E))
    (ν := TensorEigenIdx (I := I) (M := M) g r s)
    (fun a => fun i => fun y => ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y)
    (fun i => diffNumeratorAggregateK_unconditional (I := I) (M := M)
      g r s i α P₀ m K l (fChartEffPrev i))
    (fun a i => (h_inner a).1 i) (fun a => (h_inner a).2)⟩

/-- Chart-locality-free twin of
`eigenvectorChartRHSDiffNumerator_layerC_wkpNorm_le_uniform`. -/
private lemma eigenvectorChartRHSDiffNumerator_layerC_wkpNorm_le_uniform_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_iter_m : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ m (Fin.init l))
        (chartTargetEuclid (I := I) (M := M) α)) :
    (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y =>
            densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
              eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ m (Fin.init l) y)
          (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y =>
                densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
                  eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                    g r s i α P₀ m (Fin.init l) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C *
              diffNumeratorAggregateK_unconditional (I := I) (M := M)
                g r s i α P₀ m K l (fChartEffPrev i) := by
  classical
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le_uniform
    (I := I) (M := M) α K
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
  have h_factor : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) K 2
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ m (Fin.init l))
          (chartTargetEuclid (I := I) (M := M) α) ∧
        eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ m (Fin.init l)
          =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α \
              chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)) := by
    intro i
    exact ⟨(h_iter_m i).le_of_le (by omega),
      eigenvectorChartIteratedPartial_unconditional_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ m (Fin.init l)⟩
  refine ⟨fun i => (hC₀ _ (h_factor i).1 (h_factor i).2).1,
    C₀, hC₀_nn, fun i => ?_⟩
  refine le_trans ((hC₀ _ (h_factor i).1 (h_factor i).2).2) ?_
  gcongr
  refine le_trans (wkpNorm_iteratedPartial_le_unconditional
    (I := I) (M := M) g r s i α P₀ m K l) ?_
  rw [diffNumeratorAggregateK_unconditional]
  exact le_trans le_add_self (le_trans le_self_add le_self_add)

/-- Chart-locality-free twin of
`eigenvectorChartRHSDiffNumerator_layerD_wkpNorm_le_uniform`. -/
private lemma eigenvectorChartRHSDiffNumerator_layerD_wkpNorm_le_uniform_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_prev : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      (fChartEffPrev i) =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y =>
            densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
              fChartEffPrev i y)
          (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y =>
                densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
                  fChartEffPrev i y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C *
              diffNumeratorAggregateK_unconditional (I := I) (M := M)
                g r s i α P₀ m K l (fChartEffPrev i) := by
  classical
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le_uniform
    (I := I) (M := M) α K
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
  have h_factor : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) K 2 (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α) := fun i =>
    (h_prev i).le_of_le (by omega)
  refine ⟨fun i => (hC₀ _ (h_factor i) (h_prev_zero i)).1,
    C₀, hC₀_nn, fun i => ?_⟩
  refine le_trans ((hC₀ _ (h_factor i) (h_prev_zero i)).2) ?_
  gcongr
  rw [diffNumeratorAggregateK_unconditional]
  exact le_add_self

/-- Chart-locality-free twin of
`eigenvectorChartRHSDiffNumerator_layerE_wkpNorm_le_uniform`. -/
private lemma eigenvectorChartRHSDiffNumerator_layerE_wkpNorm_le_uniform_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_prev : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      (fChartEffPrev i) =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y =>
            densityOnEuclid (I := I) g α y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
                (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α) y)
          (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y =>
                densityOnEuclid (I := I) g α y *
                  chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
                    (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C *
              diffNumeratorAggregateK_unconditional (I := I) (M := M)
                g r s i α P₀ m K l (fChartEffPrev i) := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le_uniform
    (I := I) (M := M) α K
    (densityOnEuclid_contDiffOn (I := I) g α)
  have h_factor : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) K 2
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
            (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α))
          (chartTargetEuclid (I := I) (M := M) α) ∧
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
            (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α)
          =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α \
              chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)) := by
    intro i
    refine ⟨(h_prev i).chosenWeakPartial_mem (l (Fin.last m)), ?_⟩
    exact chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
      (I := I) (M := M) α (h_prev_zero i) (l (Fin.last m))
  refine ⟨fun i => (hC₀ _ (h_factor i).1 (h_factor i).2).1,
    C₀, hC₀_nn, fun i => ?_⟩
  refine le_trans ((hC₀ _ (h_factor i).1 (h_factor i).2).2) ?_
  gcongr
  refine le_trans (wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E)
    K hΩ_open _ (l (Fin.last m))) ?_
  rw [diffNumeratorAggregateK_unconditional]
  exact le_trans le_add_self le_self_add

/-- Chart-locality-free twin of
`eigenvectorChartRHSDiffNumerator_wkpNorm_le_uniform`. -/
theorem eigenvectorChartRHSDiffNumerator_wkpNorm_le_uniform_unconditional
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
            (eigenvectorChartRHSDiffNumerator_unconditional (I := I) (M := M)
              g r s i α P₀ m l (fChartEffPrev i))
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK_unconditional (I := I) (M := M)
              g r s i α P₀ m K l (fChartEffPrev i) := by
  classical
  obtain ⟨hA_mem, CA, hCA_nn, hCA⟩ :=
    eigenvectorChartRHSDiffNumerator_layerA_wkpNorm_le_uniform_unconditional
      (I := I) (M := M) g r s α P₀ m K l fChartEffPrev
      (fun i a => h_iter i (m + 1) (Fin.cons a (Fin.init l)))
  obtain ⟨hB_mem, CB, hCB_nn, hCB⟩ :=
    eigenvectorChartRHSDiffNumerator_layerB_wkpNorm_le_uniform_unconditional
      (I := I) (M := M) g r s α P₀ m K l fChartEffPrev
      (fun i a => h_iter i (m + 1) (Fin.cons a (Fin.init l)))
  obtain ⟨hC_mem, CC, hCC_nn, hCC⟩ :=
    eigenvectorChartRHSDiffNumerator_layerC_wkpNorm_le_uniform_unconditional
      (I := I) (M := M) g r s α P₀ m K l fChartEffPrev
      (fun i => h_iter i m (Fin.init l))
  obtain ⟨hD_mem, CD, hCD_nn, hCD⟩ :=
    eigenvectorChartRHSDiffNumerator_layerD_wkpNorm_le_uniform_unconditional
      (I := I) (M := M) g r s α P₀ m K l fChartEffPrev h_prev h_prev_zero
  obtain ⟨hE_mem, CE, hCE_nn, hCE⟩ :=
    eigenvectorChartRHSDiffNumerator_layerE_wkpNorm_le_uniform_unconditional
      (I := I) (M := M) g r s α P₀ m K l fChartEffPrev h_prev h_prev_zero
  refine ⟨CA + CB + CC + CD + CE, by positivity, fun i => ?_⟩
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set A := diffNumeratorAggregateK_unconditional (I := I) (M := M)
    g r s i α P₀ m K l (fChartEffPrev i) with hA_def
  set layerA : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial_unconditional (I := I) (M := M) g r s i α P₀
          (m + 1) (Fin.cons a (Fin.init l)) y with hlayerA_def
  set layerB : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y with hlayerB_def
  set layerC : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      eigenvectorChartIteratedPartial_unconditional (I := I) (M := M) g r s i α P₀
        m (Fin.init l) y with hlayerC_def
  set layerD : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      fChartEffPrev i y with hlayerD_def
  set layerE : EuclN → ℝ := fun y =>
    densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α) y
    with hlayerE_def
  have h_num_eq : eigenvectorChartRHSDiffNumerator_unconditional (I := I) (M := M)
      g r s i α P₀ m l (fChartEffPrev i) =
      fun y => layerA y + layerB y - layerC y + layerD y + layerE y := by
    funext y
    rw [eigenvectorChartRHSDiffNumerator_unconditional]
  have hA_mem_i := hA_mem i
  have hB_mem_i := hB_mem i
  have hC_mem_i := hC_mem i
  have hD_mem_i := hD_mem i
  have hE_mem_i := hE_mem i
  have hCA_i := hCA i
  have hCB_i := hCB i
  have hCC_i := hCC i
  have hCD_i := hCD i
  have hCE_i := hCE i
  rw [← hA_def] at hCA_i hCB_i hCC_i hCD_i hCE_i
  rw [← hlayerA_def] at hA_mem_i hCA_i
  rw [← hlayerB_def] at hB_mem_i hCB_i
  rw [← hlayerC_def] at hC_mem_i hCC_i
  rw [← hlayerD_def] at hD_mem_i hCD_i
  rw [← hlayerE_def] at hE_mem_i hCE_i
  rw [h_num_eq]
  set sAB : EuclN → ℝ := fun y => layerA y + layerB y with hsAB_def
  set sABC : EuclN → ℝ := fun y => sAB y - layerC y with hsABC_def
  set sABCD : EuclN → ℝ := fun y => sABC y + layerD y with hsABCD_def
  have hAB_mem : MemWkp (d := Module.finrank ℝ E) K 2 sAB Ω :=
    MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open hA_mem_i hB_mem_i
  have hABC_mem : MemWkp (d := Module.finrank ℝ E) K 2 sABC Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) (by norm_num) hΩ_open hAB_mem hC_mem_i
  have hABCD_mem : MemWkp (d := Module.finrank ℝ E) K 2 sABCD Ω :=
    MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open hABC_mem hD_mem_i
  have h_sAB_le : wkpNorm (d := Module.finrank ℝ E) K 2 sAB Ω ≤
      wkpNorm (d := Module.finrank ℝ E) K 2 layerA Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerB Ω :=
    wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      hA_mem_i hB_mem_i
  have h_sABC_le : wkpNorm (d := Module.finrank ℝ E) K 2 sABC Ω ≤
      wkpNorm (d := Module.finrank ℝ E) K 2 sAB Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerC Ω :=
    wkpNorm_sub_le (d := Module.finrank ℝ E) hΩ_open hAB_mem hC_mem_i
  have h_sABCD_le : wkpNorm (d := Module.finrank ℝ E) K 2 sABCD Ω ≤
      wkpNorm (d := Module.finrank ℝ E) K 2 sABC Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerD Ω :=
    wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      hABC_mem hD_mem_i
  have h_split : (fun y => layerA y + layerB y - layerC y + layerD y
        + layerE y) = (fun y => sABCD y + layerE y) := by
    funext y
    rw [hsABCD_def, hsABC_def, hsAB_def]
  have h_tri :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => layerA y + layerB y - layerC y + layerD y + layerE y) Ω
        ≤ wkpNorm (d := Module.finrank ℝ E) K 2 layerA Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2 layerB Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2 layerC Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2 layerD Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2 layerE Ω := by
    rw [h_split]
    have h_outer : wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => sABCD y + layerE y) Ω ≤
        wkpNorm (d := Module.finrank ℝ E) K 2 sABCD Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2 layerE Ω :=
      wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        hABCD_mem hE_mem_i
    refine le_trans h_outer ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans h_sABCD_le ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans h_sABC_le ?_
    refine add_le_add ?_ (le_refl _)
    exact h_sAB_le
  refine le_trans h_tri ?_
  have h_five :
      wkpNorm (d := Module.finrank ℝ E) K 2 layerA Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerB Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerC Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerD Ω
        + wkpNorm (d := Module.finrank ℝ E) K 2 layerE Ω
      ≤ ENNReal.ofReal CA * A + ENNReal.ofReal CB * A + ENNReal.ofReal CC * A
        + ENNReal.ofReal CD * A + ENNReal.ofReal CE * A :=
    add_le_add (add_le_add (add_le_add (add_le_add hCA_i hCB_i) hCC_i) hCD_i)
      hCE_i
  refine le_trans h_five ?_
  rw [ENNReal.ofReal_add (by positivity) hCE_nn,
    ENNReal.ofReal_add (by positivity) hCD_nn,
    ENNReal.ofReal_add (by positivity) hCC_nn,
    ENNReal.ofReal_add hCA_nn hCB_nn]
  rw [add_mul, add_mul, add_mul, add_mul]

end MainBoundUniformUnconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
