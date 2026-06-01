import DifferentialGeometry.Analysis.Sobolev.Chart.Banach
import DifferentialGeometry.Analysis.Sobolev.Chart.Completeness
import DifferentialGeometry.Analysis.Sobolev.Chart.CompletenessAux
import DifferentialGeometry.Analysis.Sobolev.Chart.MeasurablePullback
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevBanach
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridge
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridgeUniform
import DifferentialGeometry.Analysis.Sobolev.Manifold.Rellich
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Manifold-side scaffolding for the Banach completeness of `W^{k,p}_chart(M)`

This file collects scaffolding lemmas tying together the existing chart-target
Euclidean Sobolev infrastructure (per-chart Banach completeness on Euclidean
chart targets, in `EuclideanIteratedSobolevBanach.lean`) and the manifold-side
pullback construction (`pullbackToManifold` in `MeasurablePullback.lean`),
needed to assemble a manifold limit for a Cauchy sequence in the chart-based
Sobolev space `WkpChart`.

The pieces developed here are:

1. The εδ-Cauchy condition on `wkpNormChart` derived from a Mathlib `CauchySeq`
   in the seminormed `WkpChart`.
2. The per-chart Cauchy property in Euclidean `wkpNorm` on each chart target.
3. The per-chart Euclidean Banach completeness application yielding, for each
   chart `α`, a Sobolev limit `chartLimit α : EuclN → ℝ` in
   `MemWkp k p (chartTargetEuclid α)`.
4. The manifold-side candidate limit
   `manifoldLimitFun(x) := Σ_{β ∈ chartAtlasPOU_finset} pullbackToManifold β
   (chartLimit β) (x)`,
   defined as a finite POU-pulled-back sum.
5. The pointwise per-iterate POU decomposition
   `wkpChartFun u (x) = Σ_β pullbackToManifold β (chartPushed β (wkpChartFun u))
   (x)`.

These structural pieces are correct and self-contained; they form the bridge
layer for the eventual `CompleteSpace (WkpChartQuot _)` instance, whose final
assembly relies on additional chart-transition Sobolev bounds (a quantitative
analogue of `wkpNorm_smul_smooth_bounded_le_one` valid at arbitrary `k` and
across chart-transition diffeomorphisms applied to weak-Sobolev inputs). That
final assembly is left to follow-up work.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

section
variable [NeZero (Module.finrank ℝ E)]

/-- A Mathlib `CauchySeq` of `WkpChart` elements yields the εδ-Cauchy condition
in `wkpNormChart` (ENNReal-valued). -/
theorem wkpNormChart_cauchy_of_seminormCauchySeq
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) g k p hp}
    (hf : CauchySeq f) :
    ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) g k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε := by
  intro ε hε_pos
  rw [Metric.cauchySeq_iff] at hf
  obtain ⟨N, hN⟩ := hf ε hε_pos
  refine ⟨N, ?_⟩
  intro m n hm hn
  have hdist := hN m hm n hn
  rw [dist_eq_norm] at hdist
  have h_norm_eq : ‖f m - f n‖ =
      (wkpNormChart (I := I) (M := M) g k p (wkpChartFun (f m - f n))).toReal := rfl
  rw [h_norm_eq] at hdist
  have h_sub_val :
      wkpChartFun (f m - f n) =
        fun x => wkpChartFun (f m) x - wkpChartFun (f n) x := by
    ext x; rfl
  rw [h_sub_val] at hdist
  have h_lt_top : wkpNormChart (I := I) (M := M) g k p
      (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) < ⊤ :=
    wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) g hp
      (MemWkpChart_sub (I := I) (M := M) g hp
        (wkpChartFun_memWkpChart (f m)) (wkpChartFun_memWkpChart (f n)))
  have h_ne_top : wkpNormChart (I := I) (M := M) g k p
      (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≠ ⊤ := h_lt_top.ne
  rw [← ENNReal.ofReal_toReal h_ne_top]
  exact ENNReal.ofReal_le_ofReal hdist.le

/-- For each chart `α`, the chart-pushed sequence is `wkpNorm`-Cauchy on
`chartTargetEuclid α`. -/
theorem chartPushed_cauchy_of_wkpNormChart_cauchy
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) g k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) g k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε)
    (α : M) :
    ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) k p
        (fun y => chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
          (wkpChartFun (f m)) y -
          chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
            (wkpChartFun (f n)) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤ ENNReal.ofReal ε := by
  intro ε hε_pos
  obtain ⟨N, hN⟩ := h_cauchy ε hε_pos
  refine ⟨N, ?_⟩
  intro m n hm hn
  have h_le := hN m n hm hn
  have h_chartPushed_eq : (fun y => chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        (wkpChartFun (f m)) y -
        chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
          (wkpChartFun (f n)) y) =
      chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) := by
    funext y
    unfold chartPushed
    ring
  rw [h_chartPushed_eq]
  unfold wkpNormChart at h_le
  have h_summand_le_tsum :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
          (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x))
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ∑' α' : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α'
            (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x))
          (chartTargetEuclid (I := I) (M := M) α') :=
    ENNReal.le_tsum α
  exact le_trans h_summand_le_tsum h_le

/-- For each chart `α`, the chart-pushed sequence has a `wkpNorm`-limit which
is itself in `MemWkp k p` of the chart target. -/
theorem exists_chart_limit
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) g k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) g k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε)
    (α : M) :
    ∃ v_α : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p v_α
        (chartTargetEuclid (I := I) (M := M) α) ∧
      Tendsto
        (fun n =>
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) k p
            (fun y => chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
              (wkpChartFun (f n)) y - v_α y)
            (chartTargetEuclid (I := I) (M := M) α))
        atTop (𝓝 0) := by
  have h_chart_cauchy := chartPushed_cauchy_of_wkpNormChart_cauchy
    (I := I) (M := M) (g := g) (hp := hp) h_cauchy α
  have h_chart_mem : ∀ n,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
          (wkpChartFun (f n)))
        (chartTargetEuclid (I := I) (M := M) α) := fun n =>
    (wkpChartFun_memWkpChart (f n)) α
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.exists_limit_of_wkpNorm_cauchy
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    k p hp_one hp_top h_chart_mem h_chart_cauchy

/-- A choice of per-chart Euclidean Sobolev limit for a given Cauchy sequence. -/
noncomputable def chartLimit
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) g k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) g k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε)
    (α : M) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  (exists_chart_limit (I := I) (M := M) g hp_one hp_top h_cauchy α).choose

/-- The chosen per-chart limit lies in `MemWkp k p` of the chart target. -/
lemma chartLimit_memWkp
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) g k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) g k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε)
    (α : M) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p
      (chartLimit (I := I) (M := M) hp_one hp_top h_cauchy α)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (exists_chart_limit (I := I) (M := M) g hp_one hp_top h_cauchy α).choose_spec.1

/-- The chart-pushed Cauchy sequence converges in `wkpNorm` to the chosen limit. -/
lemma chartLimit_tendsto
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) g k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) g k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε)
    (α : M) :
    Tendsto
      (fun n =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) k p
          (fun y => chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
            (wkpChartFun (f n)) y -
            chartLimit (I := I) (M := M) hp_one hp_top h_cauchy α y)
          (chartTargetEuclid (I := I) (M := M) α))
      atTop (𝓝 0) :=
  (exists_chart_limit (I := I) (M := M) g hp_one hp_top h_cauchy α).choose_spec.2

/-- The candidate manifold limit, defined as the finite POU-pulled-back sum of
the per-chart Euclidean Sobolev limits. The sum is over `chartAtlasPOU_finset`,
a finite set on a compact manifold. -/
noncomputable def manifoldLimitFun
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) g k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) g k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε) : M → ℝ :=
  fun x =>
    ∑ β ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M),
      pullbackToManifold (I := I) β
        (chartLimit (I := I) (M := M) hp_one hp_top h_cauchy β) x

/-- The per-iterate POU decomposition: on a compact manifold, `wkpChartFun u(x)`
equals the finite sum of the chart-β-pushed-and-pulled-back contributions over
`chartAtlasPOU_finset`. -/
lemma wkpChartFun_eq_finset_sum_pullback
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    (u : WkpChart (I := I) (M := M) g k p hp) :
    (fun x : M => wkpChartFun u x) =
      fun x =>
        ∑ β ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
            (I := I) (M := M),
          pullbackToManifold (I := I) β
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) β
              (wkpChartFun u)) x := by
  classical
  funext x
  have h_eq : ∀ β ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
        (I := I) (M := M),
      pullbackToManifold (I := I) β
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) β
            (wkpChartFun u)) x =
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x *
          wkpChartFun u x := by
    intro β _
    classical
    by_cases hxβ : x ∈ (chartAt H β).source
    · exact pullbackToManifold_chartPushed_apply_of_mem (I := I) β (wkpChartFun u) hxβ
    · rw [pullbackToManifold_apply_of_notMem (I := I) (α := β) _ hxβ]
      have h_subord :=
        DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate (I := I) (M := M)
      have h_tsupp : tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
          I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ (chartAt H β).source := h_subord β
      have h_x_notin : x ∉ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
          I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) := fun h => hxβ (h_tsupp h)
      have h_rho_zero :
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x = 0 :=
        image_eq_zero_of_notMem_tsupport h_x_notin
      rw [h_rho_zero]; ring
  rw [Finset.sum_congr rfl h_eq]
  have h_factor :
      ∑ β ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
        (I := I) (M := M),
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x *
          wkpChartFun u x =
      (∑ β ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
        (I := I) (M := M),
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x) *
        wkpChartFun u x := by
    rw [Finset.sum_mul]
  rw [h_factor]
  rw [chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x, one_mul]

end

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
