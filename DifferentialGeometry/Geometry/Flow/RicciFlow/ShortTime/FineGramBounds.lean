import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.FineChartCover
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconv

/-!
# Uniform raw Gram jets on finite refined chart carriers

The small-carrier parametrix needs raw, unweighted chart-Gram coefficients on
the full closed outer coordinate balls, not only on the original canonical
partition support.  This file applies `chartGram_of_orders` separately on each
such compact pullback and takes a finite nonnegative sum of the resulting
constants.  The family-uniform covariant bounds are restricted directly from
`Set.univ`; no partition weight is divided out.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Analysis.Sobolev.Chart

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [I.Boundaryless]
      [T2Space M] [SigmaCompactSpace M]

/-- Non-circular coefficient preparation on a fixed chart carrier.  First a
positive coordinate collar radius `r₀` is chosen using only compactness and the
chart target.  Then one constant is obtained on the resulting fixed compact
buffer for every raw Gram jet of order at most three.  A later refinement may
choose its radius from this constant while requiring `r ≤ r₀`. -/
theorem bufferGram3_bnd
    {ι : Type*}
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (α : M) {K : Set M} (hK : IsCompact K)
    (hKsrc : K ⊆ (extChartAt I α).source)
    (B : ℝ)
    (hbdd : ∀ k : ι, ∀ q : ℕ, q ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ q (gSeq k) gRef B) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      ∃ C : ℝ, 0 ≤ C ∧
        Metric.cthickening r₀ ((extChartAt I α) '' K) ⊆
            (extChartAt I α).target ∧
          IsCompact (chartBuffer (extChartAt I α) K r₀) ∧
          chartBuffer (extChartAt I α) K r₀ ⊆ (chartAt H α).source ∧
          ∀ q : ℕ, q ≤ 3 → ∀ k : ι,
            ∀ y ∈ chartBuffer (extChartAt I α) K r₀,
              ∀ i j : Fin (Module.finrank ℝ E),
                ‖iteratedFDeriv ℝ q
                  (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE
                    (I := I) (gSeq k) α i j) (extChartAt I α y)‖ ≤ C := by
  classical
  obtain ⟨r₀, hr₀, hcollar, hbufferCpt, hbufferSrc⟩ :=
    exists_chartBuffer (I := I) (extChartAt I α) hK hKsrc
  have hbufferChart :
      chartBuffer (extChartAt I α) K r₀ ⊆ (chartAt H α).source := by
    intro y hy
    have hy' : y ∈ (extChartAt I α).source := hbufferSrc hy
    simpa only [extChartAt_source_eq_chartAt_source] using hy'
  choose Cq hCq hbound using fun q : Fin 4 =>
    chartGram_of_orders (I := I) gRef gSeq α hbufferCpt hbufferChart q.val B
      (fun k m hm y _hy => hbdd k m (by omega) y (Set.mem_univ y))
  let C : ℝ := ∑ q : Fin 4, Cq q
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun q _ => hCq q
  refine ⟨r₀, hr₀, C, hC, hcollar, hbufferCpt, hbufferChart, ?_⟩
  intro q hq k y hy i j
  let q' : Fin 4 := ⟨q, by omega⟩
  exact (hbound q' k y hy i j).trans
    (Finset.single_le_sum (fun m _ => hCq m) (Finset.mem_univ q'))

/-- Uniform order-`r` raw chart-Gram bound on a finite family of refined outer
closed balls.  The outer-ball hypothesis is purely chart geometry; the metric
bound itself is obtained by restricting the supplied `Set.univ` covariant
bound to each compact pullback. -/
theorem fineGram_of_orders
    {ι : Type*}
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (α : M) {K : Set M} (S : Finset K) (ε : ℝ)
    (houter : ∀ z : S,
      Metric.closedBall ((extChartAt I α) (z.1 : K)) (2 * ε) ⊆
        (extChartAt I α).target)
    (r : ℕ) (B : ℝ)
    (hbdd : ∀ k : ι, ∀ q : ℕ, q ≤ r →
      MetricCovDerivOrderBoundOn (I := I) Set.univ q (gSeq k) gRef B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : S, ∀ k : ι,
        ∀ y ∈ chartClosedBall (extChartAt I α)
          ((extChartAt I α) (z.1 : K)) (2 * ε),
          ∀ i j : Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ r
              (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE
                (I := I) (gSeq k) α i j) (extChartAt I α y)‖ ≤ C := by
  classical
  have hper : ∀ z : S, ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ι,
        ∀ y ∈ chartClosedBall (extChartAt I α)
          ((extChartAt I α) (z.1 : K)) (2 * ε),
          ∀ i j : Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ r
              (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE
                (I := I) (gSeq k) α i j) (extChartAt I α y)‖ ≤ C := by
    intro z
    let Kc : Set M := chartClosedBall (extChartAt I α)
      ((extChartAt I α) (z.1 : K)) (2 * ε)
    have hKc : IsCompact Kc :=
      chartClosedBall_cpt (extChartAt I α)
        ((extChartAt I α) (z.1 : K)) (2 * ε) (houter z)
    have hKsrc : Kc ⊆ (chartAt H α).source := by
      intro y hy
      have hy' : y ∈ (extChartAt I α).source :=
        chartClosedBall_src (extChartAt I α)
          ((extChartAt I α) (z.1 : K)) (2 * ε) (houter z) hy
      simpa only [extChartAt_source_eq_chartAt_source] using hy'
    exact chartGram_of_orders (I := I) gRef gSeq α hKc hKsrc r B
      (fun k q hq y _hy => hbdd k q hq y (Set.mem_univ y))
  choose Cz hCz hbound using hper
  let C : ℝ := ∑ z : S, Cz z
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun z _ => hCz z
  refine ⟨C, hC, ?_⟩
  intro z k y hy i j
  exact (hbound z k y hy i j).trans
    (Finset.single_le_sum (fun w _ => hCz w) (Finset.mem_univ z))

/-- One family-uniform constant controls every raw chart-Gram jet of order at
most three on every finite refined outer closed ball. -/
theorem fineGram3_bnd
    {ι : Type*}
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (α : M) {K : Set M} (S : Finset K) (ε : ℝ)
    (houter : ∀ z : S,
      Metric.closedBall ((extChartAt I α) (z.1 : K)) (2 * ε) ⊆
        (extChartAt I α).target)
    (B : ℝ)
    (hbdd : ∀ k : ι, ∀ q : ℕ, q ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ q (gSeq k) gRef B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ q : ℕ, q ≤ 3 → ∀ z : S, ∀ k : ι,
        ∀ y ∈ chartClosedBall (extChartAt I α)
          ((extChartAt I α) (z.1 : K)) (2 * ε),
          ∀ i j : Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ q
              (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE
                (I := I) (gSeq k) α i j) (extChartAt I α y)‖ ≤ C := by
  classical
  choose Cq hCq hbound using fun q : Fin 4 =>
    fineGram_of_orders (I := I) gRef gSeq α S ε houter q.val B
      (fun k m hm => hbdd k m (by omega))
  let C : ℝ := ∑ q : Fin 4, Cq q
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun q _ => hCq q
  refine ⟨C, hC, ?_⟩
  intro q hq z k y hy i j
  let q' : Fin 4 := ⟨q, by omega⟩
  exact (hbound q' z k y hy i j).trans
    (Finset.single_le_sum (fun m _ => hCq m) (Finset.mem_univ q'))

end DifferentialGeometry.PDE.RicciFlow
