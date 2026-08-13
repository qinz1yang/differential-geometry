import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.FineChartCover
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconv
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Analysis.Sobolev.Chart

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [I.Boundaryless]
      [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
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
                  (DifferentialGeometry.Geometry.Operator.chartGramOnE
                    (I := I) (gSeq k) α i j) (extChartAt I α y)‖ ≤ C := by
  classical
  obtain ⟨r₀, hr₀, hcollar, hbufferCpt, hbufferSrc⟩ :=
    exists_chartBuffer_of_continuousOn (extChartAt I α)
      (continuousOn_extChartAt α) (continuousOn_extChartAt_symm α)
      (isOpen_extChartAt_target α) hK hKsrc
  have hbufferChart :
      chartBuffer (extChartAt I α) K r₀ ⊆ (chartAt H α).source := by
    intro y hy
    have hy' : y ∈ (extChartAt I α).source := hbufferSrc hy
    simpa only [extChartAt_source] using hy'
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

omit [NeZero (Module.finrank ℝ E)] in
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
              (DifferentialGeometry.Geometry.Operator.chartGramOnE
                (I := I) (gSeq k) α i j) (extChartAt I α y)‖ ≤ C := by
  classical
  have hper : ∀ z : S, ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ι,
        ∀ y ∈ chartClosedBall (extChartAt I α)
          ((extChartAt I α) (z.1 : K)) (2 * ε),
          ∀ i j : Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ r
              (DifferentialGeometry.Geometry.Operator.chartGramOnE
                (I := I) (gSeq k) α i j) (extChartAt I α y)‖ ≤ C := by
    intro z
    let Kc : Set M := chartClosedBall (extChartAt I α)
      ((extChartAt I α) (z.1 : K)) (2 * ε)
    have hKc : IsCompact Kc :=
      chartClosedBall_cpt_of_continuousOn (extChartAt I α)
        ((extChartAt I α) (z.1 : K)) (2 * ε)
        (continuousOn_extChartAt_symm α) (houter z)
    have hKsrc : Kc ⊆ (chartAt H α).source := by
      intro y hy
      have hy' : y ∈ (extChartAt I α).source :=
        chartClosedBall_src (extChartAt I α)
          ((extChartAt I α) (z.1 : K)) (2 * ε) (houter z) hy
      simpa only [extChartAt_source] using hy'
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

omit [NeZero (Module.finrank ℝ E)] in
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
              (DifferentialGeometry.Geometry.Operator.chartGramOnE
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
