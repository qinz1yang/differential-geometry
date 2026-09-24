import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFirstLoss
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceForwardScalar
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget

noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u v
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Y : Type*} [TopologicalSpace Y] {I : ModelWithCorners ℝ E Y} [I.Boundaryless]
  {X : Type v} [TopologicalSpace X] [ChartedSpace Y X] [IsManifold I ∞ X]

theorem exists_first_event_incoming_chart_of_initial_scalar_bound
    (J : X → (H.stage first).Carrier) (hJ : IsSmoothEmbedding I ThreeModel ∞ J)
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hscalar : ∀ x, metricScalarAt (H.initialMetric first) (J x) ≤ Q)
    (hderiv : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q < (H.event j).incoming.flow.scalar t x →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
          C * (H.event j).incoming.flow.scalar t x ^ 2)
    (htime : 8 * C * (H.time last - H.time first) * Q ≤ 1)
    (hnot : ¬ range J ⊆ range (H.backwardSurvivorMap first last hle first le_rfl hle)) :
    ∃ (i : Fin H.eventCount) (hf : first ≤ i.castSucc), i.succ ≤ last ∧
      (∀ (k : Fin (H.eventCount + 1)) (hk : first ≤ k), k ≤ i.castSucc →
        range J ⊆ range (H.backwardSurvivorMap first k hk first le_rfl hk)) ∧
      ∃ Ξ : X → H.backwardSurvivorTerminalFace first i hf,
        IsSmoothEmbedding I ThreeModel ∞ Ξ ∧
        (∀ x, H.backwardSurvivorMap first i.castSucc hf first le_rfl hf (Ξ x).val = J x) ∧
        ∃ x : X, ∀ y : (H.stage i.succ).Carrier,
          ¬ (H.event i).RegularCrossing
            (H.backwardSurvivorTerminalFaceMap first i hf (Ξ x)).val y := by
  obtain ⟨i, hf, hl, hpast, Φ, hΦ, hbirth, x, hx⟩ :=
    H.exists_first_event_without_regularCrossing first last hle J hJ hnot
  have hterminal (z : X) : (Φ z).val ∈ (H.event i).incoming.terminalRegularRegion := by
    let A : BackwardPointTrace H first i.castSucc hf (Φ z).val := Classical.choice (Φ z).property
    apply A.mem_incoming_terminalRegularRegion_of_initial_scalar_bound
      (H.event i).incoming (H.event_initial i) (Φ z).val hq hqQ
      (fun j hj hji t ht hhigh => hderiv j hj (hji.trans (i.castSucc_lt_succ.le.trans hl))
        (A.point j.castSucc hj (j.castSucc_lt_succ.le.trans hji)) t ht hhigh)
      isOpen_univ (mem_univ _) (fun y _ => hderiv i hf hl y) ?_ ?_
    · rw [← H.backwardSurvivorMap_eq_point first i.castSucc hf first le_rfl hf (Φ z) A,
        hbirth]
      exact hscalar z
    · have hQ : 0 < Q := hq.trans_le hqQ
      have ht := H.time_strictMono.monotone hl
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sub_le_sub_right ht _) (by positivity : 0 ≤ 8 * (C : ℝ)))
          hQ.le).trans htime
  let Ξ : X → H.backwardSurvivorTerminalFace first i hf := fun z => ⟨Φ z, hterminal z⟩
  have hΞ : IsSmoothEmbedding I ThreeModel ∞ Ξ :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen I ThreeModel
      (H.backwardSurvivorTerminalFace first i hf) Ξ hΦ
  exact ⟨i, hf, hl, hpast, Ξ, hΞ, hbirth, x, hx⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
