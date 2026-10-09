import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceScalarTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFirstLoss
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceForwardScalar
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingReciprocal

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u v
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Y : Type*} [TopologicalSpace Y] {I : ModelWithCorners ℝ E Y} [I.Boundaryless]
  {X : Type v} [TopologicalSpace X] [ChartedSpace Y X] [IsManifold I ∞ X]

theorem exists_first_event_incoming_chart_of_frequently_scalar_le_after_survival
    (J : X → (H.stage first).Carrier) (hJ : IsSmoothEmbedding I ThreeModel ∞ J)
    (next : Fin (H.eventCount + 1)) (hnext : first ≤ next)
    (hsurvived : range J ⊆ range (H.backwardSurvivorMap first next hnext first le_rfl hnext))
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hderiv : ∀ j : Fin H.eventCount, next ≤ j.castSucc → j.succ ≤ last →
      ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q < (H.event j).incoming.flow.scalar t x →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
          C * (H.event j).incoming.flow.scalar t x ^ 2)
    (hscalar : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc), next ≤ j.castSucc → j.succ ≤ last →
      ∀ (x : (H.stage j.castSucc).Carrier) (A : BackwardPointTrace H first j.castSucc hf x),
        A.point first le_rfl hf ∈ range J →
        ∃ B : ℝ, ∃ᶠ t in 𝓝[<] H.time j.succ, (H.event j).incoming.flow.scalar t x ≤ B)
    (hnot : ¬ range J ⊆ range (H.backwardSurvivorMap first last hle first le_rfl hle)) :
    ∃ (i : Fin H.eventCount) (hf : first ≤ i.castSucc), next ≤ i.castSucc ∧ i.succ ≤ last ∧
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
  have hnexti : next ≤ i.castSucc := by
    by_contra hnotnext
    have hinext : i.succ ≤ next := by
      have hlt : i.castSucc < next := lt_of_not_ge hnotnext
      exact hlt
    obtain ⟨z, hz⟩ := hsurvived (mem_range_self x)
    let A : BackwardPointTrace H first next hnext z.val := Classical.choice z.property
    let B : BackwardPointTrace H first i.castSucc hf (Φ x).val := Classical.choice (Φ x).property
    have hA := H.backwardSurvivorMap_eq_point first next hnext first le_rfl hnext z A
    have hB := H.backwardSurvivorMap_eq_point first i.castSucc hf first le_rfl hf (Φ x) B
    have hpoint : A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hinext) = (Φ x).val :=
      (A.restrictLast hf (i.castSucc_lt_succ.le.trans hinext)).endpoint_eq_of_point_first_eq B
        (hA.symm.trans (hz.trans ((hbirth x).symm.trans hB)))
    have hcross := A.crossing i hf hinext
    rw [hpoint] at hcross
    exact hx _ hcross
  have hterminal (z : X) : (Φ z).val ∈ (H.event i).incoming.terminalRegularRegion := by
    let A : BackwardPointTrace H first i.castSucc hf (Φ z).val := Classical.choice (Φ z).property
    have hA : A.point first le_rfl hf ∈ range J := by
      rw [← H.backwardSurvivorMap_eq_point first i.castSucc hf first le_rfl hf (Φ z) A,
        hbirth]
      exact mem_range_self z
    obtain ⟨B, hB⟩ := hscalar i hf hnexti hl (Φ z).val A hA
    exact (H.event i).incoming.mem_terminalRegularRegion_of_frequently_scalar_le
      hq (hderiv i hnexti hl) hB
  let Ξ : X → H.backwardSurvivorTerminalFace first i hf := fun z => ⟨Φ z, hterminal z⟩
  have hΞ : IsSmoothEmbedding I ThreeModel ∞ Ξ :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen I ThreeModel
      (H.backwardSurvivorTerminalFace first i hf) Ξ hΦ
  exact ⟨i, hf, hnexti, hl, hpast, Ξ, hΞ, hbirth, x, hx⟩


theorem exists_first_event_incoming_chart_of_frequently_scalar_le
    (J : X → (H.stage first).Carrier) (hJ : IsSmoothEmbedding I ThreeModel ∞ J)
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hderiv : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q < (H.event j).incoming.flow.scalar t x →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
          C * (H.event j).incoming.flow.scalar t x ^ 2)
    (hscalar : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc), j.succ ≤ last →
      ∀ (x : (H.stage j.castSucc).Carrier) (A : BackwardPointTrace H first j.castSucc hf x),
        A.point first le_rfl hf ∈ range J →
        ∃ B : ℝ, ∃ᶠ t in 𝓝[<] H.time j.succ, (H.event j).incoming.flow.scalar t x ≤ B)
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
  have hself : range J ⊆ range (H.backwardSurvivorMap first first le_rfl first le_rfl le_rfl) := by
    rintro _ ⟨x, rfl⟩
    let z : H.backwardSurvivorDomain first first le_rfl :=
      ⟨J x, ⟨BackwardPointTrace.singleton H first (J x)⟩⟩
    exact ⟨z, H.backwardSurvivorMap_last first first le_rfl z⟩
  obtain ⟨i, hf, _, hl, hrest⟩ :=
    H.exists_first_event_incoming_chart_of_frequently_scalar_le_after_survival first last hle J hJ
      first le_rfl hself hq hderiv (fun j hf _ hl => hscalar j hf hl) hnot
  exact ⟨i, hf, hl, hrest⟩

theorem exists_first_event_incoming_chart_of_scalar_bound_at_later_time
    (J : X → (H.stage first).Carrier) (hJ : IsSmoothEmbedding I ThreeModel ∞ J)
    (next : Fin H.eventCount) (hnext : first ≤ next.castSucc)
    (hsurvived : range J ⊆ range
      (H.backwardSurvivorMap first next.castSucc hnext first le_rfl hnext))
    {q Q τ : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hτ : τ ∈ Ico (H.time next.castSucc) (H.time next.succ))
    (hscalar : ∀ (x : (H.stage next.castSucc).Carrier)
      (A : BackwardPointTrace H first next.castSucc hnext x),
      A.point first le_rfl hnext ∈ range J → (H.event next).incoming.flow.scalar τ x ≤ Q)
    (hderiv : ∀ j : Fin H.eventCount, next.castSucc ≤ j.castSucc → j.succ ≤ last →
      ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q < (H.event j).incoming.flow.scalar t x →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
          C * (H.event j).incoming.flow.scalar t x ^ 2)
    (htime : 2 * C * (H.time last - τ) * Q ≤ 1)
    (hnot : ¬ range J ⊆ range (H.backwardSurvivorMap first last hle first le_rfl hle)) :
    ∃ (i : Fin H.eventCount) (hf : first ≤ i.castSucc), next.castSucc ≤ i.castSucc ∧ i.succ ≤ last ∧
      (∀ (k : Fin (H.eventCount + 1)) (hk : first ≤ k), k ≤ i.castSucc →
        range J ⊆ range (H.backwardSurvivorMap first k hk first le_rfl hk)) ∧
      ∃ Ξ : X → H.backwardSurvivorTerminalFace first i hf,
        IsSmoothEmbedding I ThreeModel ∞ Ξ ∧
        (∀ x, H.backwardSurvivorMap first i.castSucc hf first le_rfl hf (Ξ x).val = J x) ∧
        ∃ x : X, ∀ y : (H.stage i.succ).Carrier,
          ¬ (H.event i).RegularCrossing
            (H.backwardSurvivorTerminalFaceMap first i hf (Ξ x)).val y := by
  apply H.exists_first_event_incoming_chart_of_frequently_scalar_le_after_survival
    first last hle J hJ next.castSucc hnext hsurvived hq hderiv ?_ hnot
  intro j hf hnj hl x A hx
  have hj : next ≤ j := Fin.castSucc_le_castSucc_iff.mp hnj
  have htauj : τ < H.time j.succ := hτ.2.trans_le
    (H.time_strictMono.monotone (Fin.succ_le_succ_iff.mpr hj))
  have hAτ : (H.event next).incoming.flow.scalar τ (A.point next.castSucc hnext hnj) ≤ Q :=
    hscalar _ (A.restrictLast hnext hnj) hx
  refine ⟨2 * Q, Filter.Eventually.frequently ?_⟩
  filter_upwards [Ioo_mem_nhdsLT htauj, Ioo_mem_nhdsLT (H.event j).incoming.lt] with t htτ ht
  have hb := A.scalar_le_two_mul_of_earlier_scalar_le_at_time hq next j hnext hj le_rfl
    (fun k hk hkj => hderiv k hk
      ((Fin.succ_le_succ_iff.mpr (Fin.castSucc_le_castSucc_iff.mp hkj)).trans hl) _)
    hτ ⟨ht.1.le, ht.2⟩ htτ.1.le hqQ hAτ ?_
  · simpa only [A.endpoint_eq] using hb
  have hQ : 0 < Q := hq.trans_le hqQ
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (sub_le_sub_right (ht.2.le.trans (H.time_strictMono.monotone hl)) τ)
      (by positivity : 0 ≤ 2 * (C : ℝ))) hQ.le).trans htime

theorem exists_first_event_incoming_chart_of_scalar_bound_at_time
    (first : Fin H.eventCount) (last : Fin (H.eventCount + 1)) (hle : first.castSucc ≤ last)
    (J : X → (H.stage first.castSucc).Carrier) (hJ : IsSmoothEmbedding I ThreeModel ∞ J)
    {q Q τ : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hτ : τ ∈ Ico (H.time first.castSucc) (H.time first.succ))
    (hscalar : ∀ x, (H.event first).incoming.flow.scalar τ (J x) ≤ Q)
    (hderiv : ∀ j : Fin H.eventCount, first.castSucc ≤ j.castSucc → j.succ ≤ last →
      ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q < (H.event j).incoming.flow.scalar t x →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
          C * (H.event j).incoming.flow.scalar t x ^ 2)
    (htime : 2 * C * (H.time last - τ) * Q ≤ 1)
    (hnot : ¬ range J ⊆ range
      (H.backwardSurvivorMap first.castSucc last hle first.castSucc le_rfl hle)) :
    ∃ (i : Fin H.eventCount) (hf : first.castSucc ≤ i.castSucc), i.succ ≤ last ∧
      (∀ (k : Fin (H.eventCount + 1)) (hk : first.castSucc ≤ k), k ≤ i.castSucc →
        range J ⊆ range (H.backwardSurvivorMap first.castSucc k hk first.castSucc le_rfl hk)) ∧
      ∃ Ξ : X → H.backwardSurvivorTerminalFace first.castSucc i hf,
        IsSmoothEmbedding I ThreeModel ∞ Ξ ∧
        (∀ x, H.backwardSurvivorMap first.castSucc i.castSucc hf first.castSucc le_rfl hf
          (Ξ x).val = J x) ∧
        ∃ x : X, ∀ y : (H.stage i.succ).Carrier,
          ¬ (H.event i).RegularCrossing
            (H.backwardSurvivorTerminalFaceMap first.castSucc i hf (Ξ x)).val y := by
  have hself : range J ⊆ range
      (H.backwardSurvivorMap first.castSucc first.castSucc le_rfl first.castSucc le_rfl le_rfl) := by
    rintro _ ⟨x, rfl⟩
    let z : H.backwardSurvivorDomain first.castSucc first.castSucc le_rfl :=
      ⟨J x, ⟨BackwardPointTrace.singleton H first.castSucc (J x)⟩⟩
    exact ⟨z, H.backwardSurvivorMap_last first.castSucc first.castSucc le_rfl z⟩
  obtain ⟨i, hf, _, hl, hrest⟩ :=
    H.exists_first_event_incoming_chart_of_scalar_bound_at_later_time first.castSucc last hle
      J hJ first le_rfl hself hq hqQ hτ (by
        intro x A hx
        rw [A.endpoint_eq] at hx
        obtain ⟨z, rfl⟩ := hx
        exact hscalar z) hderiv htime hnot
  exact ⟨i, hf, hl, hrest⟩


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
  apply H.exists_first_event_incoming_chart_of_frequently_scalar_le
    first last hle J hJ hq hderiv ?_ hnot
  intro j hf hl x A hx
  obtain ⟨z, hz⟩ := hx
  refine ⟨2 * Q, ?_⟩
  apply Filter.Eventually.frequently
  filter_upwards [Ioo_mem_nhdsLT (H.event j).incoming.lt] with t ht
  apply A.scalar_incoming_le_two_mul_initial_of_time_sub_le
    (H.event j).incoming (H.event_initial j) x hq hqQ
    (fun k hk hkj => hderiv k hk (hkj.trans (j.castSucc_lt_succ.le.trans hl)) _)
    (hderiv j hf hl x) ?_ ⟨ht.1.le,ht.2⟩ ?_
  · rw [← hz]
    exact hscalar z
  · have hQ : 0 < Q := hq.trans_le hqQ
    have hdt : t - H.time first ≤ H.time last - H.time first :=
      sub_le_sub_right (ht.2.le.trans (H.time_strictMono.monotone hl)) _
    have hnonneg : 0 ≤ (C : ℝ) * Q := mul_nonneg C.coe_nonneg hQ.le
    have ht0 : 0 ≤ H.time last - H.time first := sub_nonneg.mpr (H.time_strictMono.monotone hle)
    nlinarith [mul_le_mul_of_nonneg_right hdt hnonneg, mul_nonneg hnonneg ht0]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
