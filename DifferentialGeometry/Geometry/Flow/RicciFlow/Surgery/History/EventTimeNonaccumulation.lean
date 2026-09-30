import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryEventVolumeBound

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable (time : ℕ → ℝ) (hzero : time 0 = 0)
  (stage : ℕ → OrientedThreeStage.{u}) (metric : (j : ℕ) → (stage j).Metric)
  (event : (j : ℕ) → MetricCutCapEvent (stage j) (stage (j + 1)) (time j) (time (j + 1)))
  (hinitial : ∀ j, (event j).incoming.flow.base.metric (time j) = metric j)
  (houtput : ∀ j, (event j).outputMetric = metric (j + 1))

private local instance (P : OrientedThreeStage.{u}) : MeasurableSpace P.Carrier := borel P.Carrier
private local instance (P : OrientedThreeStage.{u}) : BorelSpace P.Carrier := ⟨rfl⟩
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    MeasurableSpace G.terminalRegularOpen := borel G.terminalRegularOpen
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    BorelSpace G.terminalRegularOpen := ⟨rfl⟩
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

include event in
private theorem event_time_strictMono : StrictMono time :=
  strictMono_nat_of_lt_succ (fun j => (event j).incoming.lt)

private def eventPrefix (n : ℕ) : ObservedHistory.{u} where
  horizon := time n
  horizon_nonneg := hzero ▸ (event_time_strictMono time stage event).monotone (Nat.zero_le n)
  eventCount := n
  time := fun j => time j.val
  time_strictMono := fun _ _ h => (event_time_strictMono time stage event) h
  time_zero := hzero
  time_le_horizon := le_rfl
  stage := fun j => stage j.val
  initialMetric := fun j => metric j.val
  event := fun j => event j.val
  event_initial := fun j => hinitial j.val
  event_output := fun j => houtput j.val
  finalSlab h := False.elim (lt_irrefl _ h)
  final_initial h := False.elim (lt_irrefl _ h)

include hzero hinitial houtput in
theorem event_index_le_of_volume_debit {v K T : ℝ} (hv : 0 < v) (hK : 0 ≤ K)
    (hscalar : ∀ j : ℕ, time (j + 1) ≤ T → ∀ t ∈ Ico (time j) (time (j + 1)),
      ∀ x : (stage j).Carrier, -K ≤ metricScalarAt ((event j).incoming.flow.base.metric t) x)
    (hdebit : ∀ j : ℕ, time (j + 1) ≤ T →
      ∃ F : Set (event j).incoming.terminalRegularOpen, IsCompact F ∧
        riemannianVolumeMeasure ThreeModel (stage (j + 1)).Carrier (event j).outputMetric univ +
          ENNReal.ofReal ((Nat.card (event j).transition.trace.tubes.Index : ℝ) * v) ≤
        riemannianVolumeMeasure ThreeModel (event j).incoming.terminalRegularOpen
          (event j).terminal.metric F)
    {n : ℕ} (hn : time n ≤ T) :
    (n : ℝ) ≤ Nat.card (ConnectedComponents (stage 0).Carrier) +
      2 * (Real.exp (K * T) *
        (riemannianVolumeMeasure ThreeModel (stage 0).Carrier (metric 0) univ).toReal / v) := by
  let H := eventPrefix time hzero stage metric event hinitial houtput n
  have hb (j : Fin n) : time (j.val + 1) ≤ T :=
    ((event_time_strictMono time stage event).monotone (Nat.succ_le_of_lt j.isLt)).trans hn
  exact H.eventCount_le_card_initial_add_volume_bound hv hK hn
    (fun j => hscalar j.val (hb j)) (fun j => hdebit j.val (hb j))

include hzero hinitial houtput in
theorem finite_eventTimes_le_of_volume_debit {v K T : ℝ} (hv : 0 < v) (hK : 0 ≤ K)
    (hscalar : ∀ j : ℕ, time (j + 1) ≤ T → ∀ t ∈ Ico (time j) (time (j + 1)),
      ∀ x : (stage j).Carrier, -K ≤ metricScalarAt ((event j).incoming.flow.base.metric t) x)
    (hdebit : ∀ j : ℕ, time (j + 1) ≤ T →
      ∃ F : Set (event j).incoming.terminalRegularOpen, IsCompact F ∧
        riemannianVolumeMeasure ThreeModel (stage (j + 1)).Carrier (event j).outputMetric univ +
          ENNReal.ofReal ((Nat.card (event j).transition.trace.tubes.Index : ℝ) * v) ≤
        riemannianVolumeMeasure ThreeModel (event j).incoming.terminalRegularOpen
          (event j).terminal.metric F) :
    Set.Finite {j : ℕ | time (j + 1) ≤ T} := by
  let B := (Nat.card (ConnectedComponents (stage 0).Carrier) : ℝ) +
    2 * (Real.exp (K * T) *
      (riemannianVolumeMeasure ThreeModel (stage 0).Carrier (metric 0) univ).toReal / v)
  apply (Set.finite_Iic ⌈B⌉₊).subset
  intro j hj
  have h := event_index_le_of_volume_debit time hzero stage metric event
    hinitial houtput hv hK hscalar hdebit hj
  have hjB : (j : ℝ) ≤ B := by dsimp only [B]; push_cast at h; linarith
  exact_mod_cast hjB.trans (Nat.le_ceil B)

include hzero hinitial houtput in
theorem tendsto_eventTime_atTop_of_volume_debit
    (hcontrolled : ∀ T : ℝ, ∃ v K : ℝ, 0 < v ∧ 0 ≤ K ∧
      (∀ j : ℕ, time (j + 1) ≤ T → ∀ t ∈ Ico (time j) (time (j + 1)),
        ∀ x : (stage j).Carrier, -K ≤ metricScalarAt ((event j).incoming.flow.base.metric t) x) ∧
      ∀ j : ℕ, time (j + 1) ≤ T →
        ∃ F : Set (event j).incoming.terminalRegularOpen, IsCompact F ∧
          riemannianVolumeMeasure ThreeModel (stage (j + 1)).Carrier (event j).outputMetric univ +
            ENNReal.ofReal ((Nat.card (event j).transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel (event j).incoming.terminalRegularOpen
            (event j).terminal.metric F) :
    Tendsto time atTop atTop := by
  apply (event_time_strictMono time stage event).monotone.tendsto_atTop_atTop
  intro T
  obtain ⟨v,K,hv,hK,hscalar,hdebit⟩ := hcontrolled T
  let B := (Nat.card (ConnectedComponents (stage 0).Carrier) : ℝ) +
    2 * (Real.exp (K * T) *
      (riemannianVolumeMeasure ThreeModel (stage 0).Carrier (metric 0) univ).toReal / v)
  obtain ⟨n, hn⟩ := exists_nat_gt B
  refine ⟨n, le_of_not_gt ?_⟩
  intro ht
  have h := event_index_le_of_volume_debit time hzero stage metric event
    hinitial houtput hv hK hscalar hdebit ht.le
  exact (not_le_of_gt hn) h

include hzero hinitial houtput in
theorem event_index_le_of_cut_scale_upper_bound
    (scale : ℕ → ℝ) {Qmax K T : ℝ} (hQmax : 0 < Qmax) (hK : 0 ≤ K)
    (hscale : ∀ j : ℕ, time (j + 1) ≤ T → 0 < scale j ∧ scale j ≤ Qmax)
    (hscalar : ∀ j : ℕ, time (j + 1) ≤ T → ∀ t ∈ Ico (time j) (time (j + 1)),
      ∀ x : (stage j).Carrier, -K ≤ metricScalarAt ((event j).incoming.flow.base.metric t) x)
    (hdebit : ∀ j : ℕ, time (j + 1) ≤ T →
      ∃ F : Set (event j).incoming.terminalRegularOpen, IsCompact F ∧
        riemannianVolumeMeasure ThreeModel (stage (j + 1)).Carrier (event j).outputMetric univ +
          ENNReal.ofReal ((Nat.card (event j).transition.trace.tubes.Index : ℝ) *
            scale j ^ (-3 / 2 : ℝ)) ≤
        riemannianVolumeMeasure ThreeModel (event j).incoming.terminalRegularOpen
          (event j).terminal.metric F)
    {n : ℕ} (hn : time n ≤ T) :
    (n : ℝ) ≤ Nat.card (ConnectedComponents (stage 0).Carrier) +
      2 * (Real.exp (K * T) *
        (riemannianVolumeMeasure ThreeModel (stage 0).Carrier (metric 0) univ).toReal /
          Qmax ^ (-3 / 2 : ℝ)) := by
  apply event_index_le_of_volume_debit time hzero stage metric event hinitial houtput
    (Real.rpow_pos_of_pos hQmax _) hK hscalar _ hn
  intro j hj
  obtain ⟨F,hF,hvol⟩ := hdebit j hj
  refine ⟨F,hF,le_trans ?_ hvol⟩
  apply add_le_add_right
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Real.rpow_le_rpow_of_nonpos (hscale j hj).1 (hscale j hj).2 (by norm_num)

include hzero hinitial houtput in
theorem incoming_scalar_lower_of_event_preservation
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (metric 0) a₀ x)
    (hlower : ∀ x, -3 / a₀ ≤ metricScalarAt (metric 0) x)
    (hcurvature : ∀ j : ℕ, ∀ a : ℝ, 0 < a →
      (∀ x, InFixedHamiltonIveyRegion (event j).terminal.metric a x) →
      ∀ x, InFixedHamiltonIveyRegion (event j).outputMetric a x)
    (hpreserve : ∀ j : ℕ, ∀ B : ℝ, B ≤ 0 →
      (∀ x, B ≤ metricScalarAt (event j).terminal.metric x) →
      ∀ x, B ≤ metricScalarAt (event j).outputMetric x)
    (j : ℕ) {t : ℝ} (ht : t ∈ Ico (time j) (time (j + 1))) (x : (stage j).Carrier) :
    -(3 / a₀) ≤ metricScalarAt ((event j).incoming.flow.base.metric t) x := by
  let H := eventPrefix time hzero stage metric event hinitial houtput (j + 1)
  have hall := H.fixedHamiltonIveyRegion_and_scalar_lower_of_preservation
    (fun k => hcurvature k.val) (fun k => hpreserve k.val) ha₀ hfixed hlower
  have ht' : t ∈ H.stageDomain (Fin.last j).castSucc := by
    simp only [H, eventPrefix, ObservedHistory.stageDomain, Fin.lastCases_castSucc,
      Fin.val_last, Fin.val_castSucc, Fin.val_succ]
    exact ht
  have hmetric : H.stageMetric (Fin.last j).castSucc t =
      (event j).incoming.flow.base.metric t := by
    dsimp only [H, eventPrefix, ObservedHistory.stageMetric]
    rw [Fin.lastCases_castSucc]
    rfl
  have hlow := (hall.1 (Fin.last j).castSucc t ht' x).2
  rw [hmetric] at hlow
  have ht0 : 0 ≤ t :=
    (hzero ▸ (event_time_strictMono time stage event).monotone (Nat.zero_le j)).trans ht.1
  have hdiv : 3 / (a₀ + t) ≤ 3 / a₀ :=
    div_le_div_of_nonneg_left (by norm_num) ha₀ (by linarith)
  have hneg : -(3 / a₀) ≤ -3 / (a₀ + t) := by
    simpa only [neg_div] using neg_le_neg hdiv
  exact hneg.trans hlow

include hzero hinitial houtput in
theorem tendsto_eventTime_atTop_of_bounded_cut_scale
    (scale : ℕ → ℝ)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (metric 0) a₀ x)
    (hlower : ∀ x, -3 / a₀ ≤ metricScalarAt (metric 0) x)
    (hcurvature : ∀ j : ℕ, ∀ a : ℝ, 0 < a →
      (∀ x, InFixedHamiltonIveyRegion (event j).terminal.metric a x) →
      ∀ x, InFixedHamiltonIveyRegion (event j).outputMetric a x)
    (hpreserve : ∀ j : ℕ, ∀ B : ℝ, B ≤ 0 →
      (∀ x, B ≤ metricScalarAt (event j).terminal.metric x) →
      ∀ x, B ≤ metricScalarAt (event j).outputMetric x)
    (hscale : ∀ j, 0 < scale j)
    (hbound : ∀ T : ℝ, ∃ Qmax : ℝ, ∀ j, time (j + 1) ≤ T → scale j ≤ Qmax)
    (hdebit : ∀ j : ℕ,
      ∃ F : Set (event j).incoming.terminalRegularOpen, IsCompact F ∧
        riemannianVolumeMeasure ThreeModel (stage (j + 1)).Carrier (event j).outputMetric univ +
          ENNReal.ofReal ((Nat.card (event j).transition.trace.tubes.Index : ℝ) *
            scale j ^ (-3 / 2 : ℝ)) ≤
        riemannianVolumeMeasure ThreeModel (event j).incoming.terminalRegularOpen
          (event j).terminal.metric F) :
    Tendsto time atTop atTop := by
  apply (event_time_strictMono time stage event).monotone.tendsto_atTop_atTop
  intro T
  obtain ⟨Qmax,hQmax⟩ := hbound T
  let Q := max Qmax 1
  have hQ : 0 < Q := zero_lt_one.trans_le (le_max_right _ _)
  let B := (Nat.card (ConnectedComponents (stage 0).Carrier) : ℝ) +
    2 * (Real.exp ((3 / a₀) * T) *
      (riemannianVolumeMeasure ThreeModel (stage 0).Carrier (metric 0) univ).toReal /
        Q ^ (-3 / 2 : ℝ))
  obtain ⟨n,hn⟩ := exists_nat_gt B
  refine ⟨n,le_of_not_gt ?_⟩
  intro ht
  have hb := event_index_le_of_cut_scale_upper_bound time hzero stage metric event
    hinitial houtput scale hQ (by positivity : 0 ≤ 3 / a₀)
    (fun j hj => ⟨hscale j,(hQmax j hj).trans (le_max_left _ _)⟩)
    (fun j _ t ht x => incoming_scalar_lower_of_event_preservation time hzero
      stage metric event hinitial houtput ha₀ hfixed hlower hcurvature hpreserve j ht x)
    (fun j _ => hdebit j) ht.le
  exact (not_le_of_gt hn) hb

include hzero hinitial houtput in
theorem not_tendsto_eventTime_of_volume_debit
    {T : ℝ}
    (hscalar : ∃ K : ℝ, 0 ≤ K ∧
      ∀ j : ℕ, ∀ t ∈ Ico (time j) (time (j + 1)),
        ∀ x : (stage j).Carrier, -K ≤ metricScalarAt ((event j).incoming.flow.base.metric t) x)
    (hdebit : ∃ v : ℝ, 0 < v ∧ ∀ j : ℕ,
      ∃ F : Set (event j).incoming.terminalRegularOpen, IsCompact F ∧
        riemannianVolumeMeasure ThreeModel (stage (j + 1)).Carrier (event j).outputMetric univ +
          ENNReal.ofReal ((Nat.card (event j).transition.trace.tubes.Index : ℝ) * v) ≤
        riemannianVolumeMeasure ThreeModel (event j).incoming.terminalRegularOpen
          (event j).terminal.metric F) :
    ¬ Tendsto time atTop (𝓝 T) := by
  intro hlim
  obtain ⟨K,hK,hscalar⟩ := hscalar
  obtain ⟨v,hv,hdebit⟩ := hdebit
  have hb (n : ℕ) : time n ≤ T :=
    ge_of_tendsto hlim (Filter.eventually_atTop.2
      ⟨n,fun j hj => (event_time_strictMono time stage event).monotone hj⟩)
  let B := (Nat.card (ConnectedComponents (stage 0).Carrier) : ℝ) +
    2 * (Real.exp (K * T) *
      (riemannianVolumeMeasure ThreeModel (stage 0).Carrier (metric 0) univ).toReal / v)
  obtain ⟨n,hn⟩ := exists_nat_gt B
  exact (not_le_of_gt hn) (event_index_le_of_volume_debit time hzero stage metric event
    hinitial houtput hv hK (fun j _ => hscalar j) (fun j _ => hdebit j) (hb n))

include hzero hinitial houtput in
theorem tendsto_eventTime_atTop_of_discrete_cut_scale
    (scale : ℕ → ℝ)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (metric 0) a₀ x)
    (hlower : ∀ x, -3 / a₀ ≤ metricScalarAt (metric 0) x)
    (hcurvature : ∀ j : ℕ, ∀ a : ℝ, 0 < a →
      (∀ x, InFixedHamiltonIveyRegion (event j).terminal.metric a x) →
      ∀ x, InFixedHamiltonIveyRegion (event j).outputMetric a x)
    (hpreserve : ∀ j : ℕ, ∀ B : ℝ, B ≤ 0 →
      (∀ x, B ≤ metricScalarAt (event j).terminal.metric x) →
      ∀ x, B ≤ metricScalarAt (event j).outputMetric x)
    (hscale : ∀ j, 0 < scale j)
    (schedule : ℕ → ℝ)
    (hbound : ∀ j, scale j ≤ schedule ⌊time (j + 1)⌋₊)
    (hdebit : ∀ j : ℕ,
      ∃ F : Set (event j).incoming.terminalRegularOpen, IsCompact F ∧
        riemannianVolumeMeasure ThreeModel (stage (j + 1)).Carrier (event j).outputMetric univ +
          ENNReal.ofReal ((Nat.card (event j).transition.trace.tubes.Index : ℝ) *
            scale j ^ (-3 / 2 : ℝ)) ≤
        riemannianVolumeMeasure ThreeModel (event j).incoming.terminalRegularOpen
          (event j).terminal.metric F) :
    Tendsto time atTop atTop := by
  apply tendsto_eventTime_atTop_of_bounded_cut_scale time hzero stage metric event hinitial houtput
    scale ha₀ hfixed hlower hcurvature hpreserve hscale _ hdebit
  intro T
  classical
  let N := ⌊T⌋₊
  let S := Finset.range (N + 1)
  have hS : S.Nonempty := ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
  refine ⟨S.sup' hS schedule, ?_⟩
  intro j hj
  have hindex : ⌊time (j + 1)⌋₊ ∈ S :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono hj))
  exact (hbound j).trans (Finset.le_sup' schedule hindex)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
