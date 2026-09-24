import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalVolumeGrowth
import DifferentialGeometry.Analysis.Estimates.ExponentialSums
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Curvature
open scoped BigOperators ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance (P : OrientedThreeStage.{u}) : MeasurableSpace P.Carrier := borel P.Carrier
private local instance (P : OrientedThreeStage.{u}) : BorelSpace P.Carrier := ⟨rfl⟩
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    MeasurableSpace G.terminalRegularOpen := borel G.terminalRegularOpen
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    BorelSpace G.terminalRegularOpen := ⟨rfl⟩

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

theorem MetricCutCapEvent.volume_add_debit_le_exp_mul_initial
    {P Q : OrientedThreeStage.{u}} {a s K d : ℝ} (E : MetricCutCapEvent P Q a s)
    (hd : 0 ≤ d)
    (hscalar : ∀ t ∈ Ico a s, ∀ x : P.Carrier,
      -K ≤ metricScalarAt (E.incoming.flow.base.metric t) x)
    {F : Set E.incoming.terminalRegularOpen} (hF : IsCompact F)
    (hdebit : riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ +
      ENNReal.ofReal d ≤
        riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric F) :
    (riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ).toReal + d ≤
      Real.exp (K * (s - a)) *
        (riemannianVolumeMeasure ThreeModel P.Carrier
          (E.incoming.flow.base.metric a) univ).toReal := by
  have hbound := hdebit.trans (E.terminal.volume_compact_le_exp_mul_initial E.incoming
    hscalar hF)
  let _ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace E.outputMetric
  let _ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (E.incoming.flow.base.metric a)
  have hreal := (ENNReal.toReal_le_toReal
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))).mpr hbound
  simpa only [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hd, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] using hreal

theorem ObservedHistory.exp_mul_volume_add_sum_debit_le_initial_volume
    (H : ObservedHistory.{u}) (debit : Fin H.eventCount → ℝ) {K : ℝ}
    (hdebit : ∀ i, 0 ≤ debit i)
    (hscalar : ∀ i : Fin H.eventCount, ∀ t ∈ Ico (H.time i.castSucc) (H.time i.succ),
      ∀ x : (H.stage i.castSucc).Carrier,
      -K ≤ metricScalarAt ((H.event i).incoming.flow.base.metric t) x)
    (hcap : ∀ i : Fin H.eventCount, ∃ F : Set (H.event i).incoming.terminalRegularOpen,
      IsCompact F ∧
      riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.event i).outputMetric univ +
        ENNReal.ofReal (debit i) ≤
      riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
        (H.event i).terminal.metric F) :
    Real.exp (-K * H.time (Fin.last H.eventCount)) *
      (riemannianVolumeMeasure ThreeModel (H.stage (Fin.last H.eventCount)).Carrier
        (H.initialMetric (Fin.last H.eventCount)) univ).toReal +
      ∑ i : Fin H.eventCount, Real.exp (-K * H.time i.succ) * debit i ≤
        (riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier
          (H.initialMetric 0) univ).toReal := by
  simpa only [H.time_zero, mul_zero, Real.exp_zero, one_mul] using
    (DifferentialGeometry.Analysis.exp_mul_add_sum_le_of_successive_debits H.time
      (fun i => (riemannianVolumeMeasure ThreeModel (H.stage i).Carrier
        (H.initialMetric i) univ).toReal) debit K (by
          intro i
          obtain ⟨F, hF, hvol⟩ := hcap i
          have h := (H.event i).volume_add_debit_le_exp_mul_initial
            (hdebit i) (hscalar i) hF hvol
          simpa only [H.event_initial, H.event_output] using h))

theorem ObservedHistory.sum_debit_le_exp_mul_initial_volume
    (H : ObservedHistory.{u}) (debit : Fin H.eventCount → ℝ) {K T : ℝ}
    (hK : 0 ≤ K) (hT : H.horizon ≤ T) (hdebit : ∀ i, 0 ≤ debit i)
    (hscalar : ∀ i : Fin H.eventCount, ∀ t ∈ Ico (H.time i.castSucc) (H.time i.succ),
      ∀ x : (H.stage i.castSucc).Carrier,
      -K ≤ metricScalarAt ((H.event i).incoming.flow.base.metric t) x)
    (hcap : ∀ i : Fin H.eventCount, ∃ F : Set (H.event i).incoming.terminalRegularOpen,
      IsCompact F ∧
      riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.event i).outputMetric univ +
        ENNReal.ofReal (debit i) ≤
      riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
        (H.event i).terminal.metric F) :
    ∑ i : Fin H.eventCount, debit i ≤ Real.exp (K * T) *
      (riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier (H.initialMetric 0) univ).toReal := by
  simpa only [H.time_zero, sub_zero] using
    (DifferentialGeometry.Analysis.sum_le_exp_mul_of_successive_debits H.time
    (fun i => (riemannianVolumeMeasure ThreeModel (H.stage i).Carrier
      (H.initialMetric i) univ).toReal) debit hK
    (fun i => (H.time_strictMono.monotone (Fin.le_last i.succ)).trans (H.time_le_horizon.trans hT))
    ENNReal.toReal_nonneg hdebit (by
      intro i
      obtain ⟨F, hF, hvol⟩ := hcap i
      have h := (H.event i).volume_add_debit_le_exp_mul_initial
        (hdebit i) (hscalar i) hF hvol
      simpa only [H.event_initial, H.event_output] using h))

theorem ObservedHistory.sum_cut_count_mul_le_exp_mul_initial_volume
    (H : ObservedHistory.{u}) {v K T : ℝ} (hv : 0 ≤ v)
    (hK : 0 ≤ K) (hT : H.horizon ≤ T)
    (hscalar : ∀ i : Fin H.eventCount, ∀ t ∈ Ico (H.time i.castSucc) (H.time i.succ),
      ∀ x : (H.stage i.castSucc).Carrier,
      -K ≤ metricScalarAt ((H.event i).incoming.flow.base.metric t) x)
    (hcap : ∀ i : Fin H.eventCount, ∃ F : Set (H.event i).incoming.terminalRegularOpen,
      IsCompact F ∧
      riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.event i).outputMetric univ +
        ENNReal.ofReal ((Nat.card (H.event i).transition.trace.tubes.Index : ℝ) * v) ≤
      riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
        (H.event i).terminal.metric F) :
    (∑ i : Fin H.eventCount, (Nat.card (H.event i).transition.trace.tubes.Index : ℝ)) * v ≤
      Real.exp (K * T) *
        (riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier
          (H.initialMetric 0) univ).toReal := by
  rw [Finset.sum_mul]
  exact H.sum_debit_le_exp_mul_initial_volume
    (fun i => (Nat.card (H.event i).transition.trace.tubes.Index : ℝ) * v) hK hT
    (fun _ => mul_nonneg (Nat.cast_nonneg _) hv) hscalar hcap

theorem ObservedHistory.sum_cut_count_mul_le_of_fixedHamiltonIveyRegion
    (H : ObservedHistory.{u}) {parameters : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x)
    (hlower : ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x)
    {v T : ℝ} (hv : 0 ≤ v) (hT : H.horizon ≤ T)
    (hcap : ∀ i : Fin H.eventCount, ∃ F : Set (H.event i).incoming.terminalRegularOpen,
      IsCompact F ∧
      riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.event i).outputMetric univ +
        ENNReal.ofReal ((Nat.card (H.event i).transition.trace.tubes.Index : ℝ) * v) ≤
      riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
        (H.event i).terminal.metric F) :
    (∑ i : Fin H.eventCount, (Nat.card (H.event i).transition.trace.tubes.Index : ℝ)) * v ≤
      Real.exp ((3 / a₀) * T) *
        (riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier
          (H.initialMetric 0) univ).toReal := by
  apply H.sum_cut_count_mul_le_exp_mul_initial_volume hv (by positivity) hT ?_ hcap
  have hp := H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hlower
  intro i t ht x
  have htime : 0 ≤ t := (H.time_nonneg i.castSucc).trans ht.1
  have ht' : t ∈ H.stageDomain i.castSucc := by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using ht
  have hl := (hp.1 i.castSucc t ht' x).2
  simp only [ObservedHistory.stageMetric, Fin.lastCases_castSucc] at hl
  have hd : 3 / (a₀ + t) ≤ 3 / a₀ :=
    div_le_div_of_nonneg_left (by norm_num) ha₀ (by linarith)
  have hneg : -(3 / a₀) ≤ -3 / (a₀ + t) := by
    simpa only [neg_div] using neg_le_neg hd
  exact hneg.trans hl

theorem exists_pos_volume_debit_of_finite_scales
    {β : Type*} [Finite β] (scale : β → ℝ) (hscale : ∀ b, 0 < scale b) :
    ∃ v : ℝ, 0 < v ∧ (∀ b, v ≤ scale b ^ (-3 / 2 : ℝ)) ∧
      ∀ (H : ObservedHistory.{u}) (bin : Fin H.eventCount → β) {K T : ℝ},
      0 ≤ K → H.horizon ≤ T →
      (∀ i : Fin H.eventCount, ∀ t ∈ Ico (H.time i.castSucc) (H.time i.succ),
        ∀ x : (H.stage i.castSucc).Carrier,
        -K ≤ metricScalarAt ((H.event i).incoming.flow.base.metric t) x) →
      (∀ i : Fin H.eventCount, ∃ F : Set (H.event i).incoming.terminalRegularOpen,
        IsCompact F ∧
        riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.event i).outputMetric univ +
          ENNReal.ofReal ((Nat.card (H.event i).transition.trace.tubes.Index : ℝ) *
            scale (bin i) ^ (-3 / 2 : ℝ)) ≤
        riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
          (H.event i).terminal.metric F) →
      (∑ i : Fin H.eventCount, (Nat.card (H.event i).transition.trace.tubes.Index : ℝ)) ≤
        Real.exp (K * T) *
          (riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier
            (H.initialMetric 0) univ).toReal / v := by
  classical
  let := Fintype.ofFinite β
  have hex : ∃ v : ℝ, 0 < v ∧ ∀ b, v ≤ scale b ^ (-3 / 2 : ℝ) := by
    by_cases hne : (Finset.univ : Finset β).Nonempty
    · refine ⟨Finset.univ.inf' hne (fun b => scale b ^ (-3 / 2 : ℝ)), ?_, ?_⟩
      · exact (Finset.lt_inf'_iff hne).mpr (fun b _ => Real.rpow_pos_of_pos (hscale b) _)
      · intro b
        exact Finset.inf'_le _ (Finset.mem_univ b)
    · refine ⟨1, zero_lt_one, ?_⟩
      intro b
      exact (hne ⟨b, Finset.mem_univ b⟩).elim
  obtain ⟨v, hv, hle⟩ := hex
  refine ⟨v, hv, hle, ?_⟩
  intro H bin K T hK hT hscalar hcap
  apply (le_div_iff₀ hv).mpr
  apply H.sum_cut_count_mul_le_exp_mul_initial_volume hv.le hK hT hscalar
  intro i
  obtain ⟨F, hF, hvol⟩ := hcap i
  refine ⟨F, hF, le_trans ?_ hvol⟩
  apply add_le_add_right
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (hle (bin i)) (Nat.cast_nonneg _)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
