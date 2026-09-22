import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryComponentCount
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryVolumeDebit

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

theorem ObservedHistory.eventCount_le_card_initial_add_volume_bound
    (H : ObservedHistory.{u}) {v K T : ℝ} (hv : 0 < v)
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
    (H.eventCount : ℝ) ≤ Nat.card (ConnectedComponents (H.stage 0).Carrier) +
      2 * (Real.exp (K * T) *
        (riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier
          (H.initialMetric 0) univ).toReal / v) := by
  have hc : (H.eventCount : ℝ) ≤ Nat.card (ConnectedComponents (H.stage 0).Carrier) +
      2 * ∑ i : Fin H.eventCount, (Nat.card (H.event i).transition.trace.tubes.Index : ℝ) := by
    exact_mod_cast H.eventCount_le_card_initial_add_two_mul_sum_card_cut
  have hvb := H.sum_cut_count_mul_le_exp_mul_initial_volume hv.le hK hT hscalar hcap
  have hb := (le_div_iff₀ hv).mpr hvb
  linarith

theorem ObservedHistory.eventCount_le_card_initial_add_volume_bound_of_fixedHamiltonIveyRegion
    (H : ObservedHistory.{u}) {parameters : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x)
    (hlower : ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x)
    {v T : ℝ} (hv : 0 < v) (hT : H.horizon ≤ T)
    (hcap : ∀ i : Fin H.eventCount, ∃ F : Set (H.event i).incoming.terminalRegularOpen,
      IsCompact F ∧
      riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.event i).outputMetric univ +
        ENNReal.ofReal ((Nat.card (H.event i).transition.trace.tubes.Index : ℝ) * v) ≤
      riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
        (H.event i).terminal.metric F) :
    (H.eventCount : ℝ) ≤ Nat.card (ConnectedComponents (H.stage 0).Carrier) +
      2 * (Real.exp ((3 / a₀) * T) *
        (riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier
          (H.initialMetric 0) univ).toReal / v) := by
  have hc : (H.eventCount : ℝ) ≤ Nat.card (ConnectedComponents (H.stage 0).Carrier) +
      2 * ∑ i : Fin H.eventCount, (Nat.card (H.event i).transition.trace.tubes.Index : ℝ) := by
    exact_mod_cast H.eventCount_le_card_initial_add_two_mul_sum_card_cut
  have hvb := H.sum_cut_count_mul_le_of_fixedHamiltonIveyRegion
    records ha₀ hfixed hlower hv.le hT hcap
  have hb := (le_div_iff₀ hv).mpr hvb
  linarith

theorem exists_pos_volume_debit_and_eventCount_bound_of_finite_scales
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
      (H.eventCount : ℝ) ≤ Nat.card (ConnectedComponents (H.stage 0).Carrier) +
        2 * (Real.exp (K * T) *
          (riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier
            (H.initialMetric 0) univ).toReal / v) := by
  obtain ⟨v, hv, hle, hbound⟩ := exists_pos_volume_debit_of_finite_scales scale hscale
  refine ⟨v, hv, hle, ?_⟩
  intro H bin K T hK hT hscalar hcap
  have hc : (H.eventCount : ℝ) ≤ Nat.card (ConnectedComponents (H.stage 0).Carrier) +
      2 * ∑ i : Fin H.eventCount, (Nat.card (H.event i).transition.trace.tubes.Index : ℝ) := by
    exact_mod_cast H.eventCount_le_card_initial_add_two_mul_sum_card_cut
  have hb := hbound H bin hK hT hscalar hcap
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
