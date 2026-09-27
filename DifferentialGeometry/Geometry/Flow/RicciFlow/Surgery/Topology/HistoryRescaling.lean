import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventRescaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryExtension

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

def rescale (H : ObservedHistory.{u}) (r : ℝ) (hr : 0 < r) : ObservedHistory.{u} where
  horizon := H.horizon / r
  horizon_nonneg := div_nonneg H.horizon_nonneg hr.le
  eventCount := H.eventCount
  time := fun j => H.time j / r
  time_strictMono := fun _ _ hij => div_lt_div_of_pos_right (H.time_strictMono hij) hr
  time_zero := by rw [H.time_zero, zero_div]
  time_le_horizon := (div_le_div_iff_of_pos_right hr).mpr H.time_le_horizon
  stage := H.stage
  initialMetric := fun j => scaleMetric r⁻¹ (inv_pos.mpr hr) (H.initialMetric j)
  event := fun i => (H.event i).rescale r hr
  event_initial := by
    intro i
    rw [MetricCutCapEvent.rescale_incoming_metric, mul_div_cancel₀ _ hr.ne', H.event_initial]
  event_output := by
    intro i
    rw [MetricCutCapEvent.rescale_outputMetric, H.event_output]
  finalSlab := fun h =>
    (H.finalSlab ((div_lt_div_iff_of_pos_right hr).mp h)).rescale r hr
  final_initial := by
    intro h
    rw [OrientedThreeStage.ClosedSlab.rescale_metric, mul_div_cancel₀ _ hr.ne', H.final_initial]

@[simp] theorem rescale_horizon (H : ObservedHistory.{u}) (r : ℝ) (hr : 0 < r) :
    (H.rescale r hr).horizon = H.horizon / r := rfl

@[simp] theorem rescale_eventCount (H : ObservedHistory.{u}) (r : ℝ) (hr : 0 < r) :
    (H.rescale r hr).eventCount = H.eventCount := rfl

@[simp] theorem rescale_time (H : ObservedHistory.{u}) (r : ℝ) (hr : 0 < r)
    (j : Fin (H.eventCount + 1)) : (H.rescale r hr).time j = H.time j / r := rfl

@[simp] theorem rescale_stage (H : ObservedHistory.{u}) (r : ℝ) (hr : 0 < r)
    (j : Fin (H.eventCount + 1)) : (H.rescale r hr).stage j = H.stage j := rfl

@[simp] theorem rescale_initialMetric (H : ObservedHistory.{u}) (r : ℝ) (hr : 0 < r)
    (j : Fin (H.eventCount + 1)) :
    (H.rescale r hr).initialMetric j = scaleMetric r⁻¹ (inv_pos.mpr hr) (H.initialMetric j) := rfl

theorem rescale_eventTimes (H : ObservedHistory.{u}) (r : ℝ) (hr : 0 < r) :
    (H.rescale r hr).eventTimes = (fun t => r * t) ⁻¹' H.eventTimes := by
  ext t
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, (mul_div_cancel₀ (H.time i.succ) hr.ne').symm⟩
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    change H.time i.succ / r = t
    apply (div_eq_iff hr.ne').mpr
    simpa only [mul_comm t r] using hi

theorem rescale_discards (H : ObservedHistory.{u}) (r : ℝ) (hr : 0 < r)
    (D : OrientedThreeStage.{u} → Prop)
    (hD : ∀ i : Fin H.eventCount, D (H.event i).discarded) :
    ∀ i : Fin (H.rescale r hr).eventCount, D ((H.rescale r hr).event i).discarded := hD

end ObservedHistory

namespace InitialIdentification

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {H : ObservedHistory.{u}}

def rescale (A : InitialIdentification P g H) (r : ℝ) (hr : 0 < r) :
    InitialIdentification P (scaleMetric r⁻¹ (inv_pos.mpr hr) g) (H.rescale r hr) where
  map := A.map
  positive := A.positive
  metric_eq := by
    intro x v w
    simp only [scaleMetric_inner]
    exact congrArg (fun z : ℝ => r⁻¹ * z) (A.metric_eq x v w)

@[simp] theorem rescale_map (A : InitialIdentification P g H) (r : ℝ) (hr : 0 < r) :
    (A.rescale r hr).map = A.map := rfl

def rescaleFromScaled (r : ℝ) (hr : 0 < r)
    (A : InitialIdentification P (scaleMetric r hr g) H) :
    InitialIdentification P g (H.rescale r hr) where
  map := A.map
  positive := A.positive
  metric_eq := by
    intro x v w
    change (scaleMetric r⁻¹ (inv_pos.mpr hr) (H.initialMetric 0)).inner (A.map x)
      (mfderiv ThreeModel ThreeModel A.map x v) (mfderiv ThreeModel ThreeModel A.map x w) =
        g.inner x v w
    rw [scaleMetric_inner, A.metric_eq, scaleMetric_inner,
      ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

@[simp] theorem rescaleFromScaled_map (r : ℝ) (hr : 0 < r)
    (A : InitialIdentification P (scaleMetric r hr g) H) :
    (rescaleFromScaled r hr A).map = A.map := rfl

end InitialIdentification

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
