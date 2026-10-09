import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ObservedComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ScalarRescaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRescaling

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Extinction.Families

universe u

namespace ObservedComparisonRecord

variable {H : ObservedHistory.{u}} {c A : ℝ}

def rescale (R : ObservedComparisonRecord H c A) (r : ℝ) (hr : 0 < r) :
    ObservedComparisonRecord (H.rescale r hr) (c / r) (A / r) where
  value := fun t => r⁻¹ * R.value (r * t)
  hypotheses := by
    simpa only [ObservedHistory.rescale_horizon, ObservedHistory.rescale_eventTimes]
      using R.hypotheses.rescale hr
  initial_le := scalarComparison_initial_bound_rescale hr R.initial_le

@[simp] theorem rescale_value (R : ObservedComparisonRecord H c A)
    (r : ℝ) (hr : 0 < r) (t : ℝ) :
    (R.rescale r hr).value t = r⁻¹ * R.value (r * t) := rfl

theorem rescale_threshold (R : ObservedComparisonRecord H c A)
    (r : ℝ) (hr : 0 < r) :
    extinctionThreshold (c / r) (A / r) = extinctionThreshold c A / r :=
  extinctionThreshold_div R.hypotheses.c_pos hr

end ObservedComparisonRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
