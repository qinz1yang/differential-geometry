import DifferentialGeometry.Geometry.Metric.Family.Cartesian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSolution

set_option autoImplicit false
noncomputable section
open DifferentialGeometry.Geometry.Curvature
namespace DifferentialGeometry.PDE.RicciFlow

theorem PartialStandardSolution.metricFamilySmoothOn (S : PartialStandardSolution) :
    MetricFamilySmoothOn (lifetimeInterval S.lifetime S.lifetime_pos) S.metric := by
  exact metricFamilySmoothOn_of_cartesian_smooth _ S.metric S.smooth

end DifferentialGeometry.PDE.RicciFlow
