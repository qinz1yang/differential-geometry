import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Pinching.ThroughSurgery
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.UniformDebitSurgeryStepOfFineCutNeckSupplyStrong
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.FineCutNeckSupplyStrongLeaf
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Neck.Cutoff

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem uniform_debit_surgery_step (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    UniformDebitSurgeryStepStrong P₀ g₀ :=
  uniformDebitSurgeryStepStrong_of_strongNecks_of_fineCutNeckSupplyStrong P₀ g₀
    (pinchingThroughSurgery P₀ g₀) (strong_necks_of_cutoff_class P₀ g₀)
    (fineCutNeckSupplyStrong_holds P₀ g₀)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
