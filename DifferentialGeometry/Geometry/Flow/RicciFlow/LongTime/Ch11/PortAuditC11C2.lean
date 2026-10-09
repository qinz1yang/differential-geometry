import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FiniteJointFirstVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FiniteJointFirstVariationPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FiniteJointSecondVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FiniteJointSecondVariationPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.LocalClockTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.LocalClockTransferPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.FiniteJointRayTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.FiniteJointRayTracePortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.FiniteJointTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.FiniteJointTracePortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalWeightedMinimum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalWeightedMinimumPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothCollarSupport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothCollarSupportPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BirthAnchorDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BirthAnchorDistancePortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BirthDepthExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BirthDepthExtensionPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BirthTimeZeroBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BirthTimeZeroBoundPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BirthWindowAnchorBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BirthWindowAnchorBoundPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingBirthGradient
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingBirthGradientPortC11P

set_option autoImplicit false
noncomputable section

/-!
# S-CH11-CONS G2 consumer 汇总（`_C11C` 第 2 批）

一次 `import` 全部已落地的 ch11 donor 派生模块（B1 verbatim、B2/B3/EXT verbatim、20 个 split shim、
FIX 的 `PortC11P` 与 extension `C11X`），对其中每个**用户写的 public 声明**（theorem / def / inductive）
做 `example : type_of% @D := @D` 的型检查。顺带证明这些模块可以同时 import（无重名冲突）。
只含 `example`，不引入任何声明；生成脚本 `build-logs/scratch/S-CH11-CONS/mkconsumer.py`。
-/

-- RF.Perelman.LGeometry.Action.Regularized.FiniteJointFirstVariation  （无用户声明：shim / re-export）

-- RF.Perelman.LGeometry.Action.Regularized.FiniteJointFirstVariationPortC11P
section
example : type_of% @DifferentialGeometry.PDE.RicciFlow.Perelman.hasDerivAt_finiteJointAction_line :=
  @DifferentialGeometry.PDE.RicciFlow.Perelman.hasDerivAt_finiteJointAction_line
example : type_of% @DifferentialGeometry.PDE.RicciFlow.Perelman.hasFDerivAt_finiteJointAction :=
  @DifferentialGeometry.PDE.RicciFlow.Perelman.hasFDerivAt_finiteJointAction
end

-- RF.Perelman.LGeometry.Action.Regularized.FiniteJointSecondVariation  （无用户声明：shim / re-export）

-- RF.Perelman.LGeometry.Action.Regularized.FiniteJointSecondVariationPortC11P
section
example :
    type_of% @DifferentialGeometry.PDE.RicciFlow.Perelman.hasDerivAt_deriv_finiteJointAction_line :=
  @DifferentialGeometry.PDE.RicciFlow.Perelman.hasDerivAt_deriv_finiteJointAction_line
end

-- RF.Perelman.LGeometry.Action.Regularized.LocalClockTransfer  （无用户声明：shim / re-export）

-- RF.Perelman.LGeometry.Action.Regularized.LocalClockTransferPortC11P  （无用户声明：shim / re-export）

-- RF.Perelman.LGeometry.Index.FiniteJointRayTrace  （无用户声明：shim / re-export）

-- RF.Perelman.LGeometry.Index.FiniteJointRayTracePortC11P
section
example :
    type_of% @DifferentialGeometry.PDE.RicciFlow.Perelman.lVelocity_parameter_ray_eq_mfderiv :=
  @DifferentialGeometry.PDE.RicciFlow.Perelman.lVelocity_parameter_ray_eq_mfderiv
open DifferentialGeometry.PDE.RicciFlow.Perelman in
example : type_of% @sum_lRegularizedIndex_parameter_rays_eq_energy :=
  @sum_lRegularizedIndex_parameter_rays_eq_energy
end

-- RF.Perelman.LGeometry.Index.FiniteJointTrace  （无用户声明：shim / re-export）

-- RF.Perelman.LGeometry.Index.FiniteJointTracePortC11P
section
open DifferentialGeometry.PDE.RicciFlow.Perelman in
example : type_of% @exists_compatible_joint_variation_with_index_trace_energy :=
  @exists_compatible_joint_variation_with_index_trace_energy
end

-- RF.Surgery.LGeometry.Action.PhysicalWeightedMinimum  （无用户声明：shim / re-export）

-- RF.Surgery.LGeometry.Action.PhysicalWeightedMinimumPortC11P
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @physicalWeightedCost := @physicalWeightedCost
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @exists_seeded_physicalWeightedCost_minimum_of_cutoff_records :=
  @exists_seeded_physicalWeightedCost_minimum_of_cutoff_records
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @isLocalMin_physical_weighted_of_extended_minimum_and_same_support :=
  @isLocalMin_physical_weighted_of_extended_minimum_and_same_support
end

-- RF.Surgery.LGeometry.Action.SmoothCollarSupport  （无用户声明：shim / re-export）

-- RF.Surgery.LGeometry.Action.SmoothCollarSupportPortC11P
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory in
example : type_of% @exists_smooth_collar_cost_support := @exists_smooth_collar_cost_support
end

-- RF.Surgery.Topology.BirthAnchorDistance  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.BirthAnchorDistancePortC11P
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @eventually_scalar_le_at_normalized_distance_before_birth :=
  @eventually_scalar_le_at_normalized_distance_before_birth
end

-- RF.Surgery.Topology.BirthDepthExtension  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.BirthDepthExtensionPortC11P
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @depthExtendable_add_of_windowAnchorBound_at_birth :=
  @depthExtendable_add_of_windowAnchorBound_at_birth
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @exists_subseq_depthExtendable_all_at_birth_of_initialIdentification :=
  @exists_subseq_depthExtendable_all_at_birth_of_initialIdentification
end

-- RF.Surgery.Topology.BirthTimeZeroBound  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.BirthTimeZeroBoundPortC11P
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @derivativeBound_inputs_at_birth := @derivativeBound_inputs_at_birth
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @eventually_scalar_le_on_normalized_ball_at_birth :=
  @eventually_scalar_le_on_normalized_ball_at_birth
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @exists_eventually_isTracedRegion_at_birth_of_scalar_le_on_ball :=
  @exists_eventually_isTracedRegion_at_birth_of_scalar_le_on_ball
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @exists_depth_schedule_isTracedRegion_at_birth :=
  @exists_depth_schedule_isTracedRegion_at_birth
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @exists_subseq_scalar_le_on_normalized_balls_at_birth :=
  @exists_subseq_scalar_le_on_normalized_balls_at_birth
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @exists_subseq_depthExtendable_pos_at_birth :=
  @exists_subseq_depthExtendable_pos_at_birth
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @tendsto_scale_mul_birth_time_atTop_of_initialIdentification :=
  @tendsto_scale_mul_birth_time_atTop_of_initialIdentification
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @exists_subseq_depthExtendable_pos_at_birth_of_initialIdentification :=
  @exists_subseq_depthExtendable_pos_at_birth_of_initialIdentification
end

-- RF.Surgery.Topology.BirthWindowAnchorBound  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.BirthWindowAnchorBoundPortC11P
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @exists_subseq_windowAnchorBound_at_birth_of_depthExtendable :=
  @exists_subseq_windowAnchorBound_at_birth_of_depthExtendable
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory in
example : type_of% @exists_subseq_all_depth_or_maximal_window_at_birth :=
  @exists_subseq_all_depth_or_maximal_window_at_birth
end

-- RF.Surgery.Topology.IncomingBirthGradient  （无用户声明：shim / re-export）

-- RF.Surgery.Topology.IncomingBirthGradientPortC11P
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab in
example : type_of% @abs_scalarDifferential_le_at_birth_of_gradientBoundBefore :=
  @abs_scalarDifferential_le_at_birth_of_gradientBoundBefore
end
