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
import Lean

set_option autoImplicit false

/-!
# ch11 搬入模块的 declaration audit（`_C11C`，S-CH11-CONS G2）

照 `DeclarationAudit.lean` 的格式，但 ch11 搬入模块全部**无任何 admission**：`expected` 为空，任何
`sorryAx`（类型里、值里、公理依赖里）、unsafe、自带 `axiomInfo` 都报错。`owned` = 被审计模块；
`authored` = 其中用户写的 public theorem 名（必须存在于环境）。生成脚本
`build-logs/scratch/S-CH11-CONS/mkconsumer.py`。不改已跟踪的 `DeclarationAudit.lean`。
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let owned : List String := [
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.\
      FiniteJointFirstVariation",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.\
      FiniteJointFirstVariationPortC11P",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.\
      FiniteJointSecondVariation",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.\
      FiniteJointSecondVariationPortC11P",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.\
      LocalClockTransfer",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.\
      LocalClockTransferPortC11P",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.\
      FiniteJointRayTrace",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.\
      FiniteJointRayTracePortC11P",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.\
      FiniteJointTrace",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.\
      FiniteJointTracePortC11P",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.\
      PhysicalWeightedMinimum",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.\
      PhysicalWeightedMinimumPortC11P",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.\
      SmoothCollarSupport",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.\
      SmoothCollarSupportPortC11P",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BirthAnchorDistance",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      BirthAnchorDistancePortC11P",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BirthDepthExtension",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      BirthDepthExtensionPortC11P",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BirthTimeZeroBound",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      BirthTimeZeroBoundPortC11P",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BirthWindowAnchorBound",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      BirthWindowAnchorBoundPortC11P",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingBirthGradient",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.\
      IncomingBirthGradientPortC11P"]
  let authored : List String := [
    "DifferentialGeometry.PDE.RicciFlow.Perelman.hasDerivAt_finiteJointAction_line",
    "DifferentialGeometry.PDE.RicciFlow.Perelman.hasFDerivAt_finiteJointAction",
    "DifferentialGeometry.PDE.RicciFlow.Perelman.hasDerivAt_deriv_finiteJointAction_line",
    "DifferentialGeometry.PDE.RicciFlow.Perelman.lVelocity_parameter_ray_eq_mfderiv",
    "DifferentialGeometry.PDE.RicciFlow.Perelman.\
      sum_lRegularizedIndex_parameter_rays_eq_energy",
    "DifferentialGeometry.PDE.RicciFlow.Perelman.\
      exists_compatible_joint_variation_with_index_trace_energy",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      exists_seeded_physicalWeightedCost_minimum_of_cutoff_records",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      isLocalMin_physical_weighted_of_extended_minimum_and_same_support",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.\
      exists_smooth_collar_cost_support",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      eventually_scalar_le_at_normalized_distance_before_birth",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      depthExtendable_add_of_windowAnchorBound_at_birth",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      exists_subseq_depthExtendable_all_at_birth_of_initialIdentification",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      derivativeBound_inputs_at_birth",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      eventually_scalar_le_on_normalized_ball_at_birth",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      exists_eventually_isTracedRegion_at_birth_of_scalar_le_on_ball",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      exists_depth_schedule_isTracedRegion_at_birth",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      exists_subseq_scalar_le_on_normalized_balls_at_birth",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      exists_subseq_depthExtendable_pos_at_birth",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      tendsto_scale_mul_birth_time_atTop_of_initialIdentification",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      exists_subseq_depthExtendable_pos_at_birth_of_initialIdentification",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      exists_subseq_windowAnchorBound_at_birth_of_depthExtendable",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.\
      exists_subseq_all_depth_or_maximal_window_at_birth",
    "DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.\
      abs_scalarDifferential_le_at_birth_of_gradientBoundBefore"]
  for s in authored do
    unless (env.find? s.toName).isSome do throwError "Missing declaration {s}"
  let expected : List Name := []
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for modS in owned do
    let mod := modS.toName
    let some idx := env.getModuleIdx? mod | throwError "Missing module {mod}"
    for name in env.header.moduleData[idx.toNat]!.constNames do
      let some info := env.find? name | throwError "Unchecked declaration {name}"
      if info.isAxiom || info.isUnsafe then
        throwError "Unexpected axiomInfo or unsafe declaration {name}"
      if info.type.getUsedConstants.contains ``sorryAx then
        throwError "Admission in declaration type {name}"
      let valueUses := (info.value? (allowOpaque := true)).map Expr.getUsedConstants
      if valueUses.any (fun ns => ns.contains ``sorryAx) then
        unless expected.contains name do throwError "Unregistered direct admission {name}"
      for ax in (← collectAxioms name) do
        unless allowed.contains ax do throwError "Unexpected axioms {ax} in {name}"
      count := count + 1
  let msg : String := s!"ch11 declaration audit: {owned.length} modules, {count} declarations, "
    ++ s!"{authored.length} authored theorems present, 0 admissions."
  logInfo msg
