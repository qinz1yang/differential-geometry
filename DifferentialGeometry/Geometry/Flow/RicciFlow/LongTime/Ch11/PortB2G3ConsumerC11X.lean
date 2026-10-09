import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.SmallEnlargementScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.ScaffoldData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IdentifiedHistoryPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmallPrefixTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalCollarReserve
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.InterleavedJointAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.InterleavedJoins
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalClockSupport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.StageSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceScalarControl.TimeLocal

set_option autoImplicit false
noncomputable section

/-!
# S-CH11-SHIM G3 consumer (`_C11X`)

Type-checks every public declaration of the 11 verbatim-ported astra B2 modules that compile in this
tree: `example : type_of% @D := @D`.  Own file, no new declarations.
-/

-- LongTime.CurvatureBounds
section
open GC.LongTime
example : type_of% @exists_postMetric_curvature_bounds_of_cutoff_records :=
  @exists_postMetric_curvature_bounds_of_cutoff_records
end

-- LongTime.SmallEnlargementScalar
section
open GC.LongTime.hasSmallParabolicCurvature
example : type_of% @scalar_abs_le := @scalar_abs_le
end

-- Surgery.History.ScaffoldData
section
open GC.GeneralFlow
example : type_of% @ScaffoldState := @ScaffoldState
example : type_of% @ScaffoldSuccessor := @ScaffoldSuccessor
example : type_of% @all_record_fields_of_successors := @all_record_fields_of_successors
example : type_of% @all_parameter_values_of_successors := @all_parameter_values_of_successors
end

-- Surgery.Topology.IdentifiedHistoryPinching
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
example : type_of% @exists_pinching_certificates_for_identified_histories :=
  @exists_pinching_certificates_for_identified_histories
end

-- Surgery.LGeometry.Action.SmallPrefixTrace
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
example : type_of% @regularizedStageStart_eq_max_zero := @regularizedStageStart_eq_max_zero
example : type_of% @sum_stage_action_eq_of_collapsed_suffix :=
  @sum_stage_action_eq_of_collapsed_suffix
example : type_of% @tendsto_regularizedWeightedStageAction_of_collapsed_suffix :=
  @tendsto_regularizedWeightedStageAction_of_collapsed_suffix
example : type_of% @tendsto_regularizedStage_trace_energy := @tendsto_regularizedStage_trace_energy
example : type_of% @exists_small_prefix_trace_energy_lt := @exists_small_prefix_trace_energy_lt
end

-- Surgery.LGeometry.Action.PhysicalCollarReserve
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
example : type_of% @exists_physical_collar_reserve_of_attained_action :=
  @exists_physical_collar_reserve_of_attained_action
end

-- Surgery.LGeometry.Action.InterleavedJointAction
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
example : type_of% @interleavedPieceEquiv := @interleavedPieceEquiv
example : type_of% @interleavedPieceEquiv_values := @interleavedPieceEquiv_values
example : type_of% @ActualPieceCarrier := @ActualPieceCarrier
example : type_of% @actualPieceTop := @actualPieceTop
example : type_of% @actualPieceChart := @actualPieceChart
example : type_of% @actualPieceManifold := @actualPieceManifold
example : type_of% @actualPieceT2 := @actualPieceT2
example : type_of% @interleaved_actual_flow_joint_families :=
  @interleaved_actual_flow_joint_families
end

-- Surgery.LGeometry.Action.InterleavedJoins
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
example : type_of% @interleavedJoinEquiv := @interleavedJoinEquiv
example : type_of% @interleavedJoinEquiv_values := @interleavedJoinEquiv_values
example : type_of% @exists_interleaved_actual_joins := @exists_interleaved_actual_joins
end

-- Surgery.LGeometry.Action.PhysicalClockSupport
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
example : type_of% @physical_clock_support_of_same_history_jets :=
  @physical_clock_support_of_same_history_jets
end

-- Surgery.LGeometry.Action.StageSolution
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
example : type_of% @exists_stage_incomingSlab_metric := @exists_stage_incomingSlab_metric
end

-- Surgery.Topology.BackwardTraceScalarControl.TimeLocal
section
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace
example : type_of% @scalar_le_two_mul_of_time_local_derivative_control :=
  @scalar_le_two_mul_of_time_local_derivative_control
end

end
