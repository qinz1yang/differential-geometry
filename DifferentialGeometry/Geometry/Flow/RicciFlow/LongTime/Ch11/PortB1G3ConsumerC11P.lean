import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.CollarCompetitors
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.RecentScalarCost
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothCollarCompetitors
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothCollarContact
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothSurvivorJoins

set_option autoImplicit false

/-!
# S-CH11-PORT-B1 G3 consumer (`_C11P`)

Type-checks the main theorems of the verbatim-ported astra B1 modules of group G3
(`Surgery/LGeometry/Action`: collar competitors, smooth collars, recent scalar cost).
Own file, no new declarations.
-/

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

example : type_of% @regularizedCost_le_collar_piece_action :=
  @regularizedCost_le_collar_piece_action

example : type_of% @exists_three_piece_stage_curve := @exists_three_piece_stage_curve

example : type_of% @regularizedCost_le_smooth_collar_action :=
  @regularizedCost_le_smooth_collar_action

example : type_of% @smooth_collar_action_eq_sum_stage_action :=
  @smooth_collar_action_eq_sum_stage_action

example : type_of% @exists_smooth_survivor_directed_joins := @exists_smooth_survivor_directed_joins

example : type_of% @regularizedCost_ge_recent_half_time_of_cutoff_records :=
  @regularizedCost_ge_recent_half_time_of_cutoff_records
