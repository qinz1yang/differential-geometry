import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodContinuationLeaves
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

def prefixAt (k : Fin (H.eventCount + 1)) : RetainedCoreHistory.{u} where
  horizon := H.time k
  horizon_nonneg := H.toHistory.time_nonneg k
  eventCount := k.val
  time := fun m => H.time (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) m)
  time_strictMono := fun _ _ h => H.time_strictMono h
  time_zero := H.time_zero
  time_le_horizon := le_rfl
  stage := fun m => H.stage (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) m)
  initialMetric := fun m =>
    H.initialMetric (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) m)
  coreEvent := fun i => H.coreEvent (Fin.castLE (Nat.le_of_lt_succ k.isLt) i)
  event_initial := fun i => H.event_initial (Fin.castLE (Nat.le_of_lt_succ k.isLt) i)
  event_output := fun i => H.event_output (Fin.castLE (Nat.le_of_lt_succ k.isLt) i)
  finalSlab := fun h => absurd h (lt_irrefl _)
  final_initial := fun h => absurd h (lt_irrefl _)

theorem prefixAt_time_last (k : Fin (H.eventCount + 1)) :
    (H.prefixAt k).time (Fin.last (H.prefixAt k).eventCount) = (H.prefixAt k).horizon := rfl

def backwardPointTraceOfPrefix (k : Fin (H.eventCount + 1))
    {first last : Fin ((H.prefixAt k).eventCount + 1)} {hle : first ≤ last}
    {x : ((H.prefixAt k).stage last).Carrier}
    (A : BackwardPointTrace (H.prefixAt k).toHistory first last hle x) :
    BackwardPointTrace H.toHistory
      (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) first)
      (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) last)
      (Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hle)) x where
  point m hm1 hm2 := A.point ⟨m.val, by
      have h1 : m.val ≤ last.val := hm2
      have h2 : last.val < (H.prefixAt k).toHistory.eventCount + 1 := last.isLt
      omega⟩ hm1 hm2
  endpoint_eq := A.endpoint_eq
  crossing i hf hl := A.crossing ⟨i.val, by
      have h1 : i.val + 1 ≤ last.val := hl
      have h2 : last.val < (H.prefixAt k).toHistory.eventCount + 1 := last.isLt
      omega⟩ hf hl

private def incomingBackwardNeckOfPrefix (k : Fin (H.eventCount + 1))
    {i : Fin (H.prefixAt k).eventCount} {δ r : ℝ} {m : ℕ}
    {neck : NormalizedNeck ((H.prefixAt k).toHistory.event i).terminal.metric δ m}
    (N : IncomingBackwardNeck H.toHistory (Fin.castLE (Nat.le_of_lt_succ k.isLt) i) neck r) :
    IncomingBackwardNeck (H.prefixAt k).toHistory i neck r where
  radius_pos := N.radius_pos
  left_nonneg := N.left_nonneg
  stageChart j hj ha := N.stageChart (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) hj ha
  stageChart_smooth j hj ha := N.stageChart_smooth (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) hj ha
  terminal_chart ha x := N.terminal_chart ha x
  crossing j hj ha hn x := N.crossing (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) hj ha hn x
  metric := N.metric
  terminal_metric := N.terminal_metric
  metric_on_slab j hj ha v hv h1 h2 x V W :=
    N.metric_on_slab (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) hj ha v hv h1 h2 x V W
  timeDifferenceJet := N.timeDifferenceJet
  timeDifferenceJet_eq := N.timeDifferenceJet_eq
  parabolic_closeness := N.parabolic_closeness
  metric_smooth := N.metric_smooth

def geometricCutoffRecordOfPrefix (k : Fin (H.eventCount + 1))
    {i : Fin (H.prefixAt k).eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H.toHistory (Fin.castLE (Nat.le_of_lt_succ k.isLt) i) p) :
    GeometricCutoffRecord (H.prefixAt k).toHistory i p :=
  { R with backward := fun α => H.incomingBackwardNeckOfPrefix k (R.backward α) }

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
