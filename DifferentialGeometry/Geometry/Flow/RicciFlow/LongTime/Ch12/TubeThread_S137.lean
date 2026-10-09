import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HShiftReduceV4_S137
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PrefixTrace_S106
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedRestrictionBounds_CX2

/-!
# CH12-S137 G1 (A), part 1: prefix trace -> tower trace, tube statement bookkeeping

`towerIdx_S137` / `towerTrace_S137`: the prefix trace `B` of `(sliceHistoryR_O3 F s).toHistory` as a trace of the tower
history `sliceTowerHistory_CX2 s` (`backwardPointTraceOfPrefix`).  The *tube statement* for `B`
(`|Rm| ≤ Bd` on the `R`-ball around `B` at every time `v ≤ s.time` after the first event, in the tower stage metrics) is an inline
binder text (no named Prop), see `[FROZEN] CH12-S137 tube`; `towerTrace_point_prefixTrace_S137` shows it is exactly the S95
`hbound` for the tower trace of `A` once `B = prefixTrace_S106 … (traceAtOfRestriction_CX2 … A) j`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

/-- prefix stage index -> tower stage index (`Fin.castLE`, as in `prefixAt`). -/
def towerIdx_S137 (s : RegularSlice F.observation)
    (m : Fin ((sliceHistoryR_O3 F s).eventCount + 1)) :
    Fin ((sliceTowerHistory_CX2 s).eventCount + 1) :=
  Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ (sliceStageR_O3 F s).isLt)) m

theorem towerIdx_mono_S137 (s : RegularSlice F.observation)
    {m m' : Fin ((sliceHistoryR_O3 F s).eventCount + 1)} (h : m ≤ m') :
    towerIdx_S137 s m ≤ towerIdx_S137 s m' :=
  Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp h)

/-- the prefix trace `B` regarded as a trace of the tower history. -/
def towerTrace_S137 (s : RegularSlice F.observation)
    {first : Fin ((sliceHistoryR_O3 F s).eventCount + 1)}
    {x : ((sliceHistoryR_O3 F s).toHistory.stage (Fin.last (sliceHistoryR_O3 F s).eventCount)).Carrier}
    (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory first
      (Fin.last (sliceHistoryR_O3 F s).eventCount) (Fin.le_last _) x) :
    BackwardPointTrace (sliceTowerHistory_CX2 s) (towerIdx_S137 s first)
      (towerIdx_S137 s (Fin.last (sliceHistoryR_O3 F s).eventCount))
      (towerIdx_mono_S137 s (Fin.le_last _)) x :=
  (F.tower.history (sliceIndexR_O3 F s)).backwardPointTraceOfPrefix (sliceStageR_O3 F s) B

/-- the tower trace of the prefix trace of a tower trace `Y'` is `Y'` itself (pointwise, by `rfl`). -/
theorem towerTrace_point_prefixTrace_S137 (s : RegularSlice F.observation)
    {first : Fin ((sliceTowerHistory_CX2 s).eventCount + 1)}
    {x : ((sliceTowerHistory_CX2 s).stage (towerIdx_S137 s (Fin.last (sliceHistoryR_O3 F s).eventCount))).Carrier}
    {hle : first ≤ towerIdx_S137 s (Fin.last (sliceHistoryR_O3 F s).eventCount)}
    (Y : BackwardPointTrace (sliceTowerHistory_CX2 s) first
      (towerIdx_S137 s (Fin.last (sliceHistoryR_O3 F s).eventCount)) hle x)
    (j : Fin (sliceHistoryR_O3 F s).eventCount)
    (hfj : first ≤ towerIdx_S137 s j.succ)
    (m : Fin ((sliceTowerHistory_CX2 s).eventCount + 1))
    (h1 : towerIdx_S137 s j.succ ≤ m) (h2 : m ≤ towerIdx_S137 s (Fin.last (sliceHistoryR_O3 F s).eventCount)) :
    (towerTrace_S137 s (prefixTrace_S106 (F.tower.history (sliceIndexR_O3 F s)) (sliceStageR_O3 F s)
      Y j hfj)).point m h1 h2 = Y.point m (hfj.trans h1) h2 := rfl

end GC.LongTime.Ch12
