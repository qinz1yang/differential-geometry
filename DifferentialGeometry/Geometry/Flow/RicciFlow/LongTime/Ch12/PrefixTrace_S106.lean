import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TracedBallSeeds_S95
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueSliceTransfer

/-!
# CH12-S106, group 1: tower trace -> slice-prefix trace (the `hglue` trace glue, A4 of S95/S96)

`prefixTrace_S106` restricts a trace of the tower history `H.toHistory` ending at the stage `k` to the
retained-core prefix `H.prefixAt k` (the reverse of `RetainedCoreHistory.backwardPointTraceOfPrefix`);
`hbar_tower_of_prefix_S106` turns the located barrier stated on the slice prefix
`(sliceHistoryR_O3 F s).toHistory` (records live there) with the prefix trace as centre into the
tower-indexed barrier clause `hbar` of `traced_of_seeds_ball_S95` for the tower trace
`traceAtOfRestriction_CX2 … A`.  Events/stages of the prefix are those of the tower at `Fin.castLE`
(NOTE CH12-S95 A4), so all identifications below are `rfl`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- A trace of `H.toHistory` ending at the stage `k`, restricted to the prefix `H.prefixAt k`: the trace
from the event `j.succ` of the prefix to its last stage, with the same endpoint. -/
def prefixTrace_S106 (H : RetainedCoreHistory.{u}) (k : Fin (H.eventCount + 1))
    {first : Fin (H.eventCount + 1)} {hle : first ≤ k} {x : (H.stage k).Carrier}
    (A : BackwardPointTrace H.toHistory first k hle x)
    (j : Fin (H.prefixAt k).eventCount)
    (hfj : first ≤ Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) j.succ) :
    BackwardPointTrace (H.prefixAt k).toHistory j.succ (Fin.last (H.prefixAt k).eventCount)
      (Fin.le_last _) x where
  point m hm1 hm2 := A.point (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) m)
    (hfj.trans (Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hm1)))
    (Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hm2))
  endpoint_eq := A.endpoint_eq
  crossing i hf hl := A.crossing ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ k.isLt)⟩
    (hfj.trans (Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hf)))
    (Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hl))

/-- The located barrier stated on the slice prefix (centre = prefix trace of the endpoint) gives the
tower-indexed barrier clause `hbar` of `traced_of_seeds_ball_S95` for the tower trace of `A`. -/
theorem hbar_tower_of_prefix_S106
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (s : RegularSlice F.observation)
    {l : Icc (0 : ℝ) s.history.horizon} (hlt : l ≤ sliceTop_S8 s) {r τ K : ℝ}
    {y : (s.history.stageAt (sliceTop_S8 s)).Carrier}
    (A : BackwardPointTrace s.history (s.history.activeStage l)
      (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hlt) y)
    (hbarP : ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
      (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
        (Fin.last (sliceHistoryR_O3 F s).eventCount) (Fin.le_last _)
        (restrictPoint_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s) y)),
      (sliceHistoryR_O3 F s).time j.succ ∈ Ioc (s.time - τ * r ^ 2) s.time →
      ∀ U : Set (((sliceHistoryR_O3 F s).toHistory.stage j.succ).Carrier),
      U ⊆ riemannianBallOf ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
        (B.point j.succ le_rfl (Fin.le_last _)) (20 * r) → IsPreconnected U →
      (∀ y ∈ U, metricScalarAt ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric y ≤
        (9 * K) / r ^ 2) →
      ∀ (x : ((sliceHistoryR_O3 F s).toHistory.event j).incoming.terminalRegularOpen)
        (z : ((sliceHistoryR_O3 F s).toHistory.stage j.succ).Carrier), z ∈ U →
        ((sliceHistoryR_O3 F s).toHistory.event j).RegularCrossing x.val z →
        U ⊆ interior (range ((sliceHistoryR_O3 F s).toHistory.event j).oldOutput)) :
    ∀ (i : Fin (sliceTowerHistory_CX2 s).eventCount)
      (hf : (sliceTowerHistory_CX2 s).activeStage
        (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) l) ≤ i.castSucc)
      (hl : i.succ ≤ (sliceTowerHistory_CX2 s).activeStage
        (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s))),
      (sliceTowerHistory_CX2 s).time i.succ ∈ Ioc (s.time - τ * r ^ 2) s.time →
      ∀ U : Set ((sliceTowerHistory_CX2 s).stage i.succ).Carrier,
      U ⊆ riemannianBallOf ((sliceTowerHistory_CX2 s).event i).outputMetric
        ((traceAtOfRestriction_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s)
          (hat := hlt) A).point i.succ (hf.trans i.castSucc_lt_succ.le) hl) (20 * r) →
      IsPreconnected U →
      (∀ y ∈ U, metricScalarAt ((sliceTowerHistory_CX2 s).event i).outputMetric y ≤
        (9 * K) / r ^ 2) →
      ∀ (x : ((sliceTowerHistory_CX2 s).event i).incoming.terminalRegularOpen)
        (y : ((sliceTowerHistory_CX2 s).stage i.succ).Carrier),
        y ∈ U → ((sliceTowerHistory_CX2 s).event i).RegularCrossing x.val y →
        U ⊆ interior (range ((sliceTowerHistory_CX2 s).event i).oldOutput) := by
  intro i hf hl ht U hUb hU hs x z hz hc
  have hij : i.val < (sliceHistoryR_O3 F s).eventCount :=
    Nat.lt_of_succ_le (Fin.le_iff_val_le_val.mp hl)
  let j : Fin (sliceHistoryR_O3 F s).eventCount := ⟨i.val, hij⟩
  let Y' := traceAtOfRestriction_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s)
    (hat := hlt) A
  let B := prefixTrace_S106 (F.tower.history (sliceIndexR_O3 F s)) (sliceStageR_O3 F s) Y' j
    (hf.trans i.castSucc_lt_succ.le)
  exact hbarP j B ht U hUb hU hs x z hz hc

end GC.LongTime.Ch12
