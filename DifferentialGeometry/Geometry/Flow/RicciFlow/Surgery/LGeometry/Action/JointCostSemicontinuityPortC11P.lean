import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.ClockTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.EndpointSemicontinuity

/-!
# S-CH11-FIX4 `PortC11P` port

Module `Surgery.LGeometry.Action.JointCostSemicontinuity`.

Source: donor file of the same relative path in the chapter-11 branch (ch11 HEAD a73e4bdbfd).
Verbatim it does not elaborate against this tree (3 errors, all the same cause).  `ClockTransfer`
is now a shim over `ClockTransferPortC11P`, and private declarations are mangled in the port
module, so an `open private .. from ..ClockTransfer` finds nothing.  Two repairs:
* `open private ObservedHistory.eventually_regularizedC1ActionValues_transfer_clock_on_sublevel
  from ..ClockTransferPortC11P` (module name of the port; declaration name written
  `ObservedHistory.foo`).
* the use site `htransfer := ..` also writes `ObservedHistory.foo`.
No statement, definition or proof idea is altered.  The module
`Surgery.LGeometry.Action.JointCostSemicontinuity` is a shim re-exporting this file.
-/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open private ObservedHistory.eventually_regularizedC1ActionValues_transfer_clock_on_sublevel from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.ClockTransferPortC11P
open private exists_regularizedC1Action_lt_of_regularizedCost_le from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.EndpointSemicontinuity

universe u

/-- Joint lower semicontinuity of the original action cost on one true open
first slab. The actual history, pole, scalar-cost parameter and event nodes stay
fixed. Infinite costs, including unreachable endpoints, are retained. -/
theorem lowerSemicontinuousOn_regularizedCost_clock_past_endpoint
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hupper : T ∈ H.stageDomain last)
    (hclock : ∀ w ∈ Icc a b,
      T - w ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ s ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T b j.val),
      ∀ y : (H.stage j.val).Carrier,
        -B ≤ metricScalarAt (H.stageMetric j.val (T - s ^ 2)) y)
    (x : (H.stage last).Carrier) :
    LowerSemicontinuousOn
      (fun z : ℝ × (H.stage first).Carrier =>
        H.regularizedCost first last hle T B 0 z.1 x z.2)
      (Icc a b ×ˢ univ) := by
  have hupper0 : T - 0 ^ 2 ∈ H.stageDomain last := by simpa using hupper
  have hscalarw (w : ℝ) (hw : w ∈ Icc a b) :
      ∀ j : H.StageInterval first last,
        ∀ s ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T w j.val),
        ∀ y : (H.stage j.val).Carrier,
          -B ≤ metricScalarAt (H.stageMetric j.val (T - s ^ 2)) y := by
    intro j s hs y
    exact hscalar j s ⟨hs.1, hs.2.trans_le
      (H.regularizedStageEnd_monotoneOn T j.val (ha.le.trans hw.1)
        (ha.le.trans hab) hw.2)⟩ y
  intro z hz bound hbound
  cases bound using WithTop.recTopCoe with
  | top => exact False.elim (not_lt_of_ge le_top hbound)
  | coe bound =>
    obtain ⟨ε, hε, hgap⟩ : ∃ ε : ℝ, 0 < ε ∧
        ((bound + 3 * ε : ℝ) : WithTop ℝ) <
          H.regularizedCost first last hle T B 0 z.1 x z.2 := by
      cases hval : H.regularizedCost first last hle T B 0 z.1 x z.2 using WithTop.recTopCoe with
      | top => exact ⟨1, by norm_num, WithTop.coe_lt_top _⟩
      | coe value =>
        have hreal : bound < value := WithTop.coe_lt_coe.mp (by simpa only [hval] using hbound)
        refine ⟨(value - bound) / 4, by linarith, WithTop.coe_lt_coe.mpr ?_⟩
        linarith
    have hfixed := H.lowerSemicontinuous_regularizedCost first last hle T B 0 z.1
      hupper0 (hscalarw z.1 hz.1) x z.2 ((bound + 3 * ε : ℝ) : WithTop ℝ) hgap
    have htransfer :=
      ObservedHistory.eventually_regularizedC1ActionValues_transfer_clock_on_sublevel H
      first last hle T B a b ha hab hupper hclock hscalar x z.1 hz.1
      (bound + ε) ε hε
    have hfst : Tendsto (Prod.fst : ℝ × (H.stage first).Carrier → ℝ)
        (𝓝[Icc a b ×ˢ univ] z) (𝓝[Icc a b] z.1) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hy.1
    have hsnd : Tendsto (Prod.snd : ℝ × (H.stage first).Carrier → (H.stage first).Carrier)
        (𝓝[Icc a b ×ˢ univ] z) (𝓝 z.2) :=
      continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    filter_upwards [hfst.eventually htransfer, hsnd.eventually hfixed,
      self_mem_nhdsWithin] with y hytransfer hyfixed hy
    by_contra hnot
    have hcost : H.regularizedCost first last hle T B 0 y.1 x y.2 ≤ (bound : WithTop ℝ) :=
      le_of_not_gt hnot
    obtain ⟨ell, hell, hellbound⟩ := exists_regularizedC1Action_lt_of_regularizedCost_le H
      first last hle T B 0 y.1 hupper0 (hscalarw y.1 hy.1) x y.2 bound ε hε hcost
    obtain ⟨ell', hell', hell'bound⟩ := hytransfer y.2 ell hell hellbound.le
    have hcostv : H.regularizedCost first last hle T B 0 z.1 x y.2 ≤ (ell' : WithTop ℝ) := by
      rw [H.regularizedCost_eq_regularizedC1Cost first last hle T B 0 z.1
        hupper0 (hscalarw z.1 hz.1)]
      exact H.regularizedC1Cost_le_of_competitor first last hle T 0 z.1 B
        (hscalarw z.1 hz.1) x y.2 hell'
    have hupper' : (ell' : WithTop ℝ) < ((bound + 3 * ε : ℝ) : WithTop ℝ) :=
      WithTop.coe_lt_coe.mpr (by linarith)
    exact (not_lt_of_ge (hcostv.trans hupper'.le)) hyfixed

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
