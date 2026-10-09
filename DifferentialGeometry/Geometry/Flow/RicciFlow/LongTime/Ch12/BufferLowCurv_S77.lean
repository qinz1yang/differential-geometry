import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueSliceTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceReciprocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceScalarControl

/-!
# CH12-S77, group 1: the time half of the buffer low-curvature estimate

`buffer_lowcurv_S77`: on the slice history, along any backward trace `A` of a point `y` of the slice
stage (back to a stage `first`), a scalar-curvature bound `R ≤ M` at a time `t₁` of the last slab
(`M ≥ neckRadius(s.time)⁻²`, so that P2 applies from `M` upward) gives `R ≤ 4 M` at the initial
(post-surgery) time of EVERY earlier stage along the trace, as long as `4 Ctime M (t₁ - time first) ≤ 1`.
This is the "P2 time half" of ZT's buffered neighbourhood (D-R3-13): with `M = C₀ / ρ²` it is the
curvature upper bound `R ≤ 4 C₀ / ρ²` at the births of all traced preimages, which is what turns a
young cap in the buffer into `h_j ≥ c ρ` (see `[FROZEN] CH12-S77`).  The spatial half is trivial:
`B(q, 2 a ρ) ⊆ B(p, 2 ρ)` for `a ≤ 1/2`, `q ∈ B(p, ρ)` (`hZ0` doubled ball).
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff NNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}

theorem buffer_lowcurv_S77 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (s : RegularSlice F.observation) (Ctime : ℝ≥0) (hP2 : P2_O2 Hp Ctime) {M t₁ : ℝ}
    (hM : 0 < M) (hq : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ M)
    (hlt : (sliceHistoryR_O3 F s).time (Fin.last (sliceHistoryR_O3 F s).eventCount) ≤ t₁)
    (ht₁ : t₁ < s.time) (first : Fin ((sliceHistoryR_O3 F s).eventCount + 1))
    (hle : first ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
    (y : ((sliceHistoryR_O3 F s).stage (Fin.last (sliceHistoryR_O3 F s).eventCount)).Carrier)
    (A : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory first
      (Fin.last (sliceHistoryR_O3 F s).eventCount) hle y)
    (hy : metricScalarAt ((sliceSlabR_O3 F s).flow.base.metric t₁) y ≤ M)
    (htime : 4 * Ctime * M * (t₁ - (sliceHistoryR_O3 F s).time first) ≤ 1) :
    metricScalarAt ((sliceHistoryR_O3 F s).initialMetric first) (A.point first le_rfl hle) ≤ 4 * M := by
  have hpast : (sliceHistoryR_O3 F s).time first ≤
      (sliceHistoryR_O3 F s).time (Fin.last (sliceHistoryR_O3 F s).eventCount) :=
    (sliceHistoryR_O3 F s).time_strictMono.monotone hle
  have hC : (0 : ℝ) ≤ Ctime * M := mul_nonneg Ctime.coe_nonneg hM.le
  have hslab : ((sliceSlabR_O3 F s).restrictIncoming le_rfl (sliceSlabR_O3 F s).lt le_rfl).flow.scalar
      ((sliceHistoryR_O3 F s).time (Fin.last (sliceHistoryR_O3 F s).eventCount)) y ≤ 2 * M := by
    refine OrientedThreeStage.IncomingSlab.scalar_le_two_mul_of_derivativeBoundBefore
      ((sliceSlabR_O3 F s).restrictIncoming le_rfl (sliceSlabR_O3 F s).lt le_rfl) (Ctime := Ctime)
      (qcan := M) (M := M) (t := t₁) (u := (sliceHistoryR_O3 F s).time (Fin.last (sliceHistoryR_O3 F s).eventCount))
      (v := (sliceHistoryR_O3 F s).time (Fin.last (sliceHistoryR_O3 F s).eventCount)) y
      (fun z τ hτ hqz => sliceSlab_derivative_O3 Hp s Ctime M hP2 hq z τ ⟨hτ.1, lt_trans hτ.2 ht₁⟩ hqz)
      ht₁ le_rfl le_rfl hlt hM le_rfl hy ?_
    nlinarith
  have hinit : ((sliceSlabR_O3 F s).restrictIncoming le_rfl (sliceSlabR_O3 F s).lt le_rfl).flow.scalar
      ((sliceHistoryR_O3 F s).time (Fin.last (sliceHistoryR_O3 F s).eventCount)) y =
      metricScalarAt ((sliceHistoryR_O3 F s).initialMetric (Fin.last (sliceHistoryR_O3 F s).eventCount)) y := by
    change metricScalarAt ((sliceSlabR_O3 F s).flow.base.metric _) y = _
    rw [sliceSlabR_initial_O3]
  rw [hinit] at hslab
  have hder := sliceHistory_eventSlabsDerivative_O3 Hp s Ctime M hP2 hq
  have h := BackwardPointTrace.scalar_le_two_mul_of_time_sub_le (H := (sliceHistoryR_O3 F s).toHistory)
    _ first hle y A (q := M) (Q := 2 * M) (C := Ctime) hM (by linarith)
    (fun i hf hl τ hτ hqτ => hder i (lt_of_lt_of_le i.castSucc_lt_succ hl) _ _ hτ hqτ) hslab
    (by nlinarith)
  linarith

end GC.LongTime.Ch12
