import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HShiftReduce_S131
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BufferLowCurv_S77
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SliceKernelInputs_S53

/-!
# CH12-S134, group 1: forward persistence of the scalar curvature along a trace (the P2 half of hbirth)

`fwd_scalar_lower_S134`: along any `BackwardPointTrace` `A` of a point `y` of the slice stage back to a stage
`first`, P2 above a threshold `q₀ ≥ neckRadius(s.time)⁻²` gives
`(max q₀ R(y))⁻¹ ≤ (max q₀ R(A.point first))⁻¹ + Ctime (s.time - time first)` (reciprocal form, forward direction).
`maxlower_S134` turns it into `R(birth)/(1 + Ctime R(birth) age) ≤ max q₀ R(y)`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}

theorem fwd_scalar_lower_S134 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (s : RegularSlice F.observation) (Ctime : ℝ≥0) (hP2 : P2_O2 Hp Ctime) {q₀ : ℝ} (hq₀ : 0 < q₀)
    (hq : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ q₀)
    (first : Fin ((sliceHistoryR_O3 F s).eventCount + 1))
    (hle : first ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
    (y : s.stage.Carrier)
    (A : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory first
      (Fin.last (sliceHistoryR_O3 F s).eventCount) hle y) :
    (max q₀ (metricScalarAt s.metric y))⁻¹ ≤
      (max q₀ (metricScalarAt ((sliceHistoryR_O3 F s).initialMetric first) (A.point first le_rfl hle)))⁻¹ +
        Ctime * (s.time - (sliceHistoryR_O3 F s).time first) := by
  let G := (sliceSlabR_O3 F s).restrictIncoming le_rfl (sliceSlabR_O3 F s).lt le_rfl
  let L := (sliceSlabR_O3 F s).endpointTerminalLimitMetric
    ((sliceHistoryR_O3 F s).stage (Fin.last (sliceHistoryR_O3 F s).eventCount))
  have hyG : y ∈ G.terminalRegularRegion := by
    change y ∈ ((sliceSlabR_O3 F s).restrictIncoming le_rfl (sliceSlabR_O3 F s).lt le_rfl).terminalRegularRegion
    rw [(sliceSlabR_O3 F s).terminalRegularRegion_eq_univ _]; exact mem_univ _
  let x' : G.terminalRegularOpen := ⟨y, hyG⟩
  have hLm : L.metric = s.metric.restrictOpen G.terminalRegularOpen := by
    change ((sliceSlabR_O3 F s).flow.base.metric s.time).restrictOpen _ = _
    rw [sliceSlabR_metric_time_O3 F s]
    rfl
  have hder := sliceHistory_eventSlabsDerivative_O3 Hp s Ctime q₀ hP2 hq
  have hfin := slice_hfinal_S53 Hp s Ctime q₀ hP2 hq
  have h := BackwardPointTrace.inv_max_scalar_initial_sub_incoming_terminal_le
    (H := (sliceHistoryR_O3 F s).toHistory) G L (sliceSlabR_initial_O3 F s) x' A (q := q₀) (C := Ctime)
    hq₀ (fun i hf hl τ hτ hqτ => hder i (lt_of_lt_of_le i.castSucc_lt_succ hl) _ _ hτ hqτ)
    (fun t ht hqt => hfin y t ht hqt)
  let U : TopologicalSpace.Opens s.stage.Carrier := G.terminalRegularOpen
  let x'' : U := ⟨y, hyG⟩
  have e0 : metricScalarAt (I := ThreeModel) (s.metric.restrictOpen U) x'' =
      metricScalarAt (I := ThreeModel) s.metric y := by
    have : IsManifold ThreeModel 1 U := IsManifold.of_le (I := ThreeModel) (n := ∞) (by decide)
    exact metricScalarAt_restrictOpen (I := ThreeModel) s.metric U x''
  have e1 : metricScalarAt L.metric x' = metricScalarAt s.metric y := by
    rw [hLm]; exact e0
  rw [e1] at h
  have h' := (abs_le.mp h).1
  linarith only [h']

/-- Real core: `M_b⁻¹ ≤ M_a⁻¹ + C T` (`M = max q₀ ·`), `0 < a`, `a T ≤ 1` give `a/(1+C) ≤ max q₀ b`. -/
theorem maxlower_S134 {q₀ a b C T : ℝ} (ha : 0 < a) (hq₀ : 0 < q₀) (hC : 0 ≤ C)
    (haT : a * T ≤ 1) (h : (max q₀ b)⁻¹ ≤ (max q₀ a)⁻¹ + C * T) :
    a / (1 + C) ≤ max q₀ b := by
  have hM : 0 < max q₀ b := lt_max_of_lt_left hq₀
  have h1 : (max q₀ a)⁻¹ ≤ a⁻¹ := inv_anti₀ ha (le_max_right _ _)
  have h2 : (max q₀ b)⁻¹ ≤ (1 + C) / a := by
    have : C * T ≤ C / a := by
      rw [le_div_iff₀ ha]; nlinarith only [mul_le_mul_of_nonneg_left haT hC]
    calc (max q₀ b)⁻¹ ≤ a⁻¹ + C / a := by linarith only [h, h1, this]
      _ = (1 + C) / a := by field_simp
  have h3 : a / (1 + C) = ((1 + C) / a)⁻¹ := by rw [inv_div]
  rw [h3]
  exact inv_le_of_inv_le₀ hM h2

end GC.LongTime.Ch12
