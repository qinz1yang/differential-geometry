import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialReserveTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IdentifiedHistoryPinching

/-!
# S-CH11-FIX9 port of astra `PreparedSpatialUniformPinching`（`PortC11P`）

来源：donor `PreparedSpatialUniformPinching.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补（no statement / definition /
proof idea altered；不加 `set_option`）：
* `hdomain` 的 `last` 情形：`rw [htime, hhor]` 前目标里是 `R.history.toHistory.time` /
  `.toHistory.horizon`，`htime` / `hhor` 是 `R.history.time` / `.horizon`（不同 head，`rw` 不跨）→
  先 `change` 到 `R.history.time … / R.history.horizon` 形；
* 两处 `add_le_add_right h _`（本树把加项放在左边，左右约定相反）→ `add_le_add h le_rfl`；
  `add_lt_add_right hs.2 _` → `add_lt_add_of_lt_of_le hs.2 le_rfl`；
* 陈述里 4 个只在 `intro` 里引用的 binder 名（`hLR hshift hoffset hshift_nonneg`）→ 加 `_` 前缀
  （unusedVariables；binder 名不改变陈述）。

原路径 `PreparedSpatialUniformPinching` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology

namespace GC.GeneralFlow
universe u

open private own_native_tail_trace_presentation from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialReserveTransport
open private overlapCastPoint overlapCastPoint_heq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SpatialWitnessTransport

/-- The curvature operator and its scalar argument use the same actual metric. -/
private theorem pinching_bound_of_metric_heq
    {P Q : OrientedThreeStage.{u}} (hP : P = Q)
    {gP : P.Metric} {gQ : Q.Metric} (hg : HEq gP gQ)
    {x : P.Carrier} {y : Q.Carrier} (hxy : HEq x y) (phi : ℝ → ℝ)
    (h : curvatureOperatorLowerBoundAt (I := ThreeModel) gP x
      (metricAlgebraicCurvatureTensorAt (I := ThreeModel) gP x)
      (phi (metricScalarAt (I := ThreeModel) gP x))) :
    curvatureOperatorLowerBoundAt (I := ThreeModel) gQ y
      (metricAlgebraicCurvatureTensorAt (I := ThreeModel) gQ y)
      (phi (metricScalarAt (I := ThreeModel) gQ y)) := by
  cases hP
  cases eq_of_heq hg
  cases eq_of_heq hxy
  exact h

/-- Choose the pinching function from the original data before every prepared
class, and keep it on the actual retained native clocks and postmetrics. -/
theorem exists_uniform_pinching_for_same_full_native_steps
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi ∧
    ∀ {pBase : CutoffParameters} {C : ClosedBirthConstants}
      {E B Bnext activation eta d εcut Dcut : ℝ} {mcut : ℕ}
      {L : PreparedSpatialState pBase C P g E B}
      {R : PreparedSpatialState pBase C P g B Bnext}
      (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut)
      (_hLR : PreparedSpatialSuccessor L R activation eta d)
      (_hshift : R.shift = L.history.time (Fin.last L.history.eventCount))
      (_hoffset : R.offset = L.history.eventCount)
      (_hshift_nonneg : 0 ≤ L.shift),
      W.oldNative.EventSlabsPinched phi ∧
      ∀ hfinal : W.oldNative.time (Fin.last W.oldNative.eventCount) < W.oldNative.horizon,
        Perelman.PhiAlmostNonnegative (W.oldNative.finalSlab hfinal).flow
          (Icc (W.oldNative.time (Fin.last W.oldNative.eventCount)) W.oldNative.horizon) phi := by
  obtain ⟨a, ha, hzero⟩ :=
    exists_pos_fixedHamiltonIveyRegion_for_identified_histories P g
  obtain ⟨phi, hphi, hall⟩ :=
    Perelman.exists_admissiblePinchingFunction_for_observedHistories.{u} ha
  refine ⟨phi, hphi, ?_⟩
  intro pBase C E B Bnext activation eta d εcut Dcut mcut L R W hLR hshift hoffset
    _hshift_nonneg
  have hinitial := hzero R.history.toHistory R.initial
  have hfull := (hall R.history.toHistory R.parameters R.records
    hinitial.1 hinitial.2).1
  obtain ⟨hcount, hdata, _⟩ := own_native_tail_trace_presentation W hLR hshift hoffset
  let liftStage : Fin (W.oldNative.eventCount + 1) → Fin (R.history.eventCount + 1) :=
    fun j => ⟨L.offset + j.val, by have := j.isLt; omega⟩
  have hhor : R.history.horizon = W.oldNative.horizon + L.shift := by
    rw [R.horizon_eq, W.oldNative_horizon]
    ring
  have hdomain (j : Fin (W.oldNative.eventCount + 1)) (s : ℝ)
      (hs : s ∈ W.oldNative.toHistory.stageDomain j) :
      s + L.shift ∈ R.history.toHistory.stageDomain (liftStage j) := by
    cases j using Fin.lastCases with
    | last =>
      have hlast : liftStage (Fin.last W.oldNative.eventCount) =
          Fin.last R.history.eventCount := Fin.ext hcount.symm
      have htime := (hdata (Fin.last W.oldNative.eventCount)).1
      change R.history.time (liftStage (Fin.last W.oldNative.eventCount)) =
        W.oldNative.time (Fin.last W.oldNative.eventCount) + L.shift at htime
      rw [hlast] at htime
      rw [hlast, R.history.toHistory.mem_stageDomain_last]
      have hs' := (W.oldNative.toHistory.mem_stageDomain_last s).1 hs
      change s + L.shift ∈ Icc (R.history.time (Fin.last R.history.eventCount)) R.history.horizon
      rw [htime, hhor]
      exact ⟨add_le_add hs'.1 le_rfl, add_le_add hs'.2 le_rfl⟩
    | cast i =>
      let iR : Fin R.history.eventCount :=
        ⟨L.offset + i.val, by have := i.isLt; omega⟩
      have hleft : liftStage i.castSucc = iR.castSucc := rfl
      have hright : liftStage i.succ = iR.succ := Fin.ext rfl
      have htleft := (hdata i.castSucc).1
      have htright := (hdata i.succ).1
      change R.history.time (liftStage i.castSucc) =
        W.oldNative.time i.castSucc + L.shift at htleft
      change R.history.time (liftStage i.succ) =
        W.oldNative.time i.succ + L.shift at htright
      rw [hleft] at htleft
      rw [hright] at htright
      simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] at hs
      rw [hleft]
      simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc]
      rw [htleft, htright]
      exact ⟨add_le_add hs.1 le_rfl, add_lt_add_of_lt_of_le hs.2 le_rfl⟩
  have hnative (j : Fin (W.oldNative.eventCount + 1)) (s : ℝ)
      (hs : s ∈ W.oldNative.toHistory.stageDomain j)
      (x : (W.oldNative.stage j).Carrier) :
      curvatureOperatorLowerBoundAt (I := ThreeModel)
        (W.oldNative.toHistory.stageMetric j s) x
        (metricAlgebraicCurvatureTensorAt (I := ThreeModel)
          (W.oldNative.toHistory.stageMetric j s) x)
        (phi (metricScalarAt (I := ThreeModel)
          (W.oldNative.toHistory.stageMetric j s) x)) := by
    have hstage : R.history.stage (liftStage j) = W.oldNative.stage j := (hdata j).2.1
    let y := overlapCastPoint hstage.symm x
    have hxy : HEq y x := overlapCastPoint_heq hstage.symm x
    exact pinching_bound_of_metric_heq hstage ((hdata j).2.2 s hs) hxy phi
      (hfull (liftStage j) (s + L.shift) (hdomain j s hs) y)
  constructor
  · intro i s hs x
    have hdom : s ∈ W.oldNative.toHistory.stageDomain i.castSucc := by
      simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using hs
    have h := hnative i.castSucc s hdom x
    rw [ObservedHistory.stageMetric_castSucc_apply] at h
    exact h
  · intro hfinal s hs x
    have hdom : s ∈ W.oldNative.toHistory.stageDomain (Fin.last W.oldNative.eventCount) :=
      (W.oldNative.toHistory.mem_stageDomain_last s).2 hs
    have h := hnative (Fin.last W.oldNative.eventCount) s hdom x
    rw [ObservedHistory.stageMetric_last_of_lt (h := hfinal)] at h
    exact h

end GC.GeneralFlow
