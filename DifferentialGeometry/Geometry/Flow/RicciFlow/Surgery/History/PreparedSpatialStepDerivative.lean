import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStepRetention
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.AffineHistoryParabolicBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SpatialWitnessTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStageMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.CostDefs
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
S-CH11-FIX6 patched-at-path（astra `History/PreparedSpatialStepDerivative` 的 elaboration 修补；
下游 `PreparedSpatialBirthBlockLookup` / `PreparedSpatialReserveTransport` /
`PreparedSpatialOwnThresholdDerivatives` 有 `open private … from` 本路径）。陈述 / 证明思路逐字不变，
只有 `J.toHistory.time` / `J.time` / `.horizon` 两种 head 的 `rw` 不匹配与依赖类型位的 `simpa`：
(a) `event_samePresentation_of_prefix` 的 `simpa only [hi] using hE` → `rw [hi] at hE; exact hE`；
(b) 3 处（`hTime`、`hEnd` 的 `cast` 情形前的 `rw`、`last` 情形的 `horizon_eq`）与 `cast` 情形的
    `stageIndex_time` 前补 `change` 到 `.toHistory.time` / `.time` / `.horizon` 的对应形；
(c) `hMetric` 里 `simpa only [hk, sub_add_cancel, hclock] using …`（simp 进不了 `stageMetric` 的依赖
    index 位）→ `rw [hk] at hFull; simp only [sub_add_cancel] at hFull; simp only [hclock] at hNative;
    exact hFull.trans hNative.symm`。
-/

set_option autoImplicit false
noncomputable section
open Set Filter DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff NNReal Topology Pointwise
namespace GC.GeneralFlow
universe u

open private overlapCastPoint overlapCastPoint_heq overlap_scalar_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SpatialWitnessTransport
open private retained_event_incoming_heq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CutoffRecordConcatenation

/-- The original prefix-event presentation proof, used here below the final-flow layer. -/
private theorem event_samePresentation_of_prefix
    {H J : ObservedHistory.{u}} (hp : H.IsPrefixOf J)
    (hn : H.eventCount ≤ J.eventCount) (i : Fin H.eventCount) :
    (J.event (i.castLE hn)).SamePresentation (H.event i) := by
  let a : Icc (0 : ℝ) J.horizon := ⟨H.horizon, H.horizon_nonneg, hp.horizon_le⟩
  let iR : Fin (J.restrict a).eventCount := Fin.cast hp.presentation.count_eq.symm i
  have hi : Fin.cast hp.presentation.count_eq iR = i := Fin.ext rfl
  have hE := hp.presentation.event_eq iR
  change (J.event (i.castLE hn)).SamePresentation
    (H.event (Fin.cast hp.presentation.count_eq iR)) at hE
  rw [hi] at hE
  exact hE

/-- A unit time translation preserves the one-sided derivative of an actual scalar germ. -/
private theorem derivative_bound_of_translated_germ
    {f g : ℝ → ℝ} {s c : ℝ} {Ctime : ℝ≥0}
    (h : f =ᶠ[𝓝 s] (fun u => g (u - c)))
    (hg : |derivWithin g (Iic (s - c)) (s - c)| ≤ Ctime * g (s - c) ^ 2) :
    |derivWithin f (Iic s) s| ≤ Ctime * f s ^ 2 := by
  have hset : -c +ᵥ Iic s = Iic (s - c) := by
    ext u
    change (∃ v, v ≤ s ∧ -c + v = u) ↔ u ≤ s - c
    constructor
    · rintro ⟨v, hv, rfl⟩
      linarith
    · intro hu
      exact ⟨u + c, by linarith, by ring⟩
  have hd : derivWithin f (Iic s) s = derivWithin g (Iic (s - c)) (s - c) := by
    rw [h.derivWithin_eq_of_nhds, derivWithin_comp_sub_const, hset]
  rw [hd, h.eq_of_nhds]
  exact hg

/-- Extract only the derivative certificate on an actual open stage interval. -/
private theorem native_stage_derivative_bound
    {K : RetainedCoreHistory.{u}}
    {ε C1 C2 C1s C2s qcan qs τmin : ℝ} {Ctime Cgrad : ℝ≥0}
    (hEst : NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad)
    (j : Fin (K.eventCount + 1)) (x : (K.stage j).Carrier) (t : ℝ)
    (ht : t ∈ Ioo (K.time j) (K.toHistory.stageEndTime j))
    (hR : qcan < metricScalarAt (K.toHistory.stageMetric j t) x) :
    |derivWithin (fun v => metricScalarAt (K.toHistory.stageMetric j v) x) (Iic t) t| ≤
      Ctime * metricScalarAt (K.toHistory.stageMetric j t) x ^ 2 := by
  cases j using Fin.lastCases with
  | last =>
    rw [K.toHistory.stageEndTime_last] at ht
    have hfinal : K.time (Fin.last K.eventCount) < K.horizon := ht.1.trans ht.2
    simp only [ObservedHistory.stageMetric_last_of_lt (H := K.toHistory) (h := hfinal)] at hR ⊢
    exact (hEst.2 hfinal).1 x t ht hR
  | cast i =>
    rw [K.toHistory.stageEndTime_castSucc] at ht
    simp only [ObservedHistory.stageMetric_castSucc_apply] at hR ⊢
    exact (hEst.1 i).1 x t ht hR

/-- The old native class controls its entire actual tail in the new full history.
The old full prefix is compared only on a genuine open scalar germ. -/
theorem PreparedSpatialStepRetention.derivative_bound_on_old_native_tail
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {E B Bnext activation eta d εcut Dcut : ℝ} {mcut : ℕ}
    {L : PreparedSpatialState pBase C P g E B}
    {R : PreparedSpatialState pBase C P g B Bnext}
    (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut)
    (hLR : PreparedSpatialSuccessor L R activation eta d)
    (hshift : R.shift = L.history.time (Fin.last L.history.eventCount))
    (hoffset : R.offset = L.history.eventCount)
    (j : Fin (R.history.eventCount + 1)) (hj : L.offset ≤ j.val)
    (y : (R.history.stage j).Carrier)
    (s : ℝ) (hs : s ∈ Ioo (R.history.time j) (R.history.toHistory.stageEndTime j))
    (hscalar : (L.radius ^ 2)⁻¹ <
      metricScalarAt (R.history.toHistory.stageMetric j s) y) :
    |derivWithin (fun u => metricScalarAt (R.history.toHistory.stageMetric j u) y)
      (Iic s) s| ≤
      C.Ctime * metricScalarAt (R.history.toHistory.stageMetric j s) y ^ 2 := by
  have hq : L.prepared.qcan ≤ (L.radius ^ 2)⁻¹ := by
    apply le_trans _ L.threshold_le
    apply le_trans ((le_max_left L.prepared.qcan L.prepared.qs).trans
      ((le_max_right 1 (max L.prepared.qcan L.prepared.qs)).trans L.prepared.Qbirth_ge))
    rw [L.prepared.Qall_eq]
    exact le_max_left _ _
  by_cases hjOld : j.val < L.history.eventCount
  · let iOld : Fin L.history.eventCount := ⟨j.val, hjOld⟩
    let iFull : Fin R.history.eventCount := iOld.castLE hLR.count_le
    have hjFull : j = iFull.castSucc := Fin.ext rfl
    let i : Fin L.native.eventCount :=
      ⟨j.val - L.offset, by have := L.affine.count_eq; omega⟩
    have hiOld : L.affine.eventIndex i = iOld := by
      apply Fin.ext
      change L.offset + (j.val - L.offset) = j.val
      omega
    let iK : Fin W.oldNative.eventCount := i.castLE W.oldNativeRawPrefix.count_le
    have hPresent := event_samePresentation_of_prefix hLR.initial_prefix.1 hLR.count_le iOld
    have hAffStage := L.affine.stageIndex_stage i.castSucc
    rw [AffineEventPrefix.stageIndex_castSucc, hiOld] at hAffStage
    have hRawStage := W.oldNativeRawPrefix.stage_eq i.castSucc
    change W.oldNative.stage iK.castSucc = L.native.stage i.castSucc at hRawStage
    have hStage : R.history.stage j = W.oldNative.stage iK.castSucc :=
      (congrArg R.history.stage hjFull).trans
        (hPresent.incomingStage_eq.trans (hAffStage.trans hRawStage.symm))
    have hTime : R.history.time j = W.oldNative.time iK.castSucc + L.shift := by
      have hAff := L.affine.stageIndex_time i.castSucc
      rw [AffineEventPrefix.stageIndex_castSucc, hiOld] at hAff
      have hRaw := W.oldNativeRawPrefix.time_eq i.castSucc
      change W.oldNative.time iK.castSucc = L.native.time i.castSucc at hRaw
      rw [hjFull]
      change R.history.toHistory.time iFull.castSucc = W.oldNative.time iK.castSucc + L.shift
      rw [hPresent.leftTime_eq]
      change L.history.time iOld.castSucc = W.oldNative.time iK.castSucc + L.shift
      rw [hAff, ← hRaw]
    have hEnd : R.history.toHistory.stageEndTime j =
        W.oldNative.time iK.succ + L.shift := by
      have hAff := L.affine.stageIndex_time i.succ
      rw [AffineEventPrefix.stageIndex_succ, hiOld] at hAff
      have hRaw := W.oldNativeRawPrefix.time_eq i.succ
      change W.oldNative.time iK.succ = L.native.time i.succ at hRaw
      rw [hjFull, R.history.toHistory.stageEndTime_castSucc, hPresent.eventTime_eq]
      change L.history.time iOld.succ = W.oldNative.time iK.succ + L.shift
      rw [hAff, ← hRaw]
    let z := overlapCastPoint hStage y
    have hPoint : HEq y z := (overlapCastPoint_heq hStage y).symm
    let f := fun u => metricScalarAt (R.history.toHistory.stageMetric j u) y
    let gK := fun u => metricScalarAt
      ((W.oldNative.toHistory.event iK).incoming.flow.base.metric u) z
    have hMetric (u : ℝ)
        (hu : u ∈ Ioo (R.history.time j) (R.history.toHistory.stageEndTime j)) :
        HEq (R.history.toHistory.stageMetric j u)
          ((W.oldNative.toHistory.event iK).incoming.flow.base.metric (u - L.shift)) := by
      have hPrefix := hPresent.incomingMetric_heq u
        (by simpa only [hjFull, R.history.toHistory.stageEndTime_castSucc] using
          (show u ∈ Ico (R.history.time j) (R.history.toHistory.stageEndTime j) from
            ⟨hu.1.le, hu.2⟩))
      have hAff := L.affine.incoming_metric_heq i u
      change HEq
        ((L.history.toHistory.event (L.affine.eventIndex i)).incoming.flow.base.metric u)
        ((L.native.toHistory.event i).incoming.flow.base.metric (u - L.shift)) at hAff
      rw [hiOld] at hAff
      have hRaw := retained_event_incoming_heq
        (W.oldNativeRawPrefix.stage_eq i.castSucc)
        (W.oldNativeRawPrefix.stage_eq i.succ)
        (W.oldNativeRawPrefix.time_eq i.castSucc)
        (W.oldNativeRawPrefix.time_eq i.succ)
        (W.oldNativeRawPrefix.event_heq i) (u - L.shift)
      change HEq ((W.oldNative.toHistory.event iK).incoming.flow.base.metric (u - L.shift))
        ((L.native.toHistory.event i).incoming.flow.base.metric (u - L.shift)) at hRaw
      have hFull : HEq (R.history.toHistory.stageMetric j u)
          ((R.history.toHistory.event iFull).incoming.flow.base.metric u) := by
        rw [hjFull, ObservedHistory.stageMetric_castSucc_apply]
      exact hFull.trans (hPrefix.trans (hAff.trans hRaw.symm))
    have hGerm : f =ᶠ[𝓝 s] (fun u => gK (u - L.shift)) := by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with u hu
      exact overlap_scalar_eq hStage (hMetric u hu) hPoint
    have hTimeK : s - L.shift ∈ Ioo (W.oldNative.time iK.castSucc)
        (W.oldNative.time iK.succ) := by
      rw [hTime, hEnd] at hs
      constructor <;> linarith [hs.1, hs.2]
    have hScalarK : L.prepared.qcan < gK (s - L.shift) := by
      rw [← hGerm.eq_of_nhds]
      exact hq.trans_lt hscalar
    have hBound : |derivWithin gK (Iic (s - L.shift)) (s - L.shift)| ≤
        C.Ctime * gK (s - L.shift) ^ 2 :=
      (W.oldNative_estimates.1 iK).1 z (s - L.shift) hTimeK hScalarK
    exact derivative_bound_of_translated_germ hGerm hBound
  · have hFresh : R.offset ≤ j.val := by rw [hoffset]; omega
    let k : Fin (R.native.eventCount + 1) :=
      ⟨j.val - R.offset, by have := R.affine.count_eq; have := j.isLt; omega⟩
    have hk : R.affine.stageIndex k = j := by
      apply Fin.ext
      change R.offset + (j.val - R.offset) = j.val
      omega
    let kK := W.oldNativeAffine.stageIndex k
    have hStage : R.history.stage j = W.oldNative.stage kK := by
      rw [← hk]
      exact (R.affine.stageIndex_stage k).trans
        (W.oldNativeAffine.stageIndex_stage k).symm
    have hba : R.shift = L.native.time (Fin.last L.native.eventCount) + L.shift := by
      rw [hshift]
      have h := L.affine.stageIndex_time (Fin.last L.native.eventCount)
      rw [L.affine.stageIndex_last] at h
      exact h
    have hTime : R.history.time j = W.oldNative.time kK + L.shift := by
      rw [← hk, R.affine.stageIndex_time]
      change R.native.time k + R.shift =
        W.oldNative.time (W.oldNativeAffine.stageIndex k) + L.shift
      rw [W.oldNativeAffine.stageIndex_time, hba]
      ring
    have hEnd : R.history.toHistory.stageEndTime j =
        W.oldNative.toHistory.stageEndTime kK + L.shift := by
      rw [← hk]
      change R.history.toHistory.stageEndTime (R.affine.stageIndex k) =
        W.oldNative.toHistory.stageEndTime (W.oldNativeAffine.stageIndex k) + L.shift
      cases k using Fin.lastCases with
      | last =>
        rw [R.affine.stageIndex_last, W.oldNativeAffine.stageIndex_last,
          R.history.toHistory.stageEndTime_last, W.oldNative.toHistory.stageEndTime_last]
        change R.history.horizon = W.oldNative.horizon + L.shift
        rw [R.horizon_eq, W.oldNative_horizon]
        ring
      | cast i =>
        rw [R.affine.stageIndex_castSucc, W.oldNativeAffine.stageIndex_castSucc,
          R.history.toHistory.stageEndTime_castSucc,
          W.oldNative.toHistory.stageEndTime_castSucc,
          ← R.affine.stageIndex_succ, ← W.oldNativeAffine.stageIndex_succ]
        change R.history.time (R.affine.stageIndex i.succ) =
          W.oldNative.time (W.oldNativeAffine.stageIndex i.succ) + L.shift
        rw [R.affine.stageIndex_time, W.oldNativeAffine.stageIndex_time, hba]
        ring
    let z := overlapCastPoint hStage y
    have hPoint : HEq y z := (overlapCastPoint_heq hStage y).symm
    let f := fun u => metricScalarAt (R.history.toHistory.stageMetric j u) y
    let gK := fun u => metricScalarAt (W.oldNative.toHistory.stageMetric kK u) z
    have hMetric (u : ℝ) : HEq (R.history.toHistory.stageMetric j u)
        (W.oldNative.toHistory.stageMetric kK (u - L.shift)) := by
      have hFull := R.affine.stageMetric_shift_heq R.finalMetric_heq k (u - R.shift)
      have hNative := W.oldNativeAffine.stageMetric_shift_heq W.oldNative_finalMetric k
        (u - R.shift)
      have hclock : (u - R.shift) + L.native.time (Fin.last L.native.eventCount) =
          u - L.shift := by rw [hba]; ring
      rw [hk] at hFull
      simp only [sub_add_cancel] at hFull
      simp only [hclock] at hNative
      exact hFull.trans hNative.symm
    have hGerm : f =ᶠ[𝓝 s] (fun u => gK (u - L.shift)) := by
      exact Filter.Eventually.of_forall fun u => overlap_scalar_eq hStage (hMetric u) hPoint
    have hTimeK : s - L.shift ∈ Ioo (W.oldNative.time kK)
        (W.oldNative.toHistory.stageEndTime kK) := by
      rw [hTime, hEnd] at hs
      constructor <;> linarith [hs.1, hs.2]
    have hScalarK : L.prepared.qcan < gK (s - L.shift) := by
      rw [← hGerm.eq_of_nhds]
      exact hq.trans_lt hscalar
    have hBound := native_stage_derivative_bound W.oldNative_estimates kK z
      (s - L.shift) hTimeK hScalarK
    exact derivative_bound_of_translated_germ hGerm hBound

end GC.GeneralFlow
