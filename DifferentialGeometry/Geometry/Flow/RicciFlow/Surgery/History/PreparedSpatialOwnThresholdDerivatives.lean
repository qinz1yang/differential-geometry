import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStepDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.NativeObservationDerivativeBounds

/-!
# S-CH11-FIX9 patched-at-path of astra `PreparedSpatialOwnThresholdDerivatives`

来源：donor `PreparedSpatialOwnThresholdDerivatives.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败（`open private … from` 指向的 `PreparedSpatialStepDerivative`
已由 FIX6 patched-at-path 落地，`NativeObservationDerivativeBounds` 由 FIX8 port+shim 落地）。
本文件只有 elaboration 层面修补（no statement / definition / proof idea altered；不加
`set_option`）。修法与同族 `PreparedSpatialStepDerivative`（FIX6 G5）的 `.toHistory.time` /
`.time` / `.horizon` 两种 head 的 `rw` 不匹配一致：
* `own_threshold_native_tail_stageMetric` 的 `hTime`、`hEnd`（prefix 情形）、`hEnd`（`last` 情形的
  `horizon_eq`、`cast` 情形的 `stageIndex_time`）前补 `change` 到对应 head（`J.toHistory.time` /
  `J.time` / `J.horizon`）；
* `hMetric` 里 `simpa only [hk, sub_add_cancel, hclock] using …`：simp 进不了 `stageMetric` 的
  依赖 index 位 → `rw [hk] at hFull; simp only [sub_add_cancel] at hFull;
  simp only [hclock] at hNative; exact hFull.trans hNative.symm`；
* 主定理里 `apply derivative_bound_of_translated_germ hGerm`：`fun u => ?g (u - ?c)` 的高阶模式
  统一不了 → 显式 `(g := fun w => metricScalarAt (W.oldNative.toHistory.stageMetric k w) z)
  (c := L.shift)`。

下游 `PreparedSpatialReserveTransport` 有
`open private own_threshold_native_tail_stageMetric from` 本路径，故直接在原路径修补
（不另建 PortC11P / shim）。
-/

set_option autoImplicit false
noncomputable section
open Set Filter DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal Topology Pointwise
namespace GC.GeneralFlow
universe u

open private event_samePresentation_of_prefix derivative_bound_of_translated_germ from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStepDerivative
open private overlapCastPoint overlapCastPoint_heq overlap_scalar_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SpatialWitnessTransport
open private retained_event_incoming_heq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CutoffRecordConcatenation

/-- Match the same actual native-tail stages and metrics, including the left endpoint. -/
private theorem own_threshold_native_tail_stageMetric
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {E B Bnext activation eta d εcut Dcut : ℝ} {mcut : ℕ}
    {L : PreparedSpatialState pBase C P g E B}
    {R : PreparedSpatialState pBase C P g B Bnext}
    (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut)
    (hLR : PreparedSpatialSuccessor L R activation eta d)
    (hshift : R.shift = L.history.time (Fin.last L.history.eventCount))
    (hoffset : R.offset = L.history.eventCount)
    (j : Fin (R.history.eventCount + 1)) (hj : L.offset ≤ j.val) :
    ∃ k : Fin (W.oldNative.eventCount + 1),
      R.history.stage j = W.oldNative.stage k ∧
      R.history.time j = W.oldNative.time k + L.shift ∧
      R.history.toHistory.stageEndTime j = W.oldNative.toHistory.stageEndTime k + L.shift ∧
      ∀ s : ℝ, s ∈ Ico (R.history.time j) (R.history.toHistory.stageEndTime j) →
        HEq (R.history.toHistory.stageMetric j s)
          (W.oldNative.toHistory.stageMetric k (s - L.shift)) := by
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
    have hMetric (u : ℝ)
        (hu : u ∈ Ico (R.history.time j) (R.history.toHistory.stageEndTime j)) :
        HEq (R.history.toHistory.stageMetric j u)
          ((W.oldNative.toHistory.event iK).incoming.flow.base.metric (u - L.shift)) := by
      have hPrefix := hPresent.incomingMetric_heq u
        (by simpa only [hjFull, R.history.toHistory.stageEndTime_castSucc] using
          hu)
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
    refine ⟨iK.castSucc, hStage, hTime, ?_, ?_⟩
    · simpa only [ObservedHistory.stageEndTime_castSucc] using hEnd
    · intro u hu
      simpa only [ObservedHistory.stageMetric_castSucc_apply] using hMetric u hu
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
    exact ⟨kK, hStage, hTime, hEnd, fun u _ => hMetric u⟩

/-- Transport the intrinsic gradient at the same stage, metric and point. -/
private theorem own_threshold_gradient_of_same_metric
    {P Q : OrientedThreeStage.{u}} (hP : P = Q)
    {g : P.Metric} {g' : Q.Metric} (hg : HEq g g')
    {x : P.Carrier} {y : Q.Carrier} (hx : HEq x y) {Cgrad : ℝ≥0}
    (hgrad : ∀ v : TangentSpace I3 y,
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g') y v)| ≤
        Cgrad * metricScalarAt g' y * Real.sqrt (metricScalarAt g' y) *
          Real.sqrt (g'.inner y v v)) :
    ∀ v : TangentSpace I3 x,
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g) x v)| ≤
        Cgrad * metricScalarAt g x * Real.sqrt (metricScalarAt g x) *
          Real.sqrt (g.inner x v v) := by
  cases hP
  cases eq_of_heq hg
  cases eq_of_heq hx
  exact hgrad

/-- The same retained native history supplies the original coefficients at its
own prepared threshold, including the actual gradient at a surgery birth. -/
theorem PreparedSpatialStepRetention.own_threshold_native_certificates
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {E B Bnext d eta εcut Dcut : ℝ} {mcut : ℕ}
    {L : PreparedSpatialState pBase C P g E B}
    {R : PreparedSpatialState pBase C P g B Bnext}
    (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut)
    (t : Icc (0 : ℝ) W.oldNative.horizon) (htop : (t : ℝ) < W.oldNative.horizon) :
    let K := W.oldNative
    let M := L.prepared.Qall
    K.EventSlabsDerivative C.Ctime M (K.toHistory.activeStage t) ∧
    K.EventSlabsGradient C.Cgrad M (K.toHistory.activeStage t) ∧
    (∀ i : Fin K.eventCount, i.castSucc = K.toHistory.activeStage t →
      (K.toHistory.event i).incoming.DerivativeBoundBefore C.Ctime M t) ∧
    (∀ h : K.time (Fin.last K.eventCount) < K.horizon,
      K.toHistory.activeStage t = Fin.last K.eventCount →
      ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore C.Ctime M t) ∧
    ∀ y : (K.toHistory.stageAt t).Carrier,
      M < metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage t) t) y →
      (K.time (K.toHistory.activeStage t) < (t : ℝ) →
        |derivWithin (fun v => metricScalarAt
          (K.toHistory.stageMetric (K.toHistory.activeStage t) v) y) (Iic (t : ℝ)) t| ≤
          C.Ctime * metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage t) t) y ^ 2) ∧
      ∀ v : TangentSpace I3 y,
        |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ)
          (metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage t) t)) y v)| ≤
        C.Cgrad * metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage t) t) y *
          Real.sqrt (metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage t) t) y) *
          Real.sqrt ((K.toHistory.stageMetric (K.toHistory.activeStage t) t).inner y v v) := by
  have hq : L.prepared.qcan ≤ L.prepared.Qall := by
    apply le_trans ((le_max_left L.prepared.qcan L.prepared.qs).trans
      ((le_max_right 1 (max L.prepared.qcan L.prepared.qs)).trans L.prepared.Qbirth_ge))
    rw [L.prepared.Qall_eq]
    exact le_max_left _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i _ x v hv hx
    exact (W.oldNative_estimates.1 i).1 x v hv (hq.trans_lt hx)
  · intro i _ x v hv hx
    exact (W.oldNative_estimates.1 i).2.1 x v hv (hq.trans_lt hx)
  · intro i hi x v hv hx
    have hdom := W.oldNative.toHistory.activeStage_mem t
    rw [← hi] at hdom
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, Set.mem_Ico] at hdom
    exact (W.oldNative_estimates.1 i).1 x v
      ⟨hv.1, hv.2.trans_le hdom.2.le⟩ (hq.trans_lt hx)
  · intro h _ x v hv hx
    exact (W.oldNative_estimates.2 h).1 x v ⟨hv.1, hv.2.trans htop⟩ (hq.trans_lt hx)
  · intro y hy
    have hdom : (t : ℝ) ∈ Ico
        (W.oldNative.time (W.oldNative.toHistory.activeStage t))
        (W.oldNative.toHistory.stageEndTime (W.oldNative.toHistory.activeStage t)) := by
      have h := W.oldNative.toHistory.activeStage_mem t
      generalize hj : W.oldNative.toHistory.activeStage t = j at h ⊢
      cases j using Fin.lastCases with
      | last =>
        simp only [ObservedHistory.stageDomain, Fin.lastCases_last, Set.mem_Icc] at h
        rw [W.oldNative.toHistory.stageEndTime_last]
        exact ⟨h.1, htop⟩
      | cast i =>
        simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, Set.mem_Ico] at h
        rw [W.oldNative.toHistory.stageEndTime_castSucc]
        exact h
    exact W.oldNative_estimates.time_derivative_gradient_on_stage L.prepared.qcan_pos
      (W.oldNative.toHistory.activeStage t) t hdom y (hq.trans_lt hy)

/-- The own-threshold native estimates transport along the actual retained
prefix and tail. Time derivatives use an open germ; gradients include births. -/
theorem PreparedSpatialStepRetention.time_derivative_gradient_on_old_native_tail_at_own_threshold
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
    (s : ℝ) (hs : s ∈ Ico (R.history.time j) (R.history.toHistory.stageEndTime j))
    (hscalar : L.prepared.Qall < metricScalarAt (R.history.toHistory.stageMetric j s) y) :
    (R.history.time j < s →
      |derivWithin (fun v => metricScalarAt (R.history.toHistory.stageMetric j v) y)
        (Iic s) s| ≤ C.Ctime * metricScalarAt (R.history.toHistory.stageMetric j s) y ^ 2) ∧
    ∀ v : TangentSpace I3 y,
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ)
        (metricScalarAt (R.history.toHistory.stageMetric j s)) y v)| ≤
      C.Cgrad * metricScalarAt (R.history.toHistory.stageMetric j s) y *
        Real.sqrt (metricScalarAt (R.history.toHistory.stageMetric j s) y) *
        Real.sqrt ((R.history.toHistory.stageMetric j s).inner y v v) := by
  obtain ⟨k, hStage, hTime, hEnd, hMetric⟩ :=
    own_threshold_native_tail_stageMetric W hLR hshift hoffset j hj
  let z := overlapCastPoint hStage y
  have hPoint : HEq y z := (overlapCastPoint_heq hStage y).symm
  have hq : L.prepared.qcan ≤ L.prepared.Qall := by
    apply le_trans ((le_max_left L.prepared.qcan L.prepared.qs).trans
      ((le_max_right 1 (max L.prepared.qcan L.prepared.qs)).trans L.prepared.Qbirth_ge))
    rw [L.prepared.Qall_eq]
    exact le_max_left _ _
  have hTimeK : s - L.shift ∈ Ico (W.oldNative.time k)
      (W.oldNative.toHistory.stageEndTime k) := by
    rw [hTime, hEnd] at hs
    constructor <;> linarith [hs.1, hs.2]
  have hScalar := overlap_scalar_eq hStage (hMetric s hs) hPoint
  have hScalarK : L.prepared.qcan <
      metricScalarAt (W.oldNative.toHistory.stageMetric k (s - L.shift)) z := by
    rw [← hScalar]
    exact hq.trans_lt hscalar
  have hBoth := W.oldNative_estimates.time_derivative_gradient_on_stage
    L.prepared.qcan_pos k (s - L.shift) hTimeK z hScalarK
  refine ⟨?_, ?_⟩
  · intro hstrict
    have hGerm : (fun v => metricScalarAt (R.history.toHistory.stageMetric j v) y) =ᶠ[𝓝 s]
        (fun v => metricScalarAt (W.oldNative.toHistory.stageMetric k (v - L.shift)) z) := by
      filter_upwards [Ioo_mem_nhds hstrict hs.2] with v hv
      exact overlap_scalar_eq hStage (hMetric v ⟨hv.1.le, hv.2⟩) hPoint
    apply derivative_bound_of_translated_germ
      (g := fun w => metricScalarAt (W.oldNative.toHistory.stageMetric k w) z)
      (c := L.shift) hGerm
    apply hBoth.1
    rw [hTime] at hstrict
    linarith
  · exact own_threshold_gradient_of_same_metric hStage (hMetric s hs) hPoint hBoth.2

end GC.GeneralFlow
