import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedOverlapClosedBirth
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedDistanceData

/-!
# S-CH11-FIX12 patched-at-path `PreparedOverlapClosedSeam`

来源：donor `PreparedOverlapClosedSeam.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败；本文件只有 elaboration 层面修补（no statement / definition /
proof idea altered；不加 `set_option`）。patched-at-path：下游 `PreparedSpatialStep` 对它做
`open private … from` 原路径，故不做 PortC11P + shim（原路径文本 = 本文件）：
* 陈述里 `PreparedDistanceClassProvider fixed recenter Cdist` 的 universe 被自动成 `u_1`，而证明体
  里 `exists_prepared_two_overlap_extension_with_closed_seam_with_native_certificate` 要 `.{u}`
  （l.1164 "Application type mismatch … `PreparedClassProviderWithNative.{u_1}` vs `.{u}`"）→ 陈述里
  写 `PreparedDistanceClassProvider.{u}`；
* `hHJ`：`add_lt_add_right hKB c`（本树左右约定相反，给 `c + K.horizon < c + B`）→
  `add_lt_add_of_lt_of_le hKB le_rfl`；
* 陈述里只出现、证明不引用的 binder（`I` / `IV` / `IL` / `hbuffer`）加 `_` 前缀
  （unusedVariables；binder 名不改变陈述）；
* 两处孤立 `·`（单独一行后接 `exact` / `obtain`）合并成 `· tactic`（风格 linter）。
-/

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal

namespace GC.GeneralFlow

open private exists_prepared_two_overlap_extension_with_closed_birth_with_native_certificate_with_reserve_quality from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedOverlapClosedBirth
universe u

/-- Attach closed-seam control to one existing prepared closed-birth extension.
All future-class callbacks, reserves, actual records, markings and metric
identities are retained. The stored original-metric zero bound closes the seam;
no provider, class or geometric history is selected again. The literal midpoint
restriction is queried both at H.time(last) and at H.horizon, including equality
between those two times. -/
private theorem exists_prepared_two_overlap_extension_with_closed_seam_with_native_certificate_with_reserve_quality
    (Dstar εReserve : ℝ) (hDstar : 0 < Dstar) (hεReserve : 0 < εReserve)
    (certificate : RetainedCoreHistory.{u} → Prop)
    (fixed : StaticCapScaffold) (recenter : ℝ)
    (prepareClass : PreparedClassProviderWithNative certificate fixed recenter)
    (ε C1 C2 C1s C2s Cs τmin Cbirth : ℝ) (Ctime Cgrad : ℝ≥0) (hε : 0 < ε)
    (hstr : 1 ≤ C1 ∧ 1 ≤ C2 ∧ 1 ≤ C1s ∧ 1 ≤ C2s ∧ 0 < τmin ∧ ε ≤ εStrong_C12X.{u})
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ ε K.horizon →
        NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε)
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (H : RetainedCoreHistory.{u}) (IH : InitialIdentification P g H.toHistory)
    (pH : CutoffParameters)
    (recordsH : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i pH)
    (hfixedH : pH.fixed = fixed) (hrcH : pH.recenterConstant = recenter)
    (hcapH : StandardCap.transitionEnd < pH.modelRadius + 1)
    (hcontrolH : HistoryEventControl H)
    (hwinH : ∀ i b, ((recordsH i).static b).hasCanonicalWindow)
    (κH : ℝ) (hκH : 0 < κH) (hncH : H.NoncollapsedBefore κH ε H.horizon)
    (PK : OrientedThreeStage.{u}) (gK : PK.Metric)
    (K : RetainedCoreHistory.{u}) (IK : InitialIdentification PK gK K.toHistory)
    (pOld : CutoffParameters) (δOld ρOld B εOld κClass κOld qOld qsOld QbirthOld QzeroOld QallOld : ℝ)
    (hQbirthOld : max 1 (max qOld qsOld) ≤ QbirthOld)
    (pK : CutoffParameters)
    (recordsK : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pK)
    (hclassK : K.IsCanonicalCutoffRecordFamily pOld δOld ρOld recordsK)
    (hfixedOld : pOld.fixed = fixed) (hrcOld : pOld.recenterConstant = recenter)
    (hcontrolK : HistoryEventControl K)
    (oldExtension : PreparedGeometricObservationExtensionWithNative certificate PK gK B εOld κClass pOld δOld ρOld)
    (oldControl : ∀ (V : RetainedCoreHistory.{u})
      (_IV : InitialIdentification PK gK V.toHistory) (pV : CutoffParameters)
      (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
      V.horizon ≤ B → V.IsCanonicalCutoffRecordFamily pOld δOld ρOld records →
      V.NoncollapsedBefore κOld ε V.horizon ∧
      NativeEstimates V ε C1 C2 C1s C2s qOld qsOld τmin Ctime Cgrad ∧
      ∀ t : Icc (0 : ℝ) V.toHistory.horizon,
        (t : ℝ) < V.horizon → V.time (V.toHistory.activeStage t) = (t : ℝ) →
        V.toHistory.activeStage t ≠ 0 →
        ∀ y : (V.toHistory.stageAt t).Carrier,
          QbirthOld < metricScalarAt (V.initialMetric (V.toHistory.activeStage t)) y →
          ∃ W : SpatialCanonicalWitness (V.initialMetric (V.toHistory.activeStage t))
            ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε)
    (hZeroOld : ∀ (V : ObservedHistory.{u}), InitialIdentification PK gK V →
      ∀ y : (V.stage 0).Carrier, metricScalarAt (V.initialMetric 0) y < QzeroOld)
    (hQallOld : QallOld = max QbirthOld QzeroOld)
    (c : ℝ) (offset : ℕ)
    (Aold : AffineEventPrefix K H c offset (Fin.last K.eventCount))
    (hHhor : H.horizon = K.horizon + c) (hKB : K.horizon < B)
    (Bfuture R : ℝ) (hBfuture : B < Bfuture) (hR : 0 < R) :
    ∃ (pNew : CutoffParameters)
      (δNew ρNew εNew κNewClass κNew qNew qsNew QzeroNew QbirthNew QallNew r κJ : ℝ),
      Dstar ≤ pNew.modelRadius ∧ pNew.modelAccuracy ≤ εReserve ∧
      2 ≤ pNew.modelOrder ∧ 32 * QallNew * ρNew ^ 2 ≤ 1 ∧
      (∃ C1h C2h qh : ℝ, 1 ≤ C1h ∧ 1 ≤ C2h ∧ C1h ≤ strongC1_C11SC.{u} ε C1 ∧
        C2h ≤ strongC2_C11SC.{u} ε C2 Cgrad ∧ qsNew ≤ qh ∧
        ∀ (V : RetainedCoreHistory.{u})
          (_IV : InitialIdentification (K.stage (Fin.last K.eventCount))
            (K.initialMetric (Fin.last K.eventCount)) V.toHistory)
          (pV : CutoffParameters)
          (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
          V.horizon ≤ Bfuture - K.time (Fin.last K.eventCount) →
          V.IsCanonicalCutoffRecordFamily pNew δNew ρNew records →
          RecordHypFar_C12X (5 / 4) V records →
          V.EventSlabsStronglyCanonicalFull_C12X ε ε C1h C2h qh (Fin.last V.eventCount) ∧
          ∀ hfinal : V.time (Fin.last V.eventCount) < V.horizon,
            V.StronglyCanonicalBeforeFull_C12X (Fin.last V.eventCount)
              ((V.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl) ε ε C1h C2h qh
              V.horizon) ∧
      pNew.fixed = fixed ∧ pNew.recenterConstant = recenter ∧
      0 < δNew ∧ 0 < ρNew ∧ 0 < εNew ∧ εNew < 1 / 11 ∧
      0 < κNewClass ∧ 0 < κNew ∧ 0 < qNew ∧ qNew ≤ qsNew ∧ qsNew ≤ Cs * qNew ∧
      0 < QzeroNew ∧ max 1 (max qNew qsNew) ≤ QbirthNew ∧
      QallNew = max QbirthNew QzeroNew ∧ 0 < QallNew ∧
      0 < r ∧ r ≤ R ∧ QallNew ≤ (r ^ 2)⁻¹ ∧ 0 < κJ ∧
      StandardCap.transitionEnd < pNew.modelRadius + 1 ∧
      pNew.recenterConstant * δNew ≤ 1 / 2 ∧
      (∀ (V : ObservedHistory.{u}),
        InitialIdentification (K.stage (Fin.last K.eventCount))
          (K.initialMetric (Fin.last K.eventCount)) V →
        ∀ y : (V.stage 0).Carrier, metricScalarAt (V.initialMetric 0) y < QzeroNew) ∧
      PreparedGeometricObservationExtensionWithNative certificate
        (K.stage (Fin.last K.eventCount)) (K.initialMetric (Fin.last K.eventCount))
        (Bfuture - K.time (Fin.last K.eventCount)) εNew κNewClass pNew δNew ρNew ∧
      (∀ (V : RetainedCoreHistory.{u})
        (_IV : InitialIdentification (K.stage (Fin.last K.eventCount))
          (K.initialMetric (Fin.last K.eventCount)) V.toHistory)
        (pV : CutoffParameters)
        (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
        V.horizon ≤ Bfuture - K.time (Fin.last K.eventCount) →
        V.IsCanonicalCutoffRecordFamily pNew δNew ρNew records →
        V.NoncollapsedBefore κNew ε V.horizon ∧
        NativeEstimates V ε C1 C2 C1s C2s qNew qsNew τmin Ctime Cgrad ∧
        ∀ t : Icc (0 : ℝ) V.toHistory.horizon,
          (t : ℝ) < V.horizon → V.time (V.toHistory.activeStage t) = (t : ℝ) →
          V.toHistory.activeStage t ≠ 0 →
          ∀ y : (V.toHistory.stageAt t).Carrier,
            QbirthNew < metricScalarAt (V.initialMetric (V.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (V.initialMetric (V.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε) ∧
    ∀ (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ),
      0 < δcut → 0 < ρcut → 0 < εcut → 0 < Dcut →
    ∃ (L : RetainedCoreHistory.{u})
      (IL : InitialIdentification (K.stage (Fin.last K.eventCount))
        (K.initialMetric (Fin.last K.eventCount)) L.toHistory)
      (pF : CutoffParameters)
      (native : ∀ i : Fin L.eventCount, GeometricCutoffRecord L.toHistory i pF)
      (hwin : ∀ i b, ((native i).static b).hasLinkedCanonicalWindow_C12X)
      (_hrecK : RecordHypFar_C12X (5 / 4) L native)
      (hDK : pK.modelRadius ≤ pF.modelRadius)
      (hmK : pK.modelOrder ≤ pF.modelOrder)
      (haccK : pF.modelAccuracy ≤ pK.modelAccuracy)
      (hDH : pH.modelRadius ≤ pF.modelRadius)
      (hmH : pH.modelOrder ≤ pF.modelOrder)
      (haccH : pF.modelAccuracy ≤ pH.modelAccuracy)
      (hDNew : pNew.modelRadius ≤ pF.modelRadius)
      (hmNew : pNew.modelOrder ≤ pF.modelOrder)
      (haccNew : pF.modelAccuracy ≤ pNew.modelAccuracy),
      let a := K.time (Fin.last K.eventCount)
      let b := H.time (Fin.last H.eventCount)
      let pCK := pF.withModelWindow pK.modelRadius pK.modelOrder pK.modelAccuracy
        pK.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccK)
      let coarseK := fun i : Fin L.eventCount =>
        (native i).restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
            pK.modelRadius_pos hDK hmK haccK
      let qK := pK.spliceAfter (translate_cutoff_parameters pCK a) K.horizon
      let pCH := pF.withModelWindow pH.modelRadius pH.modelOrder pH.modelAccuracy
        pH.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccH)
      let coarseH := fun i : Fin L.eventCount =>
        (native i).restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
            pH.modelRadius_pos hDH hmH haccH
      let qH := pH.spliceAfter (translate_cutoff_parameters pCH b) H.horizon
      let pReserve := pF.withModelWindow pNew.modelRadius pNew.modelOrder pNew.modelAccuracy
        pNew.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccNew)
      let reserved : ∀ i : Fin L.eventCount, GeometricCutoffRecord L.toHistory i pReserve :=
        fun i => (native i).restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
            pNew.modelRadius_pos hDNew hmNew haccNew
      ∃ (Kplus : RetainedCoreHistory.{u}) (IKplus : InitialIdentification PK gK Kplus.toHistory)
        (AK : AffineEventPrefix L Kplus a K.eventCount (Fin.last L.eventCount))
        (IoldK : RawInitialPrefix K Kplus)
        (joinedK : ∀ i : Fin Kplus.eventCount, GeometricCutoffRecord Kplus.toHistory i qK)
        (J : RetainedCoreHistory.{u}) (IJ : InitialIdentification P g J.toHistory)
        (AJ : AffineEventPrefix L J b H.eventCount (Fin.last L.eventCount))
        (IoldH : RawInitialPrefix H J)
        (joinedH : ∀ i : Fin J.eventCount, GeometricCutoffRecord J.toHistory i qH)
        (hKhor : Kplus.horizon = L.horizon + a) (hJhor : J.horizon = L.horizon + b),
        (InitialIdentification.atZero (K.stage (Fin.last K.eventCount))
          (K.initialMetric (Fin.last K.eventCount))).IsPrefixOf IL ∧
        L.horizon = B - a ∧ Kplus.horizon = B ∧ J.horizon = B + c ∧
        IK.IsPrefixOf IKplus ∧ IH.IsPrefixOf IJ ∧
        certificate L ∧ HistoryEventControl L ∧ HistoryEventControl Kplus ∧ HistoryEventControl J ∧
        L.IsCanonicalCutoffRecordFamily pNew δNew ρNew reserved ∧
        Kplus.IsCanonicalCutoffRecordFamily pOld δOld ρOld joinedK ∧
        L.NoncollapsedBefore κNew ε L.horizon ∧
        Kplus.NoncollapsedBefore κOld ε Kplus.horizon ∧
        J.NoncollapsedBefore κJ ε J.horizon ∧
        pF.fixed = fixed ∧ pF.recenterConstant = recenter ∧
        pF.modelAccuracy ≤ εcut ∧ Dcut ≤ pF.modelRadius ∧ mcut ≤ pF.modelOrder ∧
        (∀ i : Fin L.eventCount,
          pF.delta (L.time i.succ) ≤ δcut ∧ pF.neckRadius (L.time i.succ) ≤ min r ρcut) ∧
        (∀ t : ℝ, HEq (Kplus.toHistory.stageMetric (Fin.last Kplus.eventCount) (t + a))
          (L.toHistory.stageMetric (Fin.last L.eventCount) t)) ∧
        (∀ t : ℝ, HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + b))
          (L.toHistory.stageMetric (Fin.last L.eventCount) t)) ∧
        (∀ t : ℝ, t ≤ K.horizon → qK.delta t = pK.delta t ∧
          qK.neckRadius t = pK.neckRadius t ∧ qK.protectedRadius t = pK.protectedRadius t) ∧
        (∀ t : ℝ, t ≤ H.horizon → qH.delta t = pH.delta t ∧
          qH.neckRadius t = pH.neckRadius t ∧ qH.protectedRadius t = pH.protectedRadius t) ∧
        (∀ i b, ((joinedH i).static b).hasCanonicalWindow) ∧
        (∀ i : Fin K.eventCount,
          HEq (joinedK (i.castLE IoldK.count_le)).nominalRadius (recordsK i).nominalRadius ∧
          HEq (joinedK (i.castLE IoldK.count_le)).delta (recordsK i).delta ∧
          HEq (joinedK (i.castLE IoldK.count_le)).order (recordsK i).order ∧
          HEq (joinedK (i.castLE IoldK.count_le)).neck (recordsK i).neck ∧
          HEq (joinedK (i.castLE IoldK.count_le)).static (recordsK i).static) ∧
        (∀ i : Fin H.eventCount,
          HEq (joinedH (i.castLE IoldH.count_le)).nominalRadius (recordsH i).nominalRadius ∧
          HEq (joinedH (i.castLE IoldH.count_le)).delta (recordsH i).delta ∧
          HEq (joinedH (i.castLE IoldH.count_le)).order (recordsH i).order ∧
          HEq (joinedH (i.castLE IoldH.count_le)).neck (recordsH i).neck ∧
          HEq (joinedH (i.castLE IoldH.count_le)).static (recordsH i).static) ∧
        (∀ i : Fin L.eventCount,
          HEq (joinedK (AK.eventIndex i)).nominalRadius (native i).nominalRadius ∧
          HEq (joinedK (AK.eventIndex i)).delta (native i).delta ∧
          HEq (joinedK (AK.eventIndex i)).order (native i).order ∧
          HEq (joinedK (AK.eventIndex i)).neck (native i).neck ∧
          HEq (joinedK (AK.eventIndex i)).static
            (fun b => translate_presented_static_cap (L.coreEvent i) a ((coarseK i).static b))) ∧
        (∀ i : Fin L.eventCount,
          HEq (joinedH (AJ.eventIndex i)).nominalRadius (native i).nominalRadius ∧
          HEq (joinedH (AJ.eventIndex i)).delta (native i).delta ∧
          HEq (joinedH (AJ.eventIndex i)).order (native i).order ∧
          HEq (joinedH (AJ.eventIndex i)).neck (native i).neck ∧
          HEq (joinedH (AJ.eventIndex i)).static
            (fun z => translate_presented_static_cap (L.coreEvent i) b ((coarseH i).static z))) ∧
        (∀ t : Icc (0 : ℝ) L.horizon,
          J.toHistory.stageAt (AJ.shiftTime hJhor t) =
            Kplus.toHistory.stageAt (AK.shiftTime hKhor t) ∧
          HEq (J.toHistory.stageMetric (J.toHistory.activeStage (AJ.shiftTime hJhor t))
              (AJ.shiftTime hJhor t))
            (Kplus.toHistory.stageMetric (Kplus.toHistory.activeStage (AK.shiftTime hKhor t))
              (AK.shiftTime hKhor t))) ∧
        NativeEstimates Kplus ε C1 C2 C1s C2s qOld qsOld τmin Ctime Cgrad ∧
        (∀ t : Icc (0 : ℝ) Kplus.toHistory.horizon,
          (t : ℝ) < Kplus.horizon →
          Kplus.time (Kplus.toHistory.activeStage t) = (t : ℝ) →
          Kplus.toHistory.activeStage t ≠ 0 →
          ∀ y : (Kplus.toHistory.stageAt t).Carrier,
            QbirthOld < metricScalarAt (Kplus.initialMetric (Kplus.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (Kplus.initialMetric (Kplus.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε) ∧
        NativeEstimates L ε C1 C2 C1s C2s qNew qsNew τmin Ctime Cgrad ∧
        (∀ t : Icc (0 : ℝ) L.toHistory.horizon,
          (t : ℝ) < L.horizon → L.time (L.toHistory.activeStage t) = (t : ℝ) →
          L.toHistory.activeStage t ≠ 0 →
          ∀ y : (L.toHistory.stageAt t).Carrier,
            QbirthNew < metricScalarAt (L.initialMetric (L.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (L.initialMetric (L.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε) ∧
        (∀ (T : Icc (0 : ℝ) J.horizon) (_hbuffer : (T : ℝ) < J.horizon)
          (t : Icc (0 : ℝ) (J.restrict T).horizon), b ≤ (t : ℝ) →
          ∀ x : ((J.restrict T).toHistory.stageAt t).Carrier,
            QallOld < metricScalarAt
              ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t)
                t) x →
            ∃ W : SpatialCanonicalWitness
              ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t)
                t) ε (max C1s Cbirth) (max C2s (max Cbirth (Cgrad : ℝ))) x,
              W.capTubeHasNeckChart ε) ∧
        ∃ (T : Icc (0 : ℝ) J.horizon)
          (hHT : H.horizon < (T : ℝ)) (_hbuffer : (T : ℝ) < J.horizon),
          (T : ℝ) = (H.horizon + J.horizon) / 2 ∧
          0 < (T : ℝ) - H.horizon ∧ 0 < J.horizon - (T : ℝ) ∧
          let O := J.restrict T
          let IO : InitialIdentification P g O.toHistory := IJ.restrict T
          IO.IsPrefixOf IJ ∧ O.horizon = (T : ℝ) ∧
          (∀ t : Icc (0 : ℝ) O.horizon,
            HEq (O.toHistory.stageMetric (O.toHistory.activeStage t) t)
              (J.toHistory.stageMetric
                (J.toHistory.activeStage
                  ⟨(t : ℝ), t.property.1, t.property.2.trans T.property.2⟩) t)) ∧
          let spatialAt : Icc (0 : ℝ) O.horizon → Prop := fun t =>
            ∀ x : (O.toHistory.stageAt t).Carrier,
              QallOld < metricScalarAt
                (O.toHistory.stageMetric (O.toHistory.activeStage t) t) x →
              ∃ W : SpatialCanonicalWitness
                (O.toHistory.stageMetric (O.toHistory.activeStage t) t)
                ε (max C1s Cbirth) (max C2s (max Cbirth (Cgrad : ℝ))) x,
                W.capTubeHasNeckChart ε
          let tSeam : Icc (0 : ℝ) O.horizon :=
            ⟨b, H.toHistory.time_nonneg _, H.time_le_horizon.trans hHT.le⟩
          let tOld : Icc (0 : ℝ) O.horizon := ⟨H.horizon, H.horizon_nonneg, hHT.le⟩
          spatialAt tSeam ∧ spatialAt tOld := by
  obtain ⟨pNew, δNew, ρNew, εNew, κNewClass, κNew, qNew, qsNew,
    QzeroNew, QbirthNew, QallNew, r, κJ,
    hDReserve, hAccuracyReserve, hOrderReserve, hRadiusReserve, hStrongNew, hfixedNew, hrcNew,
    hδNew, hρNew, hεNew, hεNew11, hκNewClass, hκNew, hqNew, hqsNew, hqsNewC,
    hQzeroNew, hQbirthNew, hQallNew, hQallNewPos, hr, hrR, hQallr, hκJ,
    hcapNew, hrecNew, zeroNew, newExtension, newControl, make⟩ :=
    exists_prepared_two_overlap_extension_with_closed_birth_with_native_certificate_with_reserve_quality
      Dstar εReserve hDstar hεReserve certificate fixed recenter prepareClass
      ε C1 C2 C1s C2s Cs τmin Cbirth Ctime Cgrad hε hstr analytic
      P g H IH pH recordsH hfixedH hrcH hcapH hcontrolH hwinH κH hκH hncH
      PK gK K IK pOld δOld ρOld B εOld κClass κOld qOld qsOld QbirthOld hQbirthOld
      pK recordsK hclassK hfixedOld hrcOld hcontrolK oldExtension oldControl
      c offset Aold hHhor hKB Bfuture R hBfuture hR
  refine ⟨pNew, δNew, ρNew, εNew, κNewClass, κNew, qNew, qsNew,
    QzeroNew, QbirthNew, QallNew, r, κJ,
    hDReserve, hAccuracyReserve, hOrderReserve, hRadiusReserve, hStrongNew, hfixedNew, hrcNew,
    hδNew, hρNew, hεNew, hεNew11, hκNewClass, hκNew, hqNew, hqsNew, hqsNewC,
    hQzeroNew, hQbirthNew, hQallNew, hQallNewPos, hr, hrR, hQallr, hκJ,
    hcapNew, hrecNew, zeroNew, newExtension, newControl, ?_⟩
  intro δcut ρcut εcut Dcut mcut hδcut hρcut hεcut hDcut
  obtain ⟨L, IL, pF, native, hwin, hrecK, hDK, hmK, haccK, hDH, hmH, haccH,
    hDNew, hmNew, haccNew, Kplus, IKplus, AK, IoldK, joinedK,
    J, IJ, AJ, IoldH, joinedH, hKhor, hJhor, hIL, hLB, hKplusB, hJB,
    hIKplus, hIJ, hcertificateL, hcontrolL, hcontrolKplus, hcontrolJ, hclassNew, hclassKplus,
    hncL, hncKplus, hncJ, hfixedFine, hrcFine, haccFine, hradFine, horderFine,
    hfine, hfinalKplus, hfinalJ, hpastK, hpastH, hwinJ,
    hOldK, hOldH, hTailK, hTailH, hsame, hestKplus, hbirthKplus, hestL, hbirthL, _⟩ :=
    make δcut ρcut εcut Dcut mcut hδcut hρcut hεcut hDcut
  have hqsBirthOld : qsOld ≤ QbirthOld :=
    (le_max_right qOld qsOld).trans ((le_max_right 1 (max qOld qsOld)).trans hQbirthOld)
  have closed := exists_spatialCanonicalWitness_on_buffered_same_tail_observation_with_closed_seam
    AK AJ hKhor hJhor hfinalKplus hfinalJ PK gK IKplus
    hestKplus hqsBirthOld hbirthKplus hZeroOld hQallOld
  have hHJ : H.horizon < J.horizon := by
    rw [hHhor, hJB]
    exact add_lt_add_of_lt_of_le hKB le_rfl
  let T : Icc (0 : ℝ) J.horizon :=
    ⟨(H.horizon + J.horizon) / 2, by linarith [H.horizon_nonneg], by linarith⟩
  have hHT : H.horizon < (T : ℝ) := by
    change H.horizon < (H.horizon + J.horizon) / 2
    linarith
  have hbuffer : (T : ℝ) < J.horizon := by
    change (H.horizon + J.horizon) / 2 < J.horizon
    linarith
  refine ⟨L, IL, pF, native, hwin, hrecK, hDK, hmK, haccK, hDH, hmH, haccH,
    hDNew, hmNew, haccNew, Kplus, IKplus, AK, IoldK, joinedK,
    J, IJ, AJ, IoldH, joinedH, hKhor, hJhor, hIL, hLB, hKplusB, hJB,
    hIKplus, hIJ, hcertificateL, hcontrolL, hcontrolKplus, hcontrolJ, hclassNew, hclassKplus,
    hncL, hncKplus, hncJ, hfixedFine, hrcFine, haccFine, hradFine, horderFine,
    hfine, hfinalKplus, hfinalJ, hpastK, hpastH, hwinJ,
    hOldK, hOldH, hTailK, hTailH, hsame, hestKplus, hbirthKplus, hestL, hbirthL,
    closed, T, hHT, hbuffer, rfl, sub_pos.mpr hHT, sub_pos.mpr hbuffer,
    IJ.restrict_isPrefixOf T, rfl, ?_, ?_⟩
  · intro t
    exact J.toHistory.restrict_sliceMetric T t
  · dsimp only
    constructor
    · exact closed T hbuffer
        ⟨H.time (Fin.last H.eventCount), H.toHistory.time_nonneg _,
          H.time_le_horizon.trans hHT.le⟩ le_rfl
    · exact closed T hbuffer ⟨H.horizon, H.horizon_nonneg, hHT.le⟩ H.time_le_horizon

/-- Forget only the four reserve-quality bounds from the same selected native extension. -/
private theorem exists_prepared_two_overlap_extension_with_closed_seam_with_native_certificate
    (certificate : RetainedCoreHistory.{u} → Prop)
    (fixed : StaticCapScaffold) (recenter : ℝ)
    (prepareClass : PreparedClassProviderWithNative certificate fixed recenter)
    (ε C1 C2 C1s C2s Cs τmin Cbirth : ℝ) (Ctime Cgrad : ℝ≥0) (hε : 0 < ε)
    (hstr : 1 ≤ C1 ∧ 1 ≤ C2 ∧ 1 ≤ C1s ∧ 1 ≤ C2s ∧ 0 < τmin ∧ ε ≤ εStrong_C12X.{u})
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ ε K.horizon →
        NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε)
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (H : RetainedCoreHistory.{u}) (IH : InitialIdentification P g H.toHistory)
    (pH : CutoffParameters)
    (recordsH : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i pH)
    (hfixedH : pH.fixed = fixed) (hrcH : pH.recenterConstant = recenter)
    (hcapH : StandardCap.transitionEnd < pH.modelRadius + 1)
    (hcontrolH : HistoryEventControl H)
    (hwinH : ∀ i b, ((recordsH i).static b).hasCanonicalWindow)
    (κH : ℝ) (hκH : 0 < κH) (hncH : H.NoncollapsedBefore κH ε H.horizon)
    (PK : OrientedThreeStage.{u}) (gK : PK.Metric)
    (K : RetainedCoreHistory.{u}) (IK : InitialIdentification PK gK K.toHistory)
    (pOld : CutoffParameters) (δOld ρOld B εOld κClass κOld qOld qsOld QbirthOld QzeroOld QallOld : ℝ)
    (hQbirthOld : max 1 (max qOld qsOld) ≤ QbirthOld)
    (pK : CutoffParameters)
    (recordsK : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pK)
    (hclassK : K.IsCanonicalCutoffRecordFamily pOld δOld ρOld recordsK)
    (hfixedOld : pOld.fixed = fixed) (hrcOld : pOld.recenterConstant = recenter)
    (hcontrolK : HistoryEventControl K)
    (oldExtension : PreparedGeometricObservationExtensionWithNative certificate PK gK B εOld κClass pOld δOld ρOld)
    (oldControl : ∀ (V : RetainedCoreHistory.{u})
      (_IV : InitialIdentification PK gK V.toHistory) (pV : CutoffParameters)
      (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
      V.horizon ≤ B → V.IsCanonicalCutoffRecordFamily pOld δOld ρOld records →
      V.NoncollapsedBefore κOld ε V.horizon ∧
      NativeEstimates V ε C1 C2 C1s C2s qOld qsOld τmin Ctime Cgrad ∧
      ∀ t : Icc (0 : ℝ) V.toHistory.horizon,
        (t : ℝ) < V.horizon → V.time (V.toHistory.activeStage t) = (t : ℝ) →
        V.toHistory.activeStage t ≠ 0 →
        ∀ y : (V.toHistory.stageAt t).Carrier,
          QbirthOld < metricScalarAt (V.initialMetric (V.toHistory.activeStage t)) y →
          ∃ W : SpatialCanonicalWitness (V.initialMetric (V.toHistory.activeStage t))
            ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε)
    (hZeroOld : ∀ (V : ObservedHistory.{u}), InitialIdentification PK gK V →
      ∀ y : (V.stage 0).Carrier, metricScalarAt (V.initialMetric 0) y < QzeroOld)
    (hQallOld : QallOld = max QbirthOld QzeroOld)
    (c : ℝ) (offset : ℕ)
    (Aold : AffineEventPrefix K H c offset (Fin.last K.eventCount))
    (hHhor : H.horizon = K.horizon + c) (hKB : K.horizon < B)
    (Bfuture R : ℝ) (hBfuture : B < Bfuture) (hR : 0 < R) :
    ∃ (pNew : CutoffParameters)
      (δNew ρNew εNew κNewClass κNew qNew qsNew QzeroNew QbirthNew QallNew r κJ : ℝ),
      pNew.fixed = fixed ∧ pNew.recenterConstant = recenter ∧
      0 < δNew ∧ 0 < ρNew ∧ 0 < εNew ∧ εNew < 1 / 11 ∧
      0 < κNewClass ∧ 0 < κNew ∧ 0 < qNew ∧ qNew ≤ qsNew ∧ qsNew ≤ Cs * qNew ∧
      0 < QzeroNew ∧ max 1 (max qNew qsNew) ≤ QbirthNew ∧
      QallNew = max QbirthNew QzeroNew ∧ 0 < QallNew ∧
      0 < r ∧ r ≤ R ∧ QallNew ≤ (r ^ 2)⁻¹ ∧ 0 < κJ ∧
      StandardCap.transitionEnd < pNew.modelRadius + 1 ∧
      pNew.recenterConstant * δNew ≤ 1 / 2 ∧
      (∀ (V : ObservedHistory.{u}),
        InitialIdentification (K.stage (Fin.last K.eventCount))
          (K.initialMetric (Fin.last K.eventCount)) V →
        ∀ y : (V.stage 0).Carrier, metricScalarAt (V.initialMetric 0) y < QzeroNew) ∧
      PreparedGeometricObservationExtensionWithNative certificate
        (K.stage (Fin.last K.eventCount)) (K.initialMetric (Fin.last K.eventCount))
        (Bfuture - K.time (Fin.last K.eventCount)) εNew κNewClass pNew δNew ρNew ∧
      (∀ (V : RetainedCoreHistory.{u})
        (_IV : InitialIdentification (K.stage (Fin.last K.eventCount))
          (K.initialMetric (Fin.last K.eventCount)) V.toHistory)
        (pV : CutoffParameters)
        (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
        V.horizon ≤ Bfuture - K.time (Fin.last K.eventCount) →
        V.IsCanonicalCutoffRecordFamily pNew δNew ρNew records →
        V.NoncollapsedBefore κNew ε V.horizon ∧
        NativeEstimates V ε C1 C2 C1s C2s qNew qsNew τmin Ctime Cgrad ∧
        ∀ t : Icc (0 : ℝ) V.toHistory.horizon,
          (t : ℝ) < V.horizon → V.time (V.toHistory.activeStage t) = (t : ℝ) →
          V.toHistory.activeStage t ≠ 0 →
          ∀ y : (V.toHistory.stageAt t).Carrier,
            QbirthNew < metricScalarAt (V.initialMetric (V.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (V.initialMetric (V.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε) ∧
    ∀ (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ),
      0 < δcut → 0 < ρcut → 0 < εcut → 0 < Dcut →
    ∃ (L : RetainedCoreHistory.{u})
      (IL : InitialIdentification (K.stage (Fin.last K.eventCount))
        (K.initialMetric (Fin.last K.eventCount)) L.toHistory)
      (pF : CutoffParameters)
      (native : ∀ i : Fin L.eventCount, GeometricCutoffRecord L.toHistory i pF)
      (hwin : ∀ i b, ((native i).static b).hasLinkedCanonicalWindow_C12X)
      (_hrecK : RecordHypFar_C12X (5 / 4) L native)
      (hDK : pK.modelRadius ≤ pF.modelRadius)
      (hmK : pK.modelOrder ≤ pF.modelOrder)
      (haccK : pF.modelAccuracy ≤ pK.modelAccuracy)
      (hDH : pH.modelRadius ≤ pF.modelRadius)
      (hmH : pH.modelOrder ≤ pF.modelOrder)
      (haccH : pF.modelAccuracy ≤ pH.modelAccuracy)
      (hDNew : pNew.modelRadius ≤ pF.modelRadius)
      (hmNew : pNew.modelOrder ≤ pF.modelOrder)
      (haccNew : pF.modelAccuracy ≤ pNew.modelAccuracy),
      let a := K.time (Fin.last K.eventCount)
      let b := H.time (Fin.last H.eventCount)
      let pCK := pF.withModelWindow pK.modelRadius pK.modelOrder pK.modelAccuracy
        pK.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccK)
      let coarseK := fun i : Fin L.eventCount =>
        (native i).restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
            pK.modelRadius_pos hDK hmK haccK
      let qK := pK.spliceAfter (translate_cutoff_parameters pCK a) K.horizon
      let pCH := pF.withModelWindow pH.modelRadius pH.modelOrder pH.modelAccuracy
        pH.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccH)
      let coarseH := fun i : Fin L.eventCount =>
        (native i).restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
            pH.modelRadius_pos hDH hmH haccH
      let qH := pH.spliceAfter (translate_cutoff_parameters pCH b) H.horizon
      let pReserve := pF.withModelWindow pNew.modelRadius pNew.modelOrder pNew.modelAccuracy
        pNew.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccNew)
      let reserved : ∀ i : Fin L.eventCount, GeometricCutoffRecord L.toHistory i pReserve :=
        fun i => (native i).restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
            pNew.modelRadius_pos hDNew hmNew haccNew
      ∃ (Kplus : RetainedCoreHistory.{u}) (IKplus : InitialIdentification PK gK Kplus.toHistory)
        (AK : AffineEventPrefix L Kplus a K.eventCount (Fin.last L.eventCount))
        (IoldK : RawInitialPrefix K Kplus)
        (joinedK : ∀ i : Fin Kplus.eventCount, GeometricCutoffRecord Kplus.toHistory i qK)
        (J : RetainedCoreHistory.{u}) (IJ : InitialIdentification P g J.toHistory)
        (AJ : AffineEventPrefix L J b H.eventCount (Fin.last L.eventCount))
        (IoldH : RawInitialPrefix H J)
        (joinedH : ∀ i : Fin J.eventCount, GeometricCutoffRecord J.toHistory i qH)
        (hKhor : Kplus.horizon = L.horizon + a) (hJhor : J.horizon = L.horizon + b),
        (InitialIdentification.atZero (K.stage (Fin.last K.eventCount))
          (K.initialMetric (Fin.last K.eventCount))).IsPrefixOf IL ∧
        L.horizon = B - a ∧ Kplus.horizon = B ∧ J.horizon = B + c ∧
        IK.IsPrefixOf IKplus ∧ IH.IsPrefixOf IJ ∧
        certificate L ∧ HistoryEventControl L ∧ HistoryEventControl Kplus ∧ HistoryEventControl J ∧
        L.IsCanonicalCutoffRecordFamily pNew δNew ρNew reserved ∧
        Kplus.IsCanonicalCutoffRecordFamily pOld δOld ρOld joinedK ∧
        L.NoncollapsedBefore κNew ε L.horizon ∧
        Kplus.NoncollapsedBefore κOld ε Kplus.horizon ∧
        J.NoncollapsedBefore κJ ε J.horizon ∧
        pF.fixed = fixed ∧ pF.recenterConstant = recenter ∧
        pF.modelAccuracy ≤ εcut ∧ Dcut ≤ pF.modelRadius ∧ mcut ≤ pF.modelOrder ∧
        (∀ i : Fin L.eventCount,
          pF.delta (L.time i.succ) ≤ δcut ∧ pF.neckRadius (L.time i.succ) ≤ min r ρcut) ∧
        (∀ t : ℝ, HEq (Kplus.toHistory.stageMetric (Fin.last Kplus.eventCount) (t + a))
          (L.toHistory.stageMetric (Fin.last L.eventCount) t)) ∧
        (∀ t : ℝ, HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + b))
          (L.toHistory.stageMetric (Fin.last L.eventCount) t)) ∧
        (∀ t : ℝ, t ≤ K.horizon → qK.delta t = pK.delta t ∧
          qK.neckRadius t = pK.neckRadius t ∧ qK.protectedRadius t = pK.protectedRadius t) ∧
        (∀ t : ℝ, t ≤ H.horizon → qH.delta t = pH.delta t ∧
          qH.neckRadius t = pH.neckRadius t ∧ qH.protectedRadius t = pH.protectedRadius t) ∧
        (∀ i b, ((joinedH i).static b).hasCanonicalWindow) ∧
        (∀ i : Fin K.eventCount,
          HEq (joinedK (i.castLE IoldK.count_le)).nominalRadius (recordsK i).nominalRadius ∧
          HEq (joinedK (i.castLE IoldK.count_le)).delta (recordsK i).delta ∧
          HEq (joinedK (i.castLE IoldK.count_le)).order (recordsK i).order ∧
          HEq (joinedK (i.castLE IoldK.count_le)).neck (recordsK i).neck ∧
          HEq (joinedK (i.castLE IoldK.count_le)).static (recordsK i).static) ∧
        (∀ i : Fin H.eventCount,
          HEq (joinedH (i.castLE IoldH.count_le)).nominalRadius (recordsH i).nominalRadius ∧
          HEq (joinedH (i.castLE IoldH.count_le)).delta (recordsH i).delta ∧
          HEq (joinedH (i.castLE IoldH.count_le)).order (recordsH i).order ∧
          HEq (joinedH (i.castLE IoldH.count_le)).neck (recordsH i).neck ∧
          HEq (joinedH (i.castLE IoldH.count_le)).static (recordsH i).static) ∧
        (∀ i : Fin L.eventCount,
          HEq (joinedK (AK.eventIndex i)).nominalRadius (native i).nominalRadius ∧
          HEq (joinedK (AK.eventIndex i)).delta (native i).delta ∧
          HEq (joinedK (AK.eventIndex i)).order (native i).order ∧
          HEq (joinedK (AK.eventIndex i)).neck (native i).neck ∧
          HEq (joinedK (AK.eventIndex i)).static
            (fun b => translate_presented_static_cap (L.coreEvent i) a ((coarseK i).static b))) ∧
        (∀ i : Fin L.eventCount,
          HEq (joinedH (AJ.eventIndex i)).nominalRadius (native i).nominalRadius ∧
          HEq (joinedH (AJ.eventIndex i)).delta (native i).delta ∧
          HEq (joinedH (AJ.eventIndex i)).order (native i).order ∧
          HEq (joinedH (AJ.eventIndex i)).neck (native i).neck ∧
          HEq (joinedH (AJ.eventIndex i)).static
            (fun z => translate_presented_static_cap (L.coreEvent i) b ((coarseH i).static z))) ∧
        (∀ t : Icc (0 : ℝ) L.horizon,
          J.toHistory.stageAt (AJ.shiftTime hJhor t) =
            Kplus.toHistory.stageAt (AK.shiftTime hKhor t) ∧
          HEq (J.toHistory.stageMetric (J.toHistory.activeStage (AJ.shiftTime hJhor t))
              (AJ.shiftTime hJhor t))
            (Kplus.toHistory.stageMetric (Kplus.toHistory.activeStage (AK.shiftTime hKhor t))
              (AK.shiftTime hKhor t))) ∧
        NativeEstimates Kplus ε C1 C2 C1s C2s qOld qsOld τmin Ctime Cgrad ∧
        (∀ t : Icc (0 : ℝ) Kplus.toHistory.horizon,
          (t : ℝ) < Kplus.horizon →
          Kplus.time (Kplus.toHistory.activeStage t) = (t : ℝ) →
          Kplus.toHistory.activeStage t ≠ 0 →
          ∀ y : (Kplus.toHistory.stageAt t).Carrier,
            QbirthOld < metricScalarAt (Kplus.initialMetric (Kplus.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (Kplus.initialMetric (Kplus.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε) ∧
        NativeEstimates L ε C1 C2 C1s C2s qNew qsNew τmin Ctime Cgrad ∧
        (∀ t : Icc (0 : ℝ) L.toHistory.horizon,
          (t : ℝ) < L.horizon → L.time (L.toHistory.activeStage t) = (t : ℝ) →
          L.toHistory.activeStage t ≠ 0 →
          ∀ y : (L.toHistory.stageAt t).Carrier,
            QbirthNew < metricScalarAt (L.initialMetric (L.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (L.initialMetric (L.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε) ∧
        (∀ (T : Icc (0 : ℝ) J.horizon) (_hbuffer : (T : ℝ) < J.horizon)
          (t : Icc (0 : ℝ) (J.restrict T).horizon), b ≤ (t : ℝ) →
          ∀ x : ((J.restrict T).toHistory.stageAt t).Carrier,
            QallOld < metricScalarAt
              ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t)
                t) x →
            ∃ W : SpatialCanonicalWitness
              ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t)
                t) ε (max C1s Cbirth) (max C2s (max Cbirth (Cgrad : ℝ))) x,
              W.capTubeHasNeckChart ε) ∧
        ∃ (T : Icc (0 : ℝ) J.horizon)
          (hHT : H.horizon < (T : ℝ)) (_hbuffer : (T : ℝ) < J.horizon),
          (T : ℝ) = (H.horizon + J.horizon) / 2 ∧
          0 < (T : ℝ) - H.horizon ∧ 0 < J.horizon - (T : ℝ) ∧
          let O := J.restrict T
          let IO : InitialIdentification P g O.toHistory := IJ.restrict T
          IO.IsPrefixOf IJ ∧ O.horizon = (T : ℝ) ∧
          (∀ t : Icc (0 : ℝ) O.horizon,
            HEq (O.toHistory.stageMetric (O.toHistory.activeStage t) t)
              (J.toHistory.stageMetric
                (J.toHistory.activeStage
                  ⟨(t : ℝ), t.property.1, t.property.2.trans T.property.2⟩) t)) ∧
          let spatialAt : Icc (0 : ℝ) O.horizon → Prop := fun t =>
            ∀ x : (O.toHistory.stageAt t).Carrier,
              QallOld < metricScalarAt
                (O.toHistory.stageMetric (O.toHistory.activeStage t) t) x →
              ∃ W : SpatialCanonicalWitness
                (O.toHistory.stageMetric (O.toHistory.activeStage t) t)
                ε (max C1s Cbirth) (max C2s (max Cbirth (Cgrad : ℝ))) x,
                W.capTubeHasNeckChart ε
          let tSeam : Icc (0 : ℝ) O.horizon :=
            ⟨b, H.toHistory.time_nonneg _, H.time_le_horizon.trans hHT.le⟩
          let tOld : Icc (0 : ℝ) O.horizon := ⟨H.horizon, H.horizon_nonneg, hHT.le⟩
          spatialAt tSeam ∧ spatialAt tOld := by
  obtain ⟨pNew, δNew, ρNew, εNew, κNewClass, κNew, qNew, qsNew,
    QzeroNew, QbirthNew, QallNew, r, κJ, _, _, _, _, _, hOld⟩ :=
    exists_prepared_two_overlap_extension_with_closed_seam_with_native_certificate_with_reserve_quality
      1 1 one_pos one_pos
      certificate fixed recenter prepareClass
      ε C1 C2 C1s C2s Cs τmin Cbirth Ctime Cgrad hε hstr analytic
      P g H IH pH recordsH hfixedH hrcH hcapH hcontrolH hwinH κH hκH hncH
      PK gK K IK pOld δOld ρOld B εOld κClass κOld qOld qsOld
      QbirthOld QzeroOld QallOld hQbirthOld
      pK recordsK hclassK hfixedOld hrcOld hcontrolK oldExtension oldControl
      hZeroOld hQallOld c offset Aold hHhor hKB Bfuture R hBfuture hR
  exact ⟨pNew, δNew, ρNew, εNew, κNewClass, κNew, qNew, qsNew,
    QzeroNew, QbirthNew, QallNew, r, κJ, hOld⟩

/-- Compatibility projection of the same generic native construction. -/
theorem exists_prepared_two_overlap_extension_with_closed_seam
    (fixed : StaticCapScaffold) (recenter : ℝ)
    (prepareClass :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ), 0 < B →
      ∃ ε κ : ℝ, 0 < ε ∧ ε < 1 / 11 ∧ 0 < κ ∧
      ∀ (δcap ρcap εcapRequest DcapRequest : ℝ) (mcapRequest : ℕ),
        0 < δcap → 0 < ρcap → 0 < εcapRequest → 0 < DcapRequest →
      ∃ (p₀ : CutoffParameters) (δb ρb : ℝ),
        p₀.fixed = fixed ∧ p₀.recenterConstant = recenter ∧
        0 < δb ∧ δb ≤ δcap ∧ 0 < ρb ∧ ρb ≤ ρcap ∧
        p₀.modelAccuracy ≤ εcapRequest ∧ DcapRequest ≤ p₀.modelRadius ∧
        mcapRequest ≤ p₀.modelOrder ∧
        StandardCap.transitionEnd < p₀.modelRadius + 1 ∧
        p₀.recenterConstant * δb ≤ 1 / 2 ∧
        (∀ (L : RetainedCoreHistory.{u}) (_IL : InitialIdentification P g L.toHistory)
          (pL : CutoffParameters)
          (records : ∀ i : Fin L.eventCount, GeometricCutoffRecord L.toHistory i pL),
          L.horizon ≤ B → L.IsCanonicalCutoffRecordFamily p₀ δb ρb records →
          L.NoncollapsedBefore κ ε L.horizon) ∧
        PreparedGeometricObservationExtension P g B ε κ p₀ δb ρb)
    (ε C1 C2 C1s C2s Cs τmin Cbirth : ℝ) (Ctime Cgrad : ℝ≥0) (hε : 0 < ε)
    (hstr : 1 ≤ C1 ∧ 1 ≤ C2 ∧ 1 ≤ C1s ∧ 1 ≤ C2s ∧ 0 < τmin ∧ ε ≤ εStrong_C12X.{u})
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ ε K.horizon →
        NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε)
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (H : RetainedCoreHistory.{u}) (IH : InitialIdentification P g H.toHistory)
    (pH : CutoffParameters)
    (recordsH : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i pH)
    (hfixedH : pH.fixed = fixed) (hrcH : pH.recenterConstant = recenter)
    (hcapH : StandardCap.transitionEnd < pH.modelRadius + 1)
    (hcontrolH : HistoryEventControl H)
    (hwinH : ∀ i b, ((recordsH i).static b).hasCanonicalWindow)
    (κH : ℝ) (hκH : 0 < κH) (hncH : H.NoncollapsedBefore κH ε H.horizon)
    (PK : OrientedThreeStage.{u}) (gK : PK.Metric)
    (K : RetainedCoreHistory.{u}) (IK : InitialIdentification PK gK K.toHistory)
    (pOld : CutoffParameters) (δOld ρOld B εOld κClass κOld qOld qsOld QbirthOld QzeroOld QallOld : ℝ)
    (hQbirthOld : max 1 (max qOld qsOld) ≤ QbirthOld)
    (pK : CutoffParameters)
    (recordsK : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pK)
    (hclassK : K.IsCanonicalCutoffRecordFamily pOld δOld ρOld recordsK)
    (hfixedOld : pOld.fixed = fixed) (hrcOld : pOld.recenterConstant = recenter)
    (hcontrolK : HistoryEventControl K)
    (oldExtension : PreparedGeometricObservationExtension PK gK B εOld κClass pOld δOld ρOld)
    (oldControl : ∀ (V : RetainedCoreHistory.{u})
      (_IV : InitialIdentification PK gK V.toHistory) (pV : CutoffParameters)
      (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
      V.horizon ≤ B → V.IsCanonicalCutoffRecordFamily pOld δOld ρOld records →
      V.NoncollapsedBefore κOld ε V.horizon ∧
      NativeEstimates V ε C1 C2 C1s C2s qOld qsOld τmin Ctime Cgrad ∧
      ∀ t : Icc (0 : ℝ) V.toHistory.horizon,
        (t : ℝ) < V.horizon → V.time (V.toHistory.activeStage t) = (t : ℝ) →
        V.toHistory.activeStage t ≠ 0 →
        ∀ y : (V.toHistory.stageAt t).Carrier,
          QbirthOld < metricScalarAt (V.initialMetric (V.toHistory.activeStage t)) y →
          ∃ W : SpatialCanonicalWitness (V.initialMetric (V.toHistory.activeStage t))
            ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε)
    (hZeroOld : ∀ (V : ObservedHistory.{u}), InitialIdentification PK gK V →
      ∀ y : (V.stage 0).Carrier, metricScalarAt (V.initialMetric 0) y < QzeroOld)
    (hQallOld : QallOld = max QbirthOld QzeroOld)
    (c : ℝ) (offset : ℕ)
    (Aold : AffineEventPrefix K H c offset (Fin.last K.eventCount))
    (hHhor : H.horizon = K.horizon + c) (hKB : K.horizon < B)
    (Bfuture R : ℝ) (hBfuture : B < Bfuture) (hR : 0 < R) :
    ∃ (pNew : CutoffParameters)
      (δNew ρNew εNew κNewClass κNew qNew qsNew QzeroNew QbirthNew QallNew r κJ : ℝ),
      pNew.fixed = fixed ∧ pNew.recenterConstant = recenter ∧
      0 < δNew ∧ 0 < ρNew ∧ 0 < εNew ∧ εNew < 1 / 11 ∧
      0 < κNewClass ∧ 0 < κNew ∧ 0 < qNew ∧ qNew ≤ qsNew ∧ qsNew ≤ Cs * qNew ∧
      0 < QzeroNew ∧ max 1 (max qNew qsNew) ≤ QbirthNew ∧
      QallNew = max QbirthNew QzeroNew ∧ 0 < QallNew ∧
      0 < r ∧ r ≤ R ∧ QallNew ≤ (r ^ 2)⁻¹ ∧ 0 < κJ ∧
      StandardCap.transitionEnd < pNew.modelRadius + 1 ∧
      pNew.recenterConstant * δNew ≤ 1 / 2 ∧
      (∀ (V : ObservedHistory.{u}),
        InitialIdentification (K.stage (Fin.last K.eventCount))
          (K.initialMetric (Fin.last K.eventCount)) V →
        ∀ y : (V.stage 0).Carrier, metricScalarAt (V.initialMetric 0) y < QzeroNew) ∧
      PreparedGeometricObservationExtension
        (K.stage (Fin.last K.eventCount)) (K.initialMetric (Fin.last K.eventCount))
        (Bfuture - K.time (Fin.last K.eventCount)) εNew κNewClass pNew δNew ρNew ∧
      (∀ (V : RetainedCoreHistory.{u})
        (_IV : InitialIdentification (K.stage (Fin.last K.eventCount))
          (K.initialMetric (Fin.last K.eventCount)) V.toHistory)
        (pV : CutoffParameters)
        (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
        V.horizon ≤ Bfuture - K.time (Fin.last K.eventCount) →
        V.IsCanonicalCutoffRecordFamily pNew δNew ρNew records →
        V.NoncollapsedBefore κNew ε V.horizon ∧
        NativeEstimates V ε C1 C2 C1s C2s qNew qsNew τmin Ctime Cgrad ∧
        ∀ t : Icc (0 : ℝ) V.toHistory.horizon,
          (t : ℝ) < V.horizon → V.time (V.toHistory.activeStage t) = (t : ℝ) →
          V.toHistory.activeStage t ≠ 0 →
          ∀ y : (V.toHistory.stageAt t).Carrier,
            QbirthNew < metricScalarAt (V.initialMetric (V.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (V.initialMetric (V.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε) ∧
    ∀ (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ),
      0 < δcut → 0 < ρcut → 0 < εcut → 0 < Dcut →
    ∃ (L : RetainedCoreHistory.{u})
      (IL : InitialIdentification (K.stage (Fin.last K.eventCount))
        (K.initialMetric (Fin.last K.eventCount)) L.toHistory)
      (pF : CutoffParameters)
      (native : ∀ i : Fin L.eventCount, GeometricCutoffRecord L.toHistory i pF)
      (hwin : ∀ i b, ((native i).static b).hasLinkedCanonicalWindow_C12X)
      (_hrecK : RecordHypFar_C12X (5 / 4) L native)
      (hDK : pK.modelRadius ≤ pF.modelRadius)
      (hmK : pK.modelOrder ≤ pF.modelOrder)
      (haccK : pF.modelAccuracy ≤ pK.modelAccuracy)
      (hDH : pH.modelRadius ≤ pF.modelRadius)
      (hmH : pH.modelOrder ≤ pF.modelOrder)
      (haccH : pF.modelAccuracy ≤ pH.modelAccuracy)
      (hDNew : pNew.modelRadius ≤ pF.modelRadius)
      (hmNew : pNew.modelOrder ≤ pF.modelOrder)
      (haccNew : pF.modelAccuracy ≤ pNew.modelAccuracy),
      let a := K.time (Fin.last K.eventCount)
      let b := H.time (Fin.last H.eventCount)
      let pCK := pF.withModelWindow pK.modelRadius pK.modelOrder pK.modelAccuracy
        pK.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccK)
      let coarseK := fun i : Fin L.eventCount =>
        (native i).restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
            pK.modelRadius_pos hDK hmK haccK
      let qK := pK.spliceAfter (translate_cutoff_parameters pCK a) K.horizon
      let pCH := pF.withModelWindow pH.modelRadius pH.modelOrder pH.modelAccuracy
        pH.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccH)
      let coarseH := fun i : Fin L.eventCount =>
        (native i).restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
            pH.modelRadius_pos hDH hmH haccH
      let qH := pH.spliceAfter (translate_cutoff_parameters pCH b) H.horizon
      let pReserve := pF.withModelWindow pNew.modelRadius pNew.modelOrder pNew.modelAccuracy
        pNew.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccNew)
      let reserved : ∀ i : Fin L.eventCount, GeometricCutoffRecord L.toHistory i pReserve :=
        fun i => (native i).restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
            pNew.modelRadius_pos hDNew hmNew haccNew
      ∃ (Kplus : RetainedCoreHistory.{u}) (IKplus : InitialIdentification PK gK Kplus.toHistory)
        (AK : AffineEventPrefix L Kplus a K.eventCount (Fin.last L.eventCount))
        (IoldK : RawInitialPrefix K Kplus)
        (joinedK : ∀ i : Fin Kplus.eventCount, GeometricCutoffRecord Kplus.toHistory i qK)
        (J : RetainedCoreHistory.{u}) (IJ : InitialIdentification P g J.toHistory)
        (AJ : AffineEventPrefix L J b H.eventCount (Fin.last L.eventCount))
        (IoldH : RawInitialPrefix H J)
        (joinedH : ∀ i : Fin J.eventCount, GeometricCutoffRecord J.toHistory i qH)
        (hKhor : Kplus.horizon = L.horizon + a) (hJhor : J.horizon = L.horizon + b),
        (InitialIdentification.atZero (K.stage (Fin.last K.eventCount))
          (K.initialMetric (Fin.last K.eventCount))).IsPrefixOf IL ∧
        L.horizon = B - a ∧ Kplus.horizon = B ∧ J.horizon = B + c ∧
        IK.IsPrefixOf IKplus ∧ IH.IsPrefixOf IJ ∧
        HistoryEventControl L ∧ HistoryEventControl Kplus ∧ HistoryEventControl J ∧
        L.IsCanonicalCutoffRecordFamily pNew δNew ρNew reserved ∧
        Kplus.IsCanonicalCutoffRecordFamily pOld δOld ρOld joinedK ∧
        L.NoncollapsedBefore κNew ε L.horizon ∧
        Kplus.NoncollapsedBefore κOld ε Kplus.horizon ∧
        J.NoncollapsedBefore κJ ε J.horizon ∧
        pF.fixed = fixed ∧ pF.recenterConstant = recenter ∧
        pF.modelAccuracy ≤ εcut ∧ Dcut ≤ pF.modelRadius ∧ mcut ≤ pF.modelOrder ∧
        (∀ i : Fin L.eventCount,
          pF.delta (L.time i.succ) ≤ δcut ∧ pF.neckRadius (L.time i.succ) ≤ min r ρcut) ∧
        (∀ t : ℝ, HEq (Kplus.toHistory.stageMetric (Fin.last Kplus.eventCount) (t + a))
          (L.toHistory.stageMetric (Fin.last L.eventCount) t)) ∧
        (∀ t : ℝ, HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + b))
          (L.toHistory.stageMetric (Fin.last L.eventCount) t)) ∧
        (∀ t : ℝ, t ≤ K.horizon → qK.delta t = pK.delta t ∧
          qK.neckRadius t = pK.neckRadius t ∧ qK.protectedRadius t = pK.protectedRadius t) ∧
        (∀ t : ℝ, t ≤ H.horizon → qH.delta t = pH.delta t ∧
          qH.neckRadius t = pH.neckRadius t ∧ qH.protectedRadius t = pH.protectedRadius t) ∧
        (∀ i b, ((joinedH i).static b).hasCanonicalWindow) ∧
        (∀ i : Fin K.eventCount,
          HEq (joinedK (i.castLE IoldK.count_le)).nominalRadius (recordsK i).nominalRadius ∧
          HEq (joinedK (i.castLE IoldK.count_le)).delta (recordsK i).delta ∧
          HEq (joinedK (i.castLE IoldK.count_le)).order (recordsK i).order ∧
          HEq (joinedK (i.castLE IoldK.count_le)).neck (recordsK i).neck ∧
          HEq (joinedK (i.castLE IoldK.count_le)).static (recordsK i).static) ∧
        (∀ i : Fin H.eventCount,
          HEq (joinedH (i.castLE IoldH.count_le)).nominalRadius (recordsH i).nominalRadius ∧
          HEq (joinedH (i.castLE IoldH.count_le)).delta (recordsH i).delta ∧
          HEq (joinedH (i.castLE IoldH.count_le)).order (recordsH i).order ∧
          HEq (joinedH (i.castLE IoldH.count_le)).neck (recordsH i).neck ∧
          HEq (joinedH (i.castLE IoldH.count_le)).static (recordsH i).static) ∧
        (∀ i : Fin L.eventCount,
          HEq (joinedK (AK.eventIndex i)).nominalRadius (native i).nominalRadius ∧
          HEq (joinedK (AK.eventIndex i)).delta (native i).delta ∧
          HEq (joinedK (AK.eventIndex i)).order (native i).order ∧
          HEq (joinedK (AK.eventIndex i)).neck (native i).neck ∧
          HEq (joinedK (AK.eventIndex i)).static
            (fun b => translate_presented_static_cap (L.coreEvent i) a ((coarseK i).static b))) ∧
        (∀ i : Fin L.eventCount,
          HEq (joinedH (AJ.eventIndex i)).nominalRadius (native i).nominalRadius ∧
          HEq (joinedH (AJ.eventIndex i)).delta (native i).delta ∧
          HEq (joinedH (AJ.eventIndex i)).order (native i).order ∧
          HEq (joinedH (AJ.eventIndex i)).neck (native i).neck ∧
          HEq (joinedH (AJ.eventIndex i)).static
            (fun z => translate_presented_static_cap (L.coreEvent i) b ((coarseH i).static z))) ∧
        (∀ t : Icc (0 : ℝ) L.horizon,
          J.toHistory.stageAt (AJ.shiftTime hJhor t) =
            Kplus.toHistory.stageAt (AK.shiftTime hKhor t) ∧
          HEq (J.toHistory.stageMetric (J.toHistory.activeStage (AJ.shiftTime hJhor t))
              (AJ.shiftTime hJhor t))
            (Kplus.toHistory.stageMetric (Kplus.toHistory.activeStage (AK.shiftTime hKhor t))
              (AK.shiftTime hKhor t))) ∧
        NativeEstimates Kplus ε C1 C2 C1s C2s qOld qsOld τmin Ctime Cgrad ∧
        (∀ t : Icc (0 : ℝ) Kplus.toHistory.horizon,
          (t : ℝ) < Kplus.horizon →
          Kplus.time (Kplus.toHistory.activeStage t) = (t : ℝ) →
          Kplus.toHistory.activeStage t ≠ 0 →
          ∀ y : (Kplus.toHistory.stageAt t).Carrier,
            QbirthOld < metricScalarAt (Kplus.initialMetric (Kplus.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (Kplus.initialMetric (Kplus.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε) ∧
        NativeEstimates L ε C1 C2 C1s C2s qNew qsNew τmin Ctime Cgrad ∧
        (∀ t : Icc (0 : ℝ) L.toHistory.horizon,
          (t : ℝ) < L.horizon → L.time (L.toHistory.activeStage t) = (t : ℝ) →
          L.toHistory.activeStage t ≠ 0 →
          ∀ y : (L.toHistory.stageAt t).Carrier,
            QbirthNew < metricScalarAt (L.initialMetric (L.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (L.initialMetric (L.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε) ∧
        (∀ (T : Icc (0 : ℝ) J.horizon) (_hbuffer : (T : ℝ) < J.horizon)
          (t : Icc (0 : ℝ) (J.restrict T).horizon), b ≤ (t : ℝ) →
          ∀ x : ((J.restrict T).toHistory.stageAt t).Carrier,
            QallOld < metricScalarAt
              ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t)
                t) x →
            ∃ W : SpatialCanonicalWitness
              ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t)
                t) ε (max C1s Cbirth) (max C2s (max Cbirth (Cgrad : ℝ))) x,
              W.capTubeHasNeckChart ε) ∧
        ∃ (T : Icc (0 : ℝ) J.horizon)
          (hHT : H.horizon < (T : ℝ)) (_hbuffer : (T : ℝ) < J.horizon),
          (T : ℝ) = (H.horizon + J.horizon) / 2 ∧
          0 < (T : ℝ) - H.horizon ∧ 0 < J.horizon - (T : ℝ) ∧
          let O := J.restrict T
          let IO : InitialIdentification P g O.toHistory := IJ.restrict T
          IO.IsPrefixOf IJ ∧ O.horizon = (T : ℝ) ∧
          (∀ t : Icc (0 : ℝ) O.horizon,
            HEq (O.toHistory.stageMetric (O.toHistory.activeStage t) t)
              (J.toHistory.stageMetric
                (J.toHistory.activeStage
                  ⟨(t : ℝ), t.property.1, t.property.2.trans T.property.2⟩) t)) ∧
          let spatialAt : Icc (0 : ℝ) O.horizon → Prop := fun t =>
            ∀ x : (O.toHistory.stageAt t).Carrier,
              QallOld < metricScalarAt
                (O.toHistory.stageMetric (O.toHistory.activeStage t) t) x →
              ∃ W : SpatialCanonicalWitness
                (O.toHistory.stageMetric (O.toHistory.activeStage t) t)
                ε (max C1s Cbirth) (max C2s (max Cbirth (Cgrad : ℝ))) x,
                W.capTubeHasNeckChart ε
          let tSeam : Icc (0 : ℝ) O.horizon :=
            ⟨b, H.toHistory.time_nonneg _, H.time_le_horizon.trans hHT.le⟩
          let tOld : Icc (0 : ℝ) O.horizon := ⟨H.horizon, H.horizon_nonneg, hHT.le⟩
          spatialAt tSeam ∧ spatialAt tOld := by
  have nativeResult :=
    @exists_prepared_two_overlap_extension_with_closed_seam_with_native_certificate.{u} (fun _ =>
    True) fixed recenter (PreparedClassProviderWithNative.of_weak prepareClass) ε C1 C2 C1s C2s Cs
    τmin Cbirth Ctime Cgrad hε hstr analytic P g H IH pH recordsH hfixedH hrcH hcapH hcontrolH hwinH
    κH hκH hncH PK gK K IK pOld δOld ρOld B εOld κClass κOld qOld qsOld QbirthOld QzeroOld QallOld
    hQbirthOld pK recordsK hclassK hfixedOld hrcOld hcontrolK oldExtension.withTrue oldControl
    hZeroOld hQallOld c offset Aold hHhor hKB Bfuture R hBfuture hR
  obtain ⟨pNew, δNew, ρNew, εNew, κNewClass, κNew, qNew, qsNew, QzeroNew, QbirthNew, QallNew, r, κJ,
    nativeProjectionh1⟩ := nativeResult
  refine ⟨pNew, δNew, ρNew, εNew, κNewClass, κNew, qNew, qsNew, QzeroNew, QbirthNew, QallNew, r, κJ,
    ?_⟩
  obtain ⟨nativeProjectionfield2, nativeProjectionfield3, nativeProjectionfield4,
    nativeProjectionfield5, nativeProjectionfield6, nativeProjectionfield7, nativeProjectionfield8,
    nativeProjectionfield9, nativeProjectionfield10, nativeProjectionfield11,
    nativeProjectionfield12, nativeProjectionfield13, nativeProjectionfield14,
    nativeProjectionfield15, nativeProjectionfield16, nativeProjectionfield17,
    nativeProjectionfield18, nativeProjectionfield19, nativeProjectionfield20,
    nativeProjectionfield21, nativeProjectionfield22, nativeProjectionfield23, nativeProjectionh24⟩
    := nativeProjectionh1
  refine ⟨nativeProjectionfield2, nativeProjectionfield3, nativeProjectionfield4,
    nativeProjectionfield5, nativeProjectionfield6, nativeProjectionfield7, nativeProjectionfield8,
    nativeProjectionfield9, nativeProjectionfield10, nativeProjectionfield11,
    nativeProjectionfield12, nativeProjectionfield13, nativeProjectionfield14,
    nativeProjectionfield15, nativeProjectionfield16, nativeProjectionfield17,
    nativeProjectionfield18, nativeProjectionfield19, nativeProjectionfield20,
    nativeProjectionfield21, nativeProjectionfield22, nativeProjectionfield23, ?_⟩
  refine ⟨?_, ?_⟩
  · exact PreparedGeometricObservationExtensionWithNative.forget nativeProjectionh24.1
  · obtain ⟨nativeProjectionfield25, nativeProjectionh26⟩ := nativeProjectionh24.2
    refine ⟨nativeProjectionfield25, ?_⟩
    intro δcut ρcut εcut Dcut mcut nativeProjectionx27 nativeProjectionx28 nativeProjectionx29
      nativeProjectionx30
    have nativeProjectionh31 := @nativeProjectionh26 δcut ρcut εcut Dcut mcut nativeProjectionx27
      nativeProjectionx28 nativeProjectionx29 nativeProjectionx30
    obtain ⟨L, IL, pF, native, hwin, hrecK, hDK, hmK, haccK, hDH, hmH, haccH, hDNew, hmNew, haccNew,
      nativeProjectionh32⟩ := nativeProjectionh31
    refine ⟨L, IL, pF, native, hwin, hrecK, hDK, hmK, haccK, hDH, hmH, haccH, hDNew, hmNew, haccNew, ?_⟩
    dsimp only at nativeProjectionh32 ⊢
    obtain ⟨Kplus, IKplus, AK, IoldK, joinedK, J, IJ, AJ, IoldH, joinedH, hKhor, hJhor,
      nativeProjectionh33⟩ := nativeProjectionh32
    refine ⟨Kplus, IKplus, AK, IoldK, joinedK, J, IJ, AJ, IoldH, joinedH, hKhor, hJhor, ?_⟩
    obtain ⟨nativeProjectionfield34, nativeProjectionfield35, nativeProjectionfield36,
      nativeProjectionfield37, nativeProjectionfield38, nativeProjectionfield39,
      nativeProjectionh40⟩ := nativeProjectionh33
    refine ⟨nativeProjectionfield34, nativeProjectionfield35, nativeProjectionfield36,
      nativeProjectionfield37, nativeProjectionfield38, nativeProjectionfield39, ?_⟩
    exact nativeProjectionh40.2

/-- The same native construction retaining the actual event distance certificate. -/
theorem exists_prepared_two_overlap_extension_with_closed_seam_with_distance_scalars
    (Cdist : ℝ≥0)
    (fixed : StaticCapScaffold) (recenter : ℝ)
    (prepareClass : PreparedDistanceClassProvider.{u} fixed recenter Cdist)
    (ε C1 C2 C1s C2s Cs τmin Cbirth : ℝ) (Ctime Cgrad : ℝ≥0) (hε : 0 < ε)
    (hstr : 1 ≤ C1 ∧ 1 ≤ C2 ∧ 1 ≤ C1s ∧ 1 ≤ C2s ∧ 0 < τmin ∧ ε ≤ εStrong_C12X.{u})
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ ε K.horizon →
        NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε)
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (H : RetainedCoreHistory.{u}) (IH : InitialIdentification P g H.toHistory)
    (pH : CutoffParameters)
    (recordsH : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i pH)
    (hfixedH : pH.fixed = fixed) (hrcH : pH.recenterConstant = recenter)
    (hcapH : StandardCap.transitionEnd < pH.modelRadius + 1)
    (hcontrolH : HistoryEventControl H)
    (hwinH : ∀ i b, ((recordsH i).static b).hasCanonicalWindow)
    (κH : ℝ) (hκH : 0 < κH) (hncH : H.NoncollapsedBefore κH ε H.horizon)
    (PK : OrientedThreeStage.{u}) (gK : PK.Metric)
    (K : RetainedCoreHistory.{u}) (IK : InitialIdentification PK gK K.toHistory)
    (pOld : CutoffParameters) (δOld ρOld B εOld κClass κOld qOld qsOld QbirthOld QzeroOld QallOld : ℝ)
    (hQbirthOld : max 1 (max qOld qsOld) ≤ QbirthOld)
    (pK : CutoffParameters)
    (recordsK : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pK)
    (hclassK : K.IsCanonicalCutoffRecordFamily pOld δOld ρOld recordsK)
    (hfixedOld : pOld.fixed = fixed) (hrcOld : pOld.recenterConstant = recenter)
    (hcontrolK : HistoryEventControl K)
    (oldExtension : PreparedGeometricObservationExtensionWithDistance Cdist PK gK B εOld κClass pOld δOld ρOld)
    (oldControl : ∀ (V : RetainedCoreHistory.{u})
      (_IV : InitialIdentification PK gK V.toHistory) (pV : CutoffParameters)
      (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
      V.horizon ≤ B → V.IsCanonicalCutoffRecordFamily pOld δOld ρOld records →
      V.NoncollapsedBefore κOld ε V.horizon ∧
      NativeEstimates V ε C1 C2 C1s C2s qOld qsOld τmin Ctime Cgrad ∧
      ∀ t : Icc (0 : ℝ) V.toHistory.horizon,
        (t : ℝ) < V.horizon → V.time (V.toHistory.activeStage t) = (t : ℝ) →
        V.toHistory.activeStage t ≠ 0 →
        ∀ y : (V.toHistory.stageAt t).Carrier,
          QbirthOld < metricScalarAt (V.initialMetric (V.toHistory.activeStage t)) y →
          ∃ W : SpatialCanonicalWitness (V.initialMetric (V.toHistory.activeStage t))
            ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε)
    (hZeroOld : ∀ (V : ObservedHistory.{u}), InitialIdentification PK gK V →
      ∀ y : (V.stage 0).Carrier, metricScalarAt (V.initialMetric 0) y < QzeroOld)
    (hQallOld : QallOld = max QbirthOld QzeroOld)
    (c : ℝ) (offset : ℕ)
    (Aold : AffineEventPrefix K H c offset (Fin.last K.eventCount))
    (hHhor : H.horizon = K.horizon + c) (hKB : K.horizon < B)
    (Bfuture R : ℝ) (hBfuture : B < Bfuture) (hR : 0 < R) :
    ∃ (pNew : CutoffParameters)
      (δNew ρNew εNew κNewClass κNew qNew qsNew QzeroNew QbirthNew QallNew r κJ : ℝ),
      pNew.fixed = fixed ∧ pNew.recenterConstant = recenter ∧
      0 < δNew ∧ 0 < ρNew ∧ 0 < εNew ∧ εNew < 1 / 11 ∧
      0 < κNewClass ∧ 0 < κNew ∧ 0 < qNew ∧ qNew ≤ qsNew ∧ qsNew ≤ Cs * qNew ∧
      0 < QzeroNew ∧ max 1 (max qNew qsNew) ≤ QbirthNew ∧
      QallNew = max QbirthNew QzeroNew ∧ 0 < QallNew ∧
      0 < r ∧ r ≤ R ∧ QallNew ≤ (r ^ 2)⁻¹ ∧ 0 < κJ ∧
      StandardCap.transitionEnd < pNew.modelRadius + 1 ∧
      pNew.recenterConstant * δNew ≤ 1 / 2 ∧
      (∀ (V : ObservedHistory.{u}),
        InitialIdentification (K.stage (Fin.last K.eventCount))
          (K.initialMetric (Fin.last K.eventCount)) V →
        ∀ y : (V.stage 0).Carrier, metricScalarAt (V.initialMetric 0) y < QzeroNew) ∧
      PreparedGeometricObservationExtensionWithDistance Cdist
        (K.stage (Fin.last K.eventCount)) (K.initialMetric (Fin.last K.eventCount))
        (Bfuture - K.time (Fin.last K.eventCount)) εNew κNewClass pNew δNew ρNew ∧
      (∀ (V : RetainedCoreHistory.{u})
        (_IV : InitialIdentification (K.stage (Fin.last K.eventCount))
          (K.initialMetric (Fin.last K.eventCount)) V.toHistory)
        (pV : CutoffParameters)
        (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
        V.horizon ≤ Bfuture - K.time (Fin.last K.eventCount) →
        V.IsCanonicalCutoffRecordFamily pNew δNew ρNew records →
        V.NoncollapsedBefore κNew ε V.horizon ∧
        NativeEstimates V ε C1 C2 C1s C2s qNew qsNew τmin Ctime Cgrad ∧
        ∀ t : Icc (0 : ℝ) V.toHistory.horizon,
          (t : ℝ) < V.horizon → V.time (V.toHistory.activeStage t) = (t : ℝ) →
          V.toHistory.activeStage t ≠ 0 →
          ∀ y : (V.toHistory.stageAt t).Carrier,
            QbirthNew < metricScalarAt (V.initialMetric (V.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (V.initialMetric (V.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε) ∧
    ∀ (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ),
      0 < δcut → 0 < ρcut → 0 < εcut → 0 < Dcut →
    ∃ (L : RetainedCoreHistory.{u})
      (IL : InitialIdentification (K.stage (Fin.last K.eventCount))
        (K.initialMetric (Fin.last K.eventCount)) L.toHistory)
      (pF : CutoffParameters)
      (native : ∀ i : Fin L.eventCount, GeometricCutoffRecord L.toHistory i pF)
      (hwin : ∀ i b, ((native i).static b).hasLinkedCanonicalWindow_C12X)
      (_hrecK : RecordHypFar_C12X (5 / 4) L native)
      (hDK : pK.modelRadius ≤ pF.modelRadius)
      (hmK : pK.modelOrder ≤ pF.modelOrder)
      (haccK : pF.modelAccuracy ≤ pK.modelAccuracy)
      (hDH : pH.modelRadius ≤ pF.modelRadius)
      (hmH : pH.modelOrder ≤ pF.modelOrder)
      (haccH : pF.modelAccuracy ≤ pH.modelAccuracy)
      (hDNew : pNew.modelRadius ≤ pF.modelRadius)
      (hmNew : pNew.modelOrder ≤ pF.modelOrder)
      (haccNew : pF.modelAccuracy ≤ pNew.modelAccuracy),
      let a := K.time (Fin.last K.eventCount)
      let b := H.time (Fin.last H.eventCount)
      let pCK := pF.withModelWindow pK.modelRadius pK.modelOrder pK.modelAccuracy
        pK.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccK)
      let coarseK := fun i : Fin L.eventCount =>
        (native i).restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
            pK.modelRadius_pos hDK hmK haccK
      let qK := pK.spliceAfter (translate_cutoff_parameters pCK a) K.horizon
      let pCH := pF.withModelWindow pH.modelRadius pH.modelOrder pH.modelAccuracy
        pH.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccH)
      let coarseH := fun i : Fin L.eventCount =>
        (native i).restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
            pH.modelRadius_pos hDH hmH haccH
      let qH := pH.spliceAfter (translate_cutoff_parameters pCH b) H.horizon
      let pReserve := pF.withModelWindow pNew.modelRadius pNew.modelOrder pNew.modelAccuracy
        pNew.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccNew)
      let reserved : ∀ i : Fin L.eventCount, GeometricCutoffRecord L.toHistory i pReserve :=
        fun i => (native i).restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
            pNew.modelRadius_pos hDNew hmNew haccNew
      ∃ (Kplus : RetainedCoreHistory.{u}) (IKplus : InitialIdentification PK gK Kplus.toHistory)
        (AK : AffineEventPrefix L Kplus a K.eventCount (Fin.last L.eventCount))
        (IoldK : RawInitialPrefix K Kplus)
        (joinedK : ∀ i : Fin Kplus.eventCount, GeometricCutoffRecord Kplus.toHistory i qK)
        (J : RetainedCoreHistory.{u}) (IJ : InitialIdentification P g J.toHistory)
        (AJ : AffineEventPrefix L J b H.eventCount (Fin.last L.eventCount))
        (IoldH : RawInitialPrefix H J)
        (joinedH : ∀ i : Fin J.eventCount, GeometricCutoffRecord J.toHistory i qH)
        (hKhor : Kplus.horizon = L.horizon + a) (hJhor : J.horizon = L.horizon + b),
        (InitialIdentification.atZero (K.stage (Fin.last K.eventCount))
          (K.initialMetric (Fin.last K.eventCount))).IsPrefixOf IL ∧
        L.horizon = B - a ∧ Kplus.horizon = B ∧ J.horizon = B + c ∧
        IK.IsPrefixOf IKplus ∧ IH.IsPrefixOf IJ ∧
        (∀ i : Fin L.eventCount, (L.toHistory.event i).HasUniformDistanceScalar Cdist) ∧
        HistoryEventControl L ∧ HistoryEventControl Kplus ∧ HistoryEventControl J ∧
        L.IsCanonicalCutoffRecordFamily pNew δNew ρNew reserved ∧
        Kplus.IsCanonicalCutoffRecordFamily pOld δOld ρOld joinedK ∧
        L.NoncollapsedBefore κNew ε L.horizon ∧
        Kplus.NoncollapsedBefore κOld ε Kplus.horizon ∧
        J.NoncollapsedBefore κJ ε J.horizon ∧
        pF.fixed = fixed ∧ pF.recenterConstant = recenter ∧
        pF.modelAccuracy ≤ εcut ∧ Dcut ≤ pF.modelRadius ∧ mcut ≤ pF.modelOrder ∧
        (∀ i : Fin L.eventCount,
          pF.delta (L.time i.succ) ≤ δcut ∧ pF.neckRadius (L.time i.succ) ≤ min r ρcut) ∧
        (∀ t : ℝ, HEq (Kplus.toHistory.stageMetric (Fin.last Kplus.eventCount) (t + a))
          (L.toHistory.stageMetric (Fin.last L.eventCount) t)) ∧
        (∀ t : ℝ, HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + b))
          (L.toHistory.stageMetric (Fin.last L.eventCount) t)) ∧
        (∀ t : ℝ, t ≤ K.horizon → qK.delta t = pK.delta t ∧
          qK.neckRadius t = pK.neckRadius t ∧ qK.protectedRadius t = pK.protectedRadius t) ∧
        (∀ t : ℝ, t ≤ H.horizon → qH.delta t = pH.delta t ∧
          qH.neckRadius t = pH.neckRadius t ∧ qH.protectedRadius t = pH.protectedRadius t) ∧
        (∀ i b, ((joinedH i).static b).hasCanonicalWindow) ∧
        (∀ i : Fin K.eventCount,
          HEq (joinedK (i.castLE IoldK.count_le)).nominalRadius (recordsK i).nominalRadius ∧
          HEq (joinedK (i.castLE IoldK.count_le)).delta (recordsK i).delta ∧
          HEq (joinedK (i.castLE IoldK.count_le)).order (recordsK i).order ∧
          HEq (joinedK (i.castLE IoldK.count_le)).neck (recordsK i).neck ∧
          HEq (joinedK (i.castLE IoldK.count_le)).static (recordsK i).static) ∧
        (∀ i : Fin H.eventCount,
          HEq (joinedH (i.castLE IoldH.count_le)).nominalRadius (recordsH i).nominalRadius ∧
          HEq (joinedH (i.castLE IoldH.count_le)).delta (recordsH i).delta ∧
          HEq (joinedH (i.castLE IoldH.count_le)).order (recordsH i).order ∧
          HEq (joinedH (i.castLE IoldH.count_le)).neck (recordsH i).neck ∧
          HEq (joinedH (i.castLE IoldH.count_le)).static (recordsH i).static) ∧
        (∀ i : Fin L.eventCount,
          HEq (joinedK (AK.eventIndex i)).nominalRadius (native i).nominalRadius ∧
          HEq (joinedK (AK.eventIndex i)).delta (native i).delta ∧
          HEq (joinedK (AK.eventIndex i)).order (native i).order ∧
          HEq (joinedK (AK.eventIndex i)).neck (native i).neck ∧
          HEq (joinedK (AK.eventIndex i)).static
            (fun b => translate_presented_static_cap (L.coreEvent i) a ((coarseK i).static b))) ∧
        (∀ i : Fin L.eventCount,
          HEq (joinedH (AJ.eventIndex i)).nominalRadius (native i).nominalRadius ∧
          HEq (joinedH (AJ.eventIndex i)).delta (native i).delta ∧
          HEq (joinedH (AJ.eventIndex i)).order (native i).order ∧
          HEq (joinedH (AJ.eventIndex i)).neck (native i).neck ∧
          HEq (joinedH (AJ.eventIndex i)).static
            (fun z => translate_presented_static_cap (L.coreEvent i) b ((coarseH i).static z))) ∧
        (∀ t : Icc (0 : ℝ) L.horizon,
          J.toHistory.stageAt (AJ.shiftTime hJhor t) =
            Kplus.toHistory.stageAt (AK.shiftTime hKhor t) ∧
          HEq (J.toHistory.stageMetric (J.toHistory.activeStage (AJ.shiftTime hJhor t))
              (AJ.shiftTime hJhor t))
            (Kplus.toHistory.stageMetric (Kplus.toHistory.activeStage (AK.shiftTime hKhor t))
              (AK.shiftTime hKhor t))) ∧
        NativeEstimates Kplus ε C1 C2 C1s C2s qOld qsOld τmin Ctime Cgrad ∧
        (∀ t : Icc (0 : ℝ) Kplus.toHistory.horizon,
          (t : ℝ) < Kplus.horizon →
          Kplus.time (Kplus.toHistory.activeStage t) = (t : ℝ) →
          Kplus.toHistory.activeStage t ≠ 0 →
          ∀ y : (Kplus.toHistory.stageAt t).Carrier,
            QbirthOld < metricScalarAt (Kplus.initialMetric (Kplus.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (Kplus.initialMetric (Kplus.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε) ∧
        NativeEstimates L ε C1 C2 C1s C2s qNew qsNew τmin Ctime Cgrad ∧
        (∀ t : Icc (0 : ℝ) L.toHistory.horizon,
          (t : ℝ) < L.horizon → L.time (L.toHistory.activeStage t) = (t : ℝ) →
          L.toHistory.activeStage t ≠ 0 →
          ∀ y : (L.toHistory.stageAt t).Carrier,
            QbirthNew < metricScalarAt (L.initialMetric (L.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (L.initialMetric (L.toHistory.activeStage t))
              ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε) ∧
        (∀ (T : Icc (0 : ℝ) J.horizon) (_hbuffer : (T : ℝ) < J.horizon)
          (t : Icc (0 : ℝ) (J.restrict T).horizon), b ≤ (t : ℝ) →
          ∀ x : ((J.restrict T).toHistory.stageAt t).Carrier,
            QallOld < metricScalarAt
              ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t)
                t) x →
            ∃ W : SpatialCanonicalWitness
              ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t)
                t) ε (max C1s Cbirth) (max C2s (max Cbirth (Cgrad : ℝ))) x,
              W.capTubeHasNeckChart ε) ∧
        ∃ (T : Icc (0 : ℝ) J.horizon)
          (hHT : H.horizon < (T : ℝ)) (_hbuffer : (T : ℝ) < J.horizon),
          (T : ℝ) = (H.horizon + J.horizon) / 2 ∧
          0 < (T : ℝ) - H.horizon ∧ 0 < J.horizon - (T : ℝ) ∧
          let O := J.restrict T
          let IO : InitialIdentification P g O.toHistory := IJ.restrict T
          IO.IsPrefixOf IJ ∧ O.horizon = (T : ℝ) ∧
          (∀ t : Icc (0 : ℝ) O.horizon,
            HEq (O.toHistory.stageMetric (O.toHistory.activeStage t) t)
              (J.toHistory.stageMetric
                (J.toHistory.activeStage
                  ⟨(t : ℝ), t.property.1, t.property.2.trans T.property.2⟩) t)) ∧
          let spatialAt : Icc (0 : ℝ) O.horizon → Prop := fun t =>
            ∀ x : (O.toHistory.stageAt t).Carrier,
              QallOld < metricScalarAt
                (O.toHistory.stageMetric (O.toHistory.activeStage t) t) x →
              ∃ W : SpatialCanonicalWitness
                (O.toHistory.stageMetric (O.toHistory.activeStage t) t)
                ε (max C1s Cbirth) (max C2s (max Cbirth (Cgrad : ℝ))) x,
                W.capTubeHasNeckChart ε
          let tSeam : Icc (0 : ℝ) O.horizon :=
            ⟨b, H.toHistory.time_nonneg _, H.time_le_horizon.trans hHT.le⟩
          let tOld : Icc (0 : ℝ) O.horizon := ⟨H.horizon, H.horizon_nonneg, hHT.le⟩
          spatialAt tSeam ∧ spatialAt tOld := by
  exact @exists_prepared_two_overlap_extension_with_closed_seam_with_native_certificate.{u} (fun K
    => ∀ i : Fin K.eventCount, (K.toHistory.event i).HasUniformDistanceScalar Cdist) fixed recenter
    prepareClass.toNative ε C1 C2 C1s C2s Cs τmin Cbirth Ctime Cgrad hε hstr analytic P g H IH pH
    recordsH hfixedH hrcH hcapH hcontrolH hwinH κH hκH hncH PK gK K IK pOld δOld ρOld B εOld κClass
    κOld qOld qsOld QbirthOld QzeroOld QallOld hQbirthOld pK recordsK hclassK hfixedOld hrcOld
    hcontrolK oldExtension.toNative oldControl hZeroOld hQallOld c offset Aold hHhor hKB Bfuture R
    hBfuture hR

end GC.GeneralFlow
