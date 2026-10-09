import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedObservationEstimates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.AffineHistoryParabolicBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SpatialWitnessTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedDistanceData

/-!
# S-CH11-FIX12 patched-at-path `PreparedOverlapExtension`

来源：donor `PreparedOverlapExtension.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败；本文件只有 elaboration 层面修补（no statement / definition /
proof idea altered；不加 `set_option`）。patched-at-path：下游 `PreparedOverlapClosedBirth` 对它做
`open private … from` 原路径，故不做 PortC11P + shim（原路径文本 = 本文件）：
* 3 处 `htopK`（`(tK : ℝ) < Kplus.horizon`，`tK : Icc 0 Kplus.horizon`）里的 `rw [hKhor]`：motive
  不 type correct（`tK` 的类型含 `Kplus.horizon`）→ 先在 `L.horizon + a` 上证 `h2`，再
  `h2.trans_eq hKhor.symm`；
* `hT` guard 里的 `have ht := T.property.2; rw [hJhor] at ht`（`ht : ↑T ≤ J.horizon`，
  `T : Icc 0 J.horizon`，同样 motive 不 type correct）→ 直接
  `linarith [T.property.2.trans_eq hJhor]`；
* `hinit`：`simpa only [stageIndex_last] using hi` 进不了 `HEq` 的依赖位 → 先
  `rw [Aold.stageIndex_last] at hi` 再 `exact hi`（同 FIX6 坑 (x)）；
* `hreach`：`add_le_add_right hKB.le c`（本树左右约定相反）→ `add_le_add hKB.le le_rfl`；
* `hzeroK`：`simpa only [hz] using hZero …` 进不了 `∀ y : (Kplus.stage _).Carrier` 的依赖位 →
  `rw [hz]; exact hZero …`；
* 陈述里只出现、证明不引用的 binder（`IV` 等）加 `_` 前缀（unusedVariables；binder 名不改变陈述）。
-/

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal
namespace GC.GeneralFlow
universe u

open private overlapCastPoint overlapCastPoint_heq overlap_scalar_eq
  overlap_spatialWitness_transport from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SpatialWitnessTransport

/-- The native estimate packet supplies a physical spatial witness at a strictly
regular time. Both the active stage birth and the history horizon are strict;
the event-slab upper bound follows from the actual active-stage domain. -/
theorem NativeEstimates.exists_spatialCanonicalWitness_of_strict_birth
    {K : RetainedCoreHistory.{u}}
    {ε C1 C2 C1s C2s qcan qs τmin : ℝ} {Ctime Cgrad : ℝ≥0}
    (hEst : NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad)
    (t : Icc (0 : ℝ) K.horizon) (htop : (t : ℝ) < K.horizon)
    (hbirth : K.time (K.toHistory.activeStage t) < (t : ℝ)) :
    ∀ x : (K.toHistory.stageAt t).Carrier,
      qs < metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage t) t) x →
      ∃ W : SpatialCanonicalWitness
        (K.toHistory.stageMetric (K.toHistory.activeStage t) t) ε C1s C2s x,
        W.capTubeHasNeckChart ε := by
  have hdom := K.toHistory.activeStage_mem t
  change ∀ x : (K.stage (K.toHistory.activeStage t)).Carrier, _
  generalize hj : K.toHistory.activeStage t = j at hbirth hdom ⊢
  cases j using Fin.lastCases with
  | last =>
    have hfinal : K.time (Fin.last K.eventCount) < K.horizon := hbirth.trans htop
    intro x hx
    rw [ObservedHistory.stageMetric_last_of_lt (h := hfinal)] at hx ⊢
    exact (hEst.2 hfinal).2.2.2 x t ⟨hbirth, htop⟩ hx
  | cast i =>
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, Set.mem_Ico] at hdom
    intro x hx
    rw [ObservedHistory.stageMetric_castSucc_apply] at hx ⊢
    exact (hEst.1 i).2.2.2 x t ⟨hbirth, hdom.2⟩ hx

/-- A buffered actual observation receives the old native spatial estimate
through two affine views of the SAME tail L. The observation endpoint is
allowed, because the longer histories extend strictly beyond it. The query
must lie strictly beyond b and the source active-stage birth. -/
theorem exists_spatialCanonicalWitness_on_buffered_same_tail_observation
    {L Kplus J : RetainedCoreHistory.{u}} {a b : ℝ} {offsetK offsetJ : ℕ}
    (AK : AffineEventPrefix L Kplus a offsetK (Fin.last L.eventCount))
    (AJ : AffineEventPrefix L J b offsetJ (Fin.last L.eventCount))
    (hKhor : Kplus.horizon = L.horizon + a)
    (hJhor : J.horizon = L.horizon + b)
    (hKmetric : ∀ s : ℝ,
      HEq (Kplus.toHistory.stageMetric (Fin.last Kplus.eventCount) (s + a))
        (L.toHistory.stageMetric (Fin.last L.eventCount) s))
    (hJmetric : ∀ s : ℝ,
      HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (s + b))
        (L.toHistory.stageMetric (Fin.last L.eventCount) s))
    {ε C1 C2 C1s C2s qcan qs τmin : ℝ} {Ctime Cgrad : ℝ≥0}
    (hEst : NativeEstimates Kplus ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad)
    (T : Icc (0 : ℝ) J.horizon) (hbuffer : (T : ℝ) < J.horizon)
    (t : Icc (0 : ℝ) (J.restrict T).horizon) (hbt : b < (t : ℝ)) :
    let s : Icc (0 : ℝ) L.horizon :=
      ⟨(t : ℝ) - b, sub_nonneg.mpr hbt.le, by
        have htJ : (t : ℝ) ≤ J.horizon := t.property.2.trans T.property.2
        rw [hJhor] at htJ
        linarith⟩
    let tK := AK.shiftTime hKhor s
    Kplus.time (Kplus.toHistory.activeStage tK) < (tK : ℝ) →
    ∀ x : ((J.restrict T).toHistory.stageAt t).Carrier,
      qs < metricScalarAt
        ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t) x →
      ∃ W : SpatialCanonicalWitness
        ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t)
        ε C1s C2s x, W.capTubeHasNeckChart ε := by
  dsimp only
  let s : Icc (0 : ℝ) L.horizon :=
    ⟨(t : ℝ) - b, sub_nonneg.mpr hbt.le, by
      have htJ : (t : ℝ) ≤ J.horizon := t.property.2.trans T.property.2
      rw [hJhor] at htJ
      linarith⟩
  let tK := AK.shiftTime hKhor s
  let tJ : Icc (0 : ℝ) J.horizon :=
    ⟨(t : ℝ), t.property.1, t.property.2.trans T.property.2⟩
  have hshiftJ : AJ.shiftTime hJhor s = tJ := by
    apply Subtype.ext
    change (t : ℝ) - b + b = (t : ℝ)
    exact sub_add_cancel _ _
  have htopK : (tK : ℝ) < Kplus.horizon := by
    have htT : (t : ℝ) ≤ (T : ℝ) := t.property.2
    have htJ : (t : ℝ) < J.horizon := htT.trans_lt hbuffer
    rw [hJhor] at htJ
    have h2 : (tK : ℝ) < L.horizon + a := by
      change (t : ℝ) - b + a < L.horizon + a
      linarith
    exact h2.trans_eq hKhor.symm
  have hstageJK : J.toHistory.stageAt tJ = Kplus.toHistory.stageAt tK := by
    have hJ := AJ.stageAt_shift_eq hJhor s
    rw [hshiftJ] at hJ
    exact hJ.trans (AK.stageAt_shift_eq hKhor s).symm
  have hmetricJK :
      HEq (J.toHistory.stageMetric (J.toHistory.activeStage tJ) tJ)
        (Kplus.toHistory.stageMetric (Kplus.toHistory.activeStage tK) tK) := by
    have hJ := AJ.sliceMetric_shift_heq hJhor hJmetric s
    rw [hshiftJ] at hJ
    exact hJ.trans (AK.sliceMetric_shift_heq hKhor hKmetric s).symm
  have hstageOJ : (J.restrict T).toHistory.stageAt t = J.toHistory.stageAt tJ :=
    J.toHistory.restrict_stageAt T t
  have hmetricOJ :
      HEq ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t)
        (J.toHistory.stageMetric (J.toHistory.activeStage tJ) tJ) :=
    J.toHistory.restrict_sliceMetric T t
  intro hbirth x hx
  let xJ := overlapCastPoint hstageOJ x
  let xK := overlapCastPoint hstageJK xJ
  have hxOJ : HEq x xJ := (overlapCastPoint_heq hstageOJ x).symm
  have hxJK : HEq xJ xK := (overlapCastPoint_heq hstageJK xJ).symm
  have hscalarOJ := overlap_scalar_eq hstageOJ hmetricOJ hxOJ
  have hscalarJK := overlap_scalar_eq hstageJK hmetricJK hxJK
  have hxK : qs < metricScalarAt
      (Kplus.toHistory.stageMetric (Kplus.toHistory.activeStage tK) tK) xK := by
    rw [← hscalarJK, ← hscalarOJ]
    exact hx
  obtain ⟨WK, hWK⟩ :=
    hEst.exists_spatialCanonicalWitness_of_strict_birth tK htopK hbirth xK hxK
  obtain ⟨WJ, hWJ, _⟩ := overlap_spatialWitness_transport
    hstageJK.symm hmetricJK.symm hxJK.symm WK hWK
  obtain ⟨WO, hWO, _⟩ := overlap_spatialWitness_transport
    hstageOJ.symm hmetricOJ.symm hxOJ.symm WJ hWJ
  exact ⟨WO, hWO⟩


/-- A concrete ready-class continuation: one fine native L, its original
old-native join, and one attachment of the SAME L to the full history. It
retains actual class certificates and records for the analytic receivers. -/
private theorem exists_ready_two_overlap_geometric_extension_with_native_certificate
    (certificate : RetainedCoreHistory.{u} → Prop)
    (fixed : StaticCapScaffold) (recenter ε : ℝ) (hε : 0 < ε)
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
    (pOld : CutoffParameters) (δOld ρOld B εOld κClass κOld : ℝ)
    (pK : CutoffParameters)
    (recordsK : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pK)
    (hclassK : K.IsCanonicalCutoffRecordFamily pOld δOld ρOld recordsK)
    (hfixedOld : pOld.fixed = fixed) (hrcOld : pOld.recenterConstant = recenter)
    (hcontrolK : HistoryEventControl K)
    (oldExtension : PreparedGeometricObservationExtensionWithNative certificate PK gK B εOld κClass pOld δOld ρOld)
    (oldNoncollapse : ∀ (V : RetainedCoreHistory.{u})
      (_IV : InitialIdentification PK gK V.toHistory) (pV : CutoffParameters)
      (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
      V.horizon ≤ B → V.IsCanonicalCutoffRecordFamily pOld δOld ρOld records →
      V.NoncollapsedBefore κOld ε V.horizon)
    (c : ℝ) (offset : ℕ)
    (Aold : AffineEventPrefix K H c offset (Fin.last K.eventCount))
    (hHhor : H.horizon = K.horizon + c) (hKB : K.horizon < B)
    (Bfuture : ℝ) (hBfuture : B < Bfuture)
    (pNew : CutoffParameters) (δNew ρNew κNew r : ℝ)
    (hfixedNew : pNew.fixed = fixed) (hrcNew : pNew.recenterConstant = recenter)
    (hδNew : 0 < δNew) (hρNew : 0 < ρNew) (hκNew : 0 < κNew) (hr : 0 < r)
    (hcapNew : StandardCap.transitionEnd < pNew.modelRadius + 1)
    (newNoncollapse : ∀ (V : RetainedCoreHistory.{u})
      (_IV : InitialIdentification (K.stage (Fin.last K.eventCount))
        (K.initialMetric (Fin.last K.eventCount)) V.toHistory)
      (pV : CutoffParameters)
      (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
      V.horizon ≤ Bfuture - K.time (Fin.last K.eventCount) →
      V.IsCanonicalCutoffRecordFamily pNew δNew ρNew records →
      V.NoncollapsedBefore κNew ε V.horizon) :
    ∃ κJ : ℝ, 0 < κJ ∧
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
              (AK.shiftTime hKhor t))) := by
  classical
  let a := K.time (Fin.last K.eventCount)
  let b := H.time (Fin.last H.eventCount)
  have hb : b = a + c := by
    simpa only [AffineEventPrefix.stageIndex_last] using Aold.stageIndex_time (Fin.last K.eventCount)
  have hstage : H.stage (Fin.last H.eventCount) = K.stage (Fin.last K.eventCount) := by
    simpa only [AffineEventPrefix.stageIndex_last] using Aold.stageIndex_stage (Fin.last K.eventCount)
  have hinit : HEq (H.initialMetric (Fin.last H.eventCount))
      (K.initialMetric (Fin.last K.eventCount)) := by
    have hi := Aold.initialMetric_heq (Fin.last K.eventCount)
    change HEq (H.initialMetric (Aold.stageIndex (Fin.last K.eventCount)))
      (K.initialMetric (Fin.last K.eventCount)) at hi
    rw [Aold.stageIndex_last] at hi
    exact hi
  obtain ⟨κJ, hκJ, joinNC⟩ := exists_noncollapsed_affine_join
    (K.stage (Fin.last K.eventCount)) (K.initialMetric (Fin.last K.eventCount))
    hε hε hκH hκNew
  refine ⟨κJ, hκJ, ?_⟩
  intro δcut ρcut εcut Dcut mcut hδcut hρcut hεcut hDcut
  obtain ⟨εL, κL, κKplus, _, _, _, _, make⟩ :=
    oldExtension K IK pK recordsK hKB hclassK hcontrolK
  obtain ⟨L, IL, pB, pF, δbound, ρbound, v, native,
    hLB, hIL, hcertificateL, hcontrolL, hncLlocal, hfixedF, hrcF, hacc, hrad, hord,
    hδbound, hδ, hρbound, hρ, hrecF, hv, hfamily, hdebit,
    hwin, hrecK, hDK, hmK, haccK, joinK⟩ :=
    make (min δNew δcut) (min ρNew (min r ρcut))
      (min pH.modelAccuracy (min pNew.modelAccuracy εcut))
      (max pH.modelRadius (max pNew.modelRadius Dcut))
      (max pH.modelOrder (max pNew.modelOrder mcut))
      (lt_min hδNew hδcut) (lt_min hρNew (lt_min hr hρcut))
      (lt_min pH.modelAccuracy_pos (lt_min pNew.modelAccuracy_pos hεcut))
      (lt_max_of_lt_left pH.modelRadius_pos)
  have hDH : pH.modelRadius ≤ pF.modelRadius := (le_max_left _ _).trans hrad
  have hmH : pH.modelOrder ≤ pF.modelOrder := (le_max_left _ _).trans hord
  have haccH : pF.modelAccuracy ≤ pH.modelAccuracy := hacc.trans (min_le_left _ _)
  have hDNew : pNew.modelRadius ≤ pF.modelRadius :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hrad)
  have hmNew : pNew.modelOrder ≤ pF.modelOrder :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hord)
  have haccNew : pF.modelAccuracy ≤ pNew.modelAccuracy :=
    hacc.trans ((min_le_right _ _).trans (min_le_left _ _))
  let pCK := pF.withModelWindow pK.modelRadius pK.modelOrder pK.modelAccuracy
    pK.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccK)
  let qK := pK.spliceAfter (translate_cutoff_parameters pCK a) K.horizon
  let pCH := pF.withModelWindow pH.modelRadius pH.modelOrder pH.modelAccuracy
    pH.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccH)
  let coarseH := fun i : Fin L.eventCount =>
    (native i).restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
        pH.modelRadius_pos hDH hmH haccH
  let qH := pH.spliceAfter (translate_cutoff_parameters pCH b) H.horizon
  let pReserve := pF.withModelWindow pNew.modelRadius pNew.modelOrder pNew.modelAccuracy
    pNew.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccNew)
  let reserved := fun i : Fin L.eventCount =>
    (native i).restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
        pNew.modelRadius_pos hDNew hmNew haccNew
  have hfixedFine : pF.fixed = fixed := hfixedF.trans (hclassK.1.trans hfixedOld)
  have hrcFine : pF.recenterConstant = recenter :=
    hrcF.trans (hclassK.2.2.2.2.1.trans hrcOld)
  have hclassNew : L.IsCanonicalCutoffRecordFamily pNew δNew ρNew reserved := by
    refine ⟨hfixedFine.trans hfixedNew.symm, rfl, rfl, rfl,
      hrcFine.trans hrcNew.symm, ?_, ?_, ?_⟩
    · intro i z
      exact (native i).hasCanonicalWindow_restrictModelWindow
          (fun b => (hwin i b).hasCanonicalWindow)
        pNew.modelRadius_pos hDNew hmNew haccNew hcapNew z
    · intro i
      exact (hfamily.2.2.2.2.2.2.1 i).trans (hδ.trans (min_le_left _ _))
    · intro i
      exact (hfamily.2.2.2.2.2.2.2 i).trans (hρ.trans (min_le_left _ _))
  have hLFuture : L.horizon ≤ Bfuture - a :=
    hLB.trans_le (sub_le_sub_right hBfuture.le a)
  have hncL := newNoncollapse L IL pReserve reserved hLFuture hclassNew
  obtain ⟨Kplus, AK, IoldK, hnK, joinedK, hpK, IKplus, hIKplus, hKplusB,
    hcontrolKplus, hncKplusLocal, hclassKplus, hncKplusClass, hstaticKplus,
    hfinalKplus, hpastK, hwinKplus, hOldK, hTailK⟩ := joinK
  have hncKplus := oldNoncollapse Kplus IKplus qK joinedK hKplusB.le hclassKplus
  have hKhor : Kplus.horizon = L.horizon + a := by rw [hKplusB, hLB]; ring
  have hsL : L.stage 0 = K.stage (Fin.last K.eventCount) := by
    simpa only [Fin.cast_zero, ObservedHistory.restrict_stage_zero]
      using hIL.1.presentation.stage_eq 0
  have hmL : HEq (L.initialMetric 0) (K.initialMetric (Fin.last K.eventCount)) := by
    simpa only [Fin.cast_zero, ObservedHistory.restrict_initialMetric_zero,
      ObservedHistory.restrict_stage_zero] using hIL.1.presentation.initialMetric_heq 0
  have hsum : L.horizon + b = B + c := by rw [hLB, hb]; ring
  have hreach : H.horizon ≤ L.horizon + b := by
    rw [hsum, hHhor]
    exact add_le_add hKB.le le_rfl
  have hstaticH : pCH.fixed = pH.fixed ∧ pCH.modelRadius = pH.modelRadius ∧
      pCH.modelOrder = pH.modelOrder ∧ pCH.modelAccuracy = pH.modelAccuracy ∧
      pCH.recenterConstant = pH.recenterConstant :=
    ⟨hfixedFine.trans hfixedH.symm, rfl, rfl, rfl, hrcFine.trans hrcH.symm⟩
  have hwinCoarseH : ∀ i z, ((coarseH i).static z).hasCanonicalWindow := by
    intro i z
    exact (native i).hasCanonicalWindow_restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
      pH.modelRadius_pos hDH hmH haccH hcapH z
  obtain ⟨J, AJ, IoldH, hnH, joinedH, hpH, hJhor, hcontrolJ,
    hfinalJ, hpastH, hwinJ, hOldH, hTailH⟩ :=
    finite_history_concatenation_with_cutoff_records_and_raw_prefix H L hcontrolH hcontrolL
      (hsL.trans hstage.symm) (hmL.trans hinit.symm) hreach
      recordsH coarseH hstaticH hwinH hwinCoarseH
  obtain ⟨IJ, hIJ⟩ := marking_of_actual_prefix IH hpH
  have hncJ := joinNC H L J IL b H.eventCount AJ (fun i => (hcontrolL i).1)
    hpH H.time_le_horizon hJhor hfinalJ hncH hncL
  refine ⟨L, IL, pF, native, hwin, hrecK, hDK, hmK, haccK, hDH, hmH, haccH,
    hDNew, hmNew, haccNew, Kplus, IKplus, AK, IoldK, joinedK,
    J, IJ, AJ, IoldH, joinedH, hKhor, hJhor, hIL,
    hLB, hKplusB, hJhor.trans hsum, hIKplus, hIJ, hcertificateL, hcontrolL, hcontrolKplus, hcontrolJ,
    hclassNew, hclassKplus, hncL, hncKplus, hncJ,
    hfixedFine, hrcFine,
    hacc.trans ((min_le_right _ _).trans (min_le_right _ _)),
    (le_max_right _ _).trans ((le_max_right _ _).trans hrad),
    (le_max_right _ _).trans ((le_max_right _ _).trans hord),
    ?_, hfinalKplus, hfinalJ, hpastK, hpastH, hwinJ, hOldK, hOldH, hTailK, hTailH, ?_⟩
  · intro i
    exact ⟨(hfamily.2.2.2.2.2.2.1 i).trans (hδ.trans (min_le_right _ _)),
      (hfamily.2.2.2.2.2.2.2 i).trans (hρ.trans (min_le_right _ _))⟩
  · intro t
    exact ⟨(AJ.stageAt_shift_eq hJhor t).trans (AK.stageAt_shift_eq hKhor t).symm,
      (AJ.sliceMetric_shift_heq hJhor hfinalJ t).trans
        (AK.sliceMetric_shift_heq hKhor hfinalKplus t).symm⟩

/-- Compatibility projection of the same generic native construction. -/
private theorem exists_ready_two_overlap_geometric_extension
    (fixed : StaticCapScaffold) (recenter ε : ℝ) (hε : 0 < ε)
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
    (pOld : CutoffParameters) (δOld ρOld B εOld κClass κOld : ℝ)
    (pK : CutoffParameters)
    (recordsK : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pK)
    (hclassK : K.IsCanonicalCutoffRecordFamily pOld δOld ρOld recordsK)
    (hfixedOld : pOld.fixed = fixed) (hrcOld : pOld.recenterConstant = recenter)
    (hcontrolK : HistoryEventControl K)
    (oldExtension : PreparedGeometricObservationExtension PK gK B εOld κClass pOld δOld ρOld)
    (oldNoncollapse : ∀ (V : RetainedCoreHistory.{u})
      (_IV : InitialIdentification PK gK V.toHistory) (pV : CutoffParameters)
      (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
      V.horizon ≤ B → V.IsCanonicalCutoffRecordFamily pOld δOld ρOld records →
      V.NoncollapsedBefore κOld ε V.horizon)
    (c : ℝ) (offset : ℕ)
    (Aold : AffineEventPrefix K H c offset (Fin.last K.eventCount))
    (hHhor : H.horizon = K.horizon + c) (hKB : K.horizon < B)
    (Bfuture : ℝ) (hBfuture : B < Bfuture)
    (pNew : CutoffParameters) (δNew ρNew κNew r : ℝ)
    (hfixedNew : pNew.fixed = fixed) (hrcNew : pNew.recenterConstant = recenter)
    (hδNew : 0 < δNew) (hρNew : 0 < ρNew) (hκNew : 0 < κNew) (hr : 0 < r)
    (hcapNew : StandardCap.transitionEnd < pNew.modelRadius + 1)
    (newNoncollapse : ∀ (V : RetainedCoreHistory.{u})
      (_IV : InitialIdentification (K.stage (Fin.last K.eventCount))
        (K.initialMetric (Fin.last K.eventCount)) V.toHistory)
      (pV : CutoffParameters)
      (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
      V.horizon ≤ Bfuture - K.time (Fin.last K.eventCount) →
      V.IsCanonicalCutoffRecordFamily pNew δNew ρNew records →
      V.NoncollapsedBefore κNew ε V.horizon) :
    ∃ κJ : ℝ, 0 < κJ ∧
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
              (AK.shiftTime hKhor t))) := by
  have nativeResult := @exists_ready_two_overlap_geometric_extension_with_native_certificate.{u}
    (fun _ => True) fixed recenter ε hε P g H IH pH recordsH hfixedH hrcH hcapH hcontrolH hwinH κH
    hκH hncH PK gK K IK pOld δOld ρOld B εOld κClass κOld pK recordsK hclassK hfixedOld hrcOld
    hcontrolK oldExtension.withTrue oldNoncollapse c offset Aold hHhor hKB Bfuture hBfuture pNew
    δNew ρNew κNew r hfixedNew hrcNew hδNew hρNew hκNew hr hcapNew newNoncollapse
  obtain ⟨κJ, nativeProjectionh1⟩ := nativeResult
  refine ⟨κJ, ?_⟩
  obtain ⟨nativeProjectionfield2, nativeProjectionh3⟩ := nativeProjectionh1
  refine ⟨nativeProjectionfield2, ?_⟩
  intro δcut ρcut εcut Dcut mcut nativeProjectionx4 nativeProjectionx5 nativeProjectionx6
    nativeProjectionx7
  have nativeProjectionh8 := @nativeProjectionh3 δcut ρcut εcut Dcut mcut nativeProjectionx4
    nativeProjectionx5 nativeProjectionx6 nativeProjectionx7
  obtain ⟨L, IL, pF, native, hwin, hrecK, hDK, hmK, haccK, hDH, hmH, haccH, hDNew, hmNew, haccNew,
    nativeProjectionh9⟩ := nativeProjectionh8
  refine ⟨L, IL, pF, native, hwin, hrecK, hDK, hmK, haccK, hDH, hmH, haccH, hDNew, hmNew, haccNew, ?_⟩
  dsimp only at nativeProjectionh9 ⊢
  obtain ⟨Kplus, IKplus, AK, IoldK, joinedK, J, IJ, AJ, IoldH, joinedH, hKhor, hJhor,
    nativeProjectionh10⟩ := nativeProjectionh9
  refine ⟨Kplus, IKplus, AK, IoldK, joinedK, J, IJ, AJ, IoldH, joinedH, hKhor, hJhor, ?_⟩
  obtain ⟨nativeProjectionfield11, nativeProjectionfield12, nativeProjectionfield13,
    nativeProjectionfield14, nativeProjectionfield15, nativeProjectionfield16, nativeProjectionh17⟩
    := nativeProjectionh10
  refine ⟨nativeProjectionfield11, nativeProjectionfield12, nativeProjectionfield13,
    nativeProjectionfield14, nativeProjectionfield15, nativeProjectionfield16, ?_⟩
  exact nativeProjectionh17.2

/-- The same native construction retaining the actual event distance certificate. -/
private theorem exists_ready_two_overlap_geometric_extension_with_distance_scalars
    (Cdist : ℝ≥0)
    (fixed : StaticCapScaffold) (recenter ε : ℝ) (hε : 0 < ε)
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
    (pOld : CutoffParameters) (δOld ρOld B εOld κClass κOld : ℝ)
    (pK : CutoffParameters)
    (recordsK : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pK)
    (hclassK : K.IsCanonicalCutoffRecordFamily pOld δOld ρOld recordsK)
    (hfixedOld : pOld.fixed = fixed) (hrcOld : pOld.recenterConstant = recenter)
    (hcontrolK : HistoryEventControl K)
    (oldExtension : PreparedGeometricObservationExtensionWithDistance Cdist PK gK B εOld κClass pOld δOld ρOld)
    (oldNoncollapse : ∀ (V : RetainedCoreHistory.{u})
      (_IV : InitialIdentification PK gK V.toHistory) (pV : CutoffParameters)
      (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
      V.horizon ≤ B → V.IsCanonicalCutoffRecordFamily pOld δOld ρOld records →
      V.NoncollapsedBefore κOld ε V.horizon)
    (c : ℝ) (offset : ℕ)
    (Aold : AffineEventPrefix K H c offset (Fin.last K.eventCount))
    (hHhor : H.horizon = K.horizon + c) (hKB : K.horizon < B)
    (Bfuture : ℝ) (hBfuture : B < Bfuture)
    (pNew : CutoffParameters) (δNew ρNew κNew r : ℝ)
    (hfixedNew : pNew.fixed = fixed) (hrcNew : pNew.recenterConstant = recenter)
    (hδNew : 0 < δNew) (hρNew : 0 < ρNew) (hκNew : 0 < κNew) (hr : 0 < r)
    (hcapNew : StandardCap.transitionEnd < pNew.modelRadius + 1)
    (newNoncollapse : ∀ (V : RetainedCoreHistory.{u})
      (_IV : InitialIdentification (K.stage (Fin.last K.eventCount))
        (K.initialMetric (Fin.last K.eventCount)) V.toHistory)
      (pV : CutoffParameters)
      (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
      V.horizon ≤ Bfuture - K.time (Fin.last K.eventCount) →
      V.IsCanonicalCutoffRecordFamily pNew δNew ρNew records →
      V.NoncollapsedBefore κNew ε V.horizon) :
    ∃ κJ : ℝ, 0 < κJ ∧
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
              (AK.shiftTime hKhor t))) := by
  exact @exists_ready_two_overlap_geometric_extension_with_native_certificate.{u} (fun K => ∀ i :
    Fin K.eventCount, (K.toHistory.event i).HasUniformDistanceScalar Cdist) fixed recenter ε hε P g
    H IH pH recordsH hfixedH hrcH hcapH hcontrolH hwinH κH hκH hncH PK gK K IK pOld δOld ρOld B εOld
    κClass κOld pK recordsK hclassK hfixedOld hrcOld hcontrolK oldExtension.toNative oldNoncollapse
    c offset Aold hHhor hKB Bfuture hBfuture pNew δNew ρNew κNew r hfixedNew hrcNew hδNew hρNew
    hκNew hr hcapNew newNoncollapse

/-- Extend the previous native class once, then attach its SAME fine tail to
the full history. The old analytic coefficient and thresholds are preserved;
the new class and full-history coefficient precede the fine request. -/
theorem exists_prepared_two_overlap_extension
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
        (R : ∀ i : Fin L.eventCount, GeometricCutoffRecord L.toHistory i pL),
        L.horizon ≤ B → L.IsCanonicalCutoffRecordFamily p₀ δb ρb R →
        L.NoncollapsedBefore κ ε L.horizon) ∧
      PreparedGeometricObservationExtension P g B ε κ p₀ δb ρb)
    (ε C1 C2 C1s C2s Cs τmin : ℝ) (Ctime Cgrad : ℝ≥0) (hε : 0 < ε)
    (analytic :
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
    ∃ (qcan qs δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
      0 < qcan ∧ qcan ≤ qs ∧ qs ≤ Cs * qcan ∧
      0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
    ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
      (p : CutoffParameters)
      (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i p),
      K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      K.NoncollapsedBefore κ ε K.horizon →
      (∀ j : Fin K.eventCount,
        (K.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan (K.time j.succ) ∧
        (K.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan (K.time j.succ) ∧
        (K.toHistory.event j).incoming.CanonicalBefore ε C1 C2 qcan τmin (K.time j.succ) ∧
        (K.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qs (K.time j.succ)) ∧
      ∀ hfinal : K.time (Fin.last K.eventCount) < K.horizon,
        let G := (K.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl
        G.DerivativeBoundBefore Ctime qcan K.horizon ∧
        G.GradientBoundBefore Cgrad qcan K.horizon ∧
        G.CanonicalBefore ε C1 C2 qcan τmin K.horizon ∧
        G.SpatiallyCanonicalBefore ε C1s C2s qs K.horizon)
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
    (pOld : CutoffParameters) (δOld ρOld B εOld κClass κOld qOld qsOld : ℝ)
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
      NativeEstimates V ε C1 C2 C1s C2s qOld qsOld τmin Ctime Cgrad)
    (c : ℝ) (offset : ℕ)
    (Aold : AffineEventPrefix K H c offset (Fin.last K.eventCount))
    (hHhor : H.horizon = K.horizon + c) (hKB : K.horizon < B)
    (Bfuture R : ℝ) (hBfuture : B < Bfuture) (hR : 0 < R) :
    ∃ (pNew : CutoffParameters) (δNew ρNew κNew qNew qsNew r εNew κNewClass κJ : ℝ),
      pNew.fixed = fixed ∧ pNew.recenterConstant = recenter ∧
      0 < δNew ∧ 0 < ρNew ∧ 0 < κNew ∧ 0 < qNew ∧ qNew ≤ qsNew ∧ qsNew ≤ Cs * qNew ∧
      0 < r ∧ r ≤ R ∧ qsNew ≤ (r ^ 2)⁻¹ ∧
      0 < εNew ∧ εNew < 1 / 11 ∧ 0 < κNewClass ∧ 0 < κJ ∧
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
        NativeEstimates V ε C1 C2 C1s C2s qNew qsNew τmin Ctime Cgrad) ∧
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
        NativeEstimates Kplus ε C1 C2 C1s C2s qOld qsOld τmin Ctime Cgrad ∧
        NativeEstimates L ε C1 C2 C1s C2s qNew qsNew τmin Ctime Cgrad ∧
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
        ∀ (T : Icc (0 : ℝ) J.horizon) (hbuffer : (T : ℝ) < J.horizon)
          (hHT : H.horizon < (T : ℝ)),
          let s : Icc (0 : ℝ) L.horizon :=
            ⟨(T : ℝ) - b, sub_nonneg.mpr (H.time_le_horizon.trans hHT.le), by
              linarith [T.property.2.trans_eq hJhor]⟩
          let tK := AK.shiftTime hKhor s
          let tObs : Icc (0 : ℝ) (J.restrict T).horizon :=
            ⟨(T : ℝ), T.property.1, le_rfl⟩
          Kplus.time (Kplus.toHistory.activeStage tK) < (tK : ℝ) →
          ∀ x : ((J.restrict T).toHistory.stageAt tObs).Carrier,
            qsOld < metricScalarAt
              ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage tObs)
                tObs) x →
            (IJ.restrict T).IsPrefixOf IJ ∧
            ∃ W : SpatialCanonicalWitness
              ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage tObs)
                tObs) ε C1s C2s x, W.capTubeHasNeckChart ε := by
  classical
  let a := K.time (Fin.last K.eventCount)
  have hfuture : 0 < Bfuture - a :=
    sub_pos.mpr (K.time_le_horizon.trans_lt (hKB.trans hBfuture))
  obtain ⟨εNew, κNewClass, hεNew, hεNew11, hκNewClass, prepareNew⟩ :=
    prepareClass (K.stage (Fin.last K.eventCount)) (K.initialMetric (Fin.last K.eventCount))
      (Bfuture - a) hfuture
  obtain ⟨κNew, hκNew, enlargeNew⟩ :=
    exists_noncollapsedBefore_radius_enlargement hκNewClass hεNew hε
  obtain ⟨qNew, qsNew, δAnal, ρAnal, εAnal, DAnal, mAnal,
    hqNew, hqsNew, hqsNewC, hδAnal, hρAnal, hεAnal, hDAnal, newAnalytic⟩ :=
    analytic (K.stage (Fin.last K.eventCount)) (K.initialMetric (Fin.last K.eventCount))
      (Bfuture - a) κNew hfuture hκNew
  obtain ⟨pNew, δNew, ρNew, hfixedNew, hrcNew, hδNew, hδNewAnal, hρNew, hρNewAnal,
    haccNewAnal, hDNewAnal, hmNewAnal, hcapNew, hrecNew, ncNewClass, extendNew⟩ :=
    prepareNew δAnal ρAnal εAnal DAnal mAnal hδAnal hρAnal hεAnal hDAnal
  have newControl : ∀ (V : RetainedCoreHistory.{u})
      (IV : InitialIdentification (K.stage (Fin.last K.eventCount))
        (K.initialMetric (Fin.last K.eventCount)) V.toHistory)
      (pV : CutoffParameters)
      (records : ∀ i : Fin V.eventCount, GeometricCutoffRecord V.toHistory i pV),
      V.horizon ≤ Bfuture - a → V.IsCanonicalCutoffRecordFamily pNew δNew ρNew records →
      V.NoncollapsedBefore κNew ε V.horizon ∧
      NativeEstimates V ε C1 C2 C1s C2s qNew qsNew τmin Ctime Cgrad := by
    intro V IV pV records hVB hclass
    have hn := enlargeNew V V.horizon (ncNewClass V IV pV records hVB hclass)
    exact ⟨hn, newAnalytic pNew δNew ρNew haccNewAnal hDNewAnal hmNewAnal
      hδNewAnal hρNewAnal hrecNew V IV pV records hVB hclass hn⟩
  obtain ⟨r, hr, hrR, hqsr⟩ := exists_canonical_radius_below hR (hqNew.trans_le hqsNew)
  obtain ⟨κJ, hκJ, makeGeometry⟩ :=
    exists_ready_two_overlap_geometric_extension fixed recenter ε hε
      P g H IH pH recordsH hfixedH hrcH hcapH hcontrolH hwinH κH hκH hncH
      PK gK K IK pOld δOld ρOld B εOld κClass κOld pK recordsK
      hclassK hfixedOld hrcOld hcontrolK oldExtension
      (fun V IV pV records hVB hclass => (oldControl V IV pV records hVB hclass).1)
      c offset Aold hHhor hKB Bfuture hBfuture pNew δNew ρNew κNew r
      hfixedNew hrcNew hδNew hρNew hκNew hr hcapNew
      (fun V IV pV records hVB hclass => (newControl V IV pV records hVB hclass).1)
  refine ⟨pNew, δNew, ρNew, κNew, qNew, qsNew, r, εNew, κNewClass, κJ,
    hfixedNew, hrcNew, hδNew, hρNew, hκNew, hqNew, hqsNew, hqsNewC, hr, hrR, hqsr,
    hεNew, hεNew11, hκNewClass, hκJ, extendNew, newControl, ?_⟩
  intro δcut ρcut εcut Dcut mcut hδcut hρcut hεcut hDcut
  obtain ⟨L, IL, pF, native, hwin, hrecK, hDK, hmK, haccK, hDH, hmH, haccH,
    hDNew, hmNew, haccNew, Kplus, IKplus, AK, IoldK, joinedK,
    J, IJ, AJ, IoldH, joinedH, hKhor, hJhor, hIL, hLB, hKplusB, hJB,
    hIKplus, hIJ, hcontrolL, hcontrolKplus, hcontrolJ, hclassNew, hclassKplus,
    hncL, hncKplus, hncJ, hfixedFine, hrcFine, haccFine, hradFine, horderFine,
    hfine, hfinalKplus, hfinalJ, hpastK, hpastH, hwinJ, hOldK, hOldH, hTailK, hTailH,
    hsame⟩ := makeGeometry δcut ρcut εcut Dcut mcut hδcut hρcut hεcut hDcut
  have hLFuture : L.horizon ≤ Bfuture - a :=
    hLB.trans_le (sub_le_sub_right hBfuture.le a)
  have hestL := (newControl L IL _ _ hLFuture hclassNew).2
  have hestKplus := (oldControl Kplus IKplus _ joinedK hKplusB.le hclassKplus).2
  refine ⟨L, IL, pF, native, hwin, hrecK, hDK, hmK, haccK, hDH, hmH, haccH,
    hDNew, hmNew, haccNew, Kplus, IKplus, AK, IoldK, joinedK,
    J, IJ, AJ, IoldH, joinedH, hKhor, hJhor, hIL, hLB, hKplusB, hJB,
    hIKplus, hIJ, hcontrolL, hcontrolKplus, hcontrolJ, hclassNew, hclassKplus,
    hncL, hncKplus, hncJ, hestKplus, hestL, hfixedFine, hrcFine,
    haccFine, hradFine, horderFine, hfine, hfinalKplus, hfinalJ,
    hpastK, hpastH, hwinJ, hOldK, hOldH, hTailK, hTailH, hsame, ?_⟩
  intro T hbuffer hHT
  dsimp only
  intro hbirth x hx
  refine ⟨IJ.restrict_isPrefixOf T, ?_⟩
  exact exists_spatialCanonicalWitness_on_buffered_same_tail_observation
    AK AJ hKhor hJhor hfinalKplus hfinalJ hestKplus T hbuffer
    ⟨(T : ℝ), T.property.1, le_rfl⟩ (H.time_le_horizon.trans_lt hHT) hbirth x hx


/-- The same physical query receives either the regular native estimate or
its paid nonzero-birth witness. The strict observation buffer permits the
closed observation endpoint; the strict tail seam makes a native birth
nonzero. Whole spatial witnesses and their neck charts are transported by
actual metric identities and enlarged to one common pair of constants. -/
theorem exists_spatialCanonicalWitness_on_buffered_same_tail_observation_with_birth
    {L Kplus J : RetainedCoreHistory.{u}} {a b : ℝ} {offsetK offsetJ : ℕ}
    (AK : AffineEventPrefix L Kplus a offsetK (Fin.last L.eventCount))
    (AJ : AffineEventPrefix L J b offsetJ (Fin.last L.eventCount))
    (hKhor : Kplus.horizon = L.horizon + a)
    (hJhor : J.horizon = L.horizon + b)
    (hKmetric : ∀ s : ℝ,
      HEq (Kplus.toHistory.stageMetric (Fin.last Kplus.eventCount) (s + a))
        (L.toHistory.stageMetric (Fin.last L.eventCount) s))
    (hJmetric : ∀ s : ℝ,
      HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (s + b))
        (L.toHistory.stageMetric (Fin.last L.eventCount) s))
    {ε C1 C2 C1s C2s qcan qs τmin Cbirth Qbirth : ℝ} {Ctime Cgrad : ℝ≥0}
    (hEst : NativeEstimates Kplus ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad)
    (hqsBirth : qs ≤ Qbirth)
    (hBirth : ∀ tK : Icc (0 : ℝ) Kplus.toHistory.horizon,
      (tK : ℝ) < Kplus.horizon →
      Kplus.time (Kplus.toHistory.activeStage tK) = (tK : ℝ) →
      Kplus.toHistory.activeStage tK ≠ 0 →
      ∀ y : (Kplus.toHistory.stageAt tK).Carrier,
        Qbirth < metricScalarAt
          (Kplus.initialMetric (Kplus.toHistory.activeStage tK)) y →
        ∃ W : SpatialCanonicalWitness
          (Kplus.initialMetric (Kplus.toHistory.activeStage tK))
          ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε)
    (T : Icc (0 : ℝ) J.horizon) (hbuffer : (T : ℝ) < J.horizon)
    (t : Icc (0 : ℝ) (J.restrict T).horizon) (hbt : b < (t : ℝ)) :
    ∀ x : ((J.restrict T).toHistory.stageAt t).Carrier,
      Qbirth < metricScalarAt
        ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t) x →
      ∃ W : SpatialCanonicalWitness
        ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t)
        ε (max C1s Cbirth) (max C2s (max Cbirth (Cgrad : ℝ))) x,
        W.capTubeHasNeckChart ε := by
  let s : Icc (0 : ℝ) L.horizon :=
    ⟨(t : ℝ) - b, sub_nonneg.mpr hbt.le, by
      have htJ : (t : ℝ) ≤ J.horizon := t.property.2.trans T.property.2
      rw [hJhor] at htJ
      linarith⟩
  let tK := AK.shiftTime hKhor s
  let tJ : Icc (0 : ℝ) J.horizon :=
    ⟨(t : ℝ), t.property.1, t.property.2.trans T.property.2⟩
  have hshiftJ : AJ.shiftTime hJhor s = tJ := by
    apply Subtype.ext
    change (t : ℝ) - b + b = (t : ℝ)
    exact sub_add_cancel _ _
  have htopK : (tK : ℝ) < Kplus.horizon := by
    have htT : (t : ℝ) ≤ (T : ℝ) := t.property.2
    have htJ : (t : ℝ) < J.horizon := htT.trans_lt hbuffer
    rw [hJhor] at htJ
    have h2 : (tK : ℝ) < L.horizon + a := by
      change (t : ℝ) - b + a < L.horizon + a
      linarith
    exact h2.trans_eq hKhor.symm
  have hstageJK : J.toHistory.stageAt tJ = Kplus.toHistory.stageAt tK := by
    have hJ := AJ.stageAt_shift_eq hJhor s
    rw [hshiftJ] at hJ
    exact hJ.trans (AK.stageAt_shift_eq hKhor s).symm
  have hmetricJK :
      HEq (J.toHistory.stageMetric (J.toHistory.activeStage tJ) tJ)
        (Kplus.toHistory.stageMetric (Kplus.toHistory.activeStage tK) tK) := by
    have hJ := AJ.sliceMetric_shift_heq hJhor hJmetric s
    rw [hshiftJ] at hJ
    exact hJ.trans (AK.sliceMetric_shift_heq hKhor hKmetric s).symm
  have hstageOJ : (J.restrict T).toHistory.stageAt t = J.toHistory.stageAt tJ :=
    J.toHistory.restrict_stageAt T t
  have hmetricOJ :
      HEq ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t)
        (J.toHistory.stageMetric (J.toHistory.activeStage tJ) tJ) :=
    J.toHistory.restrict_sliceMetric T t
  intro x hx
  let xJ := overlapCastPoint hstageOJ x
  let xK := overlapCastPoint hstageJK xJ
  have hxOJ : HEq x xJ := (overlapCastPoint_heq hstageOJ x).symm
  have hxJK : HEq xJ xK := (overlapCastPoint_heq hstageJK xJ).symm
  have hscalarOJ := overlap_scalar_eq hstageOJ hmetricOJ hxOJ
  have hscalarJK := overlap_scalar_eq hstageJK hmetricJK hxJK
  have hxK : Qbirth < metricScalarAt
      (Kplus.toHistory.stageMetric (Kplus.toHistory.activeStage tK) tK) xK := by
    rw [← hscalarJK, ← hscalarOJ]
    exact hx
  have hsource : ∃ WK : SpatialCanonicalWitness
      (Kplus.toHistory.stageMetric (Kplus.toHistory.activeStage tK) tK)
      ε (max C1s Cbirth) (max C2s (max Cbirth (Cgrad : ℝ))) xK,
      WK.capTubeHasNeckChart ε := by
    by_cases hbirth : Kplus.time (Kplus.toHistory.activeStage tK) = (tK : ℝ)
    · have hpositive : 0 < (tK : ℝ) := by
        change 0 < (t : ℝ) - b + a
        have ha := AK.shift_nonneg
        linarith
      have hne : Kplus.toHistory.activeStage tK ≠ 0 := by
        intro hz
        have hb := hbirth
        rw [hz, Kplus.time_zero] at hb
        linarith
      have hmetricBirth :
          Kplus.toHistory.stageMetric (Kplus.toHistory.activeStage tK) tK =
            Kplus.initialMetric (Kplus.toHistory.activeStage tK) := by
        rw [← hbirth]
        exact Kplus.toHistory.stageMetric_initial _
      have hxBirth : Qbirth < metricScalarAt
          (Kplus.initialMetric (Kplus.toHistory.activeStage tK)) xK := by
        rw [← hmetricBirth]
        exact hxK
      obtain ⟨WK, hWK⟩ := hBirth tK htopK hbirth hne xK hxBirth
      rw [hmetricBirth]
      exact ⟨WK.enlargeConstants (le_max_right _ _) (le_max_right _ _),
        hWK.enlarge_constants (le_max_right _ _) (le_max_right _ _)⟩
    · have hstrict : Kplus.time (Kplus.toHistory.activeStage tK) < (tK : ℝ) :=
        lt_of_le_of_ne (Kplus.toHistory.activeStage_time_le tK) hbirth
      obtain ⟨WK, hWK⟩ :=
        hEst.exists_spatialCanonicalWitness_of_strict_birth tK htopK hstrict xK
          (hqsBirth.trans_lt hxK)
      exact ⟨WK.enlargeConstants (le_max_left _ _) (le_max_left _ _),
        hWK.enlarge_constants (le_max_left _ _) (le_max_left _ _)⟩
  obtain ⟨WK, hWK⟩ := hsource
  obtain ⟨WJ, hWJ, _⟩ := overlap_spatialWitness_transport
    hstageJK.symm hmetricJK.symm hxJK.symm WK hWK
  obtain ⟨WO, hWO, _⟩ := overlap_spatialWitness_transport
    hstageOJ.symm hmetricOJ.symm hxOJ.symm WJ hWJ
  exact ⟨WO, hWO⟩


/-- The same physical query is controlled from the closed tail seam through
any strictly buffered observation endpoint. At a native stage-zero birth, the
retained bound from the actual original marked metric makes a Qall-high point
impossible. All other queries retain the same native or paid birth witness,
with its neck chart, through the actual affine and restriction metrics. -/
theorem exists_spatialCanonicalWitness_on_buffered_same_tail_observation_with_closed_seam
    {L Kplus J : RetainedCoreHistory.{u}} {a b : ℝ} {offsetK offsetJ : ℕ}
    (AK : AffineEventPrefix L Kplus a offsetK (Fin.last L.eventCount))
    (AJ : AffineEventPrefix L J b offsetJ (Fin.last L.eventCount))
    (hKhor : Kplus.horizon = L.horizon + a)
    (hJhor : J.horizon = L.horizon + b)
    (hKmetric : ∀ s : ℝ,
      HEq (Kplus.toHistory.stageMetric (Fin.last Kplus.eventCount) (s + a))
        (L.toHistory.stageMetric (Fin.last L.eventCount) s))
    (hJmetric : ∀ s : ℝ,
      HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (s + b))
        (L.toHistory.stageMetric (Fin.last L.eventCount) s))
    (PK : OrientedThreeStage.{u}) (gK : PK.Metric)
    (IKplus : InitialIdentification PK gK Kplus.toHistory)
    {ε C1 C2 C1s C2s qcan qs τmin Cbirth Qbirth Qzero Qall : ℝ} {Ctime Cgrad : ℝ≥0}
    (hEst : NativeEstimates Kplus ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad)
    (hqsBirth : qs ≤ Qbirth)
    (hBirth : ∀ tK : Icc (0 : ℝ) Kplus.toHistory.horizon,
      (tK : ℝ) < Kplus.horizon →
      Kplus.time (Kplus.toHistory.activeStage tK) = (tK : ℝ) →
      Kplus.toHistory.activeStage tK ≠ 0 →
      ∀ y : (Kplus.toHistory.stageAt tK).Carrier,
        Qbirth < metricScalarAt
          (Kplus.initialMetric (Kplus.toHistory.activeStage tK)) y →
        ∃ W : SpatialCanonicalWitness
          (Kplus.initialMetric (Kplus.toHistory.activeStage tK))
          ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε)
    (hZero : ∀ (V : ObservedHistory.{u}), InitialIdentification PK gK V →
      ∀ y : (V.stage 0).Carrier, metricScalarAt (V.initialMetric 0) y < Qzero)
    (hQall : Qall = max Qbirth Qzero)
    (T : Icc (0 : ℝ) J.horizon) (hbuffer : (T : ℝ) < J.horizon)
    (t : Icc (0 : ℝ) (J.restrict T).horizon) (hbt : b ≤ (t : ℝ)) :
    ∀ x : ((J.restrict T).toHistory.stageAt t).Carrier,
      Qall < metricScalarAt
        ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t) x →
      ∃ W : SpatialCanonicalWitness
        ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t)
        ε (max C1s Cbirth) (max C2s (max Cbirth (Cgrad : ℝ))) x,
        W.capTubeHasNeckChart ε := by
  let s : Icc (0 : ℝ) L.horizon :=
    ⟨(t : ℝ) - b, sub_nonneg.mpr hbt, by
      have htJ : (t : ℝ) ≤ J.horizon := t.property.2.trans T.property.2
      rw [hJhor] at htJ
      linarith⟩
  let tK := AK.shiftTime hKhor s
  let tJ : Icc (0 : ℝ) J.horizon :=
    ⟨(t : ℝ), t.property.1, t.property.2.trans T.property.2⟩
  have hshiftJ : AJ.shiftTime hJhor s = tJ := by
    apply Subtype.ext
    change (t : ℝ) - b + b = (t : ℝ)
    exact sub_add_cancel _ _
  have htopK : (tK : ℝ) < Kplus.horizon := by
    have htT : (t : ℝ) ≤ (T : ℝ) := t.property.2
    have htJ : (t : ℝ) < J.horizon := htT.trans_lt hbuffer
    rw [hJhor] at htJ
    have h2 : (tK : ℝ) < L.horizon + a := by
      change (t : ℝ) - b + a < L.horizon + a
      linarith
    exact h2.trans_eq hKhor.symm
  have hstageJK : J.toHistory.stageAt tJ = Kplus.toHistory.stageAt tK := by
    have hJ := AJ.stageAt_shift_eq hJhor s
    rw [hshiftJ] at hJ
    exact hJ.trans (AK.stageAt_shift_eq hKhor s).symm
  have hmetricJK :
      HEq (J.toHistory.stageMetric (J.toHistory.activeStage tJ) tJ)
        (Kplus.toHistory.stageMetric (Kplus.toHistory.activeStage tK) tK) := by
    have hJ := AJ.sliceMetric_shift_heq hJhor hJmetric s
    rw [hshiftJ] at hJ
    exact hJ.trans (AK.sliceMetric_shift_heq hKhor hKmetric s).symm
  have hstageOJ : (J.restrict T).toHistory.stageAt t = J.toHistory.stageAt tJ :=
    J.toHistory.restrict_stageAt T t
  have hmetricOJ :
      HEq ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t)
        (J.toHistory.stageMetric (J.toHistory.activeStage tJ) tJ) :=
    J.toHistory.restrict_sliceMetric T t
  intro x hx
  let xJ := overlapCastPoint hstageOJ x
  let xK := overlapCastPoint hstageJK xJ
  have hxOJ : HEq x xJ := (overlapCastPoint_heq hstageOJ x).symm
  have hxJK : HEq xJ xK := (overlapCastPoint_heq hstageJK xJ).symm
  have hscalarOJ := overlap_scalar_eq hstageOJ hmetricOJ hxOJ
  have hscalarJK := overlap_scalar_eq hstageJK hmetricJK hxJK
  have hxK : Qall < metricScalarAt
      (Kplus.toHistory.stageMetric (Kplus.toHistory.activeStage tK) tK) xK := by
    rw [← hscalarJK, ← hscalarOJ]
    exact hx
  have hBirthAll : Qbirth ≤ Qall := by
    rw [hQall]
    exact le_max_left _ _
  have hZeroAll : Qzero ≤ Qall := by
    rw [hQall]
    exact le_max_right _ _
  have hsource : ∃ WK : SpatialCanonicalWitness
      (Kplus.toHistory.stageMetric (Kplus.toHistory.activeStage tK) tK)
      ε (max C1s Cbirth) (max C2s (max Cbirth (Cgrad : ℝ))) xK,
      WK.capTubeHasNeckChart ε := by
    by_cases hbirth : Kplus.time (Kplus.toHistory.activeStage tK) = (tK : ℝ)
    · have hmetricBirth :
          Kplus.toHistory.stageMetric (Kplus.toHistory.activeStage tK) tK =
            Kplus.initialMetric (Kplus.toHistory.activeStage tK) := by
        rw [← hbirth]
        exact Kplus.toHistory.stageMetric_initial _
      have hxBirth : Qall < metricScalarAt
          (Kplus.initialMetric (Kplus.toHistory.activeStage tK)) xK := by
        rw [← hmetricBirth]
        exact hxK
      by_cases hz : Kplus.toHistory.activeStage tK = 0
      · have hzeroK : ∀ y : (Kplus.stage (Kplus.toHistory.activeStage tK)).Carrier,
            metricScalarAt (Kplus.initialMetric (Kplus.toHistory.activeStage tK)) y < Qzero := by
          rw [hz]
          exact hZero Kplus.toHistory IKplus
        have hsmall := hzeroK xK
        have hhigh := hZeroAll.trans_lt hxBirth
        exact (not_lt_of_ge hhigh.le hsmall).elim
      · obtain ⟨WK, hWK⟩ := hBirth tK htopK hbirth hz xK (hBirthAll.trans_lt hxBirth)
        rw [hmetricBirth]
        exact ⟨WK.enlargeConstants (le_max_right _ _) (le_max_right _ _),
          hWK.enlarge_constants (le_max_right _ _) (le_max_right _ _)⟩
    · have hstrict : Kplus.time (Kplus.toHistory.activeStage tK) < (tK : ℝ) :=
        lt_of_le_of_ne (Kplus.toHistory.activeStage_time_le tK) hbirth
      obtain ⟨WK, hWK⟩ :=
        hEst.exists_spatialCanonicalWitness_of_strict_birth tK htopK hstrict xK
          (hqsBirth.trans_lt (hBirthAll.trans_lt hxK))
      exact ⟨WK.enlargeConstants (le_max_left _ _) (le_max_left _ _),
        hWK.enlarge_constants (le_max_left _ _) (le_max_left _ _)⟩
  obtain ⟨WK, hWK⟩ := hsource
  obtain ⟨WJ, hWJ, _⟩ := overlap_spatialWitness_transport
    hstageJK.symm hmetricJK.symm hxJK.symm WK hWK
  obtain ⟨WO, hWO, _⟩ := overlap_spatialWitness_transport
    hstageOJ.symm hmetricOJ.symm hxOJ.symm WJ hWJ
  exact ⟨WO, hWO⟩

end GC.GeneralFlow
