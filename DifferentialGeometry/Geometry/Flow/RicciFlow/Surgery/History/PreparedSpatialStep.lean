import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialReserveQualityData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStepRetention
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordDelayedRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedOverlapClosedSeam
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LinkedWindowTransportC11SL
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.DeepJoinC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.RadialWindowTransportC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffAccuracyGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialDistanceData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.AffineEventDistanceScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongStepC11SG

/-!
# S-CH11-FIX11 patched-at-path `PreparedSpatialStep`

来源：donor `PreparedSpatialStep.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败；下游模块对本路径 `open private … from`，
所以修补文本就放在原路径（patched-at-path）。只有 elaboration 层面修补
（no statement / definition / proof idea altered；不加 `set_option`）：
* `open private affine_future_neckRadius_budget from …CutoffRecordCanonicalRadius` → 指向
  `CutoffRecordCanonicalRadiusPortC11P`（原路径已是 port + shim，private 名住在 PortC11P）；
* 4 个陈述里 `PreparedDistanceClassProvider pBase.fixed …` → `PreparedDistanceClassProvider.{u}`
  （universe 被自动成 `u_1`，与 `.{u}` 的证明体 / `toNative` application mismatch ×4）；
* 主证明里 2 处 structure instance `{ q0 with delta := …,` / `{ qDelta with neckRadius := …,`
  首字段与 `with` 同行、续行缩进更浅，本树 parser 报 "unexpected identifier; expected '}'"
  → 首字段换行并与续行对齐（`qDelta` / `pFinal` 三处）；
* `exists_prescribed_accuracy_records_at_join` 的实参 `by simpa only [L.horizon_eq] using hdOld`
  （目标里是 `let` 变量 `H.horizon`，simp 看不见 `L.horizon_eq : L.history.horizon = E` 的 LHS）→
  `have h : H.horizon = E := L.horizon_eq; rw [h]; exact hdOld`；
* 10 处陈述 binder `I` / `IL` 不被引用 → `_I` / `_IL`（unusedVariables）；
* 10 处孤立 `·`（单独成行）与下一行合并（`linter.style.cdot`）。
-/

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal

namespace GC.GeneralFlow

open private exists_prepared_two_overlap_extension_with_closed_seam_with_native_certificate_with_reserve_quality from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedOverlapClosedSeam
universe u

open private overlapCastPoint from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SpatialWitnessTransport
open private overlapCastPoint_heq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SpatialWitnessTransport
open private overlap_scalar_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SpatialWitnessTransport
open private overlap_spatialWitness_transport from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SpatialWitnessTransport
open private affine_future_neckRadius_budget from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordCanonicalRadiusPortC11P

/-- One actual prepared successor. Its native class and radius are fixed before
all fine accuracy requests. Full records are relabelled first in accuracy and
then in radius, while the actual native reserved class remains unchanged.
Physical canonical control uses the old marked prefix below E and the buffered
closed-seam receiver from E onward. -/
private theorem exists_prepared_spatial_step_with_quality_and_native_certificate_and_small_test_margin_with_reserve_quality
    (Dstar εReserve : ℝ) (hDstar : 0 < Dstar) (hεReserve : 0 < εReserve)
    (certificate : RetainedCoreHistory.{u} → Prop)
    (joinCertificate :
      ∀ {H K J : RetainedCoreHistory.{u}} {c : ℝ},
        H.toHistory.IsPrefixOf J.toHistory →
        AffineEventPrefix K J c H.eventCount (Fin.last K.eventCount) →
        certificate H → certificate K → certificate J)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (cMax : ℝ) (hcMax : 0 < cMax)
    (prepareClass : PreparedClassProviderWithNative certificate pBase.fixed pBase.recenterConstant)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ C.Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ C.epsilon K.horizon →
        NativeEstimates K C.epsilon C.C1 C.C2 C.C1s C.C2s qcan qs C.tauMin C.Ctime C.Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y, W.capTubeHasNeckChart C.epsilon)
    {P : OrientedThreeStage.{u}} {g : P.Metric} {E B Bnext activation eta : ℝ}
    (L : PreparedSpatialState pBase C P g E B)
    (hFull : certificate L.history) (hNative : certificate L.native)
    (hExtension : PreparedGeometricObservationExtensionWithNative certificate
      L.nativeStage L.nativeMetric (B - L.shift)
      L.prepared.epsilonClass L.prepared.kappaClass
      L.prepared.parameters L.prepared.deltaBound L.prepared.radiusBound)
    (hBBnext : B < Bnext)
    (hEactivation : E ≤ activation) (hactivationB : activation < B) (heta : 0 < eta) :
    let b := L.history.time (Fin.last L.history.eventCount)
    let Pnext := L.native.stage (Fin.last L.native.eventCount)
    let gnext := L.native.initialMetric (Fin.last L.native.eventCount)
    ∃ (nextClass : ClosedBirthPreparedClass pBase C Pnext gnext (Bnext - b)) (rNext : ℝ),
      nextClass.HasReserveQuality Dstar εReserve ∧
      PreparedGeometricObservationExtensionWithNative certificate Pnext gnext (Bnext - b)
        nextClass.epsilonClass nextClass.kappaClass nextClass.parameters
        nextClass.deltaBound nextClass.radiusBound ∧
      0 < rNext ∧ rNext ≤ L.radius ∧ nextClass.Qall ≤ (rNext ^ 2)⁻¹ ∧
      rNext * Real.sqrt nextClass.Qall ≤ 100 * cMax ∧
      ∀ (εcut Dcut : ℝ) (mcut : ℕ), 0 < εcut → 0 < Dcut →
      (∀ d : ℝ, 0 < d → d < 1 → d ≤ L.parameters.delta E →
        ∃ R : PreparedSpatialState pBase C P g B Bnext,
          R.radius = rNext ∧ R.shift = b ∧ R.offset = L.history.eventCount ∧
          R.nativeStage = Pnext ∧ HEq R.nativeMetric gnext ∧
          HEq R.prepared nextClass ∧ (certificate R.history ∧ certificate R.native ∧
            PreparedGeometricObservationExtensionWithNative certificate
              R.nativeStage R.nativeMetric (Bnext - R.shift)
              R.prepared.epsilonClass R.prepared.kappaClass
              R.prepared.parameters R.prepared.deltaBound R.prepared.radiusBound) ∧
          PreparedSpatialSuccessor L R activation eta d ∧
          Nonempty (PreparedSpatialStepRetention L R d eta εcut Dcut mcut)) ∧
      ∀ accuracyCap : ℝ, 0 < accuracyCap →
        ∃ d : ℝ, 0 < d ∧ d < 1 ∧ d ≤ L.parameters.delta E ∧ d ≤ accuracyCap ∧
        ∃ R : PreparedSpatialState pBase C P g B Bnext,
          R.radius = rNext ∧ R.shift = b ∧ R.offset = L.history.eventCount ∧
          R.nativeStage = Pnext ∧ HEq R.nativeMetric gnext ∧
          HEq R.prepared nextClass ∧ (certificate R.history ∧ certificate R.native ∧
            PreparedGeometricObservationExtensionWithNative certificate
              R.nativeStage R.nativeMetric (Bnext - R.shift)
              R.prepared.epsilonClass R.prepared.kappaClass
              R.prepared.parameters R.prepared.deltaBound R.prepared.radiusBound) ∧
          PreparedSpatialSuccessor L R activation eta d ∧
          Nonempty (PreparedSpatialStepRetention L R d eta εcut Dcut mcut) := by
  classical
  dsimp only
  let H := L.history
  let K := L.native
  let c := L.shift
  let a := K.time (Fin.last K.eventCount)
  let b := H.time (Fin.last H.eventCount)
  have hE : 0 ≤ E := L.horizon_eq ▸ H.horizon_nonneg
  have hEB : E < B := hEactivation.trans_lt hactivationB
  have hba : b = a + c := by
    have h := L.affine.stageIndex_time (Fin.last K.eventCount)
    rw [L.affine.stageIndex_last] at h
    exact h
  have hcapacity : (Bnext - c) - a = Bnext - b := by rw [hba]; ring
  have hcE : c ≤ E := by
    have h1 := L.horizon_affine
    have h2 := K.horizon_nonneg
    have h3 := L.horizon_eq
    change H.horizon = K.horizon + c at h1
    linarith
  have hstr : 1 ≤ C.C1 ∧ 1 ≤ C.C2 ∧ 1 ≤ C.C1s ∧ 1 ≤ C.C2s ∧ 0 < C.tauMin ∧
      C.epsilon ≤ εStrong_C12X.{u} :=
    ⟨C.C1_ge_one, C.C2_ge_one, C.C1s_ge_one, C.C2s_ge_one, C.tauMin_pos,
      L.prepared.epsilon_strong⟩
  obtain ⟨pNew, δNew, ρNew, εNew, κNewClass, κNew, qNew, qsNew,
    QzeroNew, QbirthNew, QallNew, rSupply, κJ,
    hDReserve, hAccuracyReserve, hOrderReserve, hRadiusReserve, hStrongNew, hfixedNew, hrcNew,
    hδNew, hρNew, hεNew, hεNew11, hκNewClass, hκNew, hqNew, hqsNew, hqsNewC,
    hQzeroNew, hQbirthNew, hQallNew, hQallNewPos, hrSupply, hrSupplyOld, _hQallSupply, hκJ,
    hcapNew, hrecNew, zeroNew, newExtension, newControl, make⟩ :=
    exists_prepared_two_overlap_extension_with_closed_seam_with_native_certificate_with_reserve_quality
      Dstar εReserve hDstar hεReserve certificate pBase.fixed pBase.recenterConstant
      prepareClass C.epsilon C.C1 C.C2 C.C1s C.C2s C.Cs C.tauMin C.Cbirth
      C.Ctime C.Cgrad C.epsilon_pos hstr analytic
      P g H L.initial L.parameters L.records L.static_eq.1 L.static_eq.2.2.2.2
      L.modelRadius_bound L.eventControl L.windows L.kappa L.kappa_pos L.noncollapsed
      L.nativeStage L.nativeMetric K L.nativeInitial L.prepared.parameters
      L.prepared.deltaBound L.prepared.radiusBound (B - c) L.prepared.epsilonClass
      L.prepared.kappaClass L.prepared.kappa L.prepared.qcan L.prepared.qs
      L.prepared.Qbirth L.prepared.Qzero L.prepared.Qall L.prepared.Qbirth_ge
      L.nativeParameters L.nativeRecords L.nativeClass L.prepared.fixed_eq
      L.prepared.recenter_eq L.nativeEventControl hExtension L.prepared.control
      L.prepared.zero_bound L.prepared.Qall_eq c L.offset L.affine L.horizon_affine
      L.native_lt_capacity (Bnext - c) L.radius (sub_lt_sub_right hBBnext c) L.radius_pos
  obtain ⟨C1h, C2h, qh, hC1h, hC2h, hC1hb, hC2hb, hqh, hStrongV⟩ := hStrongNew
  let nextClass : ClosedBirthPreparedClass pBase C (K.stage (Fin.last K.eventCount))
      (K.initialMetric (Fin.last K.eventCount)) (Bnext - b) := {
    parameters := pNew
    deltaBound := δNew
    radiusBound := ρNew
    epsilonClass := εNew
    kappaClass := κNewClass
    kappa := κNew
    qcan := qNew
    qs := qsNew
    Qzero := QzeroNew
    Qbirth := QbirthNew
    Qall := QallNew
    fixed_eq := hfixedNew
    recenter_eq := hrcNew
    deltaBound_pos := hδNew
    radiusBound_pos := hρNew
    epsilonClass_pos := hεNew
    epsilonClass_small := hεNew11
    kappaClass_pos := hκNewClass
    kappa_pos := hκNew
    qcan_pos := hqNew
    qcan_le_qs := hqsNew
    qs_le := hqsNewC
    Qzero_pos := hQzeroNew
    Qbirth_ge := hQbirthNew
    Qall_eq := hQallNew
    Qall_pos := hQallNewPos
    modelRadius_bound := hcapNew
    recenter_bound := hrecNew
    zero_bound := zeroNew
    extension := by
      rw [← hcapacity]
      exact newExtension.forget
    control := by
      intro V IV pV records hVB hclass
      exact newControl V IV pV records (hVB.trans_eq hcapacity.symm) hclass
    epsilon_strong := L.prepared.epsilon_strong
    C1strong := C1h
    C2strong := C2h
    qStrong := qh
    C1strong_ge_one := hC1h
    C2strong_ge_one := hC2h
    C1strong_le := hC1hb
    C2strong_le := hC2hb
    qs_le_qStrong := hqh
    strongControl := by
      intro V IV pV records hVB hclass
      exact hStrongV V IV pV records (hVB.trans_eq hcapacity.symm) hclass }
  have hReserve : nextClass.HasReserveQuality Dstar εReserve :=
    ⟨hDReserve, hAccuracyReserve, hOrderReserve, hRadiusReserve⟩
  have hNextExtension : PreparedGeometricObservationExtensionWithNative certificate
      (K.stage (Fin.last K.eventCount)) (K.initialMetric (Fin.last K.eventCount)) (Bnext - b)
      nextClass.epsilonClass nextClass.kappaClass nextClass.parameters
      nextClass.deltaBound nextClass.radiusBound := by
    dsimp only [nextClass]
    rw [← hcapacity]
    exact newExtension
  have hsqrt : 0 < Real.sqrt nextClass.Qall := Real.sqrt_pos.2 nextClass.Qall_pos
  obtain ⟨rNext, hrNext, hrNextR, hqrNext⟩ := exists_canonical_radius_below
    (R := min rSupply (100 * cMax / Real.sqrt nextClass.Qall))
    (lt_min hrSupply (div_pos (by positivity) hsqrt))
    (lt_max_of_lt_left nextClass.Qall_pos : 0 < max nextClass.Qall nextClass.qStrong)
  have hrSupplyBound : rNext ≤ rSupply := hrNextR.trans (min_le_left _ _)
  have hrNextOld : rNext ≤ L.radius := hrSupplyBound.trans hrSupplyOld
  have hQallr : nextClass.Qall ≤ (rNext ^ 2)⁻¹ := (le_max_left _ _).trans hqrNext
  have hqStrongr : nextClass.qStrong ≤ (rNext ^ 2)⁻¹ := (le_max_right _ _).trans hqrNext
  have hFit : rNext * Real.sqrt nextClass.Qall ≤ 100 * cMax :=
    (le_div_iff₀ hsqrt).mp (hrNextR.trans (min_le_right _ _))
  refine ⟨nextClass, rNext, hReserve, hNextExtension, hrNext, hrNextOld, hQallr, hFit, ?_⟩
  intro εcut Dcut mcut hεcut hDcut
  have makeState : ∀ d : ℝ, 0 < d → d < 1 → d ≤ L.parameters.delta E →
      ∃ R : PreparedSpatialState pBase C P g B Bnext,
        R.radius = rNext ∧ R.shift = b ∧ R.offset = H.eventCount ∧
        R.nativeStage = K.stage (Fin.last K.eventCount) ∧
        HEq R.nativeMetric (K.initialMetric (Fin.last K.eventCount)) ∧
        HEq R.prepared nextClass ∧ (certificate R.history ∧ certificate R.native ∧
          PreparedGeometricObservationExtensionWithNative certificate
            R.nativeStage R.nativeMetric (Bnext - R.shift)
            R.prepared.epsilonClass R.prepared.kappaClass
            R.prepared.parameters R.prepared.deltaBound R.prepared.radiusBound) ∧
        PreparedSpatialSuccessor L R activation eta d ∧
        Nonempty (PreparedSpatialStepRetention L R d eta εcut Dcut mcut) := by
    intro d hd hdone hdOld
    obtain ⟨N, IN, pF, native, hwin, hrecK, hDK, hmK, haccK, hDH, hmH, haccH,
      hDNew, hmNew, haccNew, Kplus, IKplus, AK, IoldK, joinedK,
      J, IJ, AJ, IoldH, joinedH, hKhor, hJhor, hIN, hNB, hKplusB, hJB,
      hIKplus, hIJ, hCertificateN, hcontrolN, hcontrolKplus, hcontrolJ, hclassNew, hclassKplus,
      hncN, hncKplus, hncJ, hfixedFine, hrcFine, haccFine, hradFine, horderFine,
      hfineSupply, hfinalKplus, hfinalJ, hpastK, hpastH, hwinJ,
      hOldK, hOldH, hTailK, hTailH, hsame, hestKplus, hbirthKplus, hestN, hbirthN,
      closed, _⟩ :=
      make d (min rNext (eta * rNext)) εcut Dcut mcut
        hd (lt_min hrNext (mul_pos heta hrNext)) hεcut hDcut
    have hfine : ∀ i : Fin N.eventCount,
        pF.delta (N.time i.succ) ≤ d ∧
          pF.neckRadius (N.time i.succ) ≤ min rNext (eta * rNext) := by
      intro i
      exact ⟨(hfineSupply i).1, (hfineSupply i).2.trans (min_le_right _ _)⟩
    have hJoinedCertificates : certificate Kplus ∧ certificate J :=
      ⟨joinCertificate hIKplus.1 AK hNative hCertificateN,
        joinCertificate hIJ.1 AJ hFull hCertificateN⟩
    have hJB' : J.horizon = B := by simpa only [sub_add_cancel] using hJB
    have hNB' : N.horizon = B - b := by
      have h := hNB
      change N.horizon = (B - c) - a at h
      rw [h, hba]
      ring
    let pCH := pF.withModelWindow L.parameters.modelRadius L.parameters.modelOrder
      L.parameters.modelAccuracy L.parameters.modelRadius_pos
      (pF.modelAccuracy_pos.trans_le haccH)
    let q0 := L.parameters.spliceAfter (translate_cutoff_parameters pCH b) H.horizon
    let qDelta := q0.spliceAfter { q0 with
      delta := fun _ => d,
      delta_pos := fun _ _ => hd, delta_lt_one := fun _ _ => hdone } H.horizon
    have hdeltaFine : ∀ i : Fin N.eventCount, pCH.delta (N.time i.succ) ≤ d :=
      fun i => (hfine i).1
    have hradiusFine : ∀ i : Fin N.eventCount,
        pCH.neckRadius (N.time i.succ) ≤ rNext :=
      fun i => (hfine i).2.trans (min_le_left _ _)
    have hradiusEta : ∀ i : Fin N.eventCount,
        pCH.neckRadius (N.time i.succ) ≤ eta * rNext :=
      fun i => (hfine i).2.trans (min_le_right _ _)
    obtain ⟨hdeltaAnti, hDeltaNeck, hDeltaProtected, hDeltaPast, hDeltaAfter, accuracyRecords⟩ :=
      exists_prescribed_accuracy_records_at_join (H := H) AJ L.parameters pCH hd hdone
        (fun _ hs _ ht hst => L.delta_antitone hs.1 ht.1 hst)
        (by
          have h : H.horizon = E := L.horizon_eq
          rw [h]
          exact hdOld) hdeltaFine
    have hlinkCoarseH : ∀ i b, (((native i).restrictModelWindow
        (fun b => (hwin i b).hasCanonicalWindow) L.parameters.modelRadius_pos hDH hmH
          haccH).static b).hasLinkedCanonicalWindow_C12X :=
      fun i b => GeometricCutoffRecord.hasLinkedCanonicalWindow_restrictModelWindow_C11SL
        (native i) (fun b => (hwin i b).hasCanonicalWindow) (hwin i)
        L.parameters.modelRadius_pos hDH hmH haccH L.modelRadius_bound b
    have hlinkJoined : ∀ j b, ((joinedH j).static b).hasLinkedCanonicalWindow_C12X :=
      joined_static_linked_C11SL (pH := L.parameters) (pC := pCH) (q := q0) IoldH AJ
        ⟨rfl, rfl, rfl, rfl⟩
        ⟨L.static_eq.1.trans hfixedFine.symm, rfl, rfl, rfl⟩ L.records
        (fun i => (native i).restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
          L.parameters.modelRadius_pos hDH hmH haccH)
        joinedH (fun i => (hOldH i).2.2.2.2) (fun i => (hTailH i).2.2.2.2) L.linked
        hlinkCoarseH
    have hradJoined : RadialWindows_C12X J joinedH :=
      joined_static_radial_C12X (pH := L.parameters) (pC := pCH) (q := q0) IoldH AJ
        ⟨rfl, rfl, rfl, rfl⟩
        ⟨L.static_eq.1.trans hfixedFine.symm, rfl, rfl, rfl⟩ L.records
        (fun i => (native i).restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
          L.parameters.modelRadius_pos hDH hmH haccH)
        joinedH (fun i => (hOldH i).2.2.2.2) (fun i => (hTailH i).2.2.2.2) L.radial
        (radialWindows_restrictModelWindow_C12X native (fun i b => (hwin i b).hasCanonicalWindow)
          L.parameters.modelRadius_pos hDH hmH haccH hrecK.2)
    obtain ⟨recordsDelta, hrecordsDelta, hwindowsDelta⟩ := accuracyRecords joinedH hwinJ
    have hradDelta : RadialWindows_C12X J recordsDelta :=
      fun i => radial_of_record_static_heq_C12X (joinedH i) (recordsDelta i) rfl rfl rfl rfl
        (hrecordsDelta i).2.2.2.2.2 (hradJoined i)
    have hlinkDelta : ∀ i b, ((recordsDelta i).static b).hasLinkedCanonicalWindow_C12X :=
      fun i => linked_of_record_static_heq_C11SL (joinedH i) (recordsDelta i) rfl rfl rfl rfl
        (hrecordsDelta i).2.2.2.2.2 (hlinkJoined i)
    let pFinal := ({ qDelta with
      neckRadius := L.parameters.neckRadius,
      neckRadius_pos := L.parameters.neckRadius_pos }).spliceAfter
      { qDelta with
        neckRadius := fun _ => rNext,
        neckRadius_pos := fun _ _ => hrNext } activation
    obtain ⟨hradiusAnti, hFinalDelta, hFinalProtected, hFinalFixed, hFinalModelRadius,
      hFinalModelOrder, hFinalModelAccuracy, hFinalRecenter,
      hRadiusBefore, hRadiusAfter, hFinalPast, hRadiusBudget, radiusRecords⟩ :=
      exists_delayed_canonical_radius_records_at_join (H := H) AJ L.parameters pCH qDelta hDeltaNeck
        hrNext hrNextOld L.radius_antitone
        (fun t ht => L.radius_after t (L.horizon_eq.symm.trans_le ht))
        (L.horizon_eq.trans_le hEactivation) hradiusFine
    obtain ⟨recordsFinal, hrecordsFinal, hwindowsFinal⟩ :=
      radiusRecords recordsDelta hwindowsDelta
    have hlinkedFinal : ∀ i b, ((recordsFinal i).static b).hasLinkedCanonicalWindow_C12X :=
      fun i => linked_of_record_static_heq_C11SL (recordsDelta i) (recordsFinal i)
        hFinalFixed hFinalModelRadius hFinalModelOrder hFinalModelAccuracy
        (hrecordsFinal i).2.2.2.2.2 (hlinkDelta i)
    have hradFinal : RadialWindows_C12X J recordsFinal :=
      fun i => radial_of_record_static_heq_C12X (recordsDelta i) (recordsFinal i)
        hFinalFixed hFinalModelRadius hFinalModelOrder hFinalModelAccuracy
        (hrecordsFinal i).2.2.2.2.2 (hradDelta i)
    have hPast : ∀ t : ℝ, t ≤ E →
        pFinal.delta t = L.parameters.delta t ∧
        pFinal.neckRadius t = L.parameters.neckRadius t ∧
        pFinal.protectedRadius t = L.parameters.protectedRadius t := by
      intro t ht
      have htH : t ≤ H.horizon := ht.trans_eq L.horizon_eq.symm
      exact ⟨(hFinalPast t htH).1.trans (hDeltaPast t htH).1,
        (hFinalPast t htH).2.1.trans (hDeltaPast t htH).2.1,
        (hFinalPast t htH).2.2.trans (hDeltaPast t htH).2.2⟩
    have hDeltaFinal : ∀ t : ℝ, E < t → pFinal.delta t = d := by
      intro t ht
      exact (congrFun hFinalDelta t).trans
        (hDeltaAfter t (L.horizon_eq.trans_lt ht))
    have hRadiusBound : ∀ t : ℝ, E ≤ t → pFinal.neckRadius t ≤ L.radius := by
      intro t ht
      have h := hradiusAnti hE (hE.trans ht) ht
      rw [(hPast E le_rfl).2.1, L.radius_after E le_rfl] at h
      exact h
    have hcanonical : ∀ t : Icc (0 : ℝ) J.toHistory.horizon, (t : ℝ) < B →
        ∀ x : (J.toHistory.stageAt t).Carrier,
          (pFinal.neckRadius t ^ 2)⁻¹ < metricScalarAt
            (J.toHistory.stageMetric (J.toHistory.activeStage t) t) x →
          ∃ W : SpatialCanonicalWitness
            (J.toHistory.stageMetric (J.toHistory.activeStage t) t)
            C.epsilon (max C.C1s C.Cbirth) (max C.C2s (max C.Cbirth (C.Cgrad : ℝ))) x,
            W.capTubeHasNeckChart C.epsilon := by
      intro t htB x hx
      by_cases htE : (t : ℝ) < E
      · let tOld : Icc (0 : ℝ) H.horizon :=
          ⟨(t : ℝ), t.property.1, htE.le.trans_eq L.horizon_eq.symm⟩
        have hstage : H.toHistory.stageAt tOld = J.toHistory.stageAt t :=
          hIJ.1.stageAt_eq tOld
        have hmetric :
            HEq (H.toHistory.stageMetric (H.toHistory.activeStage tOld) tOld)
              (J.toHistory.stageMetric (J.toHistory.activeStage t) t) :=
          hIJ.1.sliceMetric_heq tOld
        let xOld := overlapCastPoint hstage.symm x
        have hpoint : HEq xOld x := overlapCastPoint_heq hstage.symm x
        have hscalar := overlap_scalar_eq hstage hmetric hpoint
        rw [(hPast (t : ℝ) htE.le).2.1, ← hscalar] at hx
        obtain ⟨W, hW⟩ := L.canonical tOld htE xOld hx
        obtain ⟨W', hW', _⟩ := overlap_spatialWitness_transport hstage hmetric hpoint W hW
        exact ⟨W', hW'⟩
      · have hEt : E ≤ (t : ℝ) := le_of_not_gt htE
        have hmaxB : max E (t : ℝ) < B := max_lt hEB htB
        have hmaxT : max E (t : ℝ) < (max E (t : ℝ) + B) / 2 := by linarith
        let T : Icc (0 : ℝ) J.horizon :=
          ⟨(max E (t : ℝ) + B) / 2, by
            have hnonneg := hE.trans (le_max_left E (t : ℝ))
            linarith, by rw [hJB']; linarith⟩
        have hbuffer : (T : ℝ) < J.horizon := by
          change (max E (t : ℝ) + B) / 2 < J.horizon
          rw [hJB']
          linarith
        have htT : (t : ℝ) ≤ (T : ℝ) := (le_max_right E (t : ℝ)).trans hmaxT.le
        let tO : Icc (0 : ℝ) (J.restrict T).horizon := ⟨(t : ℝ), t.property.1, htT⟩
        have hstage : (J.restrict T).toHistory.stageAt tO = J.toHistory.stageAt t :=
          J.toHistory.restrict_stageAt T tO
        have hmetric :
            HEq ((J.restrict T).toHistory.stageMetric
              ((J.restrict T).toHistory.activeStage tO) tO)
              (J.toHistory.stageMetric (J.toHistory.activeStage t) t) :=
          J.toHistory.restrict_sliceMetric T tO
        let xO := overlapCastPoint hstage.symm x
        have hpoint : HEq xO x := overlapCastPoint_heq hstage.symm x
        have hscalar := overlap_scalar_eq hstage hmetric hpoint
        have hradiusPos := pFinal.neckRadius_pos (t : ℝ) t.property.1
        have hthreshold : L.prepared.Qall ≤ (pFinal.neckRadius t ^ 2)⁻¹ :=
          L.threshold_le.trans (inv_anti₀ (sq_pos_of_pos hradiusPos)
            (pow_le_pow_left₀ hradiusPos.le (hRadiusBound (t : ℝ) hEt) 2))
        have hxO : L.prepared.Qall < metricScalarAt
            ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage tO) tO)
            xO := by
          rw [hscalar]
          exact hthreshold.trans_lt hx
        obtain ⟨W, hW⟩ := closed T hbuffer tO
          (H.time_le_horizon.trans (L.horizon_eq.trans_le hEt)) xO hxO
        obtain ⟨W', hW', _⟩ := overlap_spatialWitness_transport hstage hmetric hpoint W hW
        exact ⟨W', hW'⟩
    have hRecent : ∀ i : Fin J.eventCount, E < J.time i.succ →
        ∀ h, (recordsFinal i).nominalRadius h ≤ eta * rNext := by
      intro i hi h
      have htime := J.toHistory.time_nonneg i.succ
      have hdeltaPos := q0.delta_pos (J.time i.succ) htime
      have hdeltaOne := q0.delta_lt_one (J.time i.succ) htime
      have hdeltaSq : q0.delta (J.time i.succ) ^ 2 ≤ 1 := by
        simpa only [one_pow] using pow_le_pow_left₀ hdeltaPos.le hdeltaOne.le 2
      have hsmall := (joinedH i).nominal_small h
      have hproduct : q0.delta (J.time i.succ) ^ 2 * q0.neckRadius (J.time i.succ) ≤
          q0.neckRadius (J.time i.succ) :=
        mul_le_of_le_one_left (q0.neckRadius_pos _ htime).le hdeltaSq
      have hfuture := affine_future_neckRadius_budget (H := H) AJ L.parameters pCH hradiusEta
        i (L.horizon_eq.trans_lt hi)
      calc
        (recordsFinal i).nominalRadius h = (joinedH i).nominalRadius h :=
          congrFun ((hrecordsFinal i).1.trans (hrecordsDelta i).1) h
        _ ≤ q0.neckRadius (J.time i.succ) := hsmall.le.trans hproduct
        _ ≤ eta * rNext := hfuture
    let pReserve := pF.withModelWindow pNew.modelRadius pNew.modelOrder pNew.modelAccuracy
      pNew.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccNew)
    let reserved : ∀ i : Fin N.eventCount, GeometricCutoffRecord N.toHistory i pReserve :=
      fun i => (native i).restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
          pNew.modelRadius_pos hDNew hmNew haccNew
    have hrecKplus : RecordHypFar_C12X (5 / 4) Kplus joinedK := by
      refine ⟨?_, ?_⟩
      · exact deepNecks_join_C12X AK (L.native.toHistory.time_nonneg _) IoldK IoldK.count_le
          L.nativeRecords native joinedK
          (fun i => ⟨(hOldK i).1, (hOldK i).2.1, (hOldK i).2.2.1, (hOldK i).2.2.2.1⟩)
          (fun i => ⟨(hTailK i).1, (hTailK i).2.1, (hTailK i).2.2.1, (hTailK i).2.2.2.1⟩)
          (fun i => L.nativeRecordHyp.1 i) (fun i => hrecK.1 i)
      · let pCK5 := pF.withModelWindow L.nativeParameters.modelRadius
          L.nativeParameters.modelOrder L.nativeParameters.modelAccuracy
          L.nativeParameters.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccK)
        exact GC.GeneralFlow.joined_static_radial_C12X (pH := L.nativeParameters) (pC := pCK5)
          (q := L.nativeParameters.spliceAfter
            (translate_cutoff_parameters pCK5 (K.time (Fin.last K.eventCount))) K.horizon)
          IoldK AK ⟨rfl, rfl, rfl, rfl⟩
          ⟨L.nativeClass.1.trans (L.prepared.fixed_eq.trans hfixedFine.symm), rfl, rfl, rfl⟩
          L.nativeRecords
          (fun i => (native i).restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
            L.nativeParameters.modelRadius_pos hDK hmK haccK)
          joinedK (fun i => (hOldK i).2.2.2.2) (fun i => (hTailK i).2.2.2.2)
          L.nativeRecordHyp.2
          (radialWindows_restrictModelWindow_C12X native (fun i b => (hwin i b).hasCanonicalWindow)
            L.nativeParameters.modelRadius_pos hDK hmK haccK hrecK.2)
    have hKstr := L.prepared.strongControl Kplus IKplus _ joinedK hKplusB.le hclassKplus
      hrecKplus
    have hJhorK : J.horizon = Kplus.horizon + c := by
      rw [hJhor, hKhor]
      change N.horizon + b = N.horizon + a + c
      rw [hba]
      ring
    have hstrong := step_strong_C11SG (H := H) (J := J) (Kp := Kplus) (c := c) (E := E) (B := B)
      (r := L.radius) (qS := L.prepared.qStrong) (ε := C.epsilon) (C1 := L.C1S) (C2 := L.C2S)
      (C1c := L.prepared.C1strong) (C2c := L.prepared.C2strong)
      (C1' := max L.C1S L.prepared.C1strong) (C2' := max L.C2S L.prepared.C2strong)
      L.parameters.neckRadius pFinal.neckRadius L.horizon_eq hJB' hIJ.1
      (affineEventPrefix_join_C12X L.affine IoldH AJ IoldK AK hba) hJhorK
      (finalMetric_join_C11SG hba hfinalJ hfinalKplus) hcE (fun t ht => (hPast t ht).2.1)
      (fun t ht => pFinal.neckRadius_pos t ht) hRadiusBound L.strong_threshold_le
      (le_max_left _ _) (le_max_left _ _) (le_max_right _ _) (le_max_right _ _)
      (fun t ht hreg x hx => L.strong t ht hreg x hx) hKstr.1 hKstr.2
    let R : PreparedSpatialState pBase C P g B Bnext := {
      history := J
      initial := IJ
      horizon_eq := hJB'
      parameters := pFinal
      records := recordsFinal
      static_eq := L.static_eq
      modelRadius_bound := L.modelRadius_bound
      eventControl := hcontrolJ
      windows := hwindowsFinal
      linked := hlinkedFinal
      radial := hradFinal
      kappa := κJ
      kappa_pos := hκJ
      noncollapsed := hncJ
      nativeStage := K.stage (Fin.last K.eventCount)
      nativeMetric := K.initialMetric (Fin.last K.eventCount)
      native := N
      nativeInitial := IN
      nativeParameters := pReserve
      nativeRecords := reserved
      shift := b
      offset := H.eventCount
      prepared := nextClass
      nativeClass := hclassNew
      nativeRecordHyp := ⟨fun i => hrecK.1 i,
        radialWindows_restrictModelWindow_C12X native (fun i b => (hwin i b).hasCanonicalWindow)
          pNew.modelRadius_pos hDNew hmNew haccNew hrecK.2⟩
      nativeEventControl := hcontrolN
      affine := AJ
      horizon_affine := hJhor
      native_lt_capacity := by rw [hNB']; exact sub_lt_sub_right hBBnext b
      finalMetric_heq := hfinalJ
      radius := rNext
      radius_pos := hrNext
      threshold_le := hQallr
      radius_antitone := hradiusAnti
      radius_after := fun t ht => hRadiusAfter t (hactivationB.trans_le ht)
      delta_antitone := by
        intro s hs t ht hst
        rw [congrFun hFinalDelta t, congrFun hFinalDelta s]
        exact hdeltaAnti hs ht hst
      canonical := hcanonical
      C1S := max L.C1S L.prepared.C1strong
      C2S := max L.C2S L.prepared.C2strong
      C1S_ge_one := le_max_of_le_left L.C1S_ge_one
      C2S_ge_one := le_max_of_le_left L.C2S_ge_one
      C1S_le := max_le L.C1S_le L.prepared.C1strong_le
      C2S_le := max_le L.C2S_le L.prepared.C2strong_le
      strong_threshold_le := hqStrongr
      strong := hstrong }
    have hSuccessor : PreparedSpatialSuccessor L R activation eta d := by
      refine {
        initial_prefix := hIJ
        count_le := IoldH.count_le
        parameters_past := hPast
        records_preserved := ?_
        radius_le := hrNextOld
        radius_before_activation := hRadiusBefore
        radius_after_activation := hRadiusAfter
        delta_after := hDeltaFinal
        recent_records := hRecent }
      intro i
      have hd := hrecordsDelta (i.castLE IoldH.count_le)
      have hr := hrecordsFinal (i.castLE IoldH.count_le)
      have ho := hOldH i
      exact ⟨(heq_of_eq (hr.1.trans hd.1)).trans ho.1,
        (heq_of_eq (hr.2.1.trans hd.2.1)).trans ho.2.1,
        (heq_of_eq (hr.2.2.1.trans hd.2.2.1)).trans ho.2.2.1,
        (hr.2.2.2.1.trans hd.2.2.2.1).trans ho.2.2.2.1,
        (hr.2.2.2.2.2.trans hd.2.2.2.2.2).trans ho.2.2.2.2⟩
    refine ⟨R, rfl, rfl, rfl, rfl, HEq.rfl, HEq.rfl,
      ⟨hJoinedCertificates.2, hCertificateN, hNextExtension⟩, hSuccessor, ?_⟩
    refine ⟨{
      fineParameters := pF
      fineRecords := native
      fineWindows := fun i b => (hwin i b).hasCanonicalWindow
      fineLinked := hwin
      fine_fixed := hfixedFine
      fine_recenter := hrcFine
      fine_accuracy := haccFine
      fine_radius := hradFine
      fine_order := horderFine
      fine_cutoff := hfine
      full_radius := hDH
      full_order := hmH
      full_accuracy := haccH
      reserve_radius := hDNew
      reserve_order := hmNew
      reserve_accuracy := haccNew
      native_parameters := rfl
      native_records := fun _ => HEq.rfl
      full_records := ?_
      oldNative := Kplus
      oldNativeInitial := IKplus
      oldNativeParameters := L.nativeParameters.spliceAfter
        (translate_cutoff_parameters
          (pF.withModelWindow L.nativeParameters.modelRadius
            L.nativeParameters.modelOrder L.nativeParameters.modelAccuracy
            L.nativeParameters.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccK)) a)
        K.horizon
      oldNativeRecords := joinedK
      oldNativeAffine := AK
      oldNativeRawPrefix := IoldK
      oldNativeInitial_prefix := hIKplus
      oldNative_horizon := hKplusB
      oldNative_horizon_affine := hKhor
      oldNative_class := hclassKplus
      oldNative_finalMetric := hfinalKplus
      oldNative_records_preserved := hOldK
      oldNative_estimates := hestKplus }⟩
    intro i
    have hd := hrecordsDelta (AJ.eventIndex i)
    have hr := hrecordsFinal (AJ.eventIndex i)
    have ht := hTailH i
    exact ⟨(heq_of_eq (hr.1.trans hd.1)).trans ht.1,
      (heq_of_eq (hr.2.1.trans hd.2.1)).trans ht.2.1,
      (heq_of_eq (hr.2.2.1.trans hd.2.2.1)).trans ht.2.2.1,
      (hr.2.2.2.1.trans hd.2.2.2.1).trans ht.2.2.2.1,
      (hr.2.2.2.2.2.trans hd.2.2.2.2.2).trans ht.2.2.2.2⟩
  refine ⟨makeState, ?_⟩
  intro accuracyCap haccuracyCap
  let d : ℝ := min (1 / 2) (min (L.parameters.delta E) accuracyCap)
  have hd : 0 < d :=
    lt_min (by norm_num) (lt_min (L.parameters.delta_pos E hE) haccuracyCap)
  have hdone : d < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hdOld : d ≤ L.parameters.delta E := (min_le_right _ _).trans (min_le_left _ _)
  have hdCap : d ≤ accuracyCap := (min_le_right _ _).trans (min_le_right _ _)
  exact ⟨d, hd, hdone, hdOld, hdCap, makeState d hd hdone hdOld⟩

/-- Forget only the four reserve bounds from the same native successor. -/
private theorem exists_prepared_spatial_step_with_quality_and_native_certificate_and_small_test_margin
    (certificate : RetainedCoreHistory.{u} → Prop)
    (joinCertificate :
      ∀ {H K J : RetainedCoreHistory.{u}} {c : ℝ},
        H.toHistory.IsPrefixOf J.toHistory →
        AffineEventPrefix K J c H.eventCount (Fin.last K.eventCount) →
        certificate H → certificate K → certificate J)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (cMax : ℝ) (hcMax : 0 < cMax)
    (prepareClass : PreparedClassProviderWithNative certificate pBase.fixed pBase.recenterConstant)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ C.Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ C.epsilon K.horizon →
        NativeEstimates K C.epsilon C.C1 C.C2 C.C1s C.C2s qcan qs C.tauMin C.Ctime C.Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y, W.capTubeHasNeckChart C.epsilon)
    {P : OrientedThreeStage.{u}} {g : P.Metric} {E B Bnext activation eta : ℝ}
    (L : PreparedSpatialState pBase C P g E B)
    (hFull : certificate L.history) (hNative : certificate L.native)
    (hExtension : PreparedGeometricObservationExtensionWithNative certificate
      L.nativeStage L.nativeMetric (B - L.shift)
      L.prepared.epsilonClass L.prepared.kappaClass
      L.prepared.parameters L.prepared.deltaBound L.prepared.radiusBound)
    (hBBnext : B < Bnext)
    (hEactivation : E ≤ activation) (hactivationB : activation < B) (heta : 0 < eta) :
    let b := L.history.time (Fin.last L.history.eventCount)
    let Pnext := L.native.stage (Fin.last L.native.eventCount)
    let gnext := L.native.initialMetric (Fin.last L.native.eventCount)
    ∃ (nextClass : ClosedBirthPreparedClass pBase C Pnext gnext (Bnext - b)) (rNext : ℝ),
      PreparedGeometricObservationExtensionWithNative certificate Pnext gnext (Bnext - b)
        nextClass.epsilonClass nextClass.kappaClass nextClass.parameters
        nextClass.deltaBound nextClass.radiusBound ∧
      0 < rNext ∧ rNext ≤ L.radius ∧ nextClass.Qall ≤ (rNext ^ 2)⁻¹ ∧
      rNext * Real.sqrt nextClass.Qall ≤ 100 * cMax ∧
      ∀ (εcut Dcut : ℝ) (mcut : ℕ), 0 < εcut → 0 < Dcut →
      (∀ d : ℝ, 0 < d → d < 1 → d ≤ L.parameters.delta E →
        ∃ R : PreparedSpatialState pBase C P g B Bnext,
          R.radius = rNext ∧ R.shift = b ∧ R.offset = L.history.eventCount ∧
          R.nativeStage = Pnext ∧ HEq R.nativeMetric gnext ∧
          HEq R.prepared nextClass ∧ (certificate R.history ∧ certificate R.native ∧
            PreparedGeometricObservationExtensionWithNative certificate
              R.nativeStage R.nativeMetric (Bnext - R.shift)
              R.prepared.epsilonClass R.prepared.kappaClass
              R.prepared.parameters R.prepared.deltaBound R.prepared.radiusBound) ∧
          PreparedSpatialSuccessor L R activation eta d ∧
          Nonempty (PreparedSpatialStepRetention L R d eta εcut Dcut mcut)) ∧
      ∀ accuracyCap : ℝ, 0 < accuracyCap →
        ∃ d : ℝ, 0 < d ∧ d < 1 ∧ d ≤ L.parameters.delta E ∧ d ≤ accuracyCap ∧
        ∃ R : PreparedSpatialState pBase C P g B Bnext,
          R.radius = rNext ∧ R.shift = b ∧ R.offset = L.history.eventCount ∧
          R.nativeStage = Pnext ∧ HEq R.nativeMetric gnext ∧
          HEq R.prepared nextClass ∧ (certificate R.history ∧ certificate R.native ∧
            PreparedGeometricObservationExtensionWithNative certificate
              R.nativeStage R.nativeMetric (Bnext - R.shift)
              R.prepared.epsilonClass R.prepared.kappaClass
              R.prepared.parameters R.prepared.deltaBound R.prepared.radiusBound) ∧
          PreparedSpatialSuccessor L R activation eta d ∧
          Nonempty (PreparedSpatialStepRetention L R d eta εcut Dcut mcut) := by
  obtain ⟨nextClass, rNext, _, hOld⟩ :=
    exists_prepared_spatial_step_with_quality_and_native_certificate_and_small_test_margin_with_reserve_quality
      1 1 one_pos one_pos certificate joinCertificate pBase C cMax hcMax
      prepareClass analytic L hFull hNative hExtension hBBnext hEactivation hactivationB heta
  exact ⟨nextClass, rNext, hOld⟩

/-- The original quality interface projects the same radius-refined construction. -/
private theorem exists_prepared_spatial_step_with_quality_and_native_certificate
    (certificate : RetainedCoreHistory.{u} → Prop)
    (joinCertificate :
      ∀ {H K J : RetainedCoreHistory.{u}} {c : ℝ},
        H.toHistory.IsPrefixOf J.toHistory →
        AffineEventPrefix K J c H.eventCount (Fin.last K.eventCount) →
        certificate H → certificate K → certificate J)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (prepareClass : PreparedClassProviderWithNative certificate pBase.fixed pBase.recenterConstant)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ C.Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ C.epsilon K.horizon →
        NativeEstimates K C.epsilon C.C1 C.C2 C.C1s C.C2s qcan qs C.tauMin C.Ctime C.Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y, W.capTubeHasNeckChart C.epsilon)
    {P : OrientedThreeStage.{u}} {g : P.Metric} {E B Bnext activation eta : ℝ}
    (L : PreparedSpatialState pBase C P g E B)
    (hFull : certificate L.history) (hNative : certificate L.native)
    (hExtension : PreparedGeometricObservationExtensionWithNative certificate
      L.nativeStage L.nativeMetric (B - L.shift)
      L.prepared.epsilonClass L.prepared.kappaClass
      L.prepared.parameters L.prepared.deltaBound L.prepared.radiusBound)
    (hBBnext : B < Bnext)
    (hEactivation : E ≤ activation) (hactivationB : activation < B) (heta : 0 < eta) :
    let b := L.history.time (Fin.last L.history.eventCount)
    let Pnext := L.native.stage (Fin.last L.native.eventCount)
    let gnext := L.native.initialMetric (Fin.last L.native.eventCount)
    ∃ (nextClass : ClosedBirthPreparedClass pBase C Pnext gnext (Bnext - b)) (rNext : ℝ),
      PreparedGeometricObservationExtensionWithNative certificate Pnext gnext (Bnext - b)
        nextClass.epsilonClass nextClass.kappaClass nextClass.parameters
        nextClass.deltaBound nextClass.radiusBound ∧
      0 < rNext ∧ rNext ≤ L.radius ∧ nextClass.Qall ≤ (rNext ^ 2)⁻¹ ∧
      ∀ (εcut Dcut : ℝ) (mcut : ℕ), 0 < εcut → 0 < Dcut →
      (∀ d : ℝ, 0 < d → d < 1 → d ≤ L.parameters.delta E →
        ∃ R : PreparedSpatialState pBase C P g B Bnext,
          R.radius = rNext ∧ R.shift = b ∧ R.offset = L.history.eventCount ∧
          R.nativeStage = Pnext ∧ HEq R.nativeMetric gnext ∧
          HEq R.prepared nextClass ∧ (certificate R.history ∧ certificate R.native ∧
            PreparedGeometricObservationExtensionWithNative certificate
              R.nativeStage R.nativeMetric (Bnext - R.shift)
              R.prepared.epsilonClass R.prepared.kappaClass
              R.prepared.parameters R.prepared.deltaBound R.prepared.radiusBound) ∧
          PreparedSpatialSuccessor L R activation eta d ∧
          Nonempty (PreparedSpatialStepRetention L R d eta εcut Dcut mcut)) ∧
      ∀ accuracyCap : ℝ, 0 < accuracyCap →
        ∃ d : ℝ, 0 < d ∧ d < 1 ∧ d ≤ L.parameters.delta E ∧ d ≤ accuracyCap ∧
        ∃ R : PreparedSpatialState pBase C P g B Bnext,
          R.radius = rNext ∧ R.shift = b ∧ R.offset = L.history.eventCount ∧
          R.nativeStage = Pnext ∧ HEq R.nativeMetric gnext ∧
          HEq R.prepared nextClass ∧ (certificate R.history ∧ certificate R.native ∧
            PreparedGeometricObservationExtensionWithNative certificate
              R.nativeStage R.nativeMetric (Bnext - R.shift)
              R.prepared.epsilonClass R.prepared.kappaClass
              R.prepared.parameters R.prepared.deltaBound R.prepared.radiusBound) ∧
          PreparedSpatialSuccessor L R activation eta d ∧
          Nonempty (PreparedSpatialStepRetention L R d eta εcut Dcut mcut) := by
  obtain ⟨nextClass, rNext, hExtensionNext, hrNext, hrOld, hThreshold, _, make⟩ :=
    exists_prepared_spatial_step_with_quality_and_native_certificate_and_small_test_margin
      certificate joinCertificate pBase C 1 one_pos prepareClass analytic
      L hFull hNative hExtension hBBnext hEactivation hactivationB heta
  exact ⟨nextClass, rNext, hExtensionNext, hrNext, hrOld, hThreshold, make⟩

/-- Keep the original private interface by forgetting only the new retained data. -/
private theorem exists_prepared_spatial_step_with_native_certificate
    (certificate : RetainedCoreHistory.{u} → Prop)
    (joinCertificate :
      ∀ {H K J : RetainedCoreHistory.{u}} {c : ℝ},
        H.toHistory.IsPrefixOf J.toHistory →
        AffineEventPrefix K J c H.eventCount (Fin.last K.eventCount) →
        certificate H → certificate K → certificate J)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (prepareClass : PreparedClassProviderWithNative certificate pBase.fixed pBase.recenterConstant)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ C.Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ C.epsilon K.horizon →
        NativeEstimates K C.epsilon C.C1 C.C2 C.C1s C.C2s qcan qs C.tauMin C.Ctime C.Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y, W.capTubeHasNeckChart C.epsilon)
    {P : OrientedThreeStage.{u}} {g : P.Metric} {E B Bnext activation eta : ℝ}
    (L : PreparedSpatialState pBase C P g E B)
    (hFull : certificate L.history) (hNative : certificate L.native)
    (hExtension : PreparedGeometricObservationExtensionWithNative certificate
      L.nativeStage L.nativeMetric (B - L.shift)
      L.prepared.epsilonClass L.prepared.kappaClass
      L.prepared.parameters L.prepared.deltaBound L.prepared.radiusBound)
    (hBBnext : B < Bnext)
    (hEactivation : E ≤ activation) (hactivationB : activation < B) (heta : 0 < eta) :
    let b := L.history.time (Fin.last L.history.eventCount)
    let Pnext := L.native.stage (Fin.last L.native.eventCount)
    let gnext := L.native.initialMetric (Fin.last L.native.eventCount)
    ∃ (nextClass : ClosedBirthPreparedClass pBase C Pnext gnext (Bnext - b)) (rNext : ℝ),
      PreparedGeometricObservationExtensionWithNative certificate Pnext gnext (Bnext - b)
        nextClass.epsilonClass nextClass.kappaClass nextClass.parameters
        nextClass.deltaBound nextClass.radiusBound ∧
      0 < rNext ∧ rNext ≤ L.radius ∧ nextClass.Qall ≤ (rNext ^ 2)⁻¹ ∧
      (∀ d : ℝ, 0 < d → d < 1 → d ≤ L.parameters.delta E →
        ∃ R : PreparedSpatialState pBase C P g B Bnext,
          R.radius = rNext ∧ R.shift = b ∧ R.offset = L.history.eventCount ∧
          R.nativeStage = Pnext ∧ HEq R.nativeMetric gnext ∧
          HEq R.prepared nextClass ∧ (certificate R.history ∧ certificate R.native ∧
            PreparedGeometricObservationExtensionWithNative certificate
              R.nativeStage R.nativeMetric (Bnext - R.shift)
              R.prepared.epsilonClass R.prepared.kappaClass
              R.prepared.parameters R.prepared.deltaBound R.prepared.radiusBound) ∧
          PreparedSpatialSuccessor L R activation eta d) ∧
      ∀ accuracyCap : ℝ, 0 < accuracyCap →
        ∃ d : ℝ, 0 < d ∧ d < 1 ∧ d ≤ L.parameters.delta E ∧ d ≤ accuracyCap ∧
        ∃ R : PreparedSpatialState pBase C P g B Bnext,
          R.radius = rNext ∧ R.shift = b ∧ R.offset = L.history.eventCount ∧
          R.nativeStage = Pnext ∧ HEq R.nativeMetric gnext ∧
          HEq R.prepared nextClass ∧ (certificate R.history ∧ certificate R.native ∧
            PreparedGeometricObservationExtensionWithNative certificate
              R.nativeStage R.nativeMetric (Bnext - R.shift)
              R.prepared.epsilonClass R.prepared.kappaClass
              R.prepared.parameters R.prepared.deltaBound R.prepared.radiusBound) ∧
          PreparedSpatialSuccessor L R activation eta d := by
  obtain ⟨nextClass, rNext, hExtensionNext, hrNext, hrOld, hThreshold, make⟩ :=
    exists_prepared_spatial_step_with_quality_and_native_certificate
      certificate joinCertificate pBase C prepareClass analytic L hFull hNative hExtension
      hBBnext hEactivation hactivationB heta
  have hmake := make pBase.modelAccuracy pBase.modelRadius pBase.modelOrder
    pBase.modelAccuracy_pos pBase.modelRadius_pos
  refine ⟨nextClass, rNext, hExtensionNext, hrNext, hrOld, hThreshold, ?_, ?_⟩
  · intro d hd hdOne hdOld
    obtain ⟨R, hRadius, hShift, hOffset, hStage, hMetric, hClass, hCert, hSucc, _⟩ :=
      hmake.1 d hd hdOne hdOld
    exact ⟨R, hRadius, hShift, hOffset, hStage, hMetric, hClass, hCert, hSucc⟩
  · intro accuracyCap hCap
    obtain ⟨d, hd, hdOne, hdOld, hdCap, R,
      hRadius, hShift, hOffset, hStage, hMetric, hClass, hCert, hSucc, _⟩ :=
      hmake.2 accuracyCap hCap
    exact ⟨d, hd, hdOne, hdOld, hdCap, R,
      hRadius, hShift, hOffset, hStage, hMetric, hClass, hCert, hSucc⟩

/-- Compatibility through the same engine with the trivial certificate. -/
theorem exists_prepared_spatial_step
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (prepareClass :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ), 0 < B →
      ∃ ε κ : ℝ, 0 < ε ∧ ε < 1 / 11 ∧ 0 < κ ∧
      ∀ (δcap ρcap εcapRequest DcapRequest : ℝ) (mcapRequest : ℕ),
        0 < δcap → 0 < ρcap → 0 < εcapRequest → 0 < DcapRequest →
      ∃ (p₀ : CutoffParameters) (δb ρb : ℝ),
        p₀.fixed = pBase.fixed ∧ p₀.recenterConstant = pBase.recenterConstant ∧
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
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ C.Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ C.epsilon K.horizon →
        NativeEstimates K C.epsilon C.C1 C.C2 C.C1s C.C2s qcan qs C.tauMin C.Ctime C.Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y, W.capTubeHasNeckChart C.epsilon)
    {P : OrientedThreeStage.{u}} {g : P.Metric} {E B Bnext activation eta : ℝ}
    (L : PreparedSpatialState pBase C P g E B)
    (hBBnext : B < Bnext)
    (hEactivation : E ≤ activation) (hactivationB : activation < B) (heta : 0 < eta) :
    let b := L.history.time (Fin.last L.history.eventCount)
    let Pnext := L.native.stage (Fin.last L.native.eventCount)
    let gnext := L.native.initialMetric (Fin.last L.native.eventCount)
    ∃ (nextClass : ClosedBirthPreparedClass pBase C Pnext gnext (Bnext - b)) (rNext : ℝ),
      0 < rNext ∧ rNext ≤ L.radius ∧ nextClass.Qall ≤ (rNext ^ 2)⁻¹ ∧
      (∀ d : ℝ, 0 < d → d < 1 → d ≤ L.parameters.delta E →
        ∃ R : PreparedSpatialState pBase C P g B Bnext,
          R.radius = rNext ∧ R.shift = b ∧ R.offset = L.history.eventCount ∧
          R.nativeStage = Pnext ∧ HEq R.nativeMetric gnext ∧
          HEq R.prepared nextClass ∧ PreparedSpatialSuccessor L R activation eta d) ∧
      ∀ accuracyCap : ℝ, 0 < accuracyCap →
        ∃ d : ℝ, 0 < d ∧ d < 1 ∧ d ≤ L.parameters.delta E ∧ d ≤ accuracyCap ∧
        ∃ R : PreparedSpatialState pBase C P g B Bnext,
          R.radius = rNext ∧ R.shift = b ∧ R.offset = L.history.eventCount ∧
          R.nativeStage = Pnext ∧ HEq R.nativeMetric gnext ∧
          HEq R.prepared nextClass ∧ PreparedSpatialSuccessor L R activation eta d := by
  have distanceResult := @exists_prepared_spatial_step_with_native_certificate.{u} (fun _ => True)
    (by intro H K J c hp A hH hK; exact True.intro) pBase C (PreparedClassProviderWithNative.of_weak
      prepareClass) analytic P g E B Bnext activation eta L True.intro True.intro
      L.prepared.extension.withTrue hBBnext hEactivation hactivationB heta
  dsimp only at distanceResult ⊢
  obtain ⟨nextClass, rNext, distanceProjectionh1⟩ := distanceResult
  refine ⟨nextClass, rNext, ?_⟩
  obtain ⟨distanceProjectionfield2, distanceProjectionfield3, distanceProjectionfield4,
    distanceProjectionh5⟩ := (distanceProjectionh1.2)
  refine ⟨distanceProjectionfield2, distanceProjectionfield3, distanceProjectionfield4, ?_⟩
  refine ⟨?_, ?_⟩
  · intro d distanceProjectionx6 distanceProjectionx7 distanceProjectionx8
    have distanceProjectionh9 := @distanceProjectionh5.1 d distanceProjectionx6 distanceProjectionx7
      distanceProjectionx8
    obtain ⟨R, distanceProjectionh10⟩ := distanceProjectionh9
    refine ⟨R, ?_⟩
    obtain ⟨distanceProjectionfield11, distanceProjectionfield12, distanceProjectionfield13,
      distanceProjectionfield14, distanceProjectionfield15, distanceProjectionfield16,
      distanceProjectionh17⟩ := distanceProjectionh10
    refine ⟨distanceProjectionfield11, distanceProjectionfield12, distanceProjectionfield13,
      distanceProjectionfield14, distanceProjectionfield15, distanceProjectionfield16, ?_⟩
    exact distanceProjectionh17.2
  · intro accuracyCap distanceProjectionx18
    have distanceProjectionh19 := @distanceProjectionh5.2 accuracyCap distanceProjectionx18
    obtain ⟨d, distanceProjectionh20⟩ := distanceProjectionh19
    refine ⟨d, ?_⟩
    obtain ⟨distanceProjectionfield21, distanceProjectionfield22, distanceProjectionfield23,
      distanceProjectionfield24, distanceProjectionh25⟩ := distanceProjectionh20
    refine ⟨distanceProjectionfield21, distanceProjectionfield22, distanceProjectionfield23,
      distanceProjectionfield24, ?_⟩
    obtain ⟨R, distanceProjectionh26⟩ := distanceProjectionh25
    refine ⟨R, ?_⟩
    obtain ⟨distanceProjectionfield27, distanceProjectionfield28, distanceProjectionfield29,
      distanceProjectionfield30, distanceProjectionfield31, distanceProjectionfield32,
      distanceProjectionh33⟩ := distanceProjectionh26
    refine ⟨distanceProjectionfield27, distanceProjectionfield28, distanceProjectionfield29,
      distanceProjectionfield30, distanceProjectionfield31, distanceProjectionfield32, ?_⟩
    exact distanceProjectionh33.2

/-- The same selected successor/chain retaining its actual distance certificates. -/
theorem exists_prepared_spatial_step_with_distance_scalars
    (Cdist : ℝ≥0)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (prepareClass : PreparedDistanceClassProvider.{u} pBase.fixed pBase.recenterConstant Cdist)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ C.Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ C.epsilon K.horizon →
        NativeEstimates K C.epsilon C.C1 C.C2 C.C1s C.C2s qcan qs C.tauMin C.Ctime C.Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y, W.capTubeHasNeckChart C.epsilon)
    {P : OrientedThreeStage.{u}} {g : P.Metric} {E B Bnext activation eta : ℝ}
    (L : PreparedSpatialState pBase C P g E B)
    (hL : L.DistanceData Cdist)
    (hBBnext : B < Bnext)
    (hEactivation : E ≤ activation) (hactivationB : activation < B) (heta : 0 < eta) :
    let b := L.history.time (Fin.last L.history.eventCount)
    let Pnext := L.native.stage (Fin.last L.native.eventCount)
    let gnext := L.native.initialMetric (Fin.last L.native.eventCount)
    ∃ (nextClass : ClosedBirthPreparedClass pBase C Pnext gnext (Bnext - b)) (rNext : ℝ),
      nextClass.HasDistanceExtension Cdist ∧
      0 < rNext ∧ rNext ≤ L.radius ∧ nextClass.Qall ≤ (rNext ^ 2)⁻¹ ∧
      (∀ d : ℝ, 0 < d → d < 1 → d ≤ L.parameters.delta E →
        ∃ R : PreparedSpatialState pBase C P g B Bnext,
          R.radius = rNext ∧ R.shift = b ∧ R.offset = L.history.eventCount ∧
          R.nativeStage = Pnext ∧ HEq R.nativeMetric gnext ∧
          HEq R.prepared nextClass ∧ R.DistanceData Cdist ∧
          PreparedSpatialSuccessor L R activation eta d) ∧
      ∀ accuracyCap : ℝ, 0 < accuracyCap →
        ∃ d : ℝ, 0 < d ∧ d < 1 ∧ d ≤ L.parameters.delta E ∧ d ≤ accuracyCap ∧
        ∃ R : PreparedSpatialState pBase C P g B Bnext,
          R.radius = rNext ∧ R.shift = b ∧ R.offset = L.history.eventCount ∧
          R.nativeStage = Pnext ∧ HEq R.nativeMetric gnext ∧
          HEq R.prepared nextClass ∧ R.DistanceData Cdist ∧
          PreparedSpatialSuccessor L R activation eta d := by
  have distanceResult := @exists_prepared_spatial_step_with_native_certificate.{u} (fun K => ∀ i :
    Fin K.eventCount, (K.toHistory.event i).HasUniformDistanceScalar Cdist)
    (by
      intro H K J c hp A hH hK
      exact hasUniformDistanceScalar_at_affine_join hp A hH hK) pBase C prepareClass.toNative
        analytic P g E B Bnext activation eta L hL.full hL.native hL.extension hBBnext hEactivation
        hactivationB heta
  dsimp only at distanceResult ⊢
  obtain ⟨nextClass, rNext, distanceProjectionh1⟩ := distanceResult
  refine ⟨nextClass, rNext, ?_⟩
  refine ⟨?_, ?_⟩
  · exact distanceProjectionh1.1
  · obtain ⟨distanceProjectionfield2, distanceProjectionfield3, distanceProjectionfield4,
      distanceProjectionh5⟩ := distanceProjectionh1.2
    refine ⟨distanceProjectionfield2, distanceProjectionfield3, distanceProjectionfield4, ?_⟩
    refine ⟨?_, ?_⟩
    · intro d distanceProjectionx6 distanceProjectionx7 distanceProjectionx8
      have distanceProjectionh9 := @distanceProjectionh5.1 d distanceProjectionx6
        distanceProjectionx7 distanceProjectionx8
      obtain ⟨R, distanceProjectionh10⟩ := distanceProjectionh9
      refine ⟨R, ?_⟩
      obtain ⟨distanceProjectionfield11, distanceProjectionfield12, distanceProjectionfield13,
        distanceProjectionfield14, distanceProjectionfield15, distanceProjectionfield16,
        distanceProjectionh17⟩ := distanceProjectionh10
      refine ⟨distanceProjectionfield11, distanceProjectionfield12, distanceProjectionfield13,
        distanceProjectionfield14, distanceProjectionfield15, distanceProjectionfield16, ?_⟩
      refine ⟨?_, ?_⟩
      · exact ⟨distanceProjectionh17.1.1, distanceProjectionh17.1.2.1, distanceProjectionh17.1.2.2⟩
      · exact distanceProjectionh17.2
    · intro accuracyCap distanceProjectionx18
      have distanceProjectionh19 := @distanceProjectionh5.2 accuracyCap distanceProjectionx18
      obtain ⟨d, distanceProjectionh20⟩ := distanceProjectionh19
      refine ⟨d, ?_⟩
      obtain ⟨distanceProjectionfield21, distanceProjectionfield22, distanceProjectionfield23,
        distanceProjectionfield24, distanceProjectionh25⟩ := distanceProjectionh20
      refine ⟨distanceProjectionfield21, distanceProjectionfield22, distanceProjectionfield23,
        distanceProjectionfield24, ?_⟩
      obtain ⟨R, distanceProjectionh26⟩ := distanceProjectionh25
      refine ⟨R, ?_⟩
      obtain ⟨distanceProjectionfield27, distanceProjectionfield28, distanceProjectionfield29,
        distanceProjectionfield30, distanceProjectionfield31, distanceProjectionfield32,
        distanceProjectionh33⟩ := distanceProjectionh26
      refine ⟨distanceProjectionfield27, distanceProjectionfield28, distanceProjectionfield29,
        distanceProjectionfield30, distanceProjectionfield31, distanceProjectionfield32, ?_⟩
      refine ⟨?_, ?_⟩
      · exact ⟨distanceProjectionh33.1.1, distanceProjectionh33.1.2.1, distanceProjectionh33.1.2.2⟩
      · exact distanceProjectionh33.2


/-- Retain the requested fine model and the same native extension with distance data. -/
theorem exists_prepared_spatial_step_with_quality_and_distance_scalars
    (Cdist : ℝ≥0)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (prepareClass : PreparedDistanceClassProvider.{u} pBase.fixed pBase.recenterConstant Cdist)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ C.Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ C.epsilon K.horizon →
        NativeEstimates K C.epsilon C.C1 C.C2 C.C1s C.C2s qcan qs C.tauMin C.Ctime C.Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y, W.capTubeHasNeckChart C.epsilon)
    {P : OrientedThreeStage.{u}} {g : P.Metric} {E B Bnext activation eta : ℝ}
    (L : PreparedSpatialState pBase C P g E B)
    (hL : L.DistanceData Cdist)
    (hBBnext : B < Bnext)
    (hEactivation : E ≤ activation) (hactivationB : activation < B) (heta : 0 < eta) :
    let b := L.history.time (Fin.last L.history.eventCount)
    let Pnext := L.native.stage (Fin.last L.native.eventCount)
    let gnext := L.native.initialMetric (Fin.last L.native.eventCount)
    ∃ (nextClass : ClosedBirthPreparedClass pBase C Pnext gnext (Bnext - b)) (rNext : ℝ),
      nextClass.HasDistanceExtension Cdist ∧
      0 < rNext ∧ rNext ≤ L.radius ∧ nextClass.Qall ≤ (rNext ^ 2)⁻¹ ∧
      ∀ (εcut Dcut : ℝ) (mcut : ℕ), 0 < εcut → 0 < Dcut →
      (∀ d : ℝ, 0 < d → d < 1 → d ≤ L.parameters.delta E →
        ∃ R : PreparedSpatialState pBase C P g B Bnext,
          R.radius = rNext ∧ R.shift = b ∧ R.offset = L.history.eventCount ∧
          R.nativeStage = Pnext ∧ HEq R.nativeMetric gnext ∧
          HEq R.prepared nextClass ∧ R.DistanceData Cdist ∧
          PreparedSpatialSuccessor L R activation eta d ∧
          Nonempty (PreparedSpatialStepRetention L R d eta εcut Dcut mcut)) ∧
      ∀ accuracyCap : ℝ, 0 < accuracyCap →
        ∃ d : ℝ, 0 < d ∧ d < 1 ∧ d ≤ L.parameters.delta E ∧ d ≤ accuracyCap ∧
        ∃ R : PreparedSpatialState pBase C P g B Bnext,
          R.radius = rNext ∧ R.shift = b ∧ R.offset = L.history.eventCount ∧
          R.nativeStage = Pnext ∧ HEq R.nativeMetric gnext ∧
          HEq R.prepared nextClass ∧ R.DistanceData Cdist ∧
          PreparedSpatialSuccessor L R activation eta d ∧
          Nonempty (PreparedSpatialStepRetention L R d eta εcut Dcut mcut) := by
  obtain ⟨nextClass, rNext, hExtension, hrNext, hrOld, hThreshold, make⟩ :=
    exists_prepared_spatial_step_with_quality_and_native_certificate
      (fun K => ∀ i : Fin K.eventCount,
        (K.toHistory.event i).HasUniformDistanceScalar Cdist)
      (by
        intro H K J c hp A hH hK
        exact hasUniformDistanceScalar_at_affine_join hp A hH hK)
      pBase C prepareClass.toNative analytic L hL.full hL.native hL.extension
      hBBnext hEactivation hactivationB heta
  refine ⟨nextClass, rNext, hExtension, hrNext, hrOld, hThreshold, ?_⟩
  intro εcut Dcut mcut hεcut hDcut
  obtain ⟨makeExact, makeCap⟩ := make εcut Dcut mcut hεcut hDcut
  refine ⟨?_, ?_⟩
  · intro d hd hdOne hdOld
    obtain ⟨R, hRadius, hShift, hOffset, hStage, hMetric, hClass, hCert, hSucc, hRetain⟩ :=
      makeExact d hd hdOne hdOld
    exact ⟨R, hRadius, hShift, hOffset, hStage, hMetric, hClass,
      ⟨hCert.1, hCert.2.1, hCert.2.2⟩, hSucc, hRetain⟩
  · intro accuracyCap hCap
    obtain ⟨d, hd, hdOne, hdOld, hdCap, R,
      hRadius, hShift, hOffset, hStage, hMetric, hClass, hCert, hSucc, hRetain⟩ :=
      makeCap accuracyCap hCap
    exact ⟨d, hd, hdOne, hdOld, hdCap, R,
      hRadius, hShift, hOffset, hStage, hMetric, hClass,
      ⟨hCert.1, hCert.2.1, hCert.2.2⟩, hSucc, hRetain⟩

/-- The same requested-quality successor with its pre-fine small-test margin. -/
theorem exists_prepared_spatial_step_with_quality_and_distance_scalars_and_small_test_margin
    (Cdist : ℝ≥0)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (cMax : ℝ) (hcMax : 0 < cMax)
    (prepareClass : PreparedDistanceClassProvider.{u} pBase.fixed pBase.recenterConstant Cdist)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ C.Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ C.epsilon K.horizon →
        NativeEstimates K C.epsilon C.C1 C.C2 C.C1s C.C2s qcan qs C.tauMin C.Ctime C.Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y, W.capTubeHasNeckChart C.epsilon)
    {P : OrientedThreeStage.{u}} {g : P.Metric} {E B Bnext activation eta : ℝ}
    (L : PreparedSpatialState pBase C P g E B)
    (hL : L.DistanceData Cdist)
    (hBBnext : B < Bnext)
    (hEactivation : E ≤ activation) (hactivationB : activation < B) (heta : 0 < eta) :
    let b := L.history.time (Fin.last L.history.eventCount)
    let Pnext := L.native.stage (Fin.last L.native.eventCount)
    let gnext := L.native.initialMetric (Fin.last L.native.eventCount)
    ∃ (nextClass : ClosedBirthPreparedClass pBase C Pnext gnext (Bnext - b)) (rNext : ℝ),
      nextClass.HasDistanceExtension Cdist ∧
      0 < rNext ∧ rNext ≤ L.radius ∧ nextClass.Qall ≤ (rNext ^ 2)⁻¹ ∧
      rNext * Real.sqrt nextClass.Qall ≤ 100 * cMax ∧
      ∀ (εcut Dcut : ℝ) (mcut : ℕ), 0 < εcut → 0 < Dcut →
      (∀ d : ℝ, 0 < d → d < 1 → d ≤ L.parameters.delta E →
        ∃ R : PreparedSpatialState pBase C P g B Bnext,
          R.radius = rNext ∧ R.shift = b ∧ R.offset = L.history.eventCount ∧
          R.nativeStage = Pnext ∧ HEq R.nativeMetric gnext ∧
          HEq R.prepared nextClass ∧ R.DistanceData Cdist ∧
          PreparedSpatialSuccessor L R activation eta d ∧
          Nonempty (PreparedSpatialStepRetention L R d eta εcut Dcut mcut)) ∧
      ∀ accuracyCap : ℝ, 0 < accuracyCap →
        ∃ d : ℝ, 0 < d ∧ d < 1 ∧ d ≤ L.parameters.delta E ∧ d ≤ accuracyCap ∧
        ∃ R : PreparedSpatialState pBase C P g B Bnext,
          R.radius = rNext ∧ R.shift = b ∧ R.offset = L.history.eventCount ∧
          R.nativeStage = Pnext ∧ HEq R.nativeMetric gnext ∧
          HEq R.prepared nextClass ∧ R.DistanceData Cdist ∧
          PreparedSpatialSuccessor L R activation eta d ∧
          Nonempty (PreparedSpatialStepRetention L R d eta εcut Dcut mcut) := by
  obtain ⟨nextClass, rNext, hExtension, hrNext, hrOld, hThreshold, hFit, make⟩ :=
    exists_prepared_spatial_step_with_quality_and_native_certificate_and_small_test_margin
      (fun K => ∀ i : Fin K.eventCount,
        (K.toHistory.event i).HasUniformDistanceScalar Cdist)
      (by
        intro H K J c hp A hH hK
        exact hasUniformDistanceScalar_at_affine_join hp A hH hK)
      pBase C cMax hcMax prepareClass.toNative analytic L hL.full hL.native hL.extension
      hBBnext hEactivation hactivationB heta
  refine ⟨nextClass, rNext, hExtension, hrNext, hrOld, hThreshold, hFit, ?_⟩
  intro εcut Dcut mcut hεcut hDcut
  obtain ⟨makeExact, makeCap⟩ := make εcut Dcut mcut hεcut hDcut
  refine ⟨?_, ?_⟩
  · intro d hd hdOne hdOld
    obtain ⟨R, hRadius, hShift, hOffset, hStage, hMetric, hClass, hCert, hSucc, hRetain⟩ :=
      makeExact d hd hdOne hdOld
    exact ⟨R, hRadius, hShift, hOffset, hStage, hMetric, hClass,
      ⟨hCert.1, hCert.2.1, hCert.2.2⟩, hSucc, hRetain⟩
  · intro accuracyCap hCap
    obtain ⟨d, hd, hdOne, hdOld, hdCap, R,
      hRadius, hShift, hOffset, hStage, hMetric, hClass, hCert, hSucc, hRetain⟩ :=
      makeCap accuracyCap hCap
    exact ⟨d, hd, hdOne, hdOld, hdCap, R,
      hRadius, hShift, hOffset, hStage, hMetric, hClass,
      ⟨hCert.1, hCert.2.1, hCert.2.2⟩, hSucc, hRetain⟩

/-- The same distance-certified successor with all four pre-fine class bounds. -/
theorem exists_prepared_spatial_step_with_quality_and_distance_scalars_and_small_test_margin_with_reserve_quality
    (Dstar εReserve : ℝ) (hDstar : 0 < Dstar) (hεReserve : 0 < εReserve)
    (Cdist : ℝ≥0)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (cMax : ℝ) (hcMax : 0 < cMax)
    (prepareClass : PreparedDistanceClassProvider.{u} pBase.fixed pBase.recenterConstant Cdist)
    (analytic :
      ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B κ : ℝ), 0 < B → 0 < κ →
      ∃ (qcan qs Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
        0 < qcan ∧ qcan ≤ qs ∧ qs ≤ C.Cs * qcan ∧
        max 1 (max qcan qs) ≤ Qbirth ∧
        0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (K : RetainedCoreHistory.{u}) (_I : InitialIdentification P g K.toHistory)
        (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
        K.horizon ≤ B → K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        K.NoncollapsedBefore κ C.epsilon K.horizon →
        NativeEstimates K C.epsilon C.C1 C.C2 C.C1s C.C2s qcan qs C.tauMin C.Ctime C.Cgrad ∧
        ∀ t : Icc (0 : ℝ) K.toHistory.horizon,
          (t : ℝ) < K.horizon → K.time (K.toHistory.activeStage t) = (t : ℝ) →
          K.toHistory.activeStage t ≠ 0 →
          ∀ y : (K.toHistory.stageAt t).Carrier,
            Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage t)) y →
            ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage t))
              C.epsilon C.Cbirth (max C.Cbirth (C.Cgrad : ℝ)) y, W.capTubeHasNeckChart C.epsilon)
    {P : OrientedThreeStage.{u}} {g : P.Metric} {E B Bnext activation eta : ℝ}
    (L : PreparedSpatialState pBase C P g E B)
    (hL : L.DistanceData Cdist)
    (hBBnext : B < Bnext)
    (hEactivation : E ≤ activation) (hactivationB : activation < B) (heta : 0 < eta) :
    let b := L.history.time (Fin.last L.history.eventCount)
    let Pnext := L.native.stage (Fin.last L.native.eventCount)
    let gnext := L.native.initialMetric (Fin.last L.native.eventCount)
    ∃ (nextClass : ClosedBirthPreparedClass pBase C Pnext gnext (Bnext - b)) (rNext : ℝ),
      nextClass.HasReserveQuality Dstar εReserve ∧
      nextClass.HasDistanceExtension Cdist ∧
      0 < rNext ∧ rNext ≤ L.radius ∧ nextClass.Qall ≤ (rNext ^ 2)⁻¹ ∧
      rNext * Real.sqrt nextClass.Qall ≤ 100 * cMax ∧
      ∀ (εcut Dcut : ℝ) (mcut : ℕ), 0 < εcut → 0 < Dcut →
      (∀ d : ℝ, 0 < d → d < 1 → d ≤ L.parameters.delta E →
        ∃ R : PreparedSpatialState pBase C P g B Bnext,
          R.radius = rNext ∧ R.shift = b ∧ R.offset = L.history.eventCount ∧
          R.nativeStage = Pnext ∧ HEq R.nativeMetric gnext ∧
          HEq R.prepared nextClass ∧ R.DistanceData Cdist ∧
          PreparedSpatialSuccessor L R activation eta d ∧
          Nonempty (PreparedSpatialStepRetention L R d eta εcut Dcut mcut)) ∧
      ∀ accuracyCap : ℝ, 0 < accuracyCap →
        ∃ d : ℝ, 0 < d ∧ d < 1 ∧ d ≤ L.parameters.delta E ∧ d ≤ accuracyCap ∧
        ∃ R : PreparedSpatialState pBase C P g B Bnext,
          R.radius = rNext ∧ R.shift = b ∧ R.offset = L.history.eventCount ∧
          R.nativeStage = Pnext ∧ HEq R.nativeMetric gnext ∧
          HEq R.prepared nextClass ∧ R.DistanceData Cdist ∧
          PreparedSpatialSuccessor L R activation eta d ∧
          Nonempty (PreparedSpatialStepRetention L R d eta εcut Dcut mcut) := by
  obtain ⟨nextClass, rNext, hReserve, hExtension, hrNext, hrOld, hThreshold, hFit, make⟩ :=
    exists_prepared_spatial_step_with_quality_and_native_certificate_and_small_test_margin_with_reserve_quality
      Dstar εReserve hDstar hεReserve (fun K => ∀ i : Fin K.eventCount,
        (K.toHistory.event i).HasUniformDistanceScalar Cdist)
      (by
        intro H K J c hp A hH hK
        exact hasUniformDistanceScalar_at_affine_join hp A hH hK)
      pBase C cMax hcMax prepareClass.toNative analytic L hL.full hL.native hL.extension
      hBBnext hEactivation hactivationB heta
  refine ⟨nextClass, rNext, hReserve, hExtension, hrNext, hrOld, hThreshold, hFit, ?_⟩
  intro εcut Dcut mcut hεcut hDcut
  obtain ⟨makeExact, makeCap⟩ := make εcut Dcut mcut hεcut hDcut
  refine ⟨?_, ?_⟩
  · intro d hd hdOne hdOld
    obtain ⟨R, hRadius, hShift, hOffset, hStage, hMetric, hClass, hCert, hSucc, hRetain⟩ :=
      makeExact d hd hdOne hdOld
    exact ⟨R, hRadius, hShift, hOffset, hStage, hMetric, hClass,
      ⟨hCert.1, hCert.2.1, hCert.2.2⟩, hSucc, hRetain⟩
  · intro accuracyCap hCap
    obtain ⟨d, hd, hdOne, hdOld, hdCap, R,
      hRadius, hShift, hOffset, hStage, hMetric, hClass, hCert, hSucc, hRetain⟩ :=
      makeCap accuracyCap hCap
    exact ⟨d, hd, hdOne, hdOld, hdCap, R,
      hRadius, hShift, hOffset, hStage, hMetric, hClass,
      ⟨hCert.1, hCert.2.1, hCert.2.2⟩, hSucc, hRetain⟩

end GC.GeneralFlow
