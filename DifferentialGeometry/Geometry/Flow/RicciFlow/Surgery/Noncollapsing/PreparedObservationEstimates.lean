import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.GeometricObservationFineQuality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformObservationEstimatePacket
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapseRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordCanonicalRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedObservationData

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff NNReal

namespace GC.GeneralFlow
universe u

/-- A real consumer of both before-quality choices. One global epsilon and
one set of analytic constants control the SAME returned joined history and its
actual native tail. The tail radius is reserved before the fine request.
This is a finite overlap step; it does not assert a compatible infinite tower,
canonicality at surgery birth, or a larger-ball seed-volume estimate. -/
theorem exists_prepared_extension_with_two_estimate_packets :
    ∃ εbar : ℝ, 0 < εbar ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ εbar →
    ∃ (C1 C2 C1s C2s Cs τmin : ℝ) (Ctime Cgrad : ℝ≥0),
      1 ≤ C1 ∧ 1 ≤ C2 ∧ 1 ≤ C1s ∧ 1 ≤ C2s ∧ 1 ≤ Cs ∧ 0 < τmin ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ), 0 < B →
    ∃ (p₀ : CutoffParameters) (δb ρb κOld qOld qsOld : ℝ),
      0 < δb ∧ 0 < ρb ∧ 0 < κOld ∧ 0 < qOld ∧
      qOld ≤ qsOld ∧ qsOld ≤ Cs * qOld ∧
      StandardCap.transitionEnd < p₀.modelRadius + 1 ∧
    ∀ (H : RetainedCoreHistory.{u}) (IH : InitialIdentification P g H.toHistory)
      (p : CutoffParameters)
      (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
      H.horizon < B → H.IsCanonicalCutoffRecordFamily p₀ δb ρb old →
      HistoryEventControl H →
    ∀ R : ℝ, 0 < R →
    ∃ κTail qTail qsTail ρ : ℝ,
      0 < κTail ∧ 0 < qTail ∧ qTail ≤ qsTail ∧ qsTail ≤ Cs * qTail ∧
      0 < ρ ∧ ρ ≤ R ∧ qsTail ≤ (ρ ^ 2)⁻¹ ∧
    ∀ (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ),
      0 < δcut → 0 < ρcut → 0 < εcut → 0 < Dcut →
    ∃ (K : RetainedCoreHistory.{u})
      (_IK : InitialIdentification (H.stage (Fin.last H.eventCount))
        (H.initialMetric (Fin.last H.eventCount)) K.toHistory)
      (pB pF : CutoffParameters) (δbound ρbound : ℝ)
      (native : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pF)
      (J : RetainedCoreHistory.{u}) (IJ : InitialIdentification P g J.toHistory)
      (A : AffineEventPrefix K J (H.time (Fin.last H.eventCount)) H.eventCount
        (Fin.last K.eventCount))
      (I : RawInitialPrefix H J) (q : CutoffParameters)
      (records : ∀ i : Fin J.eventCount, GeometricCutoffRecord J.toHistory i q),
      K.horizon = B - H.time (Fin.last H.eventCount) ∧
      J.horizon = B ∧ IH.IsPrefixOf IJ ∧
      HistoryEventControl K ∧ HistoryEventControl J ∧
      K.IsCanonicalCutoffRecordFamily pB δbound ρbound native ∧
      J.IsCanonicalCutoffRecordFamily p₀ δb ρb records ∧
      K.NoncollapsedBefore κTail ε K.horizon ∧ J.NoncollapsedBefore κOld ε J.horizon ∧
      NativeEstimates J ε C1 C2 C1s C2s qOld qsOld τmin Ctime Cgrad ∧
      NativeEstimates K ε C1 C2 C1s C2s qTail qsTail τmin Ctime Cgrad ∧
      pF.modelAccuracy ≤ εcut ∧ Dcut ≤ pF.modelRadius ∧ mcut ≤ pF.modelOrder ∧
      (∀ i : Fin K.eventCount,
        pF.delta (K.time i.succ) ≤ δcut ∧
        pF.neckRadius (K.time i.succ) ≤ min ρ ρcut) ∧
      (∀ t : ℝ, HEq
        (J.toHistory.stageMetric (Fin.last J.eventCount)
          (t + H.time (Fin.last H.eventCount)))
        (K.toHistory.stageMetric (Fin.last K.eventCount) t)) ∧
      (∀ i : Fin H.eventCount,
        HEq (records (i.castLE I.count_le)).nominalRadius (old i).nominalRadius ∧
        HEq (records (i.castLE I.count_le)).delta (old i).delta ∧
        HEq (records (i.castLE I.count_le)).order (old i).order ∧
        HEq (records (i.castLE I.count_le)).neck (old i).neck ∧
        HEq (records (i.castLE I.count_le)).static (old i).static) ∧
      ∀ i : Fin K.eventCount,
        HEq (records (A.eventIndex i)).nominalRadius (native i).nominalRadius ∧
        HEq (records (A.eventIndex i)).delta (native i).delta ∧
        HEq (records (A.eventIndex i)).order (native i).order ∧
        HEq (records (A.eventIndex i)).neck (native i).neck := by
  obtain ⟨εbar, hεbar, analytic⟩ := exists_uniform_observation_estimate_packet.{u}
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hε hε11 hεbar'
  obtain ⟨C1, C2, C1s, C2s, Cs, τmin, Ctime, Cgrad,
    hC1, hC2, hC1s, hC2s, hCs, hτmin, analytic⟩ := analytic ε hε hε11 hεbar'
  refine ⟨C1, C2, C1s, C2s, Cs, τmin, Ctime, Cgrad,
    hC1, hC2, hC1s, hC2s, hCs, hτmin, ?_⟩
  intro P g B hB
  obtain ⟨εLocal, κLocal, hεLocal, _, hκLocal, prepare⟩ :=
    exists_prepared_geometric_observation_extension_before_quality P g B hB
  obtain ⟨κOld, hκOld, enlargeOld⟩ :=
    exists_noncollapsedBefore_radius_enlargement hκLocal hεLocal hε
  obtain ⟨qOld, qsOld, δOld, ρOld, εOld, DOld, mOld,
    hqOld, hqsOld, hqsOldC, hδOld, hρOld, hεOld, hDOld, oldAnalytic⟩ :=
    analytic P g B κOld hB hκOld
  obtain ⟨p₀, δb, ρb, hδb, hδbOld, hρb, hρbOld,
    haccOld, hDOldClass, hmOldClass, hcap, hrecOld, extend⟩ :=
    prepare δOld ρOld εOld DOld mOld hδOld hρOld hεOld hDOld
  refine ⟨p₀, δb, ρb, κOld, qOld, qsOld, hδb, hρb, hκOld,
    hqOld, hqsOld, hqsOldC, hcap, ?_⟩
  intro H IH p old hHB hold hcontrol R hR
  obtain ⟨εK, κK, κJ, hεK, _, hκK, _, make⟩ := extend H IH p old hHB hold hcontrol
  obtain ⟨κTail, hκTail, enlargeTail⟩ :=
    exists_noncollapsedBefore_radius_enlargement hκK hεK hε
  have hBtail : 0 < B - H.time (Fin.last H.eventCount) :=
    sub_pos.mpr (H.time_le_horizon.trans_lt hHB)
  obtain ⟨qTail, qsTail, δTail, ρTail, εTail, DTail, mTail,
    hqTail, hqsTail, hqsTailC, hδTail, hρTail, hεTail, hDTail, tailAnalytic⟩ :=
    analytic (H.stage (Fin.last H.eventCount)) (H.initialMetric (Fin.last H.eventCount))
      (B - H.time (Fin.last H.eventCount)) κTail hBtail hκTail
  obtain ⟨ρ, hρ, hρR, hqsρ⟩ := exists_canonical_radius_below hR (hqTail.trans_le hqsTail)
  refine ⟨κTail, qTail, qsTail, ρ, hκTail, hqTail, hqsTail, hqsTailC,
    hρ, hρR, hqsρ, ?_⟩
  intro δcut ρcut εcut Dcut mcut hδcut hρcut hεcut hDcut
  obtain ⟨K, IK, pB, pF, δbound, ρbound, v, native,
    hKB, _, hcontrolK, hncK, hfixedF, hrcF, hacc, hrad, hord,
    hδbound, hδ, hρbound, hρboundLe, hrecF, hv, hfamily, hdebit,
    hwin, hrecK, hD, hm, haccPrefix, join⟩ :=
    make (min δTail δcut) (min ρTail (min ρ ρcut))
      (min εTail εcut) (max DTail Dcut) (max mTail mcut)
      (lt_min hδTail hδcut) (lt_min hρTail (lt_min hρ hρcut))
      (lt_min hεTail hεcut) (lt_max_of_lt_right hDcut)
  have hncTail := enlargeTail K K.horizon hncK
  have htailEst := tailAnalytic pB δbound ρbound
    (hfamily.2.2.2.1.symm.le.trans (hacc.trans (min_le_left _ _)))
    ((le_max_left _ _).trans (hrad.trans hfamily.2.1.le))
    ((le_max_left _ _).trans (hord.trans hfamily.2.2.1.le))
    (hδ.trans (min_le_left _ _)) (hρboundLe.trans (min_le_left _ _)) hrecF
    K IK pF native hKB.le hfamily hncTail
  let c := H.time (Fin.last H.eventCount)
  let pC := pF.withModelWindow p.modelRadius p.modelOrder p.modelAccuracy
    p.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccPrefix)
  let q := p.spliceAfter (translate_cutoff_parameters pC c) H.horizon
  obtain ⟨J, A, I, hn, records, hp, IJ, hIJ, hJB, hcontrolJ, hncJ,
    hclassJ, hncSame, hstaticJ, hmetric, hpast, hwinJ, hOld, hTail⟩ := join
  have hncOld : J.NoncollapsedBefore κOld ε J.horizon := by
    rw [hJB]
    exact enlargeOld J B hncSame
  have holdEst := oldAnalytic p₀ δb ρb haccOld hDOldClass hmOldClass
    hδbOld hρbOld hrecOld J IJ q records hJB.le hclassJ hncOld
  refine ⟨K, IK, pB, pF, δbound, ρbound, native, J, IJ, A, I, q, records,
    hKB, hJB, hIJ, hcontrolK, hcontrolJ, hfamily, hclassJ, hncTail, hncOld,
    holdEst, htailEst, hacc.trans (min_le_right _ _),
    (le_max_right _ _).trans hrad, (le_max_right _ _).trans hord,
    ?_, hmetric, hOld, ?_⟩
  · intro i
    exact ⟨(hfamily.2.2.2.2.2.2.1 i).trans (hδ.trans (min_le_right _ _)),
      (hfamily.2.2.2.2.2.2.2 i).trans (hρboundLe.trans (min_le_right _ _))⟩
  · intro i
    exact ⟨(hTail i).1, (hTail i).2.1, (hTail i).2.2.1, (hTail i).2.2.2.1⟩

/-- Prepare the new native class for a genuinely later prospective horizon,
before requesting any new fine surgery. The current extension still ends at B.
Both class views use one fixed scaffold, and the new class's uniform
noncollapse rule applies through Bfuture even though the SAME native L has
only been constructed through B. -/
theorem exists_prepared_extension_with_reserved_later_class :
    ∃ (fixed : StaticCapScaffold) (recenter εbar : ℝ), 4 ≤ recenter ∧ 0 < εbar ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ εbar →
    ∃ (C1 C2 C1s C2s Cs τmin : ℝ) (Ctime Cgrad : ℝ≥0),
      1 ≤ C1 ∧ 1 ≤ C2 ∧ 1 ≤ C1s ∧ 1 ≤ C2s ∧ 1 ≤ Cs ∧ 0 < τmin ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ), 0 < B →
    ∃ (p₀ : CutoffParameters) (δb ρb κOld qOld qsOld : ℝ),
      p₀.fixed = fixed ∧ p₀.recenterConstant = recenter ∧
      0 < δb ∧ 0 < ρb ∧ 0 < κOld ∧ 0 < qOld ∧ qOld ≤ qsOld ∧ qsOld ≤ Cs * qOld ∧
    ∀ (H : RetainedCoreHistory.{u}) (IH : InitialIdentification P g H.toHistory)
      (p : CutoffParameters)
      (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
      H.horizon < B → H.IsCanonicalCutoffRecordFamily p₀ δb ρb old →
      HistoryEventControl H →
    ∀ Bfuture R : ℝ, B < Bfuture → 0 < R →
    ∃ (pNew : CutoffParameters) (δNew ρNew κNew qNew qsNew ρ εClass κClass : ℝ),
      pNew.fixed = fixed ∧ pNew.recenterConstant = recenter ∧
      0 < δNew ∧ 0 < ρNew ∧ 0 < κNew ∧ 0 < qNew ∧
      qNew ≤ qsNew ∧ qsNew ≤ Cs * qNew ∧
      0 < ρ ∧ ρ ≤ R ∧ qsNew ≤ (ρ ^ 2)⁻¹ ∧
      0 < εClass ∧ εClass < 1 / 11 ∧ 0 < κClass ∧
      PreparedGeometricObservationExtension
        (H.stage (Fin.last H.eventCount)) (H.initialMetric (Fin.last H.eventCount))
        (Bfuture - H.time (Fin.last H.eventCount)) εClass κClass pNew δNew ρNew ∧
      (∀ (L : RetainedCoreHistory.{u})
        (_IL : InitialIdentification (H.stage (Fin.last H.eventCount))
          (H.initialMetric (Fin.last H.eventCount)) L.toHistory)
        (pL : CutoffParameters)
        (records : ∀ i : Fin L.eventCount, GeometricCutoffRecord L.toHistory i pL),
        L.horizon ≤ Bfuture - H.time (Fin.last H.eventCount) →
        L.IsCanonicalCutoffRecordFamily pNew δNew ρNew records →
        L.NoncollapsedBefore κNew ε L.horizon) ∧
      (∀ (L : RetainedCoreHistory.{u})
        (_IL : InitialIdentification (H.stage (Fin.last H.eventCount))
          (H.initialMetric (Fin.last H.eventCount)) L.toHistory)
        (pL : CutoffParameters)
        (records : ∀ i : Fin L.eventCount, GeometricCutoffRecord L.toHistory i pL),
        L.horizon ≤ Bfuture - H.time (Fin.last H.eventCount) →
        L.IsCanonicalCutoffRecordFamily pNew δNew ρNew records →
        NativeEstimates L ε C1 C2 C1s C2s qNew qsNew τmin Ctime Cgrad) ∧
    ∀ (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ),
      0 < δcut → 0 < ρcut → 0 < εcut → 0 < Dcut →
    ∃ (L : RetainedCoreHistory.{u})
      (_IL : InitialIdentification (H.stage (Fin.last H.eventCount))
        (H.initialMetric (Fin.last H.eventCount)) L.toHistory)
      (pF pReserve : CutoffParameters)
      (native : ∀ i : Fin L.eventCount, GeometricCutoffRecord L.toHistory i pF)
      (reserved : ∀ i : Fin L.eventCount, GeometricCutoffRecord L.toHistory i pReserve)
      (J : RetainedCoreHistory.{u}) (IJ : InitialIdentification P g J.toHistory)
      (A : AffineEventPrefix L J (H.time (Fin.last H.eventCount)) H.eventCount
        (Fin.last L.eventCount))
      (I : RawInitialPrefix H J) (q : CutoffParameters)
      (records : ∀ i : Fin J.eventCount, GeometricCutoffRecord J.toHistory i q),
      L.horizon = B - H.time (Fin.last H.eventCount) ∧ J.horizon = B ∧ IH.IsPrefixOf IJ ∧
      HistoryEventControl L ∧ HistoryEventControl J ∧
      L.IsCanonicalCutoffRecordFamily pNew δNew ρNew reserved ∧
      J.IsCanonicalCutoffRecordFamily p₀ δb ρb records ∧
      L.NoncollapsedBefore κNew ε L.horizon ∧ J.NoncollapsedBefore κOld ε J.horizon ∧
      NativeEstimates J ε C1 C2 C1s C2s qOld qsOld τmin Ctime Cgrad ∧
      NativeEstimates L ε C1 C2 C1s C2s qNew qsNew τmin Ctime Cgrad ∧
      pF.modelAccuracy ≤ εcut ∧ Dcut ≤ pF.modelRadius ∧ mcut ≤ pF.modelOrder ∧
      (∀ i : Fin L.eventCount,
        pF.delta (L.time i.succ) ≤ δcut ∧
        pF.neckRadius (L.time i.succ) ≤ min ρ ρcut) ∧
      (∀ t : ℝ, HEq
        (J.toHistory.stageMetric (Fin.last J.eventCount)
          (t + H.time (Fin.last H.eventCount)))
        (L.toHistory.stageMetric (Fin.last L.eventCount) t)) ∧
      (∀ i : Fin H.eventCount,
        HEq (records (i.castLE I.count_le)).nominalRadius (old i).nominalRadius ∧
        HEq (records (i.castLE I.count_le)).delta (old i).delta ∧
        HEq (records (i.castLE I.count_le)).order (old i).order ∧
        HEq (records (i.castLE I.count_le)).neck (old i).neck ∧
        HEq (records (i.castLE I.count_le)).static (old i).static) ∧
      (∀ i : Fin L.eventCount,
        HEq (records (A.eventIndex i)).nominalRadius (native i).nominalRadius ∧
        HEq (records (A.eventIndex i)).delta (native i).delta ∧
        HEq (records (A.eventIndex i)).order (native i).order ∧
        HEq (records (A.eventIndex i)).neck (native i).neck) ∧
      ∃ (hwinNew : ∀ i b, ((native i).static b).hasLinkedCanonicalWindow_C12X)
        (_hrecKNew : RecordHypFar_C12X (5 / 4) L native)
        (hDNew : pNew.modelRadius ≤ pF.modelRadius)
        (hmNew : pNew.modelOrder ≤ pF.modelOrder)
        (haccNew : pF.modelAccuracy ≤ pNew.modelAccuracy),
        pReserve = pF.withModelWindow pNew.modelRadius pNew.modelOrder pNew.modelAccuracy
          pNew.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccNew) ∧
        ∀ i : Fin L.eventCount, HEq (reserved i)
          ((native i).restrictModelWindow (fun b => (hwinNew i b).hasCanonicalWindow)
              pNew.modelRadius_pos
            hDNew hmNew haccNew) := by
  obtain ⟨fixed, recenter, hrecenter, prepareClass⟩ :=
    exists_common_prepared_geometric_observation_extension_before_quality.{u}
  obtain ⟨εbar, hεbar, analytic⟩ := exists_uniform_observation_estimate_packet.{u}
  refine ⟨fixed, recenter, εbar, hrecenter, hεbar, ?_⟩
  intro ε hε hε11 hεbar'
  obtain ⟨C1, C2, C1s, C2s, Cs, τmin, Ctime, Cgrad,
    hC1, hC2, hC1s, hC2s, hCs, hτmin, analytic⟩ := analytic ε hε hε11 hεbar'
  refine ⟨C1, C2, C1s, C2s, Cs, τmin, Ctime, Cgrad,
    hC1, hC2, hC1s, hC2s, hCs, hτmin, ?_⟩
  intro P g B hB
  obtain ⟨εLocal, κLocal, hεLocal, _, hκLocal, prepareOld⟩ := prepareClass P g B hB
  obtain ⟨κOld, hκOld, enlargeOld⟩ :=
    exists_noncollapsedBefore_radius_enlargement hκLocal hεLocal hε
  obtain ⟨qOld, qsOld, δOld, ρOld, εOld, DOld, mOld,
    hqOld, hqsOld, hqsOldC, hδOld, hρOld, hεOld, hDOld, oldAnalytic⟩ :=
    analytic P g B κOld hB hκOld
  obtain ⟨p₀, δb, ρb, hfixedOld, hrcOld, hδb, hδbOld, hρb, hρbOld,
    haccOld, hDOldClass, hmOldClass, hcapOld, hrecOld, hncOldClass, extend⟩ :=
    prepareOld δOld ρOld εOld DOld mOld hδOld hρOld hεOld hDOld
  refine ⟨p₀, δb, ρb, κOld, qOld, qsOld, hfixedOld, hrcOld,
    hδb, hρb, hκOld, hqOld, hqsOld, hqsOldC, ?_⟩
  intro H IH p old hHB hold hcontrol Bfuture R hBfuture hR
  have hFuture : 0 < Bfuture - H.time (Fin.last H.eventCount) :=
    sub_pos.mpr (H.time_le_horizon.trans_lt (hHB.trans hBfuture))
  obtain ⟨εNewLocal, κNewLocal, hεNewLocal, hεNewLocal11, hκNewLocal, prepareNew⟩ :=
    prepareClass (H.stage (Fin.last H.eventCount)) (H.initialMetric (Fin.last H.eventCount))
      (Bfuture - H.time (Fin.last H.eventCount)) hFuture
  obtain ⟨κNew, hκNew, enlargeNew⟩ :=
    exists_noncollapsedBefore_radius_enlargement hκNewLocal hεNewLocal hε
  obtain ⟨qNew, qsNew, δAnalNew, ρAnalNew, εAnalNew, DAnalNew, mAnalNew,
    hqNew, hqsNew, hqsNewC, hδAnalNew, hρAnalNew, hεAnalNew, hDAnalNew, newAnalytic⟩ :=
    analytic (H.stage (Fin.last H.eventCount)) (H.initialMetric (Fin.last H.eventCount))
      (Bfuture - H.time (Fin.last H.eventCount)) κNew hFuture hκNew
  obtain ⟨pNew, δNew, ρNew, hfixedNew, hrcNew, hδNew, hδNewAnal, hρNew, hρNewAnal,
    haccNewAnal, hDNewAnal, hmNewAnal, hcapNew, hrecNew, hncNewClass, extendNew⟩ :=
    prepareNew δAnalNew ρAnalNew εAnalNew DAnalNew mAnalNew
      hδAnalNew hρAnalNew hεAnalNew hDAnalNew
  have newNoncollapse : ∀ (L : RetainedCoreHistory.{u})
      (IL : InitialIdentification (H.stage (Fin.last H.eventCount))
        (H.initialMetric (Fin.last H.eventCount)) L.toHistory)
      (pL : CutoffParameters)
      (records : ∀ i : Fin L.eventCount, GeometricCutoffRecord L.toHistory i pL),
      L.horizon ≤ Bfuture - H.time (Fin.last H.eventCount) →
      L.IsCanonicalCutoffRecordFamily pNew δNew ρNew records →
      L.NoncollapsedBefore κNew ε L.horizon := by
    intro L IL pL records hLB hclass
    exact enlargeNew L L.horizon (hncNewClass L IL pL records hLB hclass)
  have newEstimates : ∀ (L : RetainedCoreHistory.{u})
      (IL : InitialIdentification (H.stage (Fin.last H.eventCount))
        (H.initialMetric (Fin.last H.eventCount)) L.toHistory)
      (pL : CutoffParameters)
      (records : ∀ i : Fin L.eventCount, GeometricCutoffRecord L.toHistory i pL),
      L.horizon ≤ Bfuture - H.time (Fin.last H.eventCount) →
      L.IsCanonicalCutoffRecordFamily pNew δNew ρNew records →
      NativeEstimates L ε C1 C2 C1s C2s qNew qsNew τmin Ctime Cgrad := by
    intro L IL pL records hLB hclass
    exact newAnalytic pNew δNew ρNew haccNewAnal hDNewAnal hmNewAnal
      hδNewAnal hρNewAnal hrecNew L IL pL records hLB hclass
      (newNoncollapse L IL pL records hLB hclass)
  obtain ⟨ρ, hρ, hρR, hqsρ⟩ := exists_canonical_radius_below hR (hqNew.trans_le hqsNew)
  refine ⟨pNew, δNew, ρNew, κNew, qNew, qsNew, ρ, εNewLocal, κNewLocal,
    hfixedNew, hrcNew, hδNew, hρNew, hκNew, hqNew, hqsNew, hqsNewC, hρ, hρR, hqsρ,
    hεNewLocal, hεNewLocal11, hκNewLocal, extendNew, newNoncollapse, newEstimates, ?_⟩
  intro δcut ρcut εcut Dcut mcut hδcut hρcut hεcut hDcut
  obtain ⟨εK, κK, κJ, _, _, _, _, make⟩ := extend H IH p old hHB hold hcontrol
  obtain ⟨L, IL, pB, pF, δbound, ρbound, v, native,
    hLB, _, hcontrolL, hncL, hfixedF, hrcF, hacc, hrad, hord,
    hδbound, hδ, hρbound, hρboundLe, hrecF, hv, hfamily, hdebit,
    hwin, hrecK, hD, hm, haccPrefix, join⟩ :=
    make (min δNew δcut) (min ρNew (min ρ ρcut))
      (min pNew.modelAccuracy εcut) (max pNew.modelRadius Dcut) (max pNew.modelOrder mcut)
      (lt_min hδNew hδcut) (lt_min hρNew (lt_min hρ hρcut))
      (lt_min pNew.modelAccuracy_pos hεcut) (lt_max_of_lt_right hDcut)
  have hDNew : pNew.modelRadius ≤ pF.modelRadius := (le_max_left _ _).trans hrad
  have hmNew : pNew.modelOrder ≤ pF.modelOrder := (le_max_left _ _).trans hord
  have haccNew : pF.modelAccuracy ≤ pNew.modelAccuracy := hacc.trans (min_le_left _ _)
  let pReserve := pF.withModelWindow pNew.modelRadius pNew.modelOrder pNew.modelAccuracy
    pNew.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccNew)
  let reserved := fun i : Fin L.eventCount => (native i).restrictModelWindow
    (fun b => (hwin i b).hasCanonicalWindow) pNew.modelRadius_pos hDNew hmNew haccNew
  have hclassNew : L.IsCanonicalCutoffRecordFamily pNew δNew ρNew reserved := by
    refine ⟨hfixedF.trans (hold.1.trans (hfixedOld.trans hfixedNew.symm)),
      rfl, rfl, rfl,
      hrcF.trans (hold.2.2.2.2.1.trans (hrcOld.trans hrcNew.symm)), ?_, ?_, ?_⟩
    · intro i b
      exact (native i).hasCanonicalWindow_restrictModelWindow
          (fun b => (hwin i b).hasCanonicalWindow)
        pNew.modelRadius_pos hDNew hmNew haccNew hcapNew b
    · intro i
      exact (hfamily.2.2.2.2.2.2.1 i).trans (hδ.trans (min_le_left _ _))
    · intro i
      exact (hfamily.2.2.2.2.2.2.2 i).trans (hρboundLe.trans (min_le_left _ _))
  have hLFuture : L.horizon ≤ Bfuture - H.time (Fin.last H.eventCount) :=
    hLB.trans_le (sub_le_sub_right hBfuture.le _)
  have hncNew := newNoncollapse L IL pReserve reserved hLFuture hclassNew
  have hnewEst := newEstimates L IL pReserve reserved hLFuture hclassNew
  let c := H.time (Fin.last H.eventCount)
  let pC := pF.withModelWindow p.modelRadius p.modelOrder p.modelAccuracy
    p.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccPrefix)
  let q := p.spliceAfter (translate_cutoff_parameters pC c) H.horizon
  obtain ⟨J, A, I, hn, records, hp, IJ, hIJ, hJB, hcontrolJ, hncJ,
    hclassJ, hncSame, hstaticJ, hmetric, hpast, hwinJ, hOld, hTail⟩ := join
  have hncOld : J.NoncollapsedBefore κOld ε J.horizon := by
    rw [hJB]
    exact enlargeOld J B hncSame
  have holdEst := oldAnalytic p₀ δb ρb haccOld hDOldClass hmOldClass
    hδbOld hρbOld hrecOld J IJ q records hJB.le hclassJ hncOld
  refine ⟨L, IL, pF, pReserve, native, reserved, J, IJ, A, I, q, records,
    hLB, hJB, hIJ, hcontrolL, hcontrolJ, hclassNew, hclassJ, hncNew, hncOld,
    holdEst, hnewEst, hacc.trans (min_le_right _ _),
    (le_max_right _ _).trans hrad, (le_max_right _ _).trans hord,
    ?_, hmetric, hOld, ?_, ?_⟩
  · intro i
    exact ⟨(hfamily.2.2.2.2.2.2.1 i).trans (hδ.trans (min_le_right _ _)),
      (hfamily.2.2.2.2.2.2.2 i).trans (hρboundLe.trans (min_le_right _ _))⟩
  · intro i
    exact ⟨(hTail i).1, (hTail i).2.1, (hTail i).2.2.1, (hTail i).2.2.2.1⟩
  · exact ⟨hwin, hrecK, hDNew, hmNew, haccNew, rfl, fun _ => HEq.rfl⟩

end GC.GeneralFlow
