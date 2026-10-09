import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedRecordPrefix
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapse.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCutoffRecordFamily
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.SurgeryEventControl

/-!
S-CH11-FIX6 port（astra `Topology/CutoffRecordHistoryRestriction/Basic` 的 elaboration 修补，
接 O-CH11-FIX3B 的 WIP；陈述 / 定义 / 证明思路逐字不变）：
(a) `volume_lower_bound_of_stage_index`、`rm_bound_of_stage_eq` 是 `open private` 进来的 helper，
    dot-notation 不解析 → 写 opened-private 全名 `RetainedCoreHistory.…`；
(b) `noncollapsedBefore_restrict` 末尾 `exact hA2 ⟨i.val, by omega⟩ …` 先 `have h := …` 再
    `exact h`，并在 `omega` 之前补一条 `rfl` 的 eventCount 等式。
-/

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure
open scoped Manifold ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

open private RetainedCoreHistory.volume_lower_bound_of_stage_index
  RetainedCoreHistory.rm_bound_of_stage_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapse.Basic

namespace RetainedCoreHistory
variable (H : RetainedCoreHistory.{u})

private def incomingBackwardNeck_restrict
    (a : Icc (0 : ℝ) H.horizon) {i : Fin (H.restrict a).eventCount}
    {δ r : ℝ} {m : ℕ}
    {neck : NormalizedNeck ((H.restrict a).toHistory.event i).terminal.metric δ m}
    (N : IncomingBackwardNeck (H.prefixAt (H.toHistory.activeStage a)).toHistory i neck r) :
    IncomingBackwardNeck (H.restrict a).toHistory i neck r := by
  cases N
  constructor <;> assumption

/-- Restriction uses the given event records. Only their backward-history
index changes; the nominal radius, accuracy, finite order, neck and cap stay. -/
def restrictRecords (a : Icc (0 : ℝ) H.horizon) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p) :
    ∀ i : Fin (H.restrict a).eventCount, GeometricCutoffRecord (H.restrict a).toHistory i p :=
  fun i => { H.prefixRecords (H.toHistory.activeStage a) records i with
    backward := fun α => H.incomingBackwardNeck_restrict a
      ((H.prefixRecords (H.toHistory.activeStage a) records i).backward α) }

theorem restrictRecords_preserves (a : Icc (0 : ℝ) H.horizon) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (i : Fin (H.restrict a).eventCount) :
    let j := Fin.castLE (Nat.le_of_lt_succ (H.toHistory.activeStage a).isLt) i
    HEq (H.restrictRecords a records i).nominalRadius (records j).nominalRadius ∧
      HEq (H.restrictRecords a records i).delta (records j).delta ∧
      HEq (H.restrictRecords a records i).order (records j).order ∧
      HEq (H.restrictRecords a records i).neck (records j).neck ∧
      HEq (H.restrictRecords a records i).static (records j).static :=
  ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

theorem canonicalWindows_restrictRecords (a : Icc (0 : ℝ) H.horizon)
    {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hwin : ∀ i b, ((records i).static b).hasCanonicalWindow) :
    ∀ i b, ((H.restrictRecords a records i).static b).hasCanonicalWindow :=
  fun i b => hwin (Fin.castLE (Nat.le_of_lt_succ (H.toHistory.activeStage a).isLt) i) b

theorem isCanonicalCutoffRecordFamily_restrict (a : Icc (0 : ℝ) H.horizon)
    {p₀ p : CutoffParameters} {δ₀ ρ₀ : ℝ}
    {records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p}
    (hrec : H.IsCanonicalCutoffRecordFamily p₀ δ₀ ρ₀ records) :
    (H.restrict a).IsCanonicalCutoffRecordFamily p₀ δ₀ ρ₀ (H.restrictRecords a records) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hrec
  exact ⟨h1, h2, h3, h4, h5, H.canonicalWindows_restrictRecords a records h6,
    fun i => h7 (Fin.castLE (Nat.le_of_lt_succ (H.toHistory.activeStage a).isLt) i),
    fun i => h8 (Fin.castLE (Nat.le_of_lt_succ (H.toHistory.activeStage a).isLt) i)⟩

/-- Noncollapse pulls back to the actual restriction with the same coefficient
and radius. Both regular-slice and crossed-terminal controls are preserved. -/
theorem noncollapsedBefore_restrict (a : Icc (0 : ℝ) H.horizon) {κ ρ t₀ : ℝ}
    (hH : H.NoncollapsedBefore κ ρ t₀) (ha : (a : ℝ) ≤ t₀) :
    (H.restrict a).NoncollapsedBefore κ ρ a := by
  let L := H.restrict a
  let cast : Fin (L.eventCount + 1) → Fin (H.eventCount + 1) :=
    Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ (H.toHistory.activeStage a).isLt))
  have hmetric (v : Icc (0 : ℝ) L.horizon) :
      L.toHistory.stageMetric (L.toHistory.activeStage v) v =
        H.toHistory.stageMetric (cast (L.toHistory.activeStage v)) v :=
    eq_of_heq (H.toHistory.restrict_stageMetric a _ v (L.toHistory.activeStage_mem v))
  intro τ p r hτ hr hball
  obtain ⟨hr0, b, hbt, hb, htr⟩ := hball
  let τ' : Icc (0 : ℝ) H.horizon := ⟨τ, τ.2.1, τ.2.2.trans a.2.2⟩
  let b' : Icc (0 : ℝ) H.horizon := ⟨b, b.2.1, b.2.2.trans a.2.2⟩
  have hAτ : cast (L.toHistory.activeStage τ) = H.toHistory.activeStage τ' :=
    H.toHistory.restrict_activeStage a τ
  have hAb : cast (L.toHistory.activeStage b) = H.toHistory.activeStage b' :=
    H.toHistory.restrict_activeStage a b
  have hkb := L.toHistory.activeStage_mono hbt
  rw [hmetric]
  refine RetainedCoreHistory.volume_lower_bound_of_stage_index H hH τ' (hτ.trans ha)
    (cast (L.toHistory.activeStage τ)) hAτ.symm p hr0 hr b'
    hbt hb (cast (L.toHistory.activeStage b)) hAb.le
    (Fin.le_def.mpr (Fin.le_def.mp hkb)) ?_
  intro x hx
  have hx' : x ∈ riemannianBallOf
      (L.toHistory.stageMetric (L.toHistory.activeStage τ) τ) p r := by
    rw [hmetric]
    exact hx
  obtain ⟨A, hA1, hA2⟩ := htr x hx'
  refine ⟨H.backwardPointTraceOfPrefix (H.toHistory.activeStage a)
    ⟨A.point, A.endpoint_eq, A.crossing⟩, ?_, ?_⟩
  · intro v hbv hvt
    have hva : (v : ℝ) ≤ (a : ℝ) := (show (v : ℝ) ≤ τ from hvt).trans τ.2.2
    let vL : Icc (0 : ℝ) L.horizon := ⟨v, v.2.1, hva⟩
    have hAv : cast (L.toHistory.activeStage vL) = H.toHistory.activeStage v :=
      H.toHistory.restrict_activeStage a vL
    have hbv' : b ≤ vL := show (b : ℝ) ≤ v from hbv
    have hvt' : vL ≤ τ := show (v : ℝ) ≤ τ from hvt
    have h := hA1 vL hbv' hvt'
    rw [hmetric] at h
    refine RetainedCoreHistory.rm_bound_of_stage_eq _
      (m' := cast (L.toHistory.activeStage vL))
      (m := H.toHistory.activeStage v) hAv _ _
      (Fin.le_def.mpr (Fin.le_def.mp (L.toHistory.activeStage_mono hbv')))
      (Fin.le_def.mpr (Fin.le_def.mp (L.toHistory.activeStage_mono hvt'))) v r ?_
    exact h
  · intro i hi hil
    have hil' : i.val + 1 ≤ (L.toHistory.activeStage τ).val := Fin.le_def.mp hil
    have hk : (L.toHistory.activeStage τ).val < L.eventCount + 1 :=
      (L.toHistory.activeStage τ).isLt
    have hi' : (L.toHistory.activeStage b).val ≤ i.val := by
      change (cast (L.toHistory.activeStage b)).val ≤ i.val
      rw [hAb]
      exact Fin.le_def.mp hi
    have h := hA2 ⟨i.val, by
      have e1 : L.toHistory.eventCount = (H.restrict a).toHistory.eventCount := rfl
      omega⟩ (Fin.le_def.mpr hi') (Fin.le_def.mpr hil')
    exact h

end RetainedCoreHistory

theorem ObservedHistory.IsPrefixOf.restrict_right
    {H J : ObservedHistory.{u}} (h : H.IsPrefixOf J)
    (a : Icc (0 : ℝ) J.horizon) (ha : H.horizon ≤ (a : ℝ)) :
    H.IsPrefixOf (J.restrict a) := by
  refine ⟨ha, ?_⟩
  exact (J.restrict_restrict a ⟨H.horizon, H.horizon_nonneg, ha⟩).trans h.presentation

theorem InitialIdentification.IsPrefixOf.restrict_right
    {P : OrientedThreeStage.{u}} {g : P.Metric} {H J : ObservedHistory.{u}}
    {IH : InitialIdentification P g H} {IJ : InitialIdentification P g J}
    (h : IH.IsPrefixOf IJ) (a : Icc (0 : ℝ) J.horizon) (ha : H.horizon ≤ (a : ℝ)) :
    IH.IsPrefixOf (IJ.restrict a) :=
  ⟨h.1.restrict_right a ha, h.2⟩

/-- Restricting a genuine extension after the old horizon retains every
originally selected event record, with its actual index determined by the prefix. -/
theorem RetainedCoreHistory.restrictRecords_preserves_old
    {H J : RetainedCoreHistory.{u}} {pH pJ : CutoffParameters}
    (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i pH)
    (records : ∀ i : Fin J.eventCount, GeometricCutoffRecord J.toHistory i pJ)
    (hp : H.toHistory.IsPrefixOf J.toHistory) (hn : H.eventCount ≤ J.eventCount)
    (hOld : ∀ i : Fin H.eventCount,
      HEq (records (i.castLE hn)).nominalRadius (old i).nominalRadius ∧
      HEq (records (i.castLE hn)).delta (old i).delta ∧
      HEq (records (i.castLE hn)).order (old i).order ∧
      HEq (records (i.castLE hn)).neck (old i).neck ∧
      HEq (records (i.castLE hn)).static (old i).static)
    (a : Icc (0 : ℝ) J.horizon) (ha : H.horizon ≤ (a : ℝ)) :
    ∃ hn' : H.eventCount ≤ (J.restrict a).eventCount,
      ∀ i : Fin H.eventCount,
        HEq (J.restrictRecords a records (i.castLE hn')).nominalRadius (old i).nominalRadius ∧
        HEq (J.restrictRecords a records (i.castLE hn')).delta (old i).delta ∧
        HEq (J.restrictRecords a records (i.castLE hn')).order (old i).order ∧
        HEq (J.restrictRecords a records (i.castLE hn')).neck (old i).neck ∧
        HEq (J.restrictRecords a records (i.castLE hn')).static (old i).static := by
  let L := (J.restrict a).toHistory
  have hpL : H.toHistory.IsPrefixOf L := hp.restrict_right a ha
  have hn' : H.eventCount ≤ L.eventCount := by
    calc
      H.eventCount = (L.restrict ⟨H.horizon, H.horizon_nonneg, hpL.horizon_le⟩).eventCount :=
        hpL.presentation.count_eq.symm
      _ ≤ L.eventCount := Nat.le_of_lt_succ
        (L.activeStage ⟨H.horizon, H.horizon_nonneg, hpL.horizon_le⟩).isLt
  refine ⟨hn', ?_⟩
  intro i
  have hr := J.restrictRecords_preserves a records (i.castLE hn')
  have ho := hOld i
  exact ⟨hr.1.trans ho.1, hr.2.1.trans ho.2.1, hr.2.2.1.trans ho.2.2.1,
    hr.2.2.2.1.trans ho.2.2.2.1, hr.2.2.2.2.trans ho.2.2.2.2⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

theorem history_control_restrict {H : RetainedCoreHistory.{u}}
    (hH : HistoryEventControl H) (a : Icc (0 : ℝ) H.horizon) :
    HistoryEventControl (H.restrict a) := by
  intro i
  exact event_control_transport
    (ObservedHistory.restrict_stage_apply H.toHistory a i.castSucc).symm
    (ObservedHistory.restrict_stage_apply H.toHistory a i.succ).symm
    (ObservedHistory.restrict_time_apply H.toHistory a i.castSucc).symm
    (ObservedHistory.restrict_time_apply H.toHistory a i.succ).symm
    (H.coreEvent (Fin.castLE (Nat.le_of_lt_succ (H.toHistory.activeStage a).isLt) i))
    (hH (Fin.castLE (Nat.le_of_lt_succ (H.toHistory.activeStage a).isLt) i))

end GC.GeneralFlow
