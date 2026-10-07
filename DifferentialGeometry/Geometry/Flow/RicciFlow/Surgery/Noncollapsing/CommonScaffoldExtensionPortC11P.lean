import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.CommonScaffoldObservation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.AffineJoinNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordModelRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CutoffRecordConcatenation

/-!
# S-CH11-FIX11 port of astra `CommonScaffoldExtension`（`PortC11P`）

来源：donor `CommonScaffoldExtension.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补
（no statement / definition / proof idea altered；不加 `set_option`）：
* 3 处陈述里的 `StandardCap.transitionEnd` unknown identifier（本树此处 `StandardCap` 不解析到
  `PDE.RicciFlow.StandardCap`）→ 全名 `DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd`；
* 5 个只在 `∃` 陈述里出现、证明不引用的 binder（`I` ×2、`hp` ×3）加 `_` 前缀
  （unusedVariables；binder 名不改变陈述）。

原路径 `CommonScaffoldExtension` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff NNReal ENNReal

namespace GC.GeneralFlow

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

/-- Extend an actual marked history to any later observation time, retaining
its selected records and parameter functions. Only the new tail's static view
is restricted; its fine records, noncollapse and compact debits are also kept.
The positive local and joined coefficients precede the requested quality.
The raw initial prefix is the one from the same final concatenation. -/
theorem exists_common_scaffold_extension_with_raw_prefix_with_distance_scalars :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧
    ∃ (fixed : StaticCapScaffold) (recenter : ℝ),
    (4 ≤ recenter ∧ ∃ (A : ℝ) (hA : 0 < A),
      fixed = StaticCapScaffold.ofCollarLength A hA ∧
      DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticCollarAdmits.{0, 0, u} A hA) ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric)
      (H : RetainedCoreHistory.{u}) (IH : InitialIdentification P g H.toHistory)
      (pH : CutoffParameters)
      (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i pH),
      pH.fixed = fixed → pH.recenterConstant = recenter →
      DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd < pH.modelRadius + 1 →
      HistoryEventControl H → (∀ i b, ((old i).static b).hasCanonicalWindow) →
    ∀ (εH κH : ℝ), 0 < εH → 0 < κH →
      H.NoncollapsedBefore κH εH H.horizon →
    ∀ T : ℝ, H.horizon < T →
    ∃ εK κK κJ : ℝ, 0 < εK ∧ εK < 1 / 11 ∧ 0 < κK ∧ 0 < κJ ∧
    ∀ (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ),
      0 < δcut → 0 < ρcut → 0 < εcut → 0 < Dcut →
    ∃ (K : RetainedCoreHistory.{u})
      (IK : InitialIdentification (H.stage (Fin.last H.eventCount))
        (H.initialMetric (Fin.last H.eventCount)) K.toHistory)
      (p₀ pF : CutoffParameters) (δbound ρbound v : ℝ)
      (fine : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pF),
      K.horizon = T - H.time (Fin.last H.eventCount) ∧
      (InitialIdentification.atZero (H.stage (Fin.last H.eventCount))
        (H.initialMetric (Fin.last H.eventCount))).IsPrefixOf IK ∧
      (∀ i : Fin K.eventCount, (K.toHistory.event i).HasUniformDistanceScalar Cdist) ∧
        HistoryEventControl K ∧ K.NoncollapsedBefore κK εK K.horizon ∧
      pF.fixed = fixed ∧ pF.recenterConstant = recenter ∧
      pF.modelAccuracy ≤ εcut ∧ Dcut ≤ pF.modelRadius ∧ mcut ≤ pF.modelOrder ∧
      0 < δbound ∧ δbound ≤ δcut ∧ 0 < ρbound ∧ ρbound ≤ ρcut ∧
      p₀.recenterConstant * δbound ≤ 1 / 2 ∧ 0 < v ∧
      K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound fine ∧
      (∀ i : Fin K.eventCount,
        ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
          riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
              (K.coreEvent i).outputMetric univ +
            ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
            (K.coreEvent i).terminal.metric F) ∧
      ∃ (hwin : ∀ i b, ((fine i).static b).hasLinkedCanonicalWindow_C12X)
        (_hrecK : RecordHypFar_C12X (5 / 4) K fine)
        (hD : pH.modelRadius ≤ pF.modelRadius)
        (hm : pH.modelOrder ≤ pF.modelOrder)
        (hacc : pF.modelAccuracy ≤ pH.modelAccuracy),
        let c := H.time (Fin.last H.eventCount)
        let pC := pF.withModelWindow pH.modelRadius pH.modelOrder pH.modelAccuracy
          pH.modelRadius_pos (pF.modelAccuracy_pos.trans_le hacc)
        let coarse : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pC :=
          fun i => (fine i).restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
            pH.modelRadius_pos hD hm hacc
        let q := pH.spliceAfter (translate_cutoff_parameters pC c) H.horizon
        ∃ (J : RetainedCoreHistory.{u})
          (A : AffineEventPrefix K J c H.eventCount (Fin.last K.eventCount))
          (_I : RawInitialPrefix H J)
          (hn : H.eventCount ≤ J.eventCount)
          (records : ∀ i : Fin J.eventCount, GeometricCutoffRecord J.toHistory i q)
          (_hp : H.toHistory.IsPrefixOf J.toHistory)
          (IJ : InitialIdentification P g J.toHistory),
          IH.IsPrefixOf IJ ∧ J.horizon = T ∧ HistoryEventControl J ∧
          J.NoncollapsedBefore κJ εH T ∧
          (q.fixed = pH.fixed ∧ q.modelRadius = pH.modelRadius ∧
            q.modelOrder = pH.modelOrder ∧ q.modelAccuracy = pH.modelAccuracy ∧
            q.recenterConstant = pH.recenterConstant) ∧
          (∀ t : ℝ, HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
            (K.toHistory.stageMetric (Fin.last K.eventCount) t)) ∧
          (∀ t : ℝ, t ≤ H.horizon → q.delta t = pH.delta t ∧
            q.neckRadius t = pH.neckRadius t ∧ q.protectedRadius t = pH.protectedRadius t) ∧
          (∀ i b, ((records i).static b).hasCanonicalWindow) ∧
          (∀ i : Fin H.eventCount,
            HEq (records (i.castLE hn)).nominalRadius (old i).nominalRadius ∧
            HEq (records (i.castLE hn)).delta (old i).delta ∧
            HEq (records (i.castLE hn)).order (old i).order ∧
            HEq (records (i.castLE hn)).neck (old i).neck ∧
            HEq (records (i.castLE hn)).static (old i).static) ∧
          ∀ i : Fin K.eventCount,
            HEq (records (A.eventIndex i)).nominalRadius (fine i).nominalRadius ∧
            HEq (records (A.eventIndex i)).delta (fine i).delta ∧
            HEq (records (A.eventIndex i)).order (fine i).order ∧
            HEq (records (A.eventIndex i)).neck (fine i).neck ∧
            HEq (records (A.eventIndex i)).static
              (fun b => translate_presented_static_cap (K.coreEvent i) c ((coarse i).static b)) := by
  obtain ⟨Cdist, hCdist, fixed, recenter, hrecenter, make⟩ :=
    exists_common_scaffold_noncollapsed_geometric_observation_before_quality_with_radial_coordinates_with_distance_scalars.{u}
  refine ⟨Cdist, hCdist, fixed, recenter, hrecenter, ?_⟩
  intro P g H IH pH old hpfH hpcH hcap hcontrolH hwinH εH κH hεH hκH hncH T hT
  let c := H.time (Fin.last H.eventCount)
  have hlocal : 0 < T - c := sub_pos.mpr (H.time_le_horizon.trans_lt hT)
  obtain ⟨εK, κK, hεK, hεK11, hκK, make⟩ :=
    make (H.stage (Fin.last H.eventCount)) (H.initialMetric (Fin.last H.eventCount))
      (T - c) hlocal
  obtain ⟨κJ, hκJ, hjoin⟩ := exists_noncollapsed_affine_join
    (H.stage (Fin.last H.eventCount)) (H.initialMetric (Fin.last H.eventCount))
    hεH hεK hκH hκK
  refine ⟨εK, κK, κJ, hεK, hεK11, hκK, hκJ, ?_⟩
  intro δcut ρcut εcut Dcut mcut hδcut hρcut hεcut hDcut
  obtain ⟨p₀, δbound, ρbound, v, hfixedK, hrcK, haccK, hDK, hmK,
    hδK, hρK, hrec, hδbound, hρbound, hv, K, IK, pF, fine,
    hKB, hIK, hDistanceK, hcontrolK, hfamilyK, hradK, hrecK, hncK, hdebitK⟩ :=
    make δcut ρcut (min pH.modelAccuracy εcut)
      (max pH.modelRadius Dcut) (max pH.modelOrder mcut)
      hδcut hρcut (lt_min pH.modelAccuracy_pos hεcut)
      (lt_max_of_lt_right hDcut)
  rw [← hKB] at hncK
  have hpfK : pF.fixed = fixed := hfamilyK.1.trans hfixedK
  have hpcK : pF.recenterConstant = recenter := hfamilyK.2.2.2.2.1.trans hrcK
  have haccPair := le_min_iff.mp (hfamilyK.2.2.2.1.le.trans haccK)
  have hDPair := max_le_iff.mp (hDK.trans hfamilyK.2.1.symm.le)
  have hmPair := max_le_iff.mp (hmK.trans hfamilyK.2.2.1.symm.le)
  have hwinK := hfamilyK.2.2.2.2.2.1
  refine ⟨K, IK, p₀, pF, δbound, ρbound, v, fine, hKB, hIK, hDistanceK, hcontrolK, hncK,
    hpfK, hpcK, haccPair.2, hDPair.2, hmPair.2, hδbound, hδK, hρbound, hρK,
    hrec, hv, hfamilyK, hdebitK, (fun i b => (hradK i b).2), hrecK, hDPair.1, hmPair.1, haccPair.1, ?_⟩
  let pC := pF.withModelWindow pH.modelRadius pH.modelOrder pH.modelAccuracy
    pH.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccPair.1)
  let coarse : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pC :=
    fun i => (fine i).restrictModelWindow (hwinK i) pH.modelRadius_pos
      hDPair.1 hmPair.1 haccPair.1
  have hs : K.stage 0 = H.stage (Fin.last H.eventCount) := by
    simpa only [Fin.cast_zero, ObservedHistory.restrict_stage_zero]
      using hIK.1.presentation.stage_eq 0
  have hmetric : HEq (K.initialMetric 0) (H.initialMetric (Fin.last H.eventCount)) := by
    simpa only [Fin.cast_zero, ObservedHistory.restrict_initialMetric_zero,
      ObservedHistory.restrict_stage_zero] using hIK.1.presentation.initialMetric_heq 0
  have hsum : K.horizon + c = T := by rw [hKB]; ring
  have hreach : H.horizon ≤ K.horizon + c := hT.le.trans_eq hsum.symm
  have hstatic : pC.fixed = pH.fixed ∧ pC.modelRadius = pH.modelRadius ∧
      pC.modelOrder = pH.modelOrder ∧ pC.modelAccuracy = pH.modelAccuracy ∧
      pC.recenterConstant = pH.recenterConstant :=
    ⟨hpfK.trans hpfH.symm, rfl, rfl, rfl, hpcK.trans hpcH.symm⟩
  have hcoarse : ∀ i b, ((coarse i).static b).hasCanonicalWindow := by
    intro i b
    exact (fine i).hasCanonicalWindow_restrictModelWindow (hwinK i)
      pH.modelRadius_pos hDPair.1 hmPair.1 haccPair.1 hcap b
  obtain ⟨J, A, I, hn, records, hp, hJB, hcontrolJ, hfinal, hpast, hwinJ, hOld, hTail⟩ :=
    finite_history_concatenation_with_cutoff_records_and_raw_prefix H K hcontrolH hcontrolK
      hs hmetric hreach old coarse hstatic hwinH hcoarse
  obtain ⟨IJ, hIJ⟩ := marking_of_actual_prefix IH hp
  have hJT : J.horizon = T := hJB.trans hsum
  have hncJ := hjoin H K J IK c H.eventCount A (fun i => (hcontrolK i).1)
    hp H.time_le_horizon hJB hfinal hncH hncK
  rw [hJT] at hncJ
  refine ⟨J, A, I, hn, records, hp, IJ, hIJ, hJT, hcontrolJ, hncJ,
    ⟨rfl, rfl, rfl, rfl, rfl⟩, hfinal, hpast, hwinJ, hOld, ?_⟩
  intro i
  exact hTail i

/-- Forget only the native distance certificate from this actual producer. -/
theorem exists_common_scaffold_extension_with_raw_prefix :
    ∃ (fixed : StaticCapScaffold) (recenter : ℝ), 4 ≤ recenter ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric)
      (H : RetainedCoreHistory.{u}) (IH : InitialIdentification P g H.toHistory)
      (pH : CutoffParameters)
      (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i pH),
      pH.fixed = fixed → pH.recenterConstant = recenter →
      DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd < pH.modelRadius + 1 →
      HistoryEventControl H → (∀ i b, ((old i).static b).hasCanonicalWindow) →
    ∀ (εH κH : ℝ), 0 < εH → 0 < κH →
      H.NoncollapsedBefore κH εH H.horizon →
    ∀ T : ℝ, H.horizon < T →
    ∃ εK κK κJ : ℝ, 0 < εK ∧ εK < 1 / 11 ∧ 0 < κK ∧ 0 < κJ ∧
    ∀ (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ),
      0 < δcut → 0 < ρcut → 0 < εcut → 0 < Dcut →
    ∃ (K : RetainedCoreHistory.{u})
      (IK : InitialIdentification (H.stage (Fin.last H.eventCount))
        (H.initialMetric (Fin.last H.eventCount)) K.toHistory)
      (p₀ pF : CutoffParameters) (δbound ρbound v : ℝ)
      (fine : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pF),
      K.horizon = T - H.time (Fin.last H.eventCount) ∧
      (InitialIdentification.atZero (H.stage (Fin.last H.eventCount))
        (H.initialMetric (Fin.last H.eventCount))).IsPrefixOf IK ∧
      HistoryEventControl K ∧ K.NoncollapsedBefore κK εK K.horizon ∧
      pF.fixed = fixed ∧ pF.recenterConstant = recenter ∧
      pF.modelAccuracy ≤ εcut ∧ Dcut ≤ pF.modelRadius ∧ mcut ≤ pF.modelOrder ∧
      0 < δbound ∧ δbound ≤ δcut ∧ 0 < ρbound ∧ ρbound ≤ ρcut ∧
      p₀.recenterConstant * δbound ≤ 1 / 2 ∧ 0 < v ∧
      K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound fine ∧
      (∀ i : Fin K.eventCount,
        ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
          riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
              (K.coreEvent i).outputMetric univ +
            ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
            (K.coreEvent i).terminal.metric F) ∧
      ∃ (hwin : ∀ i b, ((fine i).static b).hasLinkedCanonicalWindow_C12X)
        (_hrecK : RecordHypFar_C12X (5 / 4) K fine)
        (hD : pH.modelRadius ≤ pF.modelRadius)
        (hm : pH.modelOrder ≤ pF.modelOrder)
        (hacc : pF.modelAccuracy ≤ pH.modelAccuracy),
        let c := H.time (Fin.last H.eventCount)
        let pC := pF.withModelWindow pH.modelRadius pH.modelOrder pH.modelAccuracy
          pH.modelRadius_pos (pF.modelAccuracy_pos.trans_le hacc)
        let coarse : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pC :=
          fun i => (fine i).restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
            pH.modelRadius_pos hD hm hacc
        let q := pH.spliceAfter (translate_cutoff_parameters pC c) H.horizon
        ∃ (J : RetainedCoreHistory.{u})
          (A : AffineEventPrefix K J c H.eventCount (Fin.last K.eventCount))
          (_I : RawInitialPrefix H J)
          (hn : H.eventCount ≤ J.eventCount)
          (records : ∀ i : Fin J.eventCount, GeometricCutoffRecord J.toHistory i q)
          (_hp : H.toHistory.IsPrefixOf J.toHistory)
          (IJ : InitialIdentification P g J.toHistory),
          IH.IsPrefixOf IJ ∧ J.horizon = T ∧ HistoryEventControl J ∧
          J.NoncollapsedBefore κJ εH T ∧
          (q.fixed = pH.fixed ∧ q.modelRadius = pH.modelRadius ∧
            q.modelOrder = pH.modelOrder ∧ q.modelAccuracy = pH.modelAccuracy ∧
            q.recenterConstant = pH.recenterConstant) ∧
          (∀ t : ℝ, HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
            (K.toHistory.stageMetric (Fin.last K.eventCount) t)) ∧
          (∀ t : ℝ, t ≤ H.horizon → q.delta t = pH.delta t ∧
            q.neckRadius t = pH.neckRadius t ∧ q.protectedRadius t = pH.protectedRadius t) ∧
          (∀ i b, ((records i).static b).hasCanonicalWindow) ∧
          (∀ i : Fin H.eventCount,
            HEq (records (i.castLE hn)).nominalRadius (old i).nominalRadius ∧
            HEq (records (i.castLE hn)).delta (old i).delta ∧
            HEq (records (i.castLE hn)).order (old i).order ∧
            HEq (records (i.castLE hn)).neck (old i).neck ∧
            HEq (records (i.castLE hn)).static (old i).static) ∧
          ∀ i : Fin K.eventCount,
            HEq (records (A.eventIndex i)).nominalRadius (fine i).nominalRadius ∧
            HEq (records (A.eventIndex i)).delta (fine i).delta ∧
            HEq (records (A.eventIndex i)).order (fine i).order ∧
            HEq (records (A.eventIndex i)).neck (fine i).neck ∧
            HEq (records (A.eventIndex i)).static
              (fun b => translate_presented_static_cap (K.coreEvent i) c ((coarse i).static b)) := by
  obtain ⟨_, _, nativeResult⟩ :=
    exists_common_scaffold_extension_with_raw_prefix_with_distance_scalars.{u}
  obtain ⟨fixed, recenter, nativeProjectionh1⟩ := nativeResult
  refine ⟨fixed, recenter, ?_⟩
  obtain ⟨nativeProjectionfield2, nativeProjectionh3⟩ := nativeProjectionh1
  refine ⟨nativeProjectionfield2.1, ?_⟩
  intro P g H IH pH old nativeProjectionx4 nativeProjectionx5 nativeProjectionx6 nativeProjectionx7
    nativeProjectionx8 εH κH nativeProjectionx9 nativeProjectionx10 nativeProjectionx11 T
    nativeProjectionx12
  have nativeProjectionh13 := @nativeProjectionh3 P g H IH pH old nativeProjectionx4
    nativeProjectionx5 nativeProjectionx6 nativeProjectionx7 nativeProjectionx8 εH κH
    nativeProjectionx9 nativeProjectionx10 nativeProjectionx11 T nativeProjectionx12
  obtain ⟨εK, κK, κJ, nativeProjectionh14⟩ := nativeProjectionh13
  refine ⟨εK, κK, κJ, ?_⟩
  obtain ⟨nativeProjectionfield15, nativeProjectionfield16, nativeProjectionfield17,
    nativeProjectionfield18, nativeProjectionh19⟩ := nativeProjectionh14
  refine ⟨nativeProjectionfield15, nativeProjectionfield16, nativeProjectionfield17,
    nativeProjectionfield18, ?_⟩
  intro δcut ρcut εcut Dcut mcut nativeProjectionx20 nativeProjectionx21 nativeProjectionx22
    nativeProjectionx23
  have nativeProjectionh24 := @nativeProjectionh19 δcut ρcut εcut Dcut mcut nativeProjectionx20
    nativeProjectionx21 nativeProjectionx22 nativeProjectionx23
  obtain ⟨K, IK, p₀, pF, δbound, ρbound, v, fine, nativeProjectionh25⟩ := nativeProjectionh24
  refine ⟨K, IK, p₀, pF, δbound, ρbound, v, fine, ?_⟩
  obtain ⟨nativeProjectionfield26, nativeProjectionfield27, nativeProjectionh28⟩ :=
    nativeProjectionh25
  refine ⟨nativeProjectionfield26, nativeProjectionfield27, ?_⟩
  exact nativeProjectionh28.2

/-- Compatibility projection of the same selected extension, omitting only
its raw initial-prefix witness. All original output data are retained. -/
theorem exists_common_scaffold_extension :
    ∃ (fixed : StaticCapScaffold) (recenter : ℝ), 4 ≤ recenter ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric)
      (H : RetainedCoreHistory.{u}) (IH : InitialIdentification P g H.toHistory)
      (pH : CutoffParameters)
      (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i pH),
      pH.fixed = fixed → pH.recenterConstant = recenter →
      DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd < pH.modelRadius + 1 →
      HistoryEventControl H → (∀ i b, ((old i).static b).hasCanonicalWindow) →
    ∀ (εH κH : ℝ), 0 < εH → 0 < κH →
      H.NoncollapsedBefore κH εH H.horizon →
    ∀ T : ℝ, H.horizon < T →
    ∃ εK κK κJ : ℝ, 0 < εK ∧ εK < 1 / 11 ∧ 0 < κK ∧ 0 < κJ ∧
    ∀ (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ),
      0 < δcut → 0 < ρcut → 0 < εcut → 0 < Dcut →
    ∃ (K : RetainedCoreHistory.{u})
      (IK : InitialIdentification (H.stage (Fin.last H.eventCount))
        (H.initialMetric (Fin.last H.eventCount)) K.toHistory)
      (p₀ pF : CutoffParameters) (δbound ρbound v : ℝ)
      (fine : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pF),
      K.horizon = T - H.time (Fin.last H.eventCount) ∧
      (InitialIdentification.atZero (H.stage (Fin.last H.eventCount))
        (H.initialMetric (Fin.last H.eventCount))).IsPrefixOf IK ∧
      HistoryEventControl K ∧ K.NoncollapsedBefore κK εK K.horizon ∧
      pF.fixed = fixed ∧ pF.recenterConstant = recenter ∧
      pF.modelAccuracy ≤ εcut ∧ Dcut ≤ pF.modelRadius ∧ mcut ≤ pF.modelOrder ∧
      0 < δbound ∧ δbound ≤ δcut ∧ 0 < ρbound ∧ ρbound ≤ ρcut ∧
      p₀.recenterConstant * δbound ≤ 1 / 2 ∧ 0 < v ∧
      K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound fine ∧
      (∀ i : Fin K.eventCount,
        ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
          riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
              (K.coreEvent i).outputMetric univ +
            ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
            (K.coreEvent i).terminal.metric F) ∧
      ∃ (hwin : ∀ i b, ((fine i).static b).hasLinkedCanonicalWindow_C12X)
        (_hrecK : RecordHypFar_C12X (5 / 4) K fine)
        (hD : pH.modelRadius ≤ pF.modelRadius)
        (hm : pH.modelOrder ≤ pF.modelOrder)
        (hacc : pF.modelAccuracy ≤ pH.modelAccuracy),
        let c := H.time (Fin.last H.eventCount)
        let pC := pF.withModelWindow pH.modelRadius pH.modelOrder pH.modelAccuracy
          pH.modelRadius_pos (pF.modelAccuracy_pos.trans_le hacc)
        let coarse : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pC :=
          fun i => (fine i).restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
            pH.modelRadius_pos hD hm hacc
        let q := pH.spliceAfter (translate_cutoff_parameters pC c) H.horizon
        ∃ (J : RetainedCoreHistory.{u})
          (A : AffineEventPrefix K J c H.eventCount (Fin.last K.eventCount))
          (hn : H.eventCount ≤ J.eventCount)
          (records : ∀ i : Fin J.eventCount, GeometricCutoffRecord J.toHistory i q)
          (_hp : H.toHistory.IsPrefixOf J.toHistory)
          (IJ : InitialIdentification P g J.toHistory),
          IH.IsPrefixOf IJ ∧ J.horizon = T ∧ HistoryEventControl J ∧
          J.NoncollapsedBefore κJ εH T ∧
          (q.fixed = pH.fixed ∧ q.modelRadius = pH.modelRadius ∧
            q.modelOrder = pH.modelOrder ∧ q.modelAccuracy = pH.modelAccuracy ∧
            q.recenterConstant = pH.recenterConstant) ∧
          (∀ t : ℝ, HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
            (K.toHistory.stageMetric (Fin.last K.eventCount) t)) ∧
          (∀ t : ℝ, t ≤ H.horizon → q.delta t = pH.delta t ∧
            q.neckRadius t = pH.neckRadius t ∧ q.protectedRadius t = pH.protectedRadius t) ∧
          (∀ i b, ((records i).static b).hasCanonicalWindow) ∧
          (∀ i : Fin H.eventCount,
            HEq (records (i.castLE hn)).nominalRadius (old i).nominalRadius ∧
            HEq (records (i.castLE hn)).delta (old i).delta ∧
            HEq (records (i.castLE hn)).order (old i).order ∧
            HEq (records (i.castLE hn)).neck (old i).neck ∧
            HEq (records (i.castLE hn)).static (old i).static) ∧
          ∀ i : Fin K.eventCount,
            HEq (records (A.eventIndex i)).nominalRadius (fine i).nominalRadius ∧
            HEq (records (A.eventIndex i)).delta (fine i).delta ∧
            HEq (records (A.eventIndex i)).order (fine i).order ∧
            HEq (records (A.eventIndex i)).neck (fine i).neck ∧
            HEq (records (A.eventIndex i)).static
              (fun b => translate_presented_static_cap (K.coreEvent i) c ((coarse i).static b)) := by
  obtain ⟨fixed, recenter, hrecenter, extend⟩ :=
    exists_common_scaffold_extension_with_raw_prefix.{u}
  refine ⟨fixed, recenter, hrecenter, ?_⟩
  intro P g H IH pH old hpfH hpcH hcap hcontrolH hwinH εH κH hεH hκH hncH T hT
  obtain ⟨εK, κK, κJ, hεK, hεK11, hκK, hκJ, make⟩ :=
    extend P g H IH pH old hpfH hpcH hcap hcontrolH hwinH εH κH hεH hκH hncH T hT
  refine ⟨εK, κK, κJ, hεK, hεK11, hκK, hκJ, ?_⟩
  intro δcut ρcut εcut Dcut mcut hδcut hρcut hεcut hDcut
  obtain ⟨K, IK, p₀, pF, δbound, ρbound, v, fine, hKB, hIK, hcontrolK, hncK,
    hpfK, hpcK, hacc, hD, hm, hδbound, hδ, hρbound, hρ, hrec, hv, hfamily, hdebit,
    hwin, hrecK, hDold, hmold, haccold, hjoined⟩ :=
    make δcut ρcut εcut Dcut mcut hδcut hρcut hεcut hDcut
  refine ⟨K, IK, p₀, pF, δbound, ρbound, v, fine, hKB, hIK, hcontrolK, hncK,
    hpfK, hpcK, hacc, hD, hm, hδbound, hδ, hρbound, hρ, hrec, hv, hfamily, hdebit,
    hwin, hrecK, hDold, hmold, haccold, ?_⟩
  obtain ⟨J, A, _, hn, records, hp, IJ, hresult⟩ := hjoined
  exact ⟨J, A, hn, records, hp, IJ, hresult⟩

end GC.GeneralFlow
