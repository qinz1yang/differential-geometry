import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.CommonScaffoldExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.RegularObservationNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.BoundedHistoryEvents
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedObservationData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedDistanceData

/-!
# S-CH11-FIX11 port of astra `GeometricObservationFineQuality`（`PortC11P`）

来源：donor `GeometricObservationFineQuality.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补
（no statement / definition / proof idea altered；不加 `set_option`）：
* `exists_common_prepared_geometric_observation_extension_before_quality_with_distance_scalars`
  的陈述 `PreparedDistanceClassProvider fixed recenter Cdist` 的 universe 被自动成 `u_1`，而证明体里
  全是 `.{u}`（"constant has level params [u, u_1] but expected [u_1]" 加 4 处
  `ObservedHistory.{u}` vs `.{u_1}` 的 application mismatch）→ 陈述里写
  `PreparedDistanceClassProvider.{u}`；
* `hδi` / `hρi` 的 `have ht := A.time_eq i.succ`（目标里是 `J.time (A.eventIndex i).succ`，`ht` 里是
  `J.time ⟨H.eventCount + ↑i.succ, _⟩`，`rw [ht]` 找不到）→ 给 `ht` 加类型 ascription
  `J.time (A.eventIndex i).succ = K.time i.succ + c`（defeq）；
* 3 个 unused binder（`IL`、`I`、`hp`）加 `_` 前缀。

原路径 `GeometricObservationFineQuality` 是只 import 本文件的 re-export shim。
-/

/-! A prepared coarse class is preserved while new events receive a finer
model request. The original records are never upgraded. -/
set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff NNReal ENNReal
namespace GC.GeneralFlow
universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

private theorem splice_event_bounds
    {H K J : RetainedCoreHistory.{u}}
    (A : AffineEventPrefix K J (H.time (Fin.last H.eventCount)) H.eventCount
      (Fin.last K.eventCount)) (I : RawInitialPrefix H J)
    (hp : H.toHistory.IsPrefixOf J.toHistory)
    (p pK : CutoffParameters) (δb ρb : ℝ)
    (hOld : ∀ i : Fin H.eventCount,
      p.delta (H.time i.succ) ≤ δb ∧ p.neckRadius (H.time i.succ) ≤ ρb)
    (hNew : ∀ i : Fin K.eventCount,
      pK.delta (K.time i.succ) ≤ δb ∧ pK.neckRadius (K.time i.succ) ≤ ρb) :
    let q := p.spliceAfter
      (translate_cutoff_parameters pK (H.time (Fin.last H.eventCount))) H.horizon
    ∀ j : Fin J.eventCount,
      q.delta (J.time j.succ) ≤ δb ∧ q.neckRadius (J.time j.succ) ≤ ρb := by
  let c := H.time (Fin.last H.eventCount)
  let pT := translate_cutoff_parameters pK c
  intro q j
  by_cases hj : J.time j.succ ≤ H.horizon
  · let i : Fin H.eventCount :=
      ⟨j.val, event_index_lt_of_birth_le_prefix_horizon hp j hj⟩
    have hi : i.castLE I.count_le = j := Fin.ext rfl
    have htime : J.time j.succ = H.time i.succ := by
      rw [← hi]
      exact I.time_eq i.succ
    have he := p.spliceAfter_eval_of_le pT hj
    exact ⟨(he.1.trans (congrArg p.delta htime)).le.trans (hOld i).1,
      (he.2.1.trans (congrArg p.neckRadius htime)).le.trans (hOld i).2⟩
  · have hcount := A.count_eq
    have hjold : H.eventCount ≤ j.val := by
      by_contra h
      have hi : j.val < H.eventCount := by omega
      let i : Fin H.eventCount := ⟨j.val, hi⟩
      have he : i.castLE I.count_le = j := Fin.ext rfl
      have ht : J.time j.succ = H.time i.succ := by
        rw [← he]
        exact I.time_eq i.succ
      exact hj (ht.trans_le (H.toHistory.time_le_horizon_at i.succ))
    let i : Fin K.eventCount := ⟨j.val - H.eventCount, by omega⟩
    have hi : A.eventIndex i = j := by
      apply Fin.ext
      change H.eventCount + (j.val - H.eventCount) = j.val
      omega
    have htime : J.time j.succ = K.time i.succ + c := by
      rw [← hi]
      exact A.time_eq i.succ
    have he := p.spliceAfter_eval_of_lt pT (lt_of_not_ge hj)
    have ht := translate_cutoff_parameters_eval pK c (K.time i.succ)
      (K.toHistory.time_nonneg _)
    have hδ : q.delta (J.time j.succ) = pK.delta (K.time i.succ) := by
      rw [he.1, htime]
      exact ht.1
    have hρ : q.neckRadius (J.time j.succ) = pK.neckRadius (K.time i.succ) := by
      rw [he.2.1, htime]
      exact ht.2.1
    exact ⟨hδ.le.trans (hNew i).1, hρ.le.trans (hNew i).2⟩

/-- Choose one scaffold before every initial metric and prospective horizon.
Each prepared class exports its genuine uniform noncollapse rule for all
matching histories through that horizon, in addition to the same before-quality
extension and all its actual native witnesses. -/
theorem exists_common_prepared_geometric_observation_extension_before_quality_with_distance_scalars :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧
    ∃ (fixed : StaticCapScaffold) (recenter : ℝ),
    (4 ≤ recenter ∧ ∃ (A : ℝ) (hA : 0 < A),
      fixed = StaticCapScaffold.ofCollarLength A hA ∧
      StandardCap.StaticCollarAdmits.{0, 0, u} A hA) ∧
      PreparedDistanceClassProvider.{u} fixed recenter Cdist := by
  classical
  obtain ⟨Cdist, hCdist, fixed, recenter, hrec, extend⟩ :=
    exists_common_scaffold_extension_with_raw_prefix_with_distance_scalars.{u}
  refine ⟨Cdist, hCdist, fixed, recenter, hrec, ?_⟩
  intro P g B hB
  obtain ⟨εbar, hεbar, prepare⟩ := exists_regular_observation_noncollapsed P g
  let ε := min (1 / 22 : ℝ) εbar
  have hε : 0 < ε := lt_min (by norm_num) hεbar
  have hε11 : ε < 1 / 11 := (min_le_left _ _).trans_lt (by norm_num)
  have hrecpos : 0 < recenter := by linarith
  obtain ⟨δN, ρN, εN, DN, mN, κ,
    hδN, hρN, hεN, hDN, hκ, hnc⟩ :=
    prepare (B + 1) ε recenter (by linarith) hε hε11
      (min_le_right _ _) hrecpos
  refine ⟨ε, κ, hε, hε11, hκ, ?_⟩
  intro δcap ρcap εcapRequest DcapRequest mcapRequest hδcap hρcap hεcapRequest hDcapRequest
  let δb := min δN (min δcap (2 * recenter)⁻¹)
  let ρb := min ρN ρcap
  have hδb : 0 < δb := lt_min hδN (lt_min hδcap (by positivity))
  have hρb : 0 < ρb := lt_min hρN hρcap
  let p₀ : CutoffParameters := {
    delta := fun _ => 1 / 2
    neckRadius := fun _ => 1
    protectedRadius := fun _ => 1
    delta_pos := fun _ _ => by norm_num
    delta_lt_one := fun _ _ => by norm_num
    neckRadius_pos := fun _ _ => one_pos
    protectedRadius_pos := fun _ _ => one_pos
    fixed := fixed
    modelRadius := max DcapRequest (max DN (standardCapL + 1))
    modelRadius_pos := hDcapRequest.trans_le (le_max_left _ _)
    modelOrder := max mN mcapRequest
    modelAccuracy := min εN (min εcapRequest (1 / 2))
    modelAccuracy_pos := lt_min hεN (lt_min hεcapRequest (by norm_num))
    recenterConstant := recenter
    recenterConstant_ge_four := hrec.1 }
  have hmodel : standardCapL + 1 ≤ p₀.modelRadius :=
    (le_max_right DN (standardCapL + 1)).trans (le_max_right _ _)
  have hcap : StandardCap.transitionEnd < p₀.modelRadius + 1 := by
    have h := hmodel
    rw [standardCapL_eq_transitionEnd] at h
    linarith
  have hδrec : p₀.recenterConstant * δb ≤ 1 / 2 := by
    have hd : δb ≤ (2 * recenter)⁻¹ :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hm : δb * (2 * recenter) ≤ 1 :=
      (le_div_iff₀ (by positivity : 0 < 2 * recenter)).mp (by simpa only [one_div] using hd)
    change recenter * δb ≤ 1 / 2
    nlinarith
  have hnoncollapse (L : RetainedCoreHistory.{u})
      (IL : InitialIdentification P g L.toHistory) (pL : CutoffParameters)
      (R : ∀ i : Fin L.eventCount, GeometricCutoffRecord L.toHistory i pL)
      (hLB : L.horizon ≤ B) (hclass : L.IsCanonicalCutoffRecordFamily p₀ δb ρb R) :
      L.NoncollapsedBefore κ ε L.horizon :=
    hnc p₀ δb ρb (min_le_left _ _)
      ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _)
      (min_le_left _ _) (min_le_left _ _) le_rfl
      L IL pL R (by linarith) hclass
  refine ⟨p₀, δb, ρb, rfl, rfl, hδb, (min_le_right _ _).trans (min_le_left _ _),
    hρb, min_le_right _ _, (min_le_right _ _).trans (min_le_left _ _),
    le_max_left _ _, le_max_right _ _,
    (min_le_right _ _).trans (min_le_right _ _), hmodel, hcap, hδrec, hnoncollapse, ?_⟩
  intro H IH p old hHB hold hcontrol
  have hfixed : p.fixed = fixed := hold.1
  have hrc : p.recenterConstant = recenter := hold.2.2.2.2.1
  have hcapH : StandardCap.transitionEnd < p.modelRadius + 1 := by
    rw [hold.2.1]
    exact hcap
  have hncH := hnoncollapse H IH p old hHB.le hold
  obtain ⟨εK, κK, κJ, hεK, hεK11, hκK, hκJ, make⟩ :=
    extend P g H IH p old hfixed hrc hcapH hcontrol hold.2.2.2.2.2.1
      ε κ hε hκ hncH B hHB
  refine ⟨εK, κK, κJ, hεK, hεK11, hκK, hκJ, ?_⟩
  intro δcut ρcut εcut Dcut mcut hδcut hρcut hεcut hDcut
  obtain ⟨K, IK, pB, pF, δbound, ρbound, v, native,
    hKB, hIK, hDistanceK, hcontrolK, hncK, hfixedF, hrcF, hacc, hrad, hord,
    hδbound, hδ, hρbound, hρ, hrecF, hv, hfamily, hdebit,
    hwin, hrecK, hD, hm, haccOld, join⟩ :=
    make (min δb δcut) (min ρb ρcut) εcut Dcut mcut
      (lt_min hδb hδcut) (lt_min hρb hρcut) hεcut hDcut
  refine ⟨K, IK, pB, pF, δbound, ρbound, v, native,
    hKB, hIK, hDistanceK, hcontrolK, hncK, hfixedF.trans hfixed.symm, hrcF.trans hrc.symm, hacc, hrad, hord,
    hδbound, hδ.trans (min_le_right _ _), hρbound, hρ.trans (min_le_right _ _),
    hrecF, hv, hfamily, hdebit, hwin, hrecK, hD, hm, haccOld, ?_⟩
  let c := H.time (Fin.last H.eventCount)
  let pC := pF.withModelWindow p.modelRadius p.modelOrder p.modelAccuracy
    p.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccOld)
  let q := p.spliceAfter (translate_cutoff_parameters pC c) H.horizon
  obtain ⟨J, A, I, hn, records, hp, IJ, hIJ, hJB, hcontrolJ, hncJ,
    hstaticJ, hmetric, hpast, hwinJ, hOld, hTail⟩ := join
  have hbudget := splice_event_bounds A I hp p pC δb ρb
    (fun i => ⟨hold.2.2.2.2.2.2.1 i, hold.2.2.2.2.2.2.2 i⟩)
    (fun i => ⟨(hfamily.2.2.2.2.2.2.1 i).trans
        (hδ.trans (min_le_left _ _)),
      (hfamily.2.2.2.2.2.2.2 i).trans (hρ.trans (min_le_left _ _))⟩)
  have hclassJ : J.IsCanonicalCutoffRecordFamily p₀ δb ρb records :=
    ⟨hstaticJ.1.trans hold.1, hstaticJ.2.1.trans hold.2.1,
      hstaticJ.2.2.1.trans hold.2.2.1, hstaticJ.2.2.2.1.trans hold.2.2.2.1,
      hstaticJ.2.2.2.2.trans hold.2.2.2.2.1, hwinJ,
      fun j => (hbudget j).1, fun j => (hbudget j).2⟩
  have hncSame := hnoncollapse J IJ q records hJB.le hclassJ
  rw [hJB] at hncSame
  exact ⟨J, A, I, hn, records, hp, IJ, hIJ, hJB, hcontrolJ, hncJ,
    hclassJ, hncSame, hstaticJ, hmetric, hpast, hwinJ, hOld, hTail⟩

/-- Forget only the native distance certificate from this actual producer. -/
theorem exists_common_prepared_geometric_observation_extension_before_quality :
    ∃ (fixed : StaticCapScaffold) (recenter : ℝ), 4 ≤ recenter ∧
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
      PreparedGeometricObservationExtension P g B ε κ p₀ δb ρb := by
  obtain ⟨_, _, nativeResult⟩ :=
    exists_common_prepared_geometric_observation_extension_before_quality_with_distance_scalars.{u}
  obtain ⟨fixed, recenter, nativeProjectionh1⟩ := nativeResult
  refine ⟨fixed, recenter, ?_⟩
  obtain ⟨nativeProjectionfield2, nativeProjectionh3⟩ := nativeProjectionh1
  refine ⟨nativeProjectionfield2.1, ?_⟩
  intro P g B nativeProjectionx4
  have nativeProjectionh5 := @nativeProjectionh3 P g B nativeProjectionx4
  obtain ⟨ε, κ, nativeProjectionh6⟩ := nativeProjectionh5
  refine ⟨ε, κ, ?_⟩
  obtain ⟨nativeProjectionfield7, nativeProjectionfield8, nativeProjectionfield9,
    nativeProjectionh10⟩ := nativeProjectionh6
  refine ⟨nativeProjectionfield7, nativeProjectionfield8, nativeProjectionfield9, ?_⟩
  intro δcap ρcap εcapRequest DcapRequest mcapRequest nativeProjectionx11 nativeProjectionx12
    nativeProjectionx13 nativeProjectionx14
  have nativeProjectionh15 := @nativeProjectionh10 δcap ρcap εcapRequest DcapRequest mcapRequest
    nativeProjectionx11 nativeProjectionx12 nativeProjectionx13 nativeProjectionx14
  obtain ⟨p₀, δb, ρb, nativeProjectionh16⟩ := nativeProjectionh15
  refine ⟨p₀, δb, ρb, ?_⟩
  obtain ⟨nativeProjectionfield17, nativeProjectionfield18, nativeProjectionfield19,
    nativeProjectionfield20, nativeProjectionfield21, nativeProjectionfield22,
    nativeProjectionfield23, nativeProjectionfield24, nativeProjectionfield25, nativeProjectionh26⟩
    := nativeProjectionh16
  refine ⟨nativeProjectionfield17, nativeProjectionfield18, nativeProjectionfield19,
    nativeProjectionfield20, nativeProjectionfield21, nativeProjectionfield22,
    nativeProjectionfield23, nativeProjectionfield24, nativeProjectionfield25, ?_⟩
  obtain ⟨nativeProjectionfield27, nativeProjectionfield28, nativeProjectionfield29,
    nativeProjectionh30⟩ := ((nativeProjectionh26.2).2)
  refine ⟨nativeProjectionfield27, nativeProjectionfield28, nativeProjectionfield29, ?_⟩
  exact PreparedGeometricObservationExtensionWithDistance.forget nativeProjectionh30

/-- Compatibility projection retaining the prepared finite-class interface.
The shared scaffold and universal class rule come from one global supplier. -/
theorem exists_prepared_geometric_observation_extension_before_quality
    (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ) (hB : 0 < B) :
    ∃ ε κ : ℝ, 0 < ε ∧ ε < 1 / 11 ∧ 0 < κ ∧
    ∀ (δcap ρcap εcapRequest DcapRequest : ℝ) (mcapRequest : ℕ),
      0 < δcap → 0 < ρcap → 0 < εcapRequest → 0 < DcapRequest →
    ∃ (p₀ : CutoffParameters) (δb ρb : ℝ),
      0 < δb ∧ δb ≤ δcap ∧ 0 < ρb ∧ ρb ≤ ρcap ∧
      p₀.modelAccuracy ≤ εcapRequest ∧ DcapRequest ≤ p₀.modelRadius ∧
      mcapRequest ≤ p₀.modelOrder ∧
      StandardCap.transitionEnd < p₀.modelRadius + 1 ∧
      p₀.recenterConstant * δb ≤ 1 / 2 ∧
    ∀ (H : RetainedCoreHistory.{u}) (IH : InitialIdentification P g H.toHistory)
      (p : CutoffParameters)
      (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
      H.horizon < B → H.IsCanonicalCutoffRecordFamily p₀ δb ρb old →
      HistoryEventControl H →
    ∃ εK κK κJ : ℝ, 0 < εK ∧ εK < 1 / 11 ∧ 0 < κK ∧ 0 < κJ ∧
    ∀ (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ),
      0 < δcut → 0 < ρcut → 0 < εcut → 0 < Dcut →
    ∃ (K : RetainedCoreHistory.{u})
      (IK : InitialIdentification (H.stage (Fin.last H.eventCount))
        (H.initialMetric (Fin.last H.eventCount)) K.toHistory)
      (pB pF : CutoffParameters) (δbound ρbound v : ℝ)
      (fine : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pF),
      K.horizon = B - H.time (Fin.last H.eventCount) ∧
      (InitialIdentification.atZero (H.stage (Fin.last H.eventCount))
        (H.initialMetric (Fin.last H.eventCount))).IsPrefixOf IK ∧
      HistoryEventControl K ∧ K.NoncollapsedBefore κK εK K.horizon ∧
      pF.fixed = p.fixed ∧ pF.recenterConstant = p.recenterConstant ∧
      pF.modelAccuracy ≤ εcut ∧ Dcut ≤ pF.modelRadius ∧ mcut ≤ pF.modelOrder ∧
      0 < δbound ∧ δbound ≤ δcut ∧ 0 < ρbound ∧ ρbound ≤ ρcut ∧
      pB.recenterConstant * δbound ≤ 1 / 2 ∧ 0 < v ∧
      K.IsCanonicalCutoffRecordFamily pB δbound ρbound fine ∧
      (∀ i : Fin K.eventCount,
        ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
          riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
              (K.coreEvent i).outputMetric univ +
            ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
            (K.coreEvent i).terminal.metric F) ∧
      ∃ (hwin : ∀ i b, ((fine i).static b).hasLinkedCanonicalWindow_C12X)
        (_hrecK : RecordHypFar_C12X (5 / 4) K fine)
        (hD : p.modelRadius ≤ pF.modelRadius)
        (hm : p.modelOrder ≤ pF.modelOrder)
        (hacc : pF.modelAccuracy ≤ p.modelAccuracy),
        let c := H.time (Fin.last H.eventCount)
        let pC := pF.withModelWindow p.modelRadius p.modelOrder p.modelAccuracy
          p.modelRadius_pos (pF.modelAccuracy_pos.trans_le hacc)
        let coarse : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i pC :=
          fun i => (fine i).restrictModelWindow (fun b => (hwin i b).hasCanonicalWindow)
              p.modelRadius_pos hD hm hacc
        let q := p.spliceAfter (translate_cutoff_parameters pC c) H.horizon
        ∃ (J : RetainedCoreHistory.{u})
          (A : AffineEventPrefix K J c H.eventCount (Fin.last K.eventCount))
          (_I : RawInitialPrefix H J)
          (hn : H.eventCount ≤ J.eventCount)
          (records : ∀ i : Fin J.eventCount, GeometricCutoffRecord J.toHistory i q)
          (_hp : H.toHistory.IsPrefixOf J.toHistory)
          (IJ : InitialIdentification P g J.toHistory),
          IH.IsPrefixOf IJ ∧ J.horizon = B ∧ HistoryEventControl J ∧
          J.NoncollapsedBefore κJ ε B ∧
          J.IsCanonicalCutoffRecordFamily p₀ δb ρb records ∧
          J.NoncollapsedBefore κ ε B ∧
          (q.fixed = p.fixed ∧ q.modelRadius = p.modelRadius ∧
            q.modelOrder = p.modelOrder ∧ q.modelAccuracy = p.modelAccuracy ∧
            q.recenterConstant = p.recenterConstant) ∧
          (∀ t : ℝ, HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
            (K.toHistory.stageMetric (Fin.last K.eventCount) t)) ∧
          (∀ t : ℝ, t ≤ H.horizon → q.delta t = p.delta t ∧
            q.neckRadius t = p.neckRadius t ∧ q.protectedRadius t = p.protectedRadius t) ∧
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
  obtain ⟨fixed, recenter, _, prepare⟩ :=
    exists_common_prepared_geometric_observation_extension_before_quality.{u}
  obtain ⟨ε, κ, hε, hε11, hκ, make⟩ := prepare P g B hB
  refine ⟨ε, κ, hε, hε11, hκ, ?_⟩
  intro δcap ρcap εcapRequest DcapRequest mcapRequest hδcap hρcap hεcapRequest hDcapRequest
  obtain ⟨p₀, δb, ρb, _, _, hδb, hδcap', hρb, hρcap', hacc, hD, hm,
    hcap, hrec, _, extend⟩ :=
    make δcap ρcap εcapRequest DcapRequest mcapRequest
      hδcap hρcap hεcapRequest hDcapRequest
  exact ⟨p₀, δb, ρb, hδb, hδcap', hρb, hρcap', hacc, hD, hm, hcap, hrec, extend⟩

/-- Prepare one finite-horizon coarse class before the supplied controlled
prefix and all additional quality requests. One actual extension keeps that
class, its old records and past parameters. Finer witnesses belong to its
new events, on the same joined history and at the actual affine indices. -/
theorem exists_geometric_observation_extension_with_fine_quality
    (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ) (hB : 0 < B) :
    ∃ (p₀ : CutoffParameters) (δb ρb ε κ : ℝ),
      0 < δb ∧ 0 < ρb ∧ 0 < ε ∧ 0 < κ ∧
      StandardCap.transitionEnd < p₀.modelRadius + 1 ∧
    ∀ (H : RetainedCoreHistory.{u}) (IH : InitialIdentification P g H.toHistory)
      (p : CutoffParameters)
      (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
      H.horizon < B → H.IsCanonicalCutoffRecordFamily p₀ δb ρb old →
      HistoryEventControl H →
    ∀ (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ),
      0 < δcut → 0 < ρcut → 0 < εcut → 0 < Dcut →
    ∃ (J : RetainedCoreHistory.{u}) (IJ : InitialIdentification P g J.toHistory)
      (K : RetainedCoreHistory.{u})
      (A : AffineEventPrefix K J (H.time (Fin.last H.eventCount)) H.eventCount
        (Fin.last K.eventCount))
      (I : RawInitialPrefix H J) (q pFine : CutoffParameters)
      (records : ∀ i : Fin J.eventCount, GeometricCutoffRecord J.toHistory i q)
      (fine : ∀ i : Fin K.eventCount,
        GeometricCutoffRecord J.toHistory (A.eventIndex i) pFine),
      J.horizon = B ∧ IH.IsPrefixOf IJ ∧ HistoryEventControl J ∧
      J.IsCanonicalCutoffRecordFamily p₀ δb ρb records ∧
      J.NoncollapsedBefore κ ε B ∧
      (∀ t : ℝ, t ≤ H.horizon → q.delta t = p.delta t ∧
        q.neckRadius t = p.neckRadius t ∧ q.protectedRadius t = p.protectedRadius t) ∧
      (∀ i : Fin H.eventCount,
        HEq (records (i.castLE I.count_le)).nominalRadius (old i).nominalRadius ∧
        HEq (records (i.castLE I.count_le)).delta (old i).delta ∧
        HEq (records (i.castLE I.count_le)).order (old i).order ∧
        HEq (records (i.castLE I.count_le)).neck (old i).neck ∧
        HEq (records (i.castLE I.count_le)).static (old i).static) ∧
      pFine.fixed = p₀.fixed ∧ pFine.recenterConstant = p₀.recenterConstant ∧
      pFine.modelAccuracy ≤ εcut ∧ Dcut ≤ pFine.modelRadius ∧
      mcut ≤ pFine.modelOrder ∧
      (∀ i b, ((fine i).static b).hasCanonicalWindow) ∧
      (∀ i : Fin K.eventCount,
        pFine.delta (J.time (A.eventIndex i).succ) ≤ δcut ∧
        pFine.neckRadius (J.time (A.eventIndex i).succ) ≤ ρcut) ∧
      ∀ i : Fin K.eventCount,
        HEq (records (A.eventIndex i)).nominalRadius (fine i).nominalRadius ∧
        HEq (records (A.eventIndex i)).delta (fine i).delta ∧
        HEq (records (A.eventIndex i)).order (fine i).order ∧
        HEq (records (A.eventIndex i)).neck (fine i).neck := by
  classical
  obtain ⟨ε, κ, hε, _, hκ, prepare⟩ :=
    exists_prepared_geometric_observation_extension_before_quality P g B hB
  obtain ⟨p₀, δb, ρb, hδb, _, hρb, _, _, _, _, hcap, _, extend⟩ :=
    prepare 1 1 1 1 0 one_pos one_pos one_pos one_pos
  refine ⟨p₀, δb, ρb, ε, κ, hδb, hρb, hε, hκ, hcap, ?_⟩
  intro H IH p old hHB hold hcontrol δcut ρcut εcut Dcut mcut
    hδcut hρcut hεcut hDcut
  obtain ⟨εK, κK, κJ, _, _, _, _, make⟩ := extend H IH p old hHB hold hcontrol
  obtain ⟨K, IK, pB, pF, δbound, ρbound, v, native,
    hKB, _, hcontrolK, hncK, hfixedF, hrcF, hacc, hrad, hord,
    hδbound, hδ, hρbound, hρ, hrecF, hv, hfamily, hdebit,
    hwin, hrecK, hD, hm, haccOld, join⟩ :=
    make δcut ρcut εcut Dcut mcut hδcut hρcut hεcut hDcut
  let c := H.time (Fin.last H.eventCount)
  let pC := pF.withModelWindow p.modelRadius p.modelOrder p.modelAccuracy
    p.modelRadius_pos (pF.modelAccuracy_pos.trans_le haccOld)
  let q := p.spliceAfter (translate_cutoff_parameters pC c) H.horizon
  obtain ⟨J, A, I, hn, records, hp, IJ, hIJ, hJB, hcontrolJ, hncJ,
    hclassJ, hncSame, hstaticJ, hmetric, hpast, hwinJ, hOld, hTail⟩ := join
  have hc : 0 ≤ c := H.toHistory.time_nonneg _
  let pFine := translate_cutoff_parameters pF c
  let fine := fun i : Fin K.eventCount => A.translateRecord hc (native i)
  refine ⟨J, IJ, K, A, I, q, pFine, records, fine,
    hJB, hIJ, hcontrolJ, hclassJ, hncSame, hpast, hOld,
    hfixedF.trans hold.1, hrcF.trans hold.2.2.2.2.1, hacc, hrad, hord, ?_, ?_, ?_⟩
  · intro i
    exact A.translateRecord_canonical hc (native i) (fun b => (hwin i b).hasCanonicalWindow)
  · intro i
    have ht : J.time (A.eventIndex i).succ = K.time i.succ + c := A.time_eq i.succ
    have he := translate_cutoff_parameters_eval pF c (K.time i.succ)
      (K.toHistory.time_nonneg _)
    have hδi : pFine.delta (J.time (A.eventIndex i).succ) = pF.delta (K.time i.succ) := by
      rw [ht]
      exact he.1
    have hρi : pFine.neckRadius (J.time (A.eventIndex i).succ) =
        pF.neckRadius (K.time i.succ) := by
      rw [ht]
      exact he.2.1
    exact ⟨hδi.le.trans ((hfamily.2.2.2.2.2.2.1 i).trans hδ),
      hρi.le.trans ((hfamily.2.2.2.2.2.2.2 i).trans hρ)⟩
  · intro i
    exact ⟨(hTail i).1.trans (A.translateRecord_nominalRadius_heq hc (native i)).symm,
      (hTail i).2.1.trans (A.translateRecord_delta_heq hc (native i)).symm,
      (hTail i).2.2.1.trans (A.translateRecord_order_heq hc (native i)).symm,
      (hTail i).2.2.2.1.trans (A.translateRecord_neck_heq hc (native i)).symm⟩

end GC.GeneralFlow
