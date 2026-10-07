import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedObservationData

/-!
# S-CH11-FIX8 port of astra `PreparedNativeCertificateData`（`PortC11P`）

来源：donor `PreparedNativeCertificateData.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败（1 个 error）。本 port 只有 elaboration 层面修补
（no statement / definition / proof idea altered）：
* `PreparedClassProviderWithNative.of_weak` 的结论里 `fun _ => True` 的 universe 不被约束，
  定理多出一个 universe 参数 `u_1`，`@h P …` 报 `OrientedThreeStage.{u_1}` ≠ `.{u}`：
  写 `PreparedClassProviderWithNative.{u}`（同一个项）；
* 陈述里 3 个未被引用的 binder（`I`、`hp`、`IL`）改成 `_I`、`_hp`、`_IL`（alpha-重命名，
  同一命题；消 unused-variable warning）。

原路径 `PreparedNativeCertificateData` 是只 import 本文件的 re-export shim。
-/

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

/-- Retain one actual native history and its witnesses while carrying or forgetting its certificate. -/
def PreparedGeometricObservationExtensionWithNative
    (certificate : RetainedCoreHistory.{u} → Prop)
    (P : OrientedThreeStage.{u}) (g : P.Metric) (B ε κ : ℝ)
    (p₀ : CutoffParameters) (δb ρb : ℝ) : Prop :=
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
      certificate K ∧ HistoryEventControl K ∧ K.NoncollapsedBefore κK εK K.horizon ∧
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
              (fun b => translate_presented_static_cap (K.coreEvent i) c ((coarse i).static b))

/-- Retain one actual native history and its witnesses while carrying or forgetting its certificate. -/
def PreparedClassProviderWithNative
    (certificate : RetainedCoreHistory.{u} → Prop)
    (fixed : StaticCapScaffold) (recenter : ℝ) : Prop :=
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
      PreparedGeometricObservationExtensionWithNative certificate P g B ε κ p₀ δb ρb

/-- Retain one actual native history and its witnesses while carrying or forgetting its certificate. -/
theorem PreparedGeometricObservationExtensionWithNative.forget
    {certificate : RetainedCoreHistory.{u} → Prop}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {B ε κ : ℝ}
    {p₀ : CutoffParameters} {δb ρb : ℝ}
    (h : PreparedGeometricObservationExtensionWithNative certificate P g B ε κ p₀ δb ρb) :
    PreparedGeometricObservationExtension P g B ε κ p₀ δb ρb := by
  intro H IH p old nativeProjectionx1 nativeProjectionx2 nativeProjectionx3
  have nativeProjectionh4 := @h H IH p old nativeProjectionx1 nativeProjectionx2 nativeProjectionx3
  obtain ⟨εK, κK, κJ, nativeProjectionh5⟩ := nativeProjectionh4
  refine ⟨εK, κK, κJ, ?_⟩
  obtain ⟨nativeProjectionfield6, nativeProjectionfield7, nativeProjectionfield8,
    nativeProjectionfield9, nativeProjectionh10⟩ := nativeProjectionh5
  refine ⟨nativeProjectionfield6, nativeProjectionfield7, nativeProjectionfield8,
    nativeProjectionfield9, ?_⟩
  intro δcut ρcut εcut Dcut mcut nativeProjectionx11 nativeProjectionx12 nativeProjectionx13
    nativeProjectionx14
  have nativeProjectionh15 := @nativeProjectionh10 δcut ρcut εcut Dcut mcut nativeProjectionx11
    nativeProjectionx12 nativeProjectionx13 nativeProjectionx14
  obtain ⟨K, IK, pB, pF, δbound, ρbound, v, fine, nativeProjectionh16⟩ := nativeProjectionh15
  refine ⟨K, IK, pB, pF, δbound, ρbound, v, fine, ?_⟩
  obtain ⟨nativeProjectionfield17, nativeProjectionfield18, nativeProjectionh19⟩ :=
    nativeProjectionh16
  refine ⟨nativeProjectionfield17, nativeProjectionfield18, ?_⟩
  exact nativeProjectionh19.2

/-- Retain one actual native history and its witnesses while carrying or forgetting its certificate. -/
theorem PreparedGeometricObservationExtension.withTrue
    {P : OrientedThreeStage.{u}} {g : P.Metric} {B ε κ : ℝ}
    {p₀ : CutoffParameters} {δb ρb : ℝ}
    (h : PreparedGeometricObservationExtension P g B ε κ p₀ δb ρb) :
    PreparedGeometricObservationExtensionWithNative (fun _ => True)
      P g B ε κ p₀ δb ρb := by
  intro H IH p old nativeProjectionx1 nativeProjectionx2 nativeProjectionx3
  have nativeProjectionh4 := @h H IH p old nativeProjectionx1 nativeProjectionx2 nativeProjectionx3
  obtain ⟨εK, κK, κJ, nativeProjectionh5⟩ := nativeProjectionh4
  refine ⟨εK, κK, κJ, ?_⟩
  obtain ⟨nativeProjectionfield6, nativeProjectionfield7, nativeProjectionfield8,
    nativeProjectionfield9, nativeProjectionh10⟩ := nativeProjectionh5
  refine ⟨nativeProjectionfield6, nativeProjectionfield7, nativeProjectionfield8,
    nativeProjectionfield9, ?_⟩
  intro δcut ρcut εcut Dcut mcut nativeProjectionx11 nativeProjectionx12 nativeProjectionx13
    nativeProjectionx14
  have nativeProjectionh15 := @nativeProjectionh10 δcut ρcut εcut Dcut mcut nativeProjectionx11
    nativeProjectionx12 nativeProjectionx13 nativeProjectionx14
  obtain ⟨K, IK, pB, pF, δbound, ρbound, v, fine, nativeProjectionh16⟩ := nativeProjectionh15
  refine ⟨K, IK, pB, pF, δbound, ρbound, v, fine, ?_⟩
  obtain ⟨nativeProjectionfield17, nativeProjectionfield18, nativeProjectionh19⟩ :=
    nativeProjectionh16
  refine ⟨nativeProjectionfield17, nativeProjectionfield18, ?_⟩
  refine ⟨True.intro, ?_⟩
  exact nativeProjectionh19

/-- Retain one actual native history and its witnesses while carrying or forgetting its certificate. -/
theorem PreparedClassProviderWithNative.of_weak
    {fixed : StaticCapScaffold} {recenter : ℝ}
    (h :
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
      PreparedGeometricObservationExtension P g B ε κ p₀ δb ρb) :
    PreparedClassProviderWithNative.{u} (fun _ => True) fixed recenter := by
  intro P g B nativeProjectionx1
  have nativeProjectionh2 := @h P g B nativeProjectionx1
  obtain ⟨ε, κ, nativeProjectionh3⟩ := nativeProjectionh2
  refine ⟨ε, κ, ?_⟩
  obtain ⟨nativeProjectionfield4, nativeProjectionfield5, nativeProjectionfield6,
    nativeProjectionh7⟩ := nativeProjectionh3
  refine ⟨nativeProjectionfield4, nativeProjectionfield5, nativeProjectionfield6, ?_⟩
  intro δcap ρcap εcapRequest DcapRequest mcapRequest nativeProjectionx8 nativeProjectionx9
    nativeProjectionx10 nativeProjectionx11
  have nativeProjectionh12 := @nativeProjectionh7 δcap ρcap εcapRequest DcapRequest mcapRequest
    nativeProjectionx8 nativeProjectionx9 nativeProjectionx10 nativeProjectionx11
  obtain ⟨p₀, δb, ρb, nativeProjectionh13⟩ := nativeProjectionh12
  refine ⟨p₀, δb, ρb, ?_⟩
  obtain ⟨nativeProjectionfield14, nativeProjectionfield15, nativeProjectionfield16,
    nativeProjectionfield17, nativeProjectionfield18, nativeProjectionfield19,
    nativeProjectionfield20, nativeProjectionfield21, nativeProjectionfield22,
    nativeProjectionfield23, nativeProjectionfield24, nativeProjectionfield25, nativeProjectionh26⟩
    := nativeProjectionh13
  refine ⟨nativeProjectionfield14, nativeProjectionfield15, nativeProjectionfield16,
    nativeProjectionfield17, nativeProjectionfield18, nativeProjectionfield19,
    nativeProjectionfield20, nativeProjectionfield21, nativeProjectionfield22,
    nativeProjectionfield23, nativeProjectionfield24, nativeProjectionfield25, ?_⟩
  exact PreparedGeometricObservationExtension.withTrue nativeProjectionh26

/-- Retain one actual native history and its witnesses while carrying or forgetting its certificate. -/
theorem PreparedClassProviderWithNative.forget
    {certificate : RetainedCoreHistory.{u} → Prop}
    {fixed : StaticCapScaffold} {recenter : ℝ}
    (h : PreparedClassProviderWithNative certificate fixed recenter) :
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
  intro P g B nativeProjectionx1
  have nativeProjectionh2 := @h P g B nativeProjectionx1
  obtain ⟨ε, κ, nativeProjectionh3⟩ := nativeProjectionh2
  refine ⟨ε, κ, ?_⟩
  obtain ⟨nativeProjectionfield4, nativeProjectionfield5, nativeProjectionfield6,
    nativeProjectionh7⟩ := nativeProjectionh3
  refine ⟨nativeProjectionfield4, nativeProjectionfield5, nativeProjectionfield6, ?_⟩
  intro δcap ρcap εcapRequest DcapRequest mcapRequest nativeProjectionx8 nativeProjectionx9
    nativeProjectionx10 nativeProjectionx11
  have nativeProjectionh12 := @nativeProjectionh7 δcap ρcap εcapRequest DcapRequest mcapRequest
    nativeProjectionx8 nativeProjectionx9 nativeProjectionx10 nativeProjectionx11
  obtain ⟨p₀, δb, ρb, nativeProjectionh13⟩ := nativeProjectionh12
  refine ⟨p₀, δb, ρb, ?_⟩
  obtain ⟨nativeProjectionfield14, nativeProjectionfield15, nativeProjectionfield16,
    nativeProjectionfield17, nativeProjectionfield18, nativeProjectionfield19,
    nativeProjectionfield20, nativeProjectionfield21, nativeProjectionfield22,
    nativeProjectionfield23, nativeProjectionfield24, nativeProjectionfield25, nativeProjectionh26⟩
    := nativeProjectionh13
  refine ⟨nativeProjectionfield14, nativeProjectionfield15, nativeProjectionfield16,
    nativeProjectionfield17, nativeProjectionfield18, nativeProjectionfield19,
    nativeProjectionfield20, nativeProjectionfield21, nativeProjectionfield22,
    nativeProjectionfield23, nativeProjectionfield24, nativeProjectionfield25, ?_⟩
  exact PreparedGeometricObservationExtensionWithNative.forget nativeProjectionh26

end GC.GeneralFlow
