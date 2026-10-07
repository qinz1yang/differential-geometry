import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CutoffRecordConcatenation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LinkedCanonicalWindowC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.RecordHypFarC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordModelRestriction.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapse.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingSlabDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingSlabCanonicalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryExtension
import DifferentialGeometry.Topology.SigmaCompactOpen

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

/-- The existing prepared-class extension rule, retaining its one actual
native history, physical records, joined prefix and final metric. This is a
predicate naming the callback, not an additional producer assumption. -/
def PreparedGeometricObservationExtension
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
              (fun b => translate_presented_static_cap (K.coreEvent i) c ((coarse i).static b))

abbrev NativeEstimates (K : RetainedCoreHistory.{u})
    (ε C1 C2 C1s C2s qcan qs τmin : ℝ) (Ctime Cgrad : ℝ≥0) : Prop :=
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
    G.SpatiallyCanonicalBefore ε C1s C2s qs K.horizon

end GC.GeneralFlow
