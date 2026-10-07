import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.VolumeBridgeLateMain_S10
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitInterfaceProps

set_option autoImplicit false
noncomputable section
open Set MeasureTheory DifferentialGeometry DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime
universe u
namespace GC.LongTime.Ch12

private local instance sigmaCompactTRO_LA {Q : OrientedThreeStage.{u}} {a s : ℝ}
    (G : Q.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

/-- Late-event version (VB-B only for events at time `≥ T`) giving the S13 shape. -/
theorem normalizedVolumeBounded_S13_of_lateEventBound_S10 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hBLate : ∃ T : ℝ, ∀ n (i : Fin (F.tower.history n).eventCount),
      T ≤ (F.tower.history n).toHistory.time i.succ →
      ∃ K : Set ((F.tower.history n).toHistory.event i).incoming.terminalRegularOpen, IsCompact K ∧
        riemannianVolumeMeasure ThreeModel ((F.tower.history n).toHistory.stage i.succ).Carrier
            ((F.tower.history n).toHistory.event i).outputMetric univ ≤
          riemannianVolumeMeasure ThreeModel
            ((F.tower.history n).toHistory.event i).incoming.terminalRegularOpen
            ((F.tower.history n).toHistory.event i).terminal.metric K) :
    NormalizedVolumeBounded_S13 Hp :=
  normalized_volume_bounded_of_lateEventBound_S10 Hp hBLate

#print axioms normalizedVolumeBounded_S13_of_lateEventBound_S10

end GC.LongTime.Ch12
