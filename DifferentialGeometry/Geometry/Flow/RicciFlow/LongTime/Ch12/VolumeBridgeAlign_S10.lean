import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.VolumeBridgeMain_S10
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitInterfaceProps

set_option autoImplicit false
noncomputable section
open Set MeasureTheory DifferentialGeometry DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime
universe u
namespace GC.LongTime.Ch12

private local instance sigmaCompactTRO_S10'' {Q : OrientedThreeStage.{u}} {a s : ℝ}
    (G : Q.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

theorem normalizedTotalVolume_eq_S13_S10 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {T : ObservationTower P g} (s : RegularSlice T) :
    normalizedTotalVolume s = normalizedTotalVolume_S13 s := rfl

/-- Gives exactly the S13 shape `NormalizedVolumeBounded_S13` (review 4.2), from the explicit
per-event volume input VB-B. -/
theorem normalizedVolumeBounded_S13_of_eventBound_S10 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hB : ∀ n (i : Fin (F.tower.history n).eventCount),
      ∃ K : Set ((F.tower.history n).toHistory.event i).incoming.terminalRegularOpen, IsCompact K ∧
        riemannianVolumeMeasure ThreeModel ((F.tower.history n).toHistory.stage i.succ).Carrier
            ((F.tower.history n).toHistory.event i).outputMetric univ ≤
          riemannianVolumeMeasure ThreeModel
            ((F.tower.history n).toHistory.event i).incoming.terminalRegularOpen
            ((F.tower.history n).toHistory.event i).terminal.metric K) :
    NormalizedVolumeBounded_S13 Hp :=
  normalized_volume_bounded_of_eventBound_S10 Hp hB

#print axioms normalized_volume_bounded_of_eventBound_S10
#print axioms normalizedVolumeBounded_S13_of_eventBound_S10

end GC.LongTime.Ch12
