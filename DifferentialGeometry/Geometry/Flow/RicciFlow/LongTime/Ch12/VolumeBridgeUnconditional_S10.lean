import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.VolumeBridgeAlign_S10
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EventVolumeAssembly_S14

set_option autoImplicit false
noncomputable section
open Set MeasureTheory DifferentialGeometry DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime
universe u
namespace GC.LongTime.Ch12

private local instance sigmaCompactTRO_UC {Q : OrientedThreeStage.{u}} {a s : ℝ}
    (G : Q.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

/-- Unconditional LTF01a: records of the profile + S14's VB-B supply `hB` for all events. -/
theorem normalizedVolumeBounded_S13_unconditional_S10 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ) :
    NormalizedVolumeBounded_S13 Hp :=
  normalizedVolumeBounded_S13_of_eventBound_S10 Hp
    (fun n i => event_volume_le_compact_S14 (Hp.records n i))

#print axioms normalizedVolumeBounded_S13_unconditional_S10

end GC.LongTime.Ch12
