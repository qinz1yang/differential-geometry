import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowDeepC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCapCoordinates

/-!
# Route β′ record hypothesis, light form (C12X, S16 round 3, O-C12X-S16K G1b)

Lead ruling (S16 round 3): the class field `strongControl` takes the record hypothesis
`RecordHypFar_C12X θ V records` as an antecedent, and the prepared state keeps it for its native
record family (`nativeRecordHyp`).  It is the conjunction of

* deep backward necks of depth factor `θ` for every cut neck (`IncomingBackwardNeckDeep_C12X`,
  S16H G4a; definitionally the `DeepBackwardNecks_C12X θ` of S16G G5), and
* radial coordinates of every static cap window (`StaticCapWitness.HasRadialCoordinates`,
  lead ruling β′; produced upstream by ST/FinitePresentedStaticCapC11X).

This file only depends on the record and static-cap definitions, so that tracked history files can
state the field without importing the `hwin` machinery.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- Every static cap window of the record family has radial coordinates. -/
def RadialWindows_C12X (H : RetainedCoreHistory.{u}) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p) : Prop :=
  ∀ (i : Fin H.eventCount) (b : (H.toHistory.event i).RetainedBoundaryIndex),
    ((records i).static b).witness.HasRadialCoordinates

/-- Route β′ record hypothesis: deep backward necks of depth factor `θ` and radial windows. -/
def RecordHypFar_C12X (θ : ℝ) (H : RetainedCoreHistory.{u}) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p) : Prop :=
  (∀ (i : Fin H.eventCount) (α : (H.toHistory.event i).transition.trace.tubes.Index),
    Nonempty (IncomingBackwardNeckDeep_C12X H.toHistory i ((records i).neck α)
      ((records i).nominalRadius ⟨α⟩) θ)) ∧
  RadialWindows_C12X H records

theorem RecordHypFar_C12X.radial {θ : ℝ} {H : RetainedCoreHistory.{u}} {p : CutoffParameters}
    {records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p}
    (h : RecordHypFar_C12X θ H records) : RadialWindows_C12X H records :=
  h.2

theorem RecordHypFar_C12X.deep {θ : ℝ} {H : RetainedCoreHistory.{u}} {p : CutoffParameters}
    {records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p}
    (h : RecordHypFar_C12X θ H records) (i : Fin H.eventCount)
    (α : (H.toHistory.event i).transition.trace.tubes.Index) :
    Nonempty (IncomingBackwardNeckDeep_C12X H.toHistory i ((records i).neck α)
      ((records i).nominalRadius ⟨α⟩) θ) :=
  h.1 i α

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
