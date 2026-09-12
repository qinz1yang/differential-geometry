import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedOrientedStage
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteHistory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.History
import DifferentialGeometry.Topology.ThreeManifold.CutCap

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def OrientedThreeStage.IncomingSlab.toSurgery {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) :
    DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab
      P.toClosedOrientedManifold a s where
  lt := G.lt
  flow := G.flow
  equation := G.equation
  smoothUpTo := G.smoothUpTo

def OrientedThreeStage.IncomingSlab.TerminalLimitMetric.toSurgery
    {P : OrientedThreeStage.{u}} {a s : ℝ}
    {G : P.IncomingSlab a s} (L : G.TerminalLimitMetric) :
    (G.toSurgery).TerminalLimitMetric where
  metric := L.metric
  converges := L.converges

theorem OrientedThreeStage.IncomingSlab.toSurgery_lt {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : (G.toSurgery).lt = G.lt := rfl

theorem OrientedThreeStage.IncomingSlab.toSurgery_flow {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : (G.toSurgery).flow = G.flow := rfl

theorem OrientedThreeStage.IncomingSlab.toSurgery_equation {P : OrientedThreeStage.{u}}
    {a s : ℝ} (G : P.IncomingSlab a s) : (G.toSurgery).equation = G.equation := rfl

theorem OrientedThreeStage.IncomingSlab.TerminalLimitMetric.toSurgery_metric
    {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}
    (L : G.TerminalLimitMetric) : (L.toSurgery).metric = L.metric := rfl

theorem OrientedThreeStage.IncomingSlab.toSurgery_terminalRegularRegion
    {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) :
    (G.toSurgery).terminalRegularRegion = G.terminalRegularRegion := rfl

theorem OrientedThreeStage.IncomingSlab.toSurgery_terminalRegularOpen
    {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) :
    (G.toSurgery).terminalRegularOpen = G.terminalRegularOpen := rfl

def SphericalTubeSystem.ofSmoothCutCapTransition {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) :
    DifferentialGeometry.Topology.SphericalTubeSystem P.toClosedOrientedManifold where
  Index := X.trace.tubes.Index
  finiteIndex := X.trace.tubes.finiteIndex
  tube := X.trace.tubes.tube
  smooth := X.tube_smooth
  disjoint := X.trace.tubes.disjoint

theorem SphericalTubeSystem.core_ofSmoothCutCapTransition {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) :
    (SphericalTubeSystem.ofSmoothCutCapTransition X).core = X.trace.tubes.core := rfl

theorem SphericalTubeSystem.removedBand_ofSmoothCutCapTransition
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (a : X.trace.tubes.Index) :
    (SphericalTubeSystem.ofSmoothCutCapTransition X).removedBand a =
      X.trace.tubes.removedBand a := rfl

theorem SphericalTubeSystem.mem_surgeryRegion_ofSmoothCutCapTransition
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (x : X.trace.tubes.core) :
    x.1 ∈ (SphericalTubeSystem.ofSmoothCutCapTransition X).surgeryRegion ↔
      ∃ a : X.trace.tubes.Index,
        x.1 ∈ X.trace.tubes.tube a ''
          {z : DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeDomain |
            (-2 : ℝ) < z.2.1 ∧ z.2.1 < 2} := by
  rw [DifferentialGeometry.Topology.SphericalTubeSystem.surgeryRegion]
  exact Set.mem_iUnion

theorem SmoothCutCapTransition.presentation_linearEquiv_eq {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (x : N.Carrier)
    (hf : Function.Bijective (mfderiv ThreeModel ThreeModel X.presentation x)) :
    (X.presentation.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv =
      LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel X.presentation x).toLinearMap hf := by
  ext v
  rw [LinearEquiv.ofBijective_apply]
  change (X.presentation.mfderivToContinuousLinearEquiv (by simp) x :
    TangentSpace ThreeModel x → TangentSpace ThreeModel (X.presentation x)) v =
    mfderiv ThreeModel ThreeModel X.presentation x v
  rfl

theorem SmoothCutCapTransition.presentation_positive_toSurgery {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) :
    ∀ x : N.Carrier, (Orientation.map (Fin 3)
      ((X.presentation.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv))
      (N.toClosedOrientedManifold.orientation.orientation x) =
    match X.presentation x with
    | Sum.inl q => Q.toClosedOrientedManifold.orientation.orientation q
    | Sum.inr d => D.toClosedOrientedManifold.orientation.orientation d := by
  intro x
  obtain ⟨hf, hfx⟩ := X.presentation_positive x
  rw [X.presentation_linearEquiv_eq x hf]
  exact hfx

structure SphericalCappingCompletion {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) where
  capping : DifferentialGeometry.Topology.SphericalCapping P.toClosedOrientedManifold
    N.toClosedOrientedManifold (SphericalTubeSystem.ofSmoothCutCapTransition X)
  coreInclusion_eq : ∀ x, capping.coreInclusion x = X.trace.capping.coreInclusion x

structure SmoothCutCapCompletion {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) extends SphericalCappingCompletion X where
  every_component_meets_core : ∀ c : ConnectedComponents Q.Carrier,
    ∃ x : (SphericalTubeSystem.ofSmoothCutCapTransition X).core, ∃ q : Q.Carrier,
      X.presentation (toSphericalCappingCompletion.capping.coreInclusion x) = Sum.inl q ∧
        ConnectedComponents.mk q = c
  retained_complement :
    (interior {q : Q.Carrier | ∃ x : (SphericalTubeSystem.ofSmoothCutCapTransition X).core,
      X.presentation (toSphericalCappingCompletion.capping.coreInclusion x) = Sum.inl q})ᶜ =
      {q : Q.Carrier | ∃ b, ∃ z : DifferentialGeometry.Topology.ClosedCell 3,
        X.presentation (toSphericalCappingCompletion.capping.cap b z) = Sum.inl q}
  presentation_positive :
    ∀ x : N.Carrier, (Orientation.map (Fin 3)
      ((X.presentation.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv))
      (N.toClosedOrientedManifold.orientation.orientation x) =
    match X.presentation x with
    | Sum.inl q => Q.toClosedOrientedManifold.orientation.orientation q
    | Sum.inr d => D.toClosedOrientedManifold.orientation.orientation d

def SphericalCutCapTransition.ofSmoothCutCapTransition
    {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (h : SmoothCutCapCompletion X) :
    DifferentialGeometry.Topology.SphericalCutCapTransition P.toClosedOrientedManifold
      Q.toClosedOrientedManifold where
  source_nonempty := X.source_nonempty
  tubes := SphericalTubeSystem.ofSmoothCutCapTransition X
  capped := N.toClosedOrientedManifold
  capping := h.capping
  discarded := D.toClosedOrientedManifold
  presentation := X.presentation
  presentation_positive := fun x => by
    convert h.presentation_positive x using 2 <;>
      first
        | rfl
        | (cases X.presentation x <;> rfl)
  every_component_meets_core := h.every_component_meets_core
  retained_complement := h.retained_complement
  nontrivial := X.trace.nontrivial

theorem SphericalCutCapTransition.ofSmoothCutCapTransition_tubes
    {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (h : SmoothCutCapCompletion X) :
    (SphericalCutCapTransition.ofSmoothCutCapTransition
        X h).tubes = SphericalTubeSystem.ofSmoothCutCapTransition X := rfl

theorem SphericalCutCapTransition.ofSmoothCutCapTransition_presentation
    {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (h : SmoothCutCapCompletion X) :
    ((SphericalCutCapTransition.ofSmoothCutCapTransition
        X h).presentation : N.Carrier → Q.Carrier ⊕ D.Carrier) = X.presentation := rfl

theorem SphericalCutCapTransition.ofSmoothCutCapTransition_coreInclusion
    {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (h : SmoothCutCapCompletion X)
    (x : X.trace.tubes.core) :
    (SphericalCutCapTransition.ofSmoothCutCapTransition
        X h).capping.coreInclusion x = X.trace.capping.coreInclusion x :=
  h.coreInclusion_eq x

theorem SphericalCutCapTransition.retainedCore_iff {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (h : SmoothCutCapCompletion X)
    (x : X.trace.tubes.core) :
    x ∈ (SphericalCutCapTransition.ofSmoothCutCapTransition
        X h).retainedCore ↔ x ∈ X.trace.retainedCore := by
  rw [DifferentialGeometry.Topology.SphericalCutCapTransition.retainedCore,
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.retainedCore,
    SphericalCutCapTransition.ofSmoothCutCapTransition_presentation]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, by
      rw [SphericalCutCapTransition.ofSmoothCutCapTransition_coreInclusion X h x,
        X.presentation_eq] at hq
      exact hq⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, by
      rw [SphericalCutCapTransition.ofSmoothCutCapTransition_coreInclusion X h x,
        X.presentation_eq]
      exact hq⟩

def ObservedHistory.toSurgeryFiniteSurgeryHistory (H : ObservedHistory.{u})
    (hn : 0 < H.eventCount)
    (hev : (i : Fin H.eventCount) →
      DifferentialGeometry.PDE.RicciFlow.Surgery.MetricCutCapEvent
        (H.stage i.castSucc).toClosedOrientedManifold
        (H.stage i.succ).toClosedOrientedManifold
        (H.time i.castSucc) (H.time i.succ))
    (hev_initial : ∀ i : Fin H.eventCount,
      (hev i).incoming.flow.base.metric (H.time i.castSucc) = H.initialMetric i.castSucc)
    (hev_output : ∀ i : Fin H.eventCount,
      (hev i).outputMetric = H.initialMetric i.succ) :
    DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u} where
  eventCount := H.eventCount
  eventCount_pos := hn
  time := H.time
  time_strictMono := H.time_strictMono
  time_zero := H.time_zero
  stage := fun i => (H.stage i).toClosedOrientedManifold
  initialMetric := fun i => H.initialMetric i
  event := hev
  event_initial := hev_initial
  event_output := hev_output

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
