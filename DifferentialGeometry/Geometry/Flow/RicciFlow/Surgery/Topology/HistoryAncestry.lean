import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Ancestry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPresentation

noncomputable section
open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory


theorem ancestorRestriction (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) :
    AncestorRestrictionData (H.restrict t) H where
  count_le := Nat.le_of_lt_succ (H.activeStage t).isLt
  stage_eq _ := rfl
  discarded_eq _ := rfl
  capped_eq _ := rfl
  transition_eq _ := HEq.rfl

theorem finite_ancestry_restrict (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier) :
    ∀ j : Fin ((H.restrict t).eventCount + 1),
      (finiteAncestorChain (H.restrict t)
        ((finiteAncestorChain H terminal).component (H.activeStage t))).component j =
      (finiteAncestorChain H terminal).component
        (Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (H.activeStage t).isLt) 1) j) := by
  intro j
  induction j using Fin.reverseInduction with
  | last =>
    exact (finiteAncestorChain (H.restrict t)
      ((finiteAncestorChain H terminal).component (H.activeStage t))).terminal_eq
  | cast j ih =>
    rw [(finiteAncestorChain (H.restrict t)
      ((finiteAncestorChain H terminal).component (H.activeStage t))).parent_eq, ih]
    exact ((finiteAncestorChain H terminal).parent_eq
      (Fin.castLE (Nat.le_of_lt_succ (H.activeStage t).isLt) j)).symm

namespace SamePresentation
variable {H K : ObservedHistory.{u}} (R : H.SamePresentation K)


def componentToOther (j : Fin (H.eventCount + 1)) :
    ConnectedComponents (H.stage j).Carrier →
      ConnectedComponents (K.stage (Fin.cast (congrArg (· + 1) R.count_eq) j)).Carrier :=
  fun c => (R.stage_eq j) ▸ c

private theorem componentToOther_parent (j : Fin H.eventCount)
    (c : ConnectedComponents (H.stage j.succ).Carrier) :
    R.componentToOther j.castSucc ((H.event j).transition.childParent c) =
      (K.event (Fin.cast R.count_eq j)).transition.childParent
        (R.componentToOther j.succ c) :=
  SmoothCutCapTransition.childParent_congr (H.event j).transition
    (K.event (Fin.cast R.count_eq j)).transition
    (R.stage_eq j.castSucc) (R.stage_eq j.succ)
    (R.event_eq j).discarded_eq (R.event_eq j).capped_eq (R.event_eq j).transition_heq c

theorem finite_ancestry
    (terminalH : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    (terminalK : ConnectedComponents (K.stage (Fin.last K.eventCount)).Carrier)
    (hterminal : R.componentToOther (Fin.last H.eventCount) terminalH =
      (finiteAncestorChain K terminalK).component
        (Fin.cast (congrArg (· + 1) R.count_eq) (Fin.last H.eventCount))) :
    ∀ j : Fin (H.eventCount + 1), R.componentToOther j
      ((finiteAncestorChain H terminalH).component j) =
      (finiteAncestorChain K terminalK).component
        (Fin.cast (congrArg (· + 1) R.count_eq) j) := by
  intro j
  induction j using Fin.reverseInduction with
  | last =>
    rw [(finiteAncestorChain H terminalH).terminal_eq]
    exact hterminal
  | cast j ih =>
    rw [(finiteAncestorChain H terminalH).parent_eq, R.componentToOther_parent, ih]
    exact ((finiteAncestorChain K terminalK).parent_eq (Fin.cast R.count_eq j)).symm

end SamePresentation
end ObservedHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
