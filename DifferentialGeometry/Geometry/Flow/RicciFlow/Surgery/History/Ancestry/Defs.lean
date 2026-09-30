import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent

noncomputable section

open Set Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

structure FiniteAncestorChain (H : ObservedHistory.{u})
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier) where
  component : (j : Fin (H.eventCount + 1)) → ConnectedComponents (H.stage j).Carrier
  terminal_eq : component (Fin.last H.eventCount) = terminal
  parent_eq : ∀ j : Fin H.eventCount,
    component j.castSucc = (H.event j).transition.childParent (component j.succ)

@[ext] theorem FiniteAncestorChain.ext {H : ObservedHistory.{u}}
    {terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier}
    (A B : FiniteAncestorChain H terminal) (h : A.component = B.component) : A = B := by
  cases A
  cases B
  cases h
  rfl

def ancestorComponent (H : ObservedHistory.{u})
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier) :
    (j : Fin (H.eventCount + 1)) → ConnectedComponents (H.stage j).Carrier :=
  Fin.reverseInduction terminal (fun j c => (H.event j).transition.childParent c)

def finiteAncestorChain (H : ObservedHistory.{u})
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier) :
    FiniteAncestorChain H terminal where
  component := ancestorComponent H terminal
  terminal_eq := by simp [ancestorComponent]
  parent_eq j := by simp [ancestorComponent]

theorem exists_unique_finiteAncestorChain (H : ObservedHistory.{u})
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier) :
    Nonempty (Unique (FiniteAncestorChain H terminal)) := by
  let canonical := finiteAncestorChain H terminal
  refine ⟨{ default := canonical, uniq := ?_ }⟩
  intro chain
  have hcomponent : chain.component = canonical.component := by
    funext j
    induction j using Fin.reverseInduction with
    | last => exact chain.terminal_eq.trans canonical.terminal_eq.symm
    | cast j ih => rw [chain.parent_eq, canonical.parent_eq, ih]
  exact FiniteAncestorChain.ext chain canonical hcomponent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
