import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncestryCore
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Comparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FreeLoopClass



noncomputable section

open Set Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem rfs_simply_connected_history (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier) :
    ∀ j : Fin (H.eventCount + 1), ∀ c : ConnectedComponents (H.stage j).Carrier,
      SimplyConnectedSpace ((H.stage j).component c).Carrier := by
  intro j
  induction j using Fin.induction with
  | zero => exact h0
  | succ j ih =>
    intro c
    let := ih ((H.event j).transition.childParent c)
    exact (H.event j).transition.child_simplyConnected c

theorem rfs_finite_ancestry (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (cutoff : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier) :
    let chain := rfs_finite_ancestor_chain H terminal
    let hSC := rfs_simply_connected_history H h0
    (∀ j : Fin (H.eventCount + 1),
      let P := (H.stage j).component (chain.component j)
      letI : ConnectedSpace P.Carrier := (H.stage j).component_connected (chain.component j)
      letI : SimplyConnectedSpace P.Carrier := hSC j (chain.component j)
      ∀ q : P.Carrier,
        Function.Injective (fun z : ℤ => positiveHomotopyClass P.orientation q ^ z) ∧
        positiveFreeContractibleClass P.orientation ≠ FreeHomotopyClass.mk
          (ContinuousMap.const (Sphere 2)
            (⟨constantLoops q, isContractibleLoop_constant q⟩ : ContractibleContinuousLoop P.Carrier))) ∧
    (∀ j : Fin H.eventCount,
      let G := cutoff j
      let child := chain.component j.succ
      let P := G.Parent child
      let Q := G.Child child
      letI : ConnectedSpace P.Carrier := (H.stage j.castSucc).component_connected
        ((H.event j).transition.childParent child)
      letI : ConnectedSpace Q.Carrier := (H.stage j.succ).component_connected child
      letI : SimplyConnectedSpace P.Carrier := hSC j.castSucc ((H.event j).transition.childParent child)
      letI : SimplyConnectedSpace Q.Carrier := hSC j.succ child
      ∃ K : G.ComparisonSupport child,
        (∀ p : P.Carrier, basedHomotopyMap K.rfs_whole_parent_map p
          (positiveHomotopyClass P.orientation p) =
            positiveHomotopyClass Q.orientation (K.rfs_whole_parent_map p)) ∧
        FreeHomotopyClass.map (contractibleLoopPostcompose K.rfs_whole_parent_map)
          (positiveFreeContractibleClass P.orientation) = positiveFreeContractibleClass Q.orientation) := by
  let chain := rfs_finite_ancestor_chain H terminal
  let hSC := rfs_simply_connected_history H h0
  constructor
  · intro j
    let P := (H.stage j).component (chain.component j)
    let : ConnectedSpace P.Carrier := (H.stage j).component_connected (chain.component j)
    let : SimplyConnectedSpace P.Carrier := hSC j (chain.component j)
    dsimp only
    intro q
    exact ⟨positiveHomotopyClass_infiniteOrder P.orientation q,
      positiveFreeContractibleClass_nontrivial P.orientation q⟩
  · intro j
    let G := cutoff j
    let child := chain.component j.succ
    let P := G.Parent child
    let Q := G.Child child
    let : ConnectedSpace P.Carrier := (H.stage j.castSucc).component_connected
      ((H.event j).transition.childParent child)
    let : ConnectedSpace Q.Carrier := (H.stage j.succ).component_connected child
    let : SimplyConnectedSpace P.Carrier := hSC j.castSucc ((H.event j).transition.childParent child)
    let : SimplyConnectedSpace Q.Carrier := hSC j.succ child
    obtain ⟨K⟩ := G.rfs_comparison_support child
    have hd : orientedDegree P.orientation Q.orientation K.rfs_whole_parent_map = 1 := by
      apply (orientedDegree_eq_iff P.orientation Q.orientation K.rfs_whole_parent_map 1).mpr
      simpa only [one_smul] using K.rfs_collapse_degree.2.2.2.1
    refine ⟨K, ?_, positiveFreeContractibleClass_natural P.orientation Q.orientation
      K.rfs_whole_parent_map hd⟩
    intro p
    simpa only [hd, zpow_one] using
      rfs_degree_class_transport P.orientation Q.orientation K.rfs_whole_parent_map p

structure AncestorRestrictionData (short long : ObservedHistory.{u}) where
  count_le : short.eventCount ≤ long.eventCount
  stage_eq : ∀ j : Fin (short.eventCount + 1), short.stage j =
    long.stage (Fin.castLE (Nat.add_le_add_right count_le 1) j)
  discarded_eq : ∀ j : Fin short.eventCount, (short.event j).discarded =
    (long.event (Fin.castLE count_le j)).discarded
  capped_eq : ∀ j : Fin short.eventCount, (short.event j).capped =
    (long.event (Fin.castLE count_le j)).capped
  transition_eq : ∀ j : Fin short.eventCount,
    HEq (short.event j).transition (long.event (Fin.castLE count_le j)).transition

namespace AncestorRestrictionData

variable {short long : ObservedHistory.{u}} (R : AncestorRestrictionData short long)


def componentToLong (j : Fin (short.eventCount + 1)) :
    ConnectedComponents (short.stage j).Carrier →
      ConnectedComponents (long.stage (Fin.castLE (Nat.add_le_add_right R.count_le 1) j)).Carrier :=
  fun c => (R.stage_eq j) ▸ c

private theorem componentToLong_parent (j : Fin short.eventCount)
    (c : ConnectedComponents (short.stage j.succ).Carrier) :
    R.componentToLong j.castSucc ((short.event j).transition.childParent c) =
      (long.event (Fin.castLE R.count_le j)).transition.childParent
        (R.componentToLong j.succ c) :=
  SmoothCutCapTransition.childParent_congr (short.event j).transition
    (long.event (Fin.castLE R.count_le j)).transition
    (R.stage_eq j.castSucc) (R.stage_eq j.succ) (R.discarded_eq j) (R.capped_eq j)
    (R.transition_eq j) c

theorem rfs_finite_ancestry_restrict
    (terminal : ConnectedComponents (long.stage (Fin.last long.eventCount)).Carrier)
    (earlier : ConnectedComponents (short.stage (Fin.last short.eventCount)).Carrier)
    (hearlier : R.componentToLong (Fin.last short.eventCount) earlier =
      (rfs_finite_ancestor_chain long terminal).component
        (Fin.castLE (Nat.add_le_add_right R.count_le 1) (Fin.last short.eventCount))) :
    ∀ j : Fin (short.eventCount + 1), R.componentToLong j
      ((rfs_finite_ancestor_chain short earlier).component j) =
        (rfs_finite_ancestor_chain long terminal).component
          (Fin.castLE (Nat.add_le_add_right R.count_le 1) j) := by
  intro j
  induction j using Fin.reverseInduction with
  | last =>
    rw [(rfs_finite_ancestor_chain short earlier).terminal_eq]
    exact hearlier
  | cast j ih =>
    rw [(rfs_finite_ancestor_chain short earlier).parent_eq, componentToLong_parent R j, ih]
    exact ((rfs_finite_ancestor_chain long terminal).parent_eq (Fin.castLE R.count_le j)).symm

end AncestorRestrictionData

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
