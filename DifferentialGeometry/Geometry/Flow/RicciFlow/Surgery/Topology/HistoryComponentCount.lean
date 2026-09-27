import DifferentialGeometry.Topology.Connected.Sum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCoreComponentCount
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.WorldBridges
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices

set_option autoImplicit false
noncomputable section

open Set Function
open scoped BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance (P : OrientedThreeStage.{u}) : LocallyConnectedSpace P.Carrier :=
  ChartedSpace.locallyConnectedSpace ThreeSpace P.Carrier

theorem SmoothCutCapTransition.card_connectedComponents_output_add_discarded_le
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N) :
    Nat.card (ConnectedComponents Q.Carrier) + Nat.card (ConnectedComponents D.Carrier) ≤
      Nat.card (ConnectedComponents P.Carrier) + Nat.card X.trace.tubes.Index := by
  let _ := X.core_compact
  let _ := X.core_locallyConnected
  have hsum : Nat.card (ConnectedComponents Q.Carrier) +
      Nat.card (ConnectedComponents D.Carrier) =
        Nat.card (ConnectedComponents (Q.Carrier ⊕ D.Carrier)) := by
    rw [← Nat.card_sum, Nat.card_congr ConnectedComponents.sumEquiv]
  rw [hsum]
  calc
    Nat.card (ConnectedComponents (Q.Carrier ⊕ D.Carrier)) ≤
        Nat.card (ConnectedComponents N.Carrier) :=
      Nat.card_le_card_of_surjective _
        (X.trace.presentation.continuous.connectedComponentsMap_surjective
          X.trace.presentation.surjective)
    _ = Nat.card (ConnectedComponents X.trace.tubes.core) :=
      (Nat.card_congr X.trace.capping.componentEquiv).symm
    _ ≤ Nat.card (ConnectedComponents P.Carrier) + Nat.card X.trace.tubes.Index :=
      X.card_connectedComponents_core_le

theorem MetricCutCapEvent.one_le_card_cut_add_card_discarded
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s) :
    1 ≤ Nat.card E.transition.trace.tubes.Index +
      Nat.card (ConnectedComponents E.discarded.Carrier) := by
  rcases nontrivial_of_metricCutCapEvent E with hcut | hdiscard
  · let _ := hcut
    have h := Nat.card_pos (α := E.transition.trace.tubes.Index)
    omega
  · let _ := hdiscard
    have h := Nat.card_pos (α := ConnectedComponents E.discarded.Carrier)
    omega

theorem ObservedHistory.eventCount_le_card_initial_add_two_mul_sum_card_cut
    (H : ObservedHistory.{u}) :
    H.eventCount ≤ Nat.card (ConnectedComponents (H.stage 0).Carrier) +
      2 * ∑ i : Fin H.eventCount, Nat.card (H.event i).transition.trace.tubes.Index := by
  have htel : ∀ n : ℕ, ∀ c : Fin (n + 1) → ℕ, ∀ d k : Fin n → ℕ,
      (∀ i, c i.succ + d i ≤ c i.castSucc + k i) →
      c (Fin.last n) + ∑ i, d i ≤ c 0 + ∑ i, k i := by
    intro n
    induction n with
    | zero => intro c d k h; simp
    | succ n ih =>
      intro c d k h
      have hp := ih (fun i => c i.castSucc) (fun i => d i.castSucc) (fun i => k i.castSucc)
        (fun i => h i.castSucc)
      have hl := h (Fin.last n)
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      change c (Fin.last n).castSucc + ∑ i : Fin n, d i.castSucc ≤
        c 0 + ∑ i : Fin n, k i.castSucc at hp
      change c (Fin.last (n + 1)) + d (Fin.last n) ≤
        c (Fin.last n).castSucc + k (Fin.last n) at hl
      omega
  let c := fun i : Fin (H.eventCount + 1) => Nat.card (ConnectedComponents (H.stage i).Carrier)
  let d := fun i : Fin H.eventCount => Nat.card (ConnectedComponents (H.event i).discarded.Carrier)
  let k := fun i : Fin H.eventCount => Nat.card (H.event i).transition.trace.tubes.Index
  have hcomp := htel H.eventCount c d k
    (fun i => (H.event i).transition.card_connectedComponents_output_add_discarded_le)
  have hone : H.eventCount ≤ ∑ i : Fin H.eventCount, (k i + d i) := by
    calc
      H.eventCount = ∑ _ : Fin H.eventCount, 1 := by simp
      _ ≤ ∑ i : Fin H.eventCount, (k i + d i) := Finset.sum_le_sum
        (fun i _ => (H.event i).one_le_card_cut_add_card_discarded)
  rw [Finset.sum_add_distrib] at hone
  change H.eventCount ≤ c 0 + 2 * ∑ i, k i
  omega

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
