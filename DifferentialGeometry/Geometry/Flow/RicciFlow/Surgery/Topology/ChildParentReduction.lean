import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCarrierCollaredStarCover
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StandardNeckCutCapInstance
import Mathlib.Topology.Homotopy.Equiv

noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem simplyConnectedSpace_componentCarrier_of_connected {X : Type u} [TopologicalSpace X]
    [ConnectedSpace X] [SimplyConnectedSpace X] (c : ConnectedComponents X) :
    SimplyConnectedSpace (ComponentCarrier c) := by
  have hmk : ∀ x : X, ConnectedComponents.mk x = c := by
    intro x
    obtain ⟨y, hy⟩ := ConnectedComponents.surjective_coe c
    rw [← hy]
    exact ConnectedComponents.coe_eq_coe'.mpr (by
      rw [PreconnectedSpace.connectedComponent_eq_univ]
      exact Set.mem_univ x)
  let e : ComponentCarrier c ≃ₜ X :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, hmk x⟩
      left_inv := fun y => Subtype.ext rfl
      right_inv := fun x => rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk fun x => hmk x }
  exact e.toHomotopyEquiv.simplyConnectedSpace

theorem sphereThreeStage_componentCarrier_simplyConnected
    (c : ConnectedComponents sphereThreeStage.Carrier) :
    SimplyConnectedSpace (sphereThreeStage.component c).Carrier := by
  have hconn : ConnectedSpace (Sphere 3) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := EuclideanSpace ℝ (Fin 4))
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num))
  exact @simplyConnectedSpace_componentCarrier_of_connected sphereThreeStage.Carrier _
    hconn (inferInstance : SimplyConnectedSpace
      DifferentialGeometry.Topology.SphereThree) c

theorem not_simplyConnectedSpace_childCarrier_of_capRange_eq_univ
    {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)
    (c : ConnectedComponents Q.Carrier) {b₁ b₂ : E.ChildCapBoundary c} (hne : b₁ ≠ b₂)
    (huniv : (⋃ b : E.ChildCapBoundary c, Set.range (E.childCap c b)) = Set.univ) :
    ¬ SimplyConnectedSpace (E.ChildCarrier c) := by
  intro hsc
  have hiff : SimplyConnectedSpace ↥(univ : Set (E.ChildCarrier c)) ↔
      SimplyConnectedSpace (E.ChildCarrier c) :=
    (Homeomorph.Set.univ (E.ChildCarrier c)).toHomotopyEquiv.simplyConnectedSpace_iff
  exact E.not_simplyConnectedSpace_of_capRange_subset_of_two_caps c hne
    (W := Set.univ) (subset_univ _) (subset_univ _) (by rw [huniv])
    (hiff.mpr hsc)

theorem exists_child_simplyConnected_witness (h : StandardNeckCutCapInputs) :
    ∃ E : SmoothCutCapTransition sphereThreeStage sphereThreeStage sphereThreeStage
        (sphereThreeStage.sum sphereThreeStage),
      (∀ c : ConnectedComponents sphereThreeStage.Carrier,
        SimplyConnectedSpace (sphereThreeStage.component (E.childParent c)).Carrier) ∧
      (∀ c : ConnectedComponents sphereThreeStage.Carrier,
        SimplyConnectedSpace (sphereThreeStage.component c).Carrier) := by
  obtain ⟨E⟩ := nonempty_smoothCutCapTransition_of_standardNeckInputs h
  exact ⟨E, fun c => sphereThreeStage_componentCarrier_simplyConnected _,
    fun c => sphereThreeStage_componentCarrier_simplyConnected _⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
