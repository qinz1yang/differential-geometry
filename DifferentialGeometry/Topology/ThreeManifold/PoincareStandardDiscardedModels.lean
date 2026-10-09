import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardDiscarded
import DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormProjective

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

def projectiveThreeSpaceLift : ConnectedClosedOrientedManifold.{u} 3 :=
  ConnectedClosedOrientedManifold.ulift.{0, u} SphericalSpaceFormGroup.antipodal.manifold

theorem isStandardFactor_projectiveThreeSpaceLift :
    isStandardFactor projectiveThreeSpaceLift.{u} :=
  Or.inl ⟨SphericalSpaceFormGroup.antipodal,
    ⟨(ClosedOrientedManifold.uliftOrientedDiffeomorph
      SphericalSpaceFormGroup.antipodal.manifold.toClosedOrientedManifold).symm⟩⟩

theorem isPoincareStandard_projectiveThreeSpaceLift :
    isPoincareStandard projectiveThreeSpaceLift.{u}.Carrier :=
  isPoincareStandard_of_standard_factor projectiveThreeSpaceLift.{u}
    isStandardFactor_projectiveThreeSpaceLift

theorem nonempty_projectiveThreeSpaceLift :
    Nonempty projectiveThreeSpaceLift.{u}.Carrier := inferInstance

def isProjectiveThreeSpaceConnectedSum
    (M : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  Nonempty (ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
    (connectedSum projectiveThreeSpaceLift.{u}
      projectiveThreeSpaceLift.{u}).toClosedOrientedManifold)

theorem isPoincareStandard_of_isProjectiveThreeSpaceConnectedSum
    {M : ConnectedClosedOrientedManifold.{u} 3}
    (h : isProjectiveThreeSpaceConnectedSum M) : isPoincareStandard M.Carrier := by
  obtain ⟨ρ⟩ := h
  exact isPoincareStandard_of_diffeomorph ρ.1
    (isPoincareStandard_connectedSum_of_standardFactor projectiveThreeSpaceLift
      projectiveThreeSpaceLift isStandardFactor_projectiveThreeSpaceLift
      isStandardFactor_projectiveThreeSpaceLift)

theorem isProjectiveThreeSpaceConnectedSum_self :
    isProjectiveThreeSpaceConnectedSum
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}) :=
  ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩

theorem nonempty_connectedSum_projectiveThreeSpaceLift :
    Nonempty (connectedSum projectiveThreeSpaceLift.{u}
      projectiveThreeSpaceLift.{u}).Carrier := inferInstance

theorem isPoincareStandard_connectedSum_projectiveThreeSpaceLift :
    isPoincareStandard (connectedSum projectiveThreeSpaceLift.{u}
      projectiveThreeSpaceLift.{u}).Carrier :=
  isPoincareStandard_of_isProjectiveThreeSpaceConnectedSum
    isProjectiveThreeSpaceConnectedSum_self

def ClosedOrientedManifold.componentwiseStandardFactorOrProjectiveThreeSpaceSum
    (D : ClosedOrientedManifold.{u} 3) : Prop :=
  ∀ C : ConnectedComponents D.Carrier,
    isStandardFactor (D.component C) ∨
      isProjectiveThreeSpaceConnectedSum (D.component C)

theorem componentwise_isPoincareStandard_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum
    (D : ClosedOrientedManifold.{u} 3)
    (h : D.componentwiseStandardFactorOrProjectiveThreeSpaceSum) :
    ∀ C : ConnectedComponents D.Carrier, isPoincareStandard (D.component C).Carrier := by
  intro C
  rcases h C with h | h
  · exact isPoincareStandard_of_standard_factor (D.component C) h
  · exact isPoincareStandard_of_isProjectiveThreeSpaceConnectedSum h

theorem componentwiseConnectedSumStandardFactor_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum
    (D : ClosedOrientedManifold.{u} 3)
    (h : D.componentwiseStandardFactorOrProjectiveThreeSpaceSum) :
    D.componentwiseConnectedSumStandardFactor := by
  intro C
  rcases h C with h | h
  · exact ⟨[D.component C], by simpa using h, ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩
  · obtain ⟨ρ⟩ := h
    refine ⟨[projectiveThreeSpaceLift.{u}, projectiveThreeSpaceLift.{u}], ?_, ?_⟩
    · intro F hF
      rw [List.mem_cons, List.mem_cons, List.mem_nil_iff] at hF
      rcases hF with rfl | rfl | hF
      · exact isStandardFactor_projectiveThreeSpaceLift
      · exact isStandardFactor_projectiveThreeSpaceLift
      · exact absurd hF (by simp)
    · exact ⟨ρ⟩

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3}

theorem poincareControlled_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum
    (E : SphericalCutCapTransition M Q)
    (h : E.discarded.componentwiseStandardFactorOrProjectiveThreeSpaceSum) :
    E.poincareControlled :=
  E.poincareControlled_of_componentwiseConnectedSumStandardFactor
    (componentwiseConnectedSumStandardFactor_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum
      E.discarded h)

end SphericalCutCapTransition

end DifferentialGeometry.Topology
