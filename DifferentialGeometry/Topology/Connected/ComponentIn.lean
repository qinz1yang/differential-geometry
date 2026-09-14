import Mathlib.Topology.Connected.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv

open Set

section

variable {X : Type*} [TopologicalSpace X]

theorem connectedComponentIn_inter_connectedComponentIn {A B : Set X} (hBA : B ⊆ A)
    (x : X) :
    connectedComponentIn (connectedComponentIn A x ∩ B) x = connectedComponentIn B x := by
  apply le_antisymm (connectedComponentIn_mono x inter_subset_right)
  by_cases hx : x ∈ B
  · apply isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx)
    exact subset_inter (connectedComponentIn_mono x hBA) (connectedComponentIn_subset B x)
  · rw [connectedComponentIn_eq_empty hx]
    exact empty_subset _

theorem image_connectedComponentIn_preimage_connectedComponentIn {A B : Set X}
    (hBA : B ⊆ A) {x : X} (hx : x ∈ B) :
    Subtype.val '' connectedComponentIn
      (Subtype.val ⁻¹' B : Set (connectedComponentIn A x))
      ⟨x, mem_connectedComponentIn (hBA hx)⟩ = connectedComponentIn B x := by
  let C := connectedComponentIn A x
  let y : C := ⟨x, mem_connectedComponentIn (hBA hx)⟩
  change Subtype.val '' connectedComponentIn (Subtype.val ⁻¹' B : Set C) y = _
  have hsub : connectedComponentIn B x ⊆ C := connectedComponentIn_mono x hBA
  have himage : Subtype.val '' (Subtype.val ⁻¹' connectedComponentIn B x : Set C) =
      connectedComponentIn B x := by
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hsub]
  apply le_antisymm
  · apply isPreconnected_connectedComponentIn.image _ continuous_subtype_val.continuousOn
      |>.subset_connectedComponentIn
        (mem_image_of_mem Subtype.val (mem_connectedComponentIn hx))
    rintro z ⟨w, hw, rfl⟩
    exact (connectedComponentIn_subset (Subtype.val ⁻¹' B : Set C) y) hw
  · rw [← himage]
    apply image_mono
    have hp : IsPreconnected (Subtype.val ⁻¹' connectedComponentIn B x : Set C) :=
      Topology.IsInducing.subtypeVal.isPreconnected_image.mp
        (himage.symm ▸ isPreconnected_connectedComponentIn)
    exact hp.subset_connectedComponentIn (mem_connectedComponentIn hx)
      (preimage_mono (connectedComponentIn_subset B x))

end

noncomputable section

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {U : Set X} {x : X} (hx : x ∈ U)

def connectedComponentHomeomorphConnectedComponentIn :
    connectedComponent (⟨x, hx⟩ : U) ≃ₜ connectedComponentIn U x :=
  (Topology.IsEmbedding.subtypeVal.homeomorphImage
    (connectedComponent (⟨x, hx⟩ : U))).trans
      (Homeomorph.setCongr (connectedComponentIn_eq_image hx).symm)

theorem simplyConnectedSpace_connectedComponentIn_iff :
    SimplyConnectedSpace (connectedComponentIn U x) ↔
      SimplyConnectedSpace (connectedComponent (⟨x, hx⟩ : U)) :=
  (connectedComponentHomeomorphConnectedComponentIn hx).toHomotopyEquiv.simplyConnectedSpace_iff.symm

end DifferentialGeometry.Topology
