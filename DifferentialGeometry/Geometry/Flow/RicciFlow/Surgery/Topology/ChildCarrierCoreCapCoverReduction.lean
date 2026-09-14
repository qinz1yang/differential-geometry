import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCarrierCoreCapCoverFrontier

set_option autoImplicit false

noncomputable section

open Set Topology

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

structure ChildCarrierCoreCapCoverData (c : ConnectedComponents Q.Carrier) : Type u where
  U : Set (E.ChildCarrier c)
  V : Set (E.ChildCarrier c)
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  cover : U ∪ V = univ
  core_subset_U : Set.range (E.childCoreInclusion c) ⊆ U
  cap_subset_V : (⋃ b : E.ChildCapBoundary c, Set.range (E.childCap c b)) ⊆ V
  simplyConnected_V : SimplyConnectedSpace ↥V
  pathConnected_inter : PathConnectedSpace ↥(U ∩ V)
  retraction : C(↥U, E.ChildCore c)
  retraction_comp_inclusion :
    retraction.comp (E.childCoreInclusionRestrict c core_subset_U) =
      ContinuousMap.id (E.ChildCore c)
  inclusion_comp_retraction_homotopic :
    ((E.childCoreInclusionRestrict c core_subset_U).comp retraction).Homotopic
      (ContinuousMap.id ↥U)

noncomputable def ChildCarrierCoreCapCoverData.toCover {c : ConnectedComponents Q.Carrier}
    (d : ChildCarrierCoreCapCoverData E c) : E.ChildCarrierCoreCapCover c where
  U := d.U
  V := d.V
  x₀ := (Classical.choice d.pathConnected_inter.nonempty).1
  isOpen_U := d.isOpen_U
  isOpen_V := d.isOpen_V
  cover := d.cover
  mem_x₀_U := (Classical.choice d.pathConnected_inter.nonempty).2.1
  mem_x₀_V := (Classical.choice d.pathConnected_inter.nonempty).2.2
  core_subset_U := d.core_subset_U
  cap_subset_V := d.cap_subset_V
  simplyConnected_V := d.simplyConnected_V
  pathConnected_inter := d.pathConnected_inter
  retraction := d.retraction
  retraction_comp_inclusion := d.retraction_comp_inclusion
  inclusion_comp_retraction_homotopic := d.inclusion_comp_retraction_homotopic

noncomputable def ChildCarrierCoreCapCoverData.ofCover {c : ConnectedComponents Q.Carrier}
    (d : E.ChildCarrierCoreCapCover c) : ChildCarrierCoreCapCoverData E c where
  U := d.U
  V := d.V
  isOpen_U := d.isOpen_U
  isOpen_V := d.isOpen_V
  cover := d.cover
  core_subset_U := d.core_subset_U
  cap_subset_V := d.cap_subset_V
  simplyConnected_V := d.simplyConnected_V
  pathConnected_inter := d.pathConnected_inter
  retraction := d.retraction
  retraction_comp_inclusion := d.retraction_comp_inclusion
  inclusion_comp_retraction_homotopic := d.inclusion_comp_retraction_homotopic

theorem nonempty_childCarrierCoreCapCoverData_iff_nonempty
    (c : ConnectedComponents Q.Carrier) :
    Nonempty (ChildCarrierCoreCapCoverData E c) ↔ Nonempty (E.ChildCarrierCoreCapCover c) :=
  ⟨fun h => h.map (ChildCarrierCoreCapCoverData.toCover E),
    fun h => h.map (ChildCarrierCoreCapCoverData.ofCover E)⟩

theorem simplyConnectedSpace_childCarrier_of_data_V_eq_univ
    {c : ConnectedComponents Q.Carrier} (d : ChildCarrierCoreCapCoverData E c)
    (hV : d.V = univ) : SimplyConnectedSpace (E.ChildCarrier c) :=
  E.simplyConnectedSpace_childCarrier_of_cover_univ_V c
    (ChildCarrierCoreCapCoverData.toCover E d) hV

theorem nonempty_childCarrierCoreCapCoverData_of_isEmpty_childCapBoundary
    (c : ConnectedComponents Q.Carrier) [IsEmpty (E.ChildCapBoundary c)]
    (hsc : SimplyConnectedSpace (E.ChildCarrier c)) :
    Nonempty (ChildCarrierCoreCapCoverData E c) :=
  (nonempty_childCarrierCoreCapCoverData_iff_nonempty E c).mpr
    (E.nonempty_childCarrierCoreCapCover_of_isEmpty_childCapBoundary c hsc)

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
