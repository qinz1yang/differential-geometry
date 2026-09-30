import DifferentialGeometry.Topology.ThreeManifold.CutCap
import Mathlib.Analysis.Normed.Module.Connected
import DifferentialGeometry.Geometry.Boundary.EmbeddingFrontier
import DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Connected.RegularClosedComponents

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

open DifferentialGeometry.Geometry.Boundary

universe u

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem image_interior_core :
    let _ := C.coreCharts
    let _ := C.coreSmooth
    (Subtype.val : T.core → M.Carrier) '' (𝓡∂ 3).interior T.core = interior T.core := by
  let _ := C.coreCharts
  let _ := C.coreSmooth
  simpa only [Subtype.range_val] using image_interior_eq_of_fullRank_embedding
    (Subtype.val : T.core → M.Carrier) C.core_induced.contMDiff
    C.core_induced.isEmbedding
    (fun x => (C.core_induced.isImmersion.isImmersionAt x).mfderiv_injective (by simp))
    (by simp)

include C in
theorem closure_interior_core : closure (interior T.core) = T.core := by
  let _ := C.coreCharts
  let _ := C.coreSmooth
  simpa only [Subtype.range_val] using closure_interior_range_of_fullRank_closedEmbedding
    (Subtype.val : T.core → M.Carrier) C.core_induced.contMDiff
    C.core_compact.isClosed.isClosedEmbedding_subtypeVal
    (fun x => (C.core_induced.isImmersion.isImmersionAt x).mfderiv_injective (by simp))
    (by simp)

include C in
theorem frontier_core : frontier T.core = ⋃ b : T.Boundary, range (T.boundarySphere b) := by
  let _ := C.coreCharts
  let _ := C.coreSmooth
  have hh := image_boundary_eq_frontier_of_fullRank_closedEmbedding
    (Subtype.val : T.core → M.Carrier) C.core_induced.contMDiff
    C.core_compact.isClosed.isClosedEmbedding_subtypeVal
    (fun x => (C.core_induced.isImmersion.isImmersionAt x).mfderiv_injective (by simp))
    (by simp)
  rw [Subtype.range_val, C.core_boundary, image_iUnion] at hh
  rw [← hh]
  congr 1
  funext b
  rw [← range_comp]
  rfl

include C in
theorem coreComponent_geometry (x : T.core) :
    let W := (Subtype.val : T.core → M.Carrier) '' connectedComponent x
    IsCompact W ∧ IsConnected W ∧ closure (interior W) = W ∧
      IsPreconnected (interior W) ∧
      frontier W = ⋃ b : {b : T.Boundary //
        ∃ z, T.coreBoundarySphere b z ∈ connectedComponent x}, range (T.boundarySphere b.val) := by
  let _ := C.coreCharts
  let _ := C.coreSmooth
  let _ : CompactSpace T.core := isCompact_iff_compactSpace.mp C.core_compact
  let _ : LocallyConnectedSpace T.core :=
    ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 3) T.core
  let _ : LocallyConnectedSpace M.Carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M.Carrier
  let W := (Subtype.val : T.core → M.Carrier) '' connectedComponent x
  have hW : W = connectedComponentIn T.core x.val :=
    (connectedComponentIn_eq_image x.property).symm
  have hcompact : IsCompact W := isClosed_connectedComponent.isCompact.image continuous_subtype_val
  have hconn : IsConnected W := isConnected_connectedComponent.image
    Subtype.val continuous_subtype_val.continuousOn
  have hregular : closure (interior W) = W := by
    rw [hW]
    exact DifferentialGeometry.Topology.closure_interior_connectedComponentIn C.closure_interior_core x.val
  have hinterior : IsPreconnected (interior W) := by
    have hh := (DifferentialGeometry.Topology.Manifold.isPreconnected_manifold_interior_inter_connectedComponent
      (I := 𝓡∂ 3) x).image Subtype.val continuous_subtype_val.continuousOn
    have heq : Subtype.val '' ((𝓡∂ 3).interior T.core ∩ connectedComponent x) = interior W := by
      rw [hW, interior_connectedComponentIn_eq_inter, connectedComponentIn_eq_image x.property,
        ← C.image_interior_core, image_inter Subtype.val_injective]
    exact heq ▸ hh
  have hpre (b : T.Boundary) : IsPreconnected (range (T.boundarySphere b)) := by
    let _ : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
      isConnected_iff_connectedSpace.mp
        (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) 0 zero_le_one)
    exact isPreconnected_range (T.boundarySphere b).continuous
  refine ⟨hcompact, hconn, hregular, hinterior, ?_⟩
  change frontier W = _
  rw [hW, frontier_connectedComponentIn_eq_iUnion C.core_compact.isClosed
    (fun b => range (T.boundarySphere b)) hpre C.frontier_core x.val]
  ext y
  constructor
  · intro hy
    obtain ⟨b, ⟨z, ⟨q, hq⟩, hz⟩, hy⟩ := mem_iUnion₂.mp hy
    rw [connectedComponentIn_eq_image x.property] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    have he : T.coreBoundarySphere b q = w := Subtype.ext (hq.trans hwz.symm)
    exact mem_iUnion.mpr ⟨⟨b, ⟨q, he.symm ▸ hw⟩⟩, hy⟩
  · intro hy
    obtain ⟨⟨b, ⟨q, hq⟩⟩, hy⟩ := mem_iUnion.mp hy
    exact mem_iUnion₂.mpr ⟨b, ⟨T.boundarySphere b q, mem_range_self q,
      (connectedComponentIn_eq_image x.property).symm ▸
        mem_image_of_mem Subtype.val hq⟩, hy⟩

end DifferentialGeometry.Topology.SphericalCapping
