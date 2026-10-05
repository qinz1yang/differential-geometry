import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopRawExclusion
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopCornerSublevel

/-!
The actual original compact cornered base equals the genuine global common defining sublevels.
Its true first-Clifford lift follows from the whole ambient cover and the entire deep core face.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private theorem sublevelExact_coreClosed : IsClosed (Set.range loopComplementVertex.map) :=
  loopComplementVertex.isClosedEmbedding_map.isClosed_range

theorem loopCircleSublevel_region {z : loopCircleBase}
    (hz : ∀ l : Fin 3, loopDefining l z ≤ 0) : loopCircleSection z ∈ loopCircleRegion := by
  by_contra hn
  by_cases hc : loopCircleSection z ∈ Set.range loopComplementVertex.map
  · have hlow : 3/4 ≤ cliffordHeight (loopCircleSection z) := by
      rwa [loopComplementVertex_range] at hc
    have hg : 1/8-‖z.val‖^2 ≤ 0 := hz 2
    have hheight := loopCircleSection_height z
    have he : cliffordHeight (loopCircleSection z) = 3/4 := by linarith
    have hf : loopCircleSection z ∈ loopComplementFace := by
      rwa [loopComplementFace_height]
    have hi : loopCircleSection z ∈ loopCircleRegion ∩ Set.range loopComplementVertex.map := by
      rwa [loopCircleRegion_core_inter]
    exact hn hi.1
  · have hsub : loopCircleRegionᶜ ⊆ loopRawPieces ∪ Set.range loopComplementVertex.map := by
      intro p hp
      have hcover : p ∈ ((loopRawPieces ∪ Set.range loopComplementVertex.map) ∪
          loopCircleRegion) := by
        rw [loopRawPieces,loopCircleRegion_cover]
        trivial
      exact hcover.resolve_right hp
    have hio : loopCircleSection z ∈ interior
        (loopRawPieces ∪ Set.range loopComplementVertex.map) := by
      apply interior_mono hsub
      rw [loopCircleRegion_compact.isClosed.isOpen_compl.interior_eq]
      exact hn
    have hic : loopCircleSection z ∈ interior (Set.range loopComplementVertex.map)ᶜ := by
      rw [sublevelExact_coreClosed.isOpen_compl.interior_eq]
      exact hc
    have hir := interior_union_inter_interior_compl_right_subset ⟨hio,hic⟩
    exact loopRawPieces_sublevel_notInterior hz hir

theorem loopCircleCornerBase_sublevel {z : loopCircleBase} :
    z ∈ loopCircleCornerBase ↔ ∀ l : Fin 3, loopDefining l z ≤ 0 := by
  constructor
  · exact loopCircleCornerBase_family
  · intro hz
    obtain ⟨q,hq,he⟩ := loopCircleSublevel_region hz
    have hqe : q = ⟨loopCircleSection z, loopCircleSection_domain z⟩ := Subtype.ext he
    rw [hqe] at hq
    change loopCircleProjection ⟨loopCircleSection z, loopCircleSection_domain z⟩
      ∈ loopCircleCornerBase at hq
    rw [loopCircleSection_projection] at hq
    exact hq

end GC.GraphManifold.Assembly
