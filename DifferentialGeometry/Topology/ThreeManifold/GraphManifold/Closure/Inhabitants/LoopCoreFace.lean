import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopVertical
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BasicModels
import DifferentialGeometry.Geometry.Boundary.EmbeddingFrontier

/-!
The complementary solid core is an actual solid-torus vertex with one whole torus face.
Its actual model boundary is the frontier of its embedded compact image.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold DifferentialGeometry.Geometry.Boundary
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

def loopComplementModel : Vertex (NoCuts.carrier standardThreeSphereLift.{0}) :=
  .zero loopComplementVertex (.solidTorus (Diffeomorph.refl (𝓡∂ 3) solidTorusSet.{0} ∞))

def loopComplementFace : Set SphereCarrier.{0} :=
  loopComplementVertex.map '' (𝓡∂ 3).boundary loopComplementVertex.Piece

def loopComplementFaceMap (t : Torus) : SphereCarrier.{0} :=
  loopComplementVertex.map (solidTorusBoundary.{0}.torusMap 0 t)

theorem loopComplementFaceMap_range : range loopComplementFaceMap = loopComplementFace := by
  have hb : (𝓡∂ 3).boundary loopComplementVertex.Piece =
      range (fun t => (solidTorusBoundary.{0}.torusMap 0 t : loopComplementVertex.Piece)) := by
    change solidTorusCarrier.{0}.model.boundary solidTorusCarrier.{0}.Carrier =
      range (solidTorusBoundary.{0}.torusMap 0)
    rw [solidTorus_boundary_eq]
    simp only [BoundaryTori.image]
    apply subset_antisymm
    · intro p hp
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      have he : i = 0 := Subsingleton.elim i 0
      exact he ▸ hi
    · intro p hp
      exact mem_iUnion.mpr ⟨0, hp⟩
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨solidTorusBoundary.{0}.torusMap 0 t, ?_, rfl⟩
    rw [hb]
    exact mem_range_self t
  · rintro ⟨q, hq, rfl⟩
    rw [hb] at hq
    obtain ⟨t, rfl⟩ := hq
    exact ⟨t, rfl⟩

theorem loopComplementFaceMap_embedding : Topology.IsEmbedding loopComplementFaceMap :=
  loopComplementVertex.isClosedEmbedding_map.isEmbedding.comp
    (solidTorusBoundary.{0}.torusMap_isEmbedding 0)

def loopComplementFaceModel : loopComplementFace ≃ₜ Circle × Circle :=
  (Homeomorph.setCongr loopComplementFaceMap_range.symm).trans
    loopComplementFaceMap_embedding.toHomeomorph.symm

theorem loopComplementFace_frontier :
    loopComplementFace = frontier (range loopComplementVertex.map) := by
  exact image_boundary_eq_frontier_of_fullRank_closedEmbedding
    loopComplementVertex.map loopComplementVertex.smooth
    loopComplementVertex.isClosedEmbedding_map
    (fun p => (loopComplementVertex.mfderiv_bijective p).injective) (by simp)

theorem loopComplementFace_height :
    loopComplementFace = {p | cliffordHeight p = 3 / 4} := by
  rw [loopComplementFace_frontier, loopComplementVertex_range]
  ext p
  constructor
  · intro hp
    have hclosed : IsClosed {q : SphereCarrier.{0} | 3 / 4 ≤ cliffordHeight q} :=
      isClosed_le continuous_const contMDiff_cliffordHeight.continuous
    have hle : 3 / 4 ≤ cliffordHeight p := hclosed.frontier_subset hp
    have hnot : ¬ 3 / 4 < cliffordHeight p := by
      intro hlt
      have hi : p ∈ interior {q : SphereCarrier.{0} | 3 / 4 ≤ cliffordHeight q} :=
        lt_subset_interior_le continuous_const contMDiff_cliffordHeight.continuous hlt
      exact hp.2 hi
    exact le_antisymm (not_lt.mp hnot) hle
  · intro hp
    have hmem : p ∈ cliffordSeamTarget := by
      have hf := norm_sphereFirst_sq_eq p
      have hs := norm_sphereSecond_sq_eq p
      rw [hp] at hf hs
      refine ⟨?_, ?_⟩
      · intro he
        rw [he, norm_zero] at hf
        norm_num at hf
      · intro he
        rw [he, norm_zero] at hs
        norm_num at hs
    have himage : cliffordSeam.{0}.symm.toOpenPartialHomeomorph.IsImage
        {q : SphereCarrier.{0} | 3 / 4 ≤ cliffordHeight q}
        (Set.univ ×ˢ Set.Ici (3 / 4 : ℝ)) := by
      intro q hq
      change ((cliffordSeamInv q).1 ∈ univ ∧ 3 / 4 ≤ (cliffordSeamInv q).2 ↔
        3 / 4 ≤ cliffordHeight q)
      simp [cliffordSeamInv]
    have hfront := himage.frontier hmem
    rw [frontier_univ_prod_eq, frontier_Ici] at hfront
    apply hfront.mp
    change (cliffordSeamInv p).1 ∈ univ ∧ (cliffordSeamInv p).2 ∈ {3 / 4}
    exact ⟨mem_univ _, hp⟩

end GC.GraphManifold.Assembly
