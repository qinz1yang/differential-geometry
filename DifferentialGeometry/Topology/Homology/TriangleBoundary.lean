import DifferentialGeometry.Topology.Homology.TetrahedronBoundary
import DifferentialGeometry.Topology.Homology.TriangleRayComplement
import DifferentialGeometry.Topology.Homology.ZeroHomologyMaps

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module
open scoped Simplicial Topology

namespace DifferentialGeometry.Topology.SimplexDegree

universe u

def standardTriangleEdge (i : Fin 3) : C(stdSimplex ℝ (Fin 2), liftedSphereSpace.{u} 0) :=
  affineSimplexMap (standardTriangleVertex ∘ i.succAbove)

theorem standardTriangleEdge_two_mem_negativeDiagonalRayComplement
    (q : stdSimplex ℝ (Fin 2)) :
    standardTriangleEdge 2 q ∈ planeNegativeDiagonalRayComplement.{u} := by
  rintro ⟨r, hr, hc⟩
  have hfin : (2 : Fin 3).succAbove (1 : Fin 2) = 1 := rfl
  have h0 := hc 0
  have h1 := hc 1
  simp [standardTriangleEdge, affineSimplexMap, standardTriangleVertex, Fin.sum_univ_two, hfin] at h0 h1
  have hs := q.property.2
  rw [Fin.sum_univ_two] at hs
  linarith

theorem standardTriangleEdge_zero_mem_positiveDiagonalRayComplement
    (q : stdSimplex ℝ (Fin 2)) :
    standardTriangleEdge 0 q ∈ planePositiveDiagonalRayComplement.{u} := by
  rintro ⟨r, hr, hc⟩
  have h0 := hc 0
  have h1 := hc 1
  simp [standardTriangleEdge, affineSimplexMap, standardTriangleVertex, Fin.sum_univ_two] at h0 h1
  have hs := q.property.2
  have hn := q.property.1 1
  rw [Fin.sum_univ_two] at hs
  linarith

theorem standardTriangleEdge_one_mem_positiveDiagonalRayComplement
    (q : stdSimplex ℝ (Fin 2)) :
    standardTriangleEdge 1 q ∈ planePositiveDiagonalRayComplement.{u} := by
  rintro ⟨r, hr, hc⟩
  have h0 := hc 0
  have h1 := hc 1
  simp [standardTriangleEdge, affineSimplexMap, standardTriangleVertex, Fin.sum_univ_two] at h0 h1
  have hs := q.property.2
  have hn := q.property.1 1
  rw [Fin.sum_univ_two] at hs
  linarith

theorem standardTriangleEdge_ne_zero (i : Fin 3) (q : stdSimplex ℝ (Fin 2)) :
    standardTriangleEdge i q ≠ (0 : liftedSphereSpace.{u} 0) := by
  intro h
  fin_cases i <;> dsimp at h
  · exact standardTriangleEdge_zero_mem_positiveDiagonalRayComplement q
      ⟨0, le_rfl, fun i => by rw [h]; rfl⟩
  · exact standardTriangleEdge_one_mem_positiveDiagonalRayComplement q
      ⟨0, le_rfl, fun i => by rw [h]; rfl⟩
  · exact standardTriangleEdge_two_mem_negativeDiagonalRayComplement q
      ⟨0, le_rfl, fun i => by rw [h]; rfl⟩

def puncturedTriangleEdge (i : Fin 3) : C(stdSimplex ℝ (Fin 2), puncturedPlane.{u}) :=
  ⟨fun q => ⟨standardTriangleEdge i q, standardTriangleEdge_ne_zero i q⟩,
    (standardTriangleEdge i).continuous.subtype_mk _⟩

private theorem triangle_simplexChain_comp {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (f : C(X, Y)) (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    integralSimplexChain n σ ≫ (integralSingularChainMap f).f n =
      integralSimplexChain n (f.comp σ) :=
  SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of X))
    (TopCat.toSSet.obj (TopCat.of Y)) (TopCat.toSSet.map (TopCat.ofHom f))
    integralSingularCoefficients
    ((TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋n⦌)).symm σ)

private def puncturedTriangleBoundaryChain : integralSingularCoefficients ⟶
    (integralSingularChains puncturedPlane.{u}).X 1 :=
  integralSimplexChain 1 (puncturedTriangleEdge 0) -
    integralSimplexChain 1 (puncturedTriangleEdge 1) +
      integralSimplexChain 1 (puncturedTriangleEdge 2)

private theorem standardTriangleChain_boundary :
    (integralSingularChains (liftedSphereSpace.{u} 0)).d 2 1 standardTriangleChain =
      integralSimplexChain 1 (standardTriangleEdge 0) (ULift.up 1) -
        integralSimplexChain 1 (standardTriangleEdge 1) (ULift.up 1) +
          integralSimplexChain 1 (standardTriangleEdge 2) (ULift.up 1) := by
  change (integralSingularChains (liftedSphereSpace.{u} 0)).d 2 1
      (DifferentialGeometry.Topology.integralSimplexChain 2 (affineSingularSimplex 2 standardTriangleVertex)) = _
  rw [DifferentialGeometry.Topology.integralSimplexChain_boundary_two]
  simp only [affineSingularSimplex_face]
  rfl

private theorem puncturedTriangleBoundaryChain_inclusion :
    (integralSingularChainMap (singularSubspaceInclusion puncturedPlane.{u})).f 1
      (puncturedTriangleBoundaryChain (ULift.up 1)) =
      (integralSingularChains (liftedSphereSpace.{u} 0)).d 2 1 standardTriangleChain := by
  rw [standardTriangleChain_boundary]
  have h (i : Fin 3) :
      (integralSingularChainMap (singularSubspaceInclusion puncturedPlane)).f 1
        (integralSimplexChain 1 (puncturedTriangleEdge i) (ULift.up 1)) =
          integralSimplexChain 1 (standardTriangleEdge i) (ULift.up 1) :=
    congrArg (fun φ : integralSingularCoefficients ⟶
      (integralSingularChains (liftedSphereSpace.{u} 0)).X 1 => φ (ULift.up 1))
        (triangle_simplexChain_comp 1 (singularSubspaceInclusion puncturedPlane) (puncturedTriangleEdge i))
  change (integralSingularChainMap (singularSubspaceInclusion puncturedPlane)).f 1
    (integralSimplexChain 1 (puncturedTriangleEdge 0) (ULift.up 1) -
      integralSimplexChain 1 (puncturedTriangleEdge 1) (ULift.up 1) +
        integralSimplexChain 1 (puncturedTriangleEdge 2) (ULift.up 1)) = _
  rw [map_add, map_sub, h 0, h 1, h 2]

private theorem puncturedTriangleBoundaryChain_eq :
    puncturedTriangleBoundaryChain = integralChainHom 1 standardTriangleBoundaryChain.{u} := by
  apply integralChainHom_ext
  apply integralSingularChainInclusion_injective 1 puncturedPlane
  rw [puncturedTriangleBoundaryChain_inclusion, standardTriangleBoundaryChain_inclusion]

private def trianglePositiveEdgeZero :
    C(stdSimplex ℝ (Fin 2), puncturedPlanePositiveRayComplement.{u}) :=
  ⟨fun q => ⟨puncturedTriangleEdge 0 q,
      standardTriangleEdge_zero_mem_positiveDiagonalRayComplement.{u} q⟩,
    (puncturedTriangleEdge 0).continuous.subtype_mk _⟩

private def trianglePositiveEdgeOne :
    C(stdSimplex ℝ (Fin 2), puncturedPlanePositiveRayComplement.{u}) :=
  ⟨fun q => ⟨puncturedTriangleEdge 1 q,
      standardTriangleEdge_one_mem_positiveDiagonalRayComplement.{u} q⟩,
    (puncturedTriangleEdge 1).continuous.subtype_mk _⟩

private def triangleNegativeEdge :
    C(stdSimplex ℝ (Fin 2), puncturedPlaneNegativeRayComplement.{u}) :=
  ⟨fun q => ⟨puncturedTriangleEdge 2 q,
      standardTriangleEdge_two_mem_negativeDiagonalRayComplement.{u} q⟩,
    (puncturedTriangleEdge 2).continuous.subtype_mk _⟩

def trianglePositiveEdgeChain : integralSingularCoefficients ⟶
    (integralSingularChains puncturedPlanePositiveRayComplement.{u}).X 1 :=
  integralSimplexChain 1 trianglePositiveEdgeZero - integralSimplexChain 1 trianglePositiveEdgeOne

def triangleNegativeEdgeChain : integralSingularCoefficients ⟶
    (integralSingularChains puncturedPlaneNegativeRayComplement.{u}).X 1 :=
  integralSimplexChain 1 triangleNegativeEdge

theorem triangleEdgeChain_split :
    trianglePositiveEdgeChain ≫
        (integralSingularChainMap (singularSubspaceInclusion puncturedPlanePositiveRayComplement)).f 1 +
      triangleNegativeEdgeChain ≫
        (integralSingularChainMap (singularSubspaceInclusion puncturedPlaneNegativeRayComplement)).f 1 =
      integralChainHom 1 standardTriangleBoundaryChain.{u} := by
  rw [trianglePositiveEdgeChain, triangleNegativeEdgeChain, Preadditive.sub_comp,
    triangle_simplexChain_comp, triangle_simplexChain_comp, triangle_simplexChain_comp]
  exact puncturedTriangleBoundaryChain_eq

private theorem triangleVertex_mem_positive (i : Fin 2) :
    standardTriangleVertex i.castSucc ∈ planePositiveDiagonalRayComplement.{u} := by
  rintro ⟨r, _, hc⟩
  have h0 := hc 0
  have h1 := hc 1
  fin_cases i <;> norm_num [standardTriangleVertex] at h0 h1 <;> linarith

private theorem triangleVertex_mem_negative (i : Fin 2) :
    standardTriangleVertex i.castSucc ∈ planeNegativeDiagonalRayComplement.{u} := by
  rintro ⟨r, _, hc⟩
  have h0 := hc 0
  have h1 := hc 1
  fin_cases i <;> norm_num [standardTriangleVertex] at h0 h1 <;> linarith

private theorem triangleVertex_ne_zero (i : Fin 2) :
    standardTriangleVertex i.castSucc ≠ (0 : liftedSphereSpace.{u} 0) := by
  intro h
  exact triangleVertex_mem_positive i ⟨0, le_rfl, fun j => by rw [h]; rfl⟩

def triangleOverlapVertex (i : Fin 2) :
    subspaceIntersection puncturedPlanePositiveRayComplement.{u} puncturedPlaneNegativeRayComplement :=
  ⟨⟨⟨standardTriangleVertex i.castSucc, triangleVertex_ne_zero i⟩,
    triangleVertex_mem_negative i⟩, triangleVertex_mem_positive i⟩

def triangleEdgeBoundaryChain : integralSingularCoefficients ⟶
    (integralSingularChains
      (subspaceIntersection puncturedPlanePositiveRayComplement.{u} puncturedPlaneNegativeRayComplement)).X 0 :=
  integralChainHom 0 (integralVertexChain (triangleOverlapVertex 1) -
    integralVertexChain (triangleOverlapVertex 0))

private theorem affineSingularSimplex_zero_vertex {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : Fin 1 → E) :
    TopCat.toSSetObj₀Equiv (affineSingularSimplex 0 v) = v 0 := by
  change affineSimplexMap v default = v 0
  rw [Subsingleton.elim (default : stdSimplex ℝ (Fin 1)) (stdSimplex.vertex 0), affineSimplexMap_vertex]

private theorem standardTriangleEdge_two_boundary :
    (integralSingularChains (liftedSphereSpace.{u} 0)).d 1 0
        (integralSimplexChain 1 (standardTriangleEdge 2) (ULift.up 1)) =
      integralVertexChain (standardTriangleVertex 1) - integralVertexChain (standardTriangleVertex 0) := by
  change (integralSingularChains (liftedSphereSpace.{u} 0)).d 1 0
    (DifferentialGeometry.Topology.integralSimplexChain 1
      (affineSingularSimplex 1 (standardTriangleVertex ∘ (2 : Fin 3).succAbove))) = _
  rw [DifferentialGeometry.Topology.integralSimplexChain_boundary_one]
  simp only [affineSingularSimplex_face, integralSimplexChain_zero_vertex]
  congr 1
  · congr 1
    exact affineSingularSimplex_zero_vertex _
  · congr 1
    exact affineSingularSimplex_zero_vertex _

private def planeNegativeInclusion :
    C(puncturedPlaneNegativeRayComplement.{u}, liftedSphereSpace.{u} 0) :=
  (singularSubspaceInclusion puncturedPlane).comp
    (singularSubspaceInclusion puncturedPlaneNegativeRayComplement)

private theorem planeNegativeChainInclusion_injective (n : ℕ) :
    Function.Injective ((integralSingularChainMap planeNegativeInclusion.{u}).f n) := by
  rw [planeNegativeInclusion, integralSingularChainMap_comp, HomologicalComplex.comp_f]
  exact (integralSingularChainInclusion_injective n puncturedPlane).comp
    (integralSingularChainInclusion_injective n puncturedPlaneNegativeRayComplement)

theorem triangleNegativeEdgeChain_boundary :
    triangleNegativeEdgeChain ≫ (integralSingularChains puncturedPlaneNegativeRayComplement.{u}).d 1 0 =
      integralChainHom 0 (integralVertexChain (triangleOverlapVertex 1).val -
        integralVertexChain (triangleOverlapVertex 0).val) := by
  apply integralChainHom_ext
  apply planeNegativeChainInclusion_injective 0
  change (integralSingularChainMap planeNegativeInclusion).f 0
      ((integralSingularChains puncturedPlaneNegativeRayComplement).d 1 0
        (triangleNegativeEdgeChain (ULift.up 1))) = _
  rw [← integralSingularChainMap_d, map_sub, integralVertexChain_map, integralVertexChain_map]
  have he : (integralSingularChainMap planeNegativeInclusion).f 1
      (triangleNegativeEdgeChain (ULift.up 1)) =
        integralSimplexChain 1 (standardTriangleEdge 2) (ULift.up 1) :=
    congrArg (fun φ : integralSingularCoefficients ⟶
      (integralSingularChains (liftedSphereSpace.{u} 0)).X 1 => φ (ULift.up 1))
      (triangle_simplexChain_comp 1 planeNegativeInclusion triangleNegativeEdge)
  rw [he, standardTriangleEdge_two_boundary]
  rfl

theorem triangleEdgeBoundaryChain_inclusion :
    triangleEdgeBoundaryChain ≫ (integralSingularChainMap
      (singularSubspaceInclusion (subspaceIntersection puncturedPlanePositiveRayComplement
        puncturedPlaneNegativeRayComplement))).f 0 =
      triangleNegativeEdgeChain ≫ (integralSingularChains puncturedPlaneNegativeRayComplement.{u}).d 1 0 := by
  rw [triangleEdgeBoundaryChain, integralChainHom_comp_map, triangleNegativeEdgeChain_boundary,
    map_sub, integralVertexChain_map, integralVertexChain_map]
  rfl

theorem triangleEdgeBoundaryChain_boundary :
    triangleEdgeBoundaryChain ≫ (integralSingularChains
      (subspaceIntersection puncturedPlanePositiveRayComplement.{u} puncturedPlaneNegativeRayComplement)).d 0 0 = 0 := by
  rw [(integralSingularChains
    (subspaceIntersection puncturedPlanePositiveRayComplement.{u} puncturedPlaneNegativeRayComplement)).shape
      0 0 (by simp), Limits.comp_zero]

end DifferentialGeometry.Topology.SimplexDegree
