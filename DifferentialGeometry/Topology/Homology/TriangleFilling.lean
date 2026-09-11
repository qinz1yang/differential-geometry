import DifferentialGeometry.Topology.Homotopy.TriangleFaces
import DifferentialGeometry.Topology.Homotopy.TrianglePathBoundary
import DifferentialGeometry.Topology.Homotopy.ConvexPlaneExtension
import DifferentialGeometry.Topology.Homology.PathEvaluation



noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set
open scoped Simplicial Topology

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X] {a b c : X}




theorem exists_integralPathTriangle (p : Path a b) (q : Path b c) (r : Path a c) :
    ∃ σ : integralSingularSimplex 2 X,
      ∀ i : Fin 3, (TopCat.toSSet.obj (TopCat.of X)).δ i σ =
        ![integralPathSimplex q, integralPathSimplex r, integralPathSimplex p] i := by
  obtain ⟨F, hF⟩ := exists_convex_plane_boundary_extension convex_planeTriangle
    isClosed_planeTriangle isBounded_planeTriangle planeTriangle_interior_nonempty
      (triangleBoundaryMap p q r)
  let σ : integralSingularSimplex 2 X := (integralSingularSimplexEquiv 2 X).symm
    (F.comp ⟨simplexTriangleHomeomorph, simplexTriangleHomeomorph.continuous⟩)
  have hf (i : Fin 3) (t : stdSimplex ℝ (Fin 2)) :
      integralSingularSimplexEquiv 1 X ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) t =
        triangleBoundaryPaths p q r (i, stdSimplexHomeomorphUnitInterval t) := by
    change (TopCat.of X).toSSetObjEquiv _ ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) t = _
    rw [TopCat.toSSetObjEquiv_δ_apply]
    change integralSingularSimplexEquiv 2 X ((integralSingularSimplexEquiv 2 X).symm
      (F.comp ⟨simplexTriangleHomeomorph, simplexTriangleHomeomorph.continuous⟩))
        (stdSimplex.map i.succAbove t) = _
    rw [Equiv.apply_symm_apply]
    change F (simplexTriangleHomeomorph (stdSimplex.map i.succAbove t)) = _
    let z := planeTriangleEdge i (stdSimplexHomeomorphUnitInterval t)
    have he : simplexTriangleHomeomorph (stdSimplex.map i.succAbove t) =
        (⟨z.val, isClosed_planeTriangle.frontier_subset z.property⟩ : planeTriangle) :=
      Subtype.ext (simplexTriangleHomeomorph_face i t)
    rw [he]
    exact (hF z).trans (triangleBoundaryMap_edge p q r i (stdSimplexHomeomorphUnitInterval t))
  refine ⟨σ, fun i => (integralSingularSimplexEquiv 1 X).injective ?_⟩
  apply ContinuousMap.ext
  intro t
  rw [hf]
  fin_cases i <;> exact (integralPathSimplex_apply _ t).symm


theorem exists_integralPathTriangle_boundary (p : Path a b) (q : Path b c) (r : Path a c) :
    ∃ σ : integralSingularSimplex 2 X,
      (integralSingularChains X).d 2 1 (integralSimplexChain 2 σ) =
        integralPathChain q - integralPathChain r + integralPathChain p := by
  obtain ⟨σ, hσ⟩ := exists_integralPathTriangle p q r
  refine ⟨σ, ?_⟩
  rw [integralSimplexChain_boundary_two, hσ 0, hσ 1, hσ 2]
  rfl

end DifferentialGeometry.Topology
