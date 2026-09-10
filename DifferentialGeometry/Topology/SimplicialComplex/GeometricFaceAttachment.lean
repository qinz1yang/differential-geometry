import DifferentialGeometry.Topology.Category.TopCat.ClosedCover
import DifferentialGeometry.Topology.Simplex.Attachment
import DifferentialGeometry.Topology.SimplicialComplex.GeometricFaceHomeomorphism
import DifferentialGeometry.Topology.SimplicialComplex.GeometricCompactness
import DifferentialGeometry.Topology.SimplicialComplex.GeometricInclusion

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Set
namespace Poincare.Topology.SimplicialComplex
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : Geometry.SimplicialComplex ℝ E) {s : Finset E}


def geometricFaceCellMap (hs : s ∈ K.faces) :
    TopCat.of (stdSimplex ℝ s) ⟶ TopCat.of K.space :=
  (TopCat.isoOfHomeo (geometricFaceHomeomorphism K hs)).hom ≫
    Poincare.TopCat.subspaceInclusion (Geometry.SimplicialComplex.convexHull_subset_space hs)


def geometricFaceAttachingMap (hs : s ∈ K.faces) :
    TopCat.of (Poincare.Simplex.boundary s) ⟶ TopCat.of (geometricFaceCostar K s).space :=
  (TopCat.isoOfHomeo (geometricFaceBoundaryHomeomorphism K hs)).hom ≫
    Poincare.TopCat.subspaceInclusion inter_subset_right


@[simp]
theorem geometricFaceCellMap_apply (hs : s ∈ K.faces) (x : stdSimplex ℝ s) :
    (geometricFaceCellMap K hs x : E) =
      Poincare.Simplex.vertexMap (fun i : s => (i : E)) x := rfl


@[simp]
theorem geometricFaceAttachingMap_apply (hs : s ∈ K.faces) (x : Poincare.Simplex.boundary s) :
    (geometricFaceAttachingMap K hs x : E) =
      Poincare.Simplex.vertexMap (fun i : s => (i : E)) x.val := rfl

@[reassoc (attr := simp)]
theorem geometricFaceAttachingMap_inclusion (hs : s ∈ K.faces) :
    Poincare.Simplex.Attachment.boundaryι ≫ geometricFaceCellMap K hs =
      geometricFaceAttachingMap K hs ≫ geometricInclusion (geometricFaceCostar_le K s) := rfl

theorem geometricFaceAttachment_isPushout [Finite K.faces] (hs : s ∈ K.facets) :
    IsPushout Poincare.Simplex.Attachment.boundaryι (geometricFaceAttachingMap K hs.1)
      (geometricFaceCellMap K hs.1) (geometricInclusion (geometricFaceCostar_le K s)) := by
  have hU : K.space = convexHull ℝ (s : Set E) ∪ (geometricFaceCostar K s).space :=
    (space_geometricFaceCostar_union K s hs).trans (union_comm _ _)
  apply (Poincare.TopCat.closedUnion_isPushout
    (s.finite_toSet.isCompact_convexHull ℝ).isClosed
    (isCompact_geometricSpace (geometricFaceCostar K s)).isClosed).of_iso'
    (TopCat.isoOfHomeo (geometricFaceBoundaryHomeomorphism K hs.1))
    (TopCat.isoOfHomeo (geometricFaceHomeomorphism K hs.1)) (Iso.refl _)
    (TopCat.isoOfHomeo (Homeomorph.setCongr hU))
  · ext x
    rfl
  · ext x
    rfl
  · ext x
    rfl
  · ext x
    rfl

end Poincare.Topology.SimplicialComplex
