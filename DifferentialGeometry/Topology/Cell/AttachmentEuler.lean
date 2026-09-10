import DifferentialGeometry.Topology.Category.TopCat.Adjunction
import DifferentialGeometry.Topology.Cell.Coordinates
import DifferentialGeometry.Topology.Simplex.AttachmentEuler

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits DifferentialGeometry.Topology
namespace DifferentialGeometry.Cell
variable {X : TopCat.{0}} (n : ℕ) (φ : C(CellBoundary n, X))


def boundaryInclusion : TopCat.of (CellBoundary n) ⟶ TopCat.of (ClosedCell n) :=
  TopCat.ofHom ⟨cellBoundaryInclusion n, continuous_cellBoundaryInclusion n⟩


def simplexAttachingMap : TopCat.of (DifferentialGeometry.Simplex.boundary (Fin (n + 1))) ⟶ X :=
  (TopCat.isoOfHomeo (stdSimplexCellBoundaryHomeomorph n)).hom ≫ TopCat.ofHom φ


def simplexCellMap : TopCat.of (stdSimplex ℝ (Fin (n + 1))) ⟶ TopCat.of (CellAdjunctionSpace n φ) :=
  (TopCat.isoOfHomeo (stdSimplexClosedCellHomeomorph n)).hom ≫
    DifferentialGeometry.TopCat.Adjunction.cellMap (boundaryInclusion n) (TopCat.ofHom φ)


theorem simplexAttachment_isPushout : IsPushout DifferentialGeometry.Simplex.Attachment.boundaryι
    (simplexAttachingMap n φ) (simplexCellMap n φ)
    (DifferentialGeometry.TopCat.Adjunction.lowerMap (boundaryInclusion n) (TopCat.ofHom φ)) := by
  apply (DifferentialGeometry.TopCat.Adjunction.isPushout (boundaryInclusion n) (TopCat.ofHom φ)).of_iso'
    (TopCat.isoOfHomeo (stdSimplexCellBoundaryHomeomorph n))
    (TopCat.isoOfHomeo (stdSimplexClosedCellHomeomorph n)) (Iso.refl _) (Iso.refl _)
  · ext x : 1
    exact stdSimplexCellBoundaryHomeomorph_inclusion n x
  · simp [simplexAttachingMap]
  · exact (Category.comp_id _).symm
  · simp


theorem finiteHomologyType_cellAdjunction (k : Type) [Field k]
    (hX : DifferentialGeometry.Homology.finiteHomologyType k X) :
    DifferentialGeometry.Homology.finiteHomologyType k (TopCat.of (CellAdjunctionSpace n φ)) :=
  DifferentialGeometry.Simplex.Attachment.finiteHomologyType_of_attachment k (simplexAttachment_isPushout n φ) hX


theorem eulerChar_cellAdjunction (k : Type) [Field k]
    (hX : DifferentialGeometry.Homology.finiteHomologyType k X) :
    DifferentialGeometry.Homology.eulerChar k (TopCat.of (CellAdjunctionSpace n φ)) =
      DifferentialGeometry.Homology.eulerChar k X + (-1 : ℤ)^n :=
  DifferentialGeometry.Simplex.Attachment.eulerChar_attachment k (simplexAttachment_isPushout n φ) hX

end DifferentialGeometry.Cell
