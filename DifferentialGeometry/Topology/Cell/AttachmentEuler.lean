import DifferentialGeometry.Topology.Category.TopCat.Adjunction
import DifferentialGeometry.Topology.Cell.Coordinates
import DifferentialGeometry.Topology.Simplex.AttachmentEuler

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits DifferentialGeometry.Topology
namespace Poincare.Cell
variable {X : TopCat.{0}} (n : ℕ) (φ : C(CellBoundary n, X))


def boundaryInclusion : TopCat.of (CellBoundary n) ⟶ TopCat.of (ClosedCell n) :=
  TopCat.ofHom ⟨cellBoundaryInclusion n, continuous_cellBoundaryInclusion n⟩


def simplexAttachingMap : TopCat.of (Poincare.Simplex.boundary (Fin (n + 1))) ⟶ X :=
  (TopCat.isoOfHomeo (stdSimplexCellBoundaryHomeomorph n)).hom ≫ TopCat.ofHom φ


def simplexCellMap : TopCat.of (stdSimplex ℝ (Fin (n + 1))) ⟶ TopCat.of (CellAdjunctionSpace n φ) :=
  (TopCat.isoOfHomeo (stdSimplexClosedCellHomeomorph n)).hom ≫
    Poincare.TopCat.Adjunction.cellMap (boundaryInclusion n) (TopCat.ofHom φ)


theorem simplexAttachment_isPushout : IsPushout Poincare.Simplex.Attachment.boundaryι
    (simplexAttachingMap n φ) (simplexCellMap n φ)
    (Poincare.TopCat.Adjunction.lowerMap (boundaryInclusion n) (TopCat.ofHom φ)) := by
  apply (Poincare.TopCat.Adjunction.isPushout (boundaryInclusion n) (TopCat.ofHom φ)).of_iso'
    (TopCat.isoOfHomeo (stdSimplexCellBoundaryHomeomorph n))
    (TopCat.isoOfHomeo (stdSimplexClosedCellHomeomorph n)) (Iso.refl _) (Iso.refl _)
  · ext x : 1
    exact stdSimplexCellBoundaryHomeomorph_inclusion n x
  · simp [simplexAttachingMap]
  · exact (Category.comp_id _).symm
  · simp


theorem finiteHomologyType_cellAdjunction (k : Type) [Field k]
    (hX : Poincare.Homology.finiteHomologyType k X) :
    Poincare.Homology.finiteHomologyType k (TopCat.of (CellAdjunctionSpace n φ)) :=
  Poincare.Simplex.Attachment.finiteHomologyType_of_attachment k (simplexAttachment_isPushout n φ) hX


theorem eulerChar_cellAdjunction (k : Type) [Field k]
    (hX : Poincare.Homology.finiteHomologyType k X) :
    Poincare.Homology.eulerChar k (TopCat.of (CellAdjunctionSpace n φ)) =
      Poincare.Homology.eulerChar k X + (-1 : ℤ)^n :=
  Poincare.Simplex.Attachment.eulerChar_attachment k (simplexAttachment_isPushout n φ) hX

end Poincare.Cell
