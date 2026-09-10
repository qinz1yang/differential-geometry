import DifferentialGeometry.Topology.ProjectiveSpace.DiskAttachment
import DifferentialGeometry.Topology.Simplex.BallHomeomorphism
import DifferentialGeometry.Topology.Simplex.AttachmentRelativeHomology

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace Poincare.ProjectiveSpace

def simplexAttachingMap (n : ℕ) :
    TopCat.of (Poincare.Simplex.boundary (Fin (n + 1))) ⟶
      TopCat.of (Projectivization ℝ (Fin n → ℝ)) :=
  (TopCat.isoOfHomeo (Poincare.Simplex.stdSimplexBoundarySphereHomeomorph n)).hom ≫
    diskAttachingMap (Fin n → ℝ)

def simplexCellMap (n : ℕ) :
    TopCat.of (stdSimplex ℝ (Fin (n + 1))) ⟶
      TopCat.of (Projectivization ℝ ((Fin n → ℝ) × ℝ)) :=
  (TopCat.isoOfHomeo (Poincare.Simplex.stdSimplexBallHomeomorph n)).hom ≫
    diskCellMap (Fin n → ℝ)


@[reassoc]
theorem boundarySphereHomeomorph_diskBoundaryInclusion (n : ℕ) :
    (TopCat.isoOfHomeo (Poincare.Simplex.stdSimplexBoundarySphereHomeomorph n)).hom ≫
        diskBoundaryInclusion (Fin n → ℝ) =
      Poincare.Simplex.Attachment.boundaryι ≫
        (TopCat.isoOfHomeo (Poincare.Simplex.stdSimplexBallHomeomorph n)).hom := by
  ext x
  rfl

theorem simplexAttachment_isPushout (n : ℕ) :
    IsPushout Poincare.Simplex.Attachment.boundaryι (simplexAttachingMap n)
      (simplexCellMap n) (projectiveCoordinateInclusion (Fin n → ℝ)) := by
  apply (diskAttachment_isPushout (Fin n → ℝ)).of_iso'
    (TopCat.isoOfHomeo (Poincare.Simplex.stdSimplexBoundarySphereHomeomorph n))
    (TopCat.isoOfHomeo (Poincare.Simplex.stdSimplexBallHomeomorph n))
    (Iso.refl _) (Iso.refl _)
  · exact boundarySphereHomeomorph_diskBoundaryInclusion n
  · simp [simplexAttachingMap]
  · simp [simplexCellMap]
  · simp

variable {k : Type} [Ring k] (R : ModuleCat.{0} k)

def simplexRelativeChainMap (n : ℕ) :
    Poincare.Homology.relativeChainComplex (TopCat.of (stdSimplex ℝ (Fin (n + 1))))
        (Poincare.Simplex.boundary (Fin (n + 1))) R ⟶
      Poincare.Homology.relativeChainComplex (TopCat.of (Projectivization ℝ ((Fin n → ℝ) × ℝ)))
        (Set.range (projectiveCoordinateInclusion (Fin n → ℝ))) R :=
  Poincare.Simplex.Attachment.cellRelativeChainMap R (simplexAttachment_isPushout n)

theorem quasiIso_simplexRelativeChainMap (n : ℕ) : QuasiIso (simplexRelativeChainMap R n) :=
  Poincare.Simplex.Attachment.quasiIso_cellRelativeChainMap R (simplexAttachment_isPushout n)

@[reassoc (attr := simp)]
theorem relativeProjection_simplexRelativeChainMap (n : ℕ) :
    Poincare.Homology.relativeProjection (TopCat.of (stdSimplex ℝ (Fin (n + 1))))
        (Poincare.Simplex.boundary (Fin (n + 1))) R ≫ simplexRelativeChainMap R n =
      ((singularChainComplexFunctor (ModuleCat.{0} k)).obj R).map (simplexCellMap n) ≫
        Poincare.Homology.relativeProjection (TopCat.of (Projectivization ℝ ((Fin n → ℝ) × ℝ)))
          (Set.range (projectiveCoordinateInclusion (Fin n → ℝ))) R :=
  Poincare.Simplex.Attachment.relativeProjection_cellRelativeChainMap R (simplexAttachment_isPushout n)

end Poincare.ProjectiveSpace
