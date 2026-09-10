import DifferentialGeometry.Topology.ProjectiveSpace.SimplexAttachment
import DifferentialGeometry.Topology.ProjectiveSpace.Coordinates
import DifferentialGeometry.Topology.Simplex.AttachmentEuler

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Simplicial

namespace DifferentialGeometry.ProjectiveSpace

variable (k : Type) [Field k]

private theorem coordinateExtension_finite_euler (n : ℕ)
    (hOld : DifferentialGeometry.Homology.finiteHomologyType k (TopCat.of (Projectivization ℝ (Fin n → ℝ)))) :
    DifferentialGeometry.Homology.finiteHomologyType k (TopCat.of (Projectivization ℝ ((Fin n → ℝ) × ℝ))) ∧
      DifferentialGeometry.Homology.eulerChar k (TopCat.of (Projectivization ℝ ((Fin n → ℝ) × ℝ))) =
        DifferentialGeometry.Homology.eulerChar k (TopCat.of (Projectivization ℝ (Fin n → ℝ))) + 1 -
          DifferentialGeometry.Homology.eulerChar k (TopCat.of (DifferentialGeometry.Simplex.boundary (Fin (n + 1)))) := by
  have hfin := DifferentialGeometry.Simplex.Attachment.finiteHomologyType_of_attachment k
    (simplexAttachment_isPushout n) hOld
  have he := DifferentialGeometry.Simplex.Attachment.eulerChar_attachment k
    (simplexAttachment_isPushout n) hOld
  refine ⟨hfin, ?_⟩
  rw [DifferentialGeometry.Simplex.eulerChar_boundary]
  omega

private theorem isEmpty_coordinateProjective_zero : IsEmpty (Projectivization ℝ (Fin 0 → ℝ)) := by
  constructor
  intro p
  induction p using Projectivization.ind with
  | h v hv => exact hv (Subsingleton.elim _ _)

theorem finiteHomologyType_coordinateProjective (n : ℕ) :
    DifferentialGeometry.Homology.finiteHomologyType k (TopCat.of (Projectivization ℝ (Fin n → ℝ))) := by
  induction n with
  | zero =>
    let := isEmpty_coordinateProjective_zero
    exact DifferentialGeometry.Homology.finiteHomologyType_of_subsingleton k
  | succ n hn =>
    exact (DifferentialGeometry.Homology.finiteHomologyType_iff_of_homeomorph k
      (coordinateExtensionHomeomorph n)).mp (coordinateExtension_finite_euler k n hn).1

theorem eulerChar_coordinateProjective_succ (n : ℕ) :
    DifferentialGeometry.Homology.eulerChar k (TopCat.of (Projectivization ℝ (Fin (n + 1) → ℝ))) =
      DifferentialGeometry.Homology.eulerChar k (TopCat.of (Projectivization ℝ (Fin n → ℝ))) + 1 -
        DifferentialGeometry.Homology.eulerChar k (TopCat.of (DifferentialGeometry.Simplex.boundary (Fin (n + 1)))) := by
  rw [← DifferentialGeometry.Homology.eulerChar_eq_of_homeomorph k
    (X := TopCat.of (Projectivization ℝ ((Fin n → ℝ) × ℝ))) (coordinateExtensionHomeomorph n)]
  exact (coordinateExtension_finite_euler k n (finiteHomologyType_coordinateProjective k n)).2

private theorem eulerChar_coordinateProjective_zero :
    DifferentialGeometry.Homology.eulerChar k (TopCat.of (Projectivization ℝ (Fin 0 → ℝ))) = 0 := by
  let := isEmpty_coordinateProjective_zero
  exact DifferentialGeometry.Homology.eulerChar_of_isEmpty k

theorem eulerChar_projectiveLine :
    DifferentialGeometry.Homology.eulerChar k (TopCat.of (Projectivization ℝ (EuclideanSpace ℝ (Fin 2)))) = 0 := by
  rw [DifferentialGeometry.Homology.eulerChar_eq_of_homeomorph k
    (Y := TopCat.of (Projectivization ℝ (Fin 2 → ℝ))) (euclideanCoordinateHomeomorph 2),
    eulerChar_coordinateProjective_succ k 1, eulerChar_coordinateProjective_succ k 0,
    eulerChar_coordinateProjective_zero k, DifferentialGeometry.Simplex.eulerChar_boundary k 0,
    DifferentialGeometry.Simplex.eulerChar_boundary k 1]
  norm_num

theorem finiteHomologyType_projectivePlane :
    DifferentialGeometry.Homology.finiteHomologyType k
      (TopCat.of (Projectivization ℝ (EuclideanSpace ℝ (Fin 3)))) :=
  (DifferentialGeometry.Homology.finiteHomologyType_iff_of_homeomorph k
    (euclideanCoordinateHomeomorph 3)).mpr (finiteHomologyType_coordinateProjective k 3)

theorem eulerChar_projectivePlane :
    DifferentialGeometry.Homology.eulerChar k (TopCat.of (Projectivization ℝ (EuclideanSpace ℝ (Fin 3)))) = 1 := by
  rw [DifferentialGeometry.Homology.eulerChar_eq_of_homeomorph k
    (Y := TopCat.of (Projectivization ℝ (Fin 3 → ℝ))) (euclideanCoordinateHomeomorph 3),
    eulerChar_coordinateProjective_succ k 2, eulerChar_coordinateProjective_succ k 1,
    eulerChar_coordinateProjective_succ k 0, eulerChar_coordinateProjective_zero k,
    DifferentialGeometry.Simplex.eulerChar_boundary k 0, DifferentialGeometry.Simplex.eulerChar_boundary k 1,
    DifferentialGeometry.Simplex.eulerChar_boundary k 2]
  norm_num

end DifferentialGeometry.ProjectiveSpace
