import DifferentialGeometry.Topology.ProjectiveSpace.SimplexAttachment
import DifferentialGeometry.Topology.ProjectiveSpace.Coordinates
import DifferentialGeometry.Topology.Simplex.AttachmentEuler

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Simplicial

namespace Poincare.ProjectiveSpace

variable (k : Type) [Field k]

private theorem coordinateExtension_finite_euler (n : ℕ)
    (hOld : Poincare.Homology.finiteHomologyType k (TopCat.of (Projectivization ℝ (Fin n → ℝ)))) :
    Poincare.Homology.finiteHomologyType k (TopCat.of (Projectivization ℝ ((Fin n → ℝ) × ℝ))) ∧
      Poincare.Homology.eulerChar k (TopCat.of (Projectivization ℝ ((Fin n → ℝ) × ℝ))) =
        Poincare.Homology.eulerChar k (TopCat.of (Projectivization ℝ (Fin n → ℝ))) + 1 -
          Poincare.Homology.eulerChar k (TopCat.of (Poincare.Simplex.boundary (Fin (n + 1)))) := by
  have hfin := Poincare.Simplex.Attachment.finiteHomologyType_of_attachment k
    (simplexAttachment_isPushout n) hOld
  have he := Poincare.Simplex.Attachment.eulerChar_attachment k
    (simplexAttachment_isPushout n) hOld
  refine ⟨hfin, ?_⟩
  rw [Poincare.Simplex.eulerChar_boundary]
  omega

private theorem isEmpty_coordinateProjective_zero : IsEmpty (Projectivization ℝ (Fin 0 → ℝ)) := by
  constructor
  intro p
  induction p using Projectivization.ind with
  | h v hv => exact hv (Subsingleton.elim _ _)

theorem finiteHomologyType_coordinateProjective (n : ℕ) :
    Poincare.Homology.finiteHomologyType k (TopCat.of (Projectivization ℝ (Fin n → ℝ))) := by
  induction n with
  | zero =>
    let := isEmpty_coordinateProjective_zero
    exact Poincare.Homology.finiteHomologyType_of_subsingleton k
  | succ n hn =>
    exact (Poincare.Homology.finiteHomologyType_iff_of_homeomorph k
      (coordinateExtensionHomeomorph n)).mp (coordinateExtension_finite_euler k n hn).1

theorem eulerChar_coordinateProjective_succ (n : ℕ) :
    Poincare.Homology.eulerChar k (TopCat.of (Projectivization ℝ (Fin (n + 1) → ℝ))) =
      Poincare.Homology.eulerChar k (TopCat.of (Projectivization ℝ (Fin n → ℝ))) + 1 -
        Poincare.Homology.eulerChar k (TopCat.of (Poincare.Simplex.boundary (Fin (n + 1)))) := by
  rw [← Poincare.Homology.eulerChar_eq_of_homeomorph k
    (X := TopCat.of (Projectivization ℝ ((Fin n → ℝ) × ℝ))) (coordinateExtensionHomeomorph n)]
  exact (coordinateExtension_finite_euler k n (finiteHomologyType_coordinateProjective k n)).2

private theorem eulerChar_coordinateProjective_zero :
    Poincare.Homology.eulerChar k (TopCat.of (Projectivization ℝ (Fin 0 → ℝ))) = 0 := by
  let := isEmpty_coordinateProjective_zero
  exact Poincare.Homology.eulerChar_of_isEmpty k

theorem eulerChar_projectiveLine :
    Poincare.Homology.eulerChar k (TopCat.of (Projectivization ℝ (EuclideanSpace ℝ (Fin 2)))) = 0 := by
  rw [Poincare.Homology.eulerChar_eq_of_homeomorph k
    (Y := TopCat.of (Projectivization ℝ (Fin 2 → ℝ))) (euclideanCoordinateHomeomorph 2),
    eulerChar_coordinateProjective_succ k 1, eulerChar_coordinateProjective_succ k 0,
    eulerChar_coordinateProjective_zero k, Poincare.Simplex.eulerChar_boundary k 0,
    Poincare.Simplex.eulerChar_boundary k 1]
  norm_num

theorem finiteHomologyType_projectivePlane :
    Poincare.Homology.finiteHomologyType k
      (TopCat.of (Projectivization ℝ (EuclideanSpace ℝ (Fin 3)))) :=
  (Poincare.Homology.finiteHomologyType_iff_of_homeomorph k
    (euclideanCoordinateHomeomorph 3)).mpr (finiteHomologyType_coordinateProjective k 3)

theorem eulerChar_projectivePlane :
    Poincare.Homology.eulerChar k (TopCat.of (Projectivization ℝ (EuclideanSpace ℝ (Fin 3)))) = 1 := by
  rw [Poincare.Homology.eulerChar_eq_of_homeomorph k
    (Y := TopCat.of (Projectivization ℝ (Fin 3 → ℝ))) (euclideanCoordinateHomeomorph 3),
    eulerChar_coordinateProjective_succ k 2, eulerChar_coordinateProjective_succ k 1,
    eulerChar_coordinateProjective_succ k 0, eulerChar_coordinateProjective_zero k,
    Poincare.Simplex.eulerChar_boundary k 0, Poincare.Simplex.eulerChar_boundary k 1,
    Poincare.Simplex.eulerChar_boundary k 2]
  norm_num

end Poincare.ProjectiveSpace
