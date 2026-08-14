import DifferentialGeometry.Topology.Handle.Defs
import DifferentialGeometry.Topology.Handle.Duality
import DifferentialGeometry.Topology.Homotopy.ClosedCell

namespace DifferentialGeometry.Topology.Handle

open DifferentialGeometry.Topology.Homotopy
open ContinuousMap
open unitInterval

def coreRetract (k l : ℕ) : StrongDeformationRetract (coreDisk k l) :=
  StrongDeformationRetract.congr (by
    ext p
    simp [coreDisk]) (StrongDeformationRetract.prod
      (StrongDeformationRetract.refl (ClosedCell k)) (closedCellRetract l))

def cocoreRetract (k l : ℕ) : StrongDeformationRetract (cocoreDisk k l) :=
  StrongDeformationRetract.congr (by
    ext p
    simp [cocoreDisk]) (StrongDeformationRetract.prod
      (closedCellRetract k) (StrongDeformationRetract.refl (ClosedCell l)))

def attachingSphereRetract (k l : ℕ) :
    StrongDeformationRetract
      ({p : AttachingRegion k l | p.2 = closedCellCenter l} : Set (AttachingRegion k l)) :=
  StrongDeformationRetract.congr (by
    ext p
    simp) (StrongDeformationRetract.prod
      (StrongDeformationRetract.refl (CellBoundary k)) (closedCellRetract l))

def beltSphereRetract (k l : ℕ) :
    StrongDeformationRetract
      ({p : BeltRegion k l | p.1 = closedCellCenter k} : Set (BeltRegion k l)) :=
  StrongDeformationRetract.congr (by
    ext p
    simp) (StrongDeformationRetract.prod
      (closedCellRetract k) (StrongDeformationRetract.refl (CellBoundary l)))

theorem coreRetract_apply (k l : ℕ) (x : ClosedCell k) (y : ClosedCell l) :
    ((coreRetract k l).retraction (x, y) : StandardHandle k l) = (x, closedCellCenter l) := by
  simp [coreRetract]

theorem cocoreRetract_apply (k l : ℕ) (x : ClosedCell k) (y : ClosedCell l) :
    ((cocoreRetract k l).retraction (x, y) : StandardHandle k l) = (closedCellCenter k, y) := by
  simp [cocoreRetract]

theorem attachingSphereRetract_apply (k l : ℕ) (u : CellBoundary k) (y : ClosedCell l) :
    ((attachingSphereRetract k l).retraction (u, y) : AttachingRegion k l) = (u, closedCellCenter l) :=
  by
  rw [attachingSphereRetract]
  rw [StrongDeformationRetract.congr_retraction_apply]
  rw [StrongDeformationRetract.prod_retraction_apply]
  rw [StrongDeformationRetract.refl_retraction_apply]
  rw [closedCellRetract_retraction_apply]

theorem beltSphereRetract_apply (k l : ℕ) (x : ClosedCell k) (v : CellBoundary l) :
    ((beltSphereRetract k l).retraction (x, v) : BeltRegion k l) = (closedCellCenter k, v) := by
  rw [beltSphereRetract]
  rw [StrongDeformationRetract.congr_retraction_apply]
  rw [StrongDeformationRetract.prod_retraction_apply]
  rw [StrongDeformationRetract.refl_retraction_apply]
  rw [closedCellRetract_retraction_apply]

theorem coreRetract_homotopy_apply (k l : ℕ) (t : I) (x : ClosedCell k) (y : ClosedCell l) :
    ((coreRetract k l).homotopy (t, (x, y)) : StandardHandle k l) = (x, radialStep l t y) := by
  rw [coreRetract]
  rw [StrongDeformationRetract.congr_homotopy_apply]
  rw [StrongDeformationRetract.prod_homotopy_apply]
  rw [StrongDeformationRetract.refl_homotopy_apply]
  rw [closedCellRetract_homotopy_apply]

theorem cocoreRetract_homotopy_apply (k l : ℕ) (t : I) (x : ClosedCell k) (y : ClosedCell l) :
    ((cocoreRetract k l).homotopy (t, (x, y)) : StandardHandle k l) = (radialStep k t x, y) := by
  rw [cocoreRetract]
  rw [StrongDeformationRetract.congr_homotopy_apply]
  rw [StrongDeformationRetract.prod_homotopy_apply]
  rw [StrongDeformationRetract.refl_homotopy_apply]
  rw [closedCellRetract_homotopy_apply]

theorem attachingSphereRetract_homotopy_apply (k l : ℕ) (t : I) (u : CellBoundary k)
    (y : ClosedCell l) :
    ((attachingSphereRetract k l).homotopy (t, (u, y)) : AttachingRegion k l) =
      (u, radialStep l t y) := by
  rw [attachingSphereRetract]
  rw [StrongDeformationRetract.congr_homotopy_apply]
  rw [StrongDeformationRetract.prod_homotopy_apply]
  rw [StrongDeformationRetract.refl_homotopy_apply]
  rw [closedCellRetract_homotopy_apply]

theorem beltSphereRetract_homotopy_apply (k l : ℕ) (t : I) (x : ClosedCell k)
    (v : CellBoundary l) :
    ((beltSphereRetract k l).homotopy (t, (x, v)) : BeltRegion k l) =
      (radialStep k t x, v) := by
  rw [beltSphereRetract]
  rw [StrongDeformationRetract.congr_homotopy_apply]
  rw [StrongDeformationRetract.prod_homotopy_apply]
  rw [StrongDeformationRetract.refl_homotopy_apply]
  rw [closedCellRetract_homotopy_apply]

theorem coreRetract_preserves_attachingRegion (k l : ℕ) (t : I) {p : StandardHandle k l}
    (hp : p ∈ attachingRegion k l) :
    (coreRetract k l).homotopy (t, p) ∈ attachingRegion k l := by
  rcases p with ⟨x, y⟩
  simpa [coreRetract, coreRetract_homotopy_apply] using hp

theorem cocoreRetract_preserves_beltRegion (k l : ℕ) (t : I) {p : StandardHandle k l}
    (hp : p ∈ beltRegion k l) :
    (cocoreRetract k l).homotopy (t, p) ∈ beltRegion k l := by
  rcases p with ⟨x, y⟩
  simpa [cocoreRetract, cocoreRetract_homotopy_apply] using hp

theorem coreRetract_swap (k l : ℕ) (t : I) (p : StandardHandle k l) :
    swap k l ((coreRetract k l).homotopy (t, p)) =
      (cocoreRetract l k).homotopy (t, swap k l p) := by
  rcases p with ⟨x, y⟩
  simp [coreRetract_homotopy_apply, cocoreRetract_homotopy_apply]

theorem cocoreRetract_swap (k l : ℕ) (t : I) (p : StandardHandle k l) :
    swap k l ((cocoreRetract k l).homotopy (t, p)) =
      (coreRetract l k).homotopy (t, swap k l p) := by
  rcases p with ⟨x, y⟩
  simp [coreRetract_homotopy_apply, cocoreRetract_homotopy_apply]

theorem attachingSphereRetract_swap (k l : ℕ) (t : I) (p : AttachingRegion k l) :
    swap k l (attachingInclusion k l ((attachingSphereRetract k l).homotopy (t, p))) =
      beltInclusion l k ((beltSphereRetract l k).homotopy (t, Prod.swap p)) := by
  rcases p with ⟨u, y⟩
  rw [attachingSphereRetract_homotopy_apply]
  rw [beltSphereRetract_homotopy_apply]
  simp [attachingInclusion, beltInclusion]

theorem beltSphereRetract_swap (k l : ℕ) (t : I) (p : BeltRegion k l) :
    swap k l (beltInclusion k l ((beltSphereRetract k l).homotopy (t, p))) =
      attachingInclusion l k ((attachingSphereRetract l k).homotopy (t, Prod.swap p)) := by
  rcases p with ⟨x, v⟩
  rw [beltSphereRetract_homotopy_apply]
  rw [attachingSphereRetract_homotopy_apply]
  simp [attachingInclusion, beltInclusion]

end DifferentialGeometry.Topology.Handle
