import DifferentialGeometry.Topology.Handle.Defs
import DifferentialGeometry.Topology.Handle.Basic
import DifferentialGeometry.Topology.Handle.Duality
import DifferentialGeometry.Topology.Handle.Retraction
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homotopy.Basic

namespace DifferentialGeometry.Topology.Handle

open ContinuousMap
open unitInterval

def coreProjection (k l : ℕ) : C(StandardHandle k l, ClosedCell k) :=
  ⟨fun p => p.1, continuous_fst⟩

def cocoreProjection (k l : ℕ) : C(StandardHandle k l, ClosedCell l) :=
  ⟨fun p => p.2, continuous_snd⟩

def coreDiskInclusionContinuousMap (k l : ℕ) : C(ClosedCell k, StandardHandle k l) :=
  ⟨coreDiskInclusion k l, continuous_coreDiskInclusion k l⟩

def cocoreDiskInclusionContinuousMap (k l : ℕ) : C(ClosedCell l, StandardHandle k l) :=
  ⟨cocoreDiskInclusion k l, continuous_cocoreDiskInclusion k l⟩

def attachingProjection (k l : ℕ) : C(AttachingRegion k l, CellBoundary k) :=
  ⟨fun a => a.1, continuous_fst⟩

def beltProjection (k l : ℕ) : C(BeltRegion k l, CellBoundary l) :=
  ⟨fun p => p.2, continuous_snd⟩

theorem attachingProjection_apply (k l : ℕ) (a : AttachingRegion k l) :
    attachingProjection k l a = a.1 := rfl

theorem beltProjection_apply (k l : ℕ) (p : BeltRegion k l) :
    beltProjection k l p = p.2 := rfl

theorem attachingProjection_comp_attachingSphereInclusionAttachingRegion (k l : ℕ)
    (u : CellBoundary k) :
    attachingProjection k l (attachingSphereInclusionAttachingRegion k l u) = u := by
  rfl

theorem beltProjection_comp_beltSphereInclusionBeltRegion (k l : ℕ) (v : CellBoundary l) :
    beltProjection k l (beltSphereInclusionBeltRegion k l v) = v := by
  rfl

theorem coreProjection_attachingProjection (k l : ℕ) (a : AttachingRegion k l) :
    coreProjection k l (attachingInclusion k l a) =
      cellBoundaryInclusion k (attachingProjection k l a) := by
  rcases a with ⟨u, y⟩
  simp [coreProjection, attachingInclusion, attachingProjection]

theorem cocoreProjection_beltProjection (k l : ℕ) (p : BeltRegion k l) :
    cocoreProjection k l (beltInclusion k l p) =
      cellBoundaryInclusion l (beltProjection k l p) := by
  rcases p with ⟨x, v⟩
  simp [cocoreProjection, beltInclusion, beltProjection]

theorem coreProjection_attachingSphereInclusionAttachingRegion (k l : ℕ) (u : CellBoundary k) :
    coreProjection k l (attachingInclusion k l (attachingSphereInclusionAttachingRegion k l u)) =
      cellBoundaryInclusion k u := by
  simp [coreProjection, attachingInclusion, attachingSphereInclusionAttachingRegion]

theorem cocoreProjection_beltSphereInclusionBeltRegion (k l : ℕ) (v : CellBoundary l) :
    cocoreProjection k l (beltInclusion k l (beltSphereInclusionBeltRegion k l v)) =
      cellBoundaryInclusion l v := by
  simp [cocoreProjection, beltInclusion, beltSphereInclusionBeltRegion]

theorem coreProjection_attachingInclusion (k l : ℕ) (a : AttachingRegion k l) :
    coreProjection k l (attachingInclusion k l a) = cellBoundaryInclusion k a.1 := by
  rcases a with ⟨u, y⟩
  simp [coreProjection, attachingInclusion]

theorem coreProjection_coreDiskInclusion (k l : ℕ) (x : ClosedCell k) :
    coreProjection k l (coreDiskInclusion k l x) = x := by
  simp [coreProjection, coreDiskInclusion]

theorem cocoreProjection_beltInclusion (k l : ℕ) (a : BeltRegion k l) :
    cocoreProjection k l (beltInclusion k l a) = cellBoundaryInclusion l a.2 := by
  rcases a with ⟨x, v⟩
  simp [cocoreProjection, beltInclusion]

theorem cocoreProjection_cocoreDiskInclusion (k l : ℕ) (y : ClosedCell l) :
    cocoreProjection k l (cocoreDiskInclusion k l y) = y := by
  simp [cocoreProjection, cocoreDiskInclusion]

noncomputable def coreProjectionCenterInclusionHomotopy (k l : ℕ) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (StandardHandle k l))
      ((coreDiskInclusionContinuousMap k l).comp (coreProjection k l))
      (coreDisk k l) := by
  have h₁ : (((ContinuousMap.id (StandardHandle k l)).restrict (coreDisk k l)).comp
        (coreRetract k l).retraction) =
      (coreDiskInclusionContinuousMap k l).comp (coreProjection k l) := by
    apply ContinuousMap.ext
    intro p
    rcases p with ⟨x, y⟩
    apply Prod.ext
    · simp [coreDiskInclusionContinuousMap, coreDiskInclusion, coreProjection, coreRetract]
    · simp [coreDiskInclusionContinuousMap, coreDiskInclusion, coreProjection, coreRetract]
  exact (coreRetract k l).homotopy.cast rfl h₁

theorem coreProjection_centerInclusion_fixed (k l : ℕ) (t : I) {p : StandardHandle k l}
    (hp : p ∈ coreDisk k l) :
    (coreProjectionCenterInclusionHomotopy k l) (t, p) = p :=
  (coreProjectionCenterInclusionHomotopy k l).eq_fst t hp

theorem coreProjection_centerInclusion_preserves_attachingRegion (k l : ℕ) (t : I)
    {p : StandardHandle k l} (hp : p ∈ attachingRegion k l) :
    (coreProjectionCenterInclusionHomotopy k l) (t, p) ∈ attachingRegion k l := by
  simpa [coreProjectionCenterInclusionHomotopy] using
    (coreRetract_preserves_attachingRegion k l t hp)

noncomputable def cocoreProjectionCenterInclusionHomotopy (k l : ℕ) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (StandardHandle k l))
      ((cocoreDiskInclusionContinuousMap k l).comp (cocoreProjection k l))
      (cocoreDisk k l) := by
  have h₁ : (((ContinuousMap.id (StandardHandle k l)).restrict (cocoreDisk k l)).comp
        (cocoreRetract k l).retraction) =
      (cocoreDiskInclusionContinuousMap k l).comp (cocoreProjection k l) := by
    apply ContinuousMap.ext
    intro p
    rcases p with ⟨x, y⟩
    apply Prod.ext
    · simp [cocoreDiskInclusionContinuousMap, cocoreDiskInclusion, cocoreProjection, cocoreRetract]
    · simp [cocoreDiskInclusionContinuousMap, cocoreDiskInclusion, cocoreProjection, cocoreRetract]
  exact (cocoreRetract k l).homotopy.cast rfl h₁

theorem cocoreProjection_centerInclusion_fixed (k l : ℕ) (t : I) {p : StandardHandle k l}
    (hp : p ∈ cocoreDisk k l) :
    (cocoreProjectionCenterInclusionHomotopy k l) (t, p) = p :=
  (cocoreProjectionCenterInclusionHomotopy k l).eq_fst t hp

theorem cocoreProjection_centerInclusion_preserves_beltRegion (k l : ℕ) (t : I)
    {p : StandardHandle k l} (hp : p ∈ beltRegion k l) :
    (cocoreProjectionCenterInclusionHomotopy k l) (t, p) ∈ beltRegion k l := by
  simpa [cocoreProjectionCenterInclusionHomotopy] using
    (cocoreRetract_preserves_beltRegion k l t hp)

theorem coreProjection_swap (k l : ℕ) (p : StandardHandle l k) :
    coreProjection k l (swap l k p) = cocoreProjection l k p := by
  rcases p with ⟨y, x⟩
  simp [coreProjection, cocoreProjection]

theorem cocoreProjection_swap (k l : ℕ) (p : StandardHandle l k) :
    cocoreProjection k l (swap l k p) = coreProjection l k p := by
  rcases p with ⟨y, x⟩
  simp [coreProjection, cocoreProjection]

theorem swap_coreProjection_centerInclusion_homotopy (k l : ℕ) (t : I) (p : StandardHandle k l) :
    swap k l ((coreProjectionCenterInclusionHomotopy k l) (t, p)) =
      (cocoreProjectionCenterInclusionHomotopy l k) (t, swap k l p) := by
  simpa [coreProjectionCenterInclusionHomotopy, cocoreProjectionCenterInclusionHomotopy]
    using coreRetract_swap k l t p

theorem swap_cocoreProjection_centerInclusion_homotopy (k l : ℕ) (t : I) (p : StandardHandle k l) :
    swap k l ((cocoreProjectionCenterInclusionHomotopy k l) (t, p)) =
      (coreProjectionCenterInclusionHomotopy l k) (t, swap k l p) := by
  simpa [coreProjectionCenterInclusionHomotopy, cocoreProjectionCenterInclusionHomotopy]
    using cocoreRetract_swap k l t p

end DifferentialGeometry.Topology.Handle
