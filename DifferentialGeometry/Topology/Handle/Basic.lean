import DifferentialGeometry.Topology.Attachment.Basic
import DifferentialGeometry.Topology.Handle.Defs
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Separation.Hausdorff

namespace DifferentialGeometry.Topology.Handle

open Function

theorem continuous_attachingInclusion (k l : ℕ) : Continuous (attachingInclusion k l) := by
  change Continuous (Prod.map (cellBoundaryInclusion k) (id : ClosedCell l → ClosedCell l))
  exact (continuous_cellBoundaryInclusion k).prodMap continuous_id

theorem continuous_beltInclusion (k l : ℕ) : Continuous (beltInclusion k l) := by
  change Continuous (Prod.map (id : ClosedCell k → ClosedCell k) (cellBoundaryInclusion l))
  exact continuous_id.prodMap (continuous_cellBoundaryInclusion l)

theorem continuous_cornerInclusion (k l : ℕ) : Continuous (cornerInclusion k l) := by
  change Continuous (Prod.map (cellBoundaryInclusion k) (cellBoundaryInclusion l))
  exact (continuous_cellBoundaryInclusion k).prodMap (continuous_cellBoundaryInclusion l)

theorem continuous_attachingCornerInclusion (k l : ℕ) : Continuous (attachingCornerInclusion k l) := by
  change Continuous (Prod.map (id : CellBoundary k → CellBoundary k) (cellBoundaryInclusion l))
  exact continuous_id.prodMap (continuous_cellBoundaryInclusion l)

theorem continuous_beltCornerInclusion (k l : ℕ) : Continuous (beltCornerInclusion k l) := by
  change Continuous (Prod.map (cellBoundaryInclusion k) (id : CellBoundary l → CellBoundary l))
  exact (continuous_cellBoundaryInclusion k).prodMap continuous_id

theorem continuous_coreDiskInclusion (k l : ℕ) : Continuous (coreDiskInclusion k l) := by
  change Continuous (fun x : ClosedCell k => (x, closedCellCenter l))
  exact continuous_id.prodMk continuous_const

theorem continuous_cocoreDiskInclusion (k l : ℕ) : Continuous (cocoreDiskInclusion k l) := by
  change Continuous (fun y : ClosedCell l => (closedCellCenter k, y))
  exact continuous_const.prodMk continuous_id

theorem continuous_attachingSphereInclusion (k l : ℕ) : Continuous (attachingSphereInclusion k l) := by
  change Continuous (fun x : CellBoundary k => (cellBoundaryInclusion k x, closedCellCenter l))
  exact (continuous_cellBoundaryInclusion k).prodMk continuous_const

theorem continuous_beltSphereInclusion (k l : ℕ) : Continuous (beltSphereInclusion k l) := by
  change Continuous (fun y : CellBoundary l => (closedCellCenter k, cellBoundaryInclusion l y))
  exact continuous_const.prodMk (continuous_cellBoundaryInclusion l)

theorem continuous_attachingSphereInclusionAttachingRegion (k l : ℕ) :
    Continuous (attachingSphereInclusionAttachingRegion k l) := by
  change Continuous (fun u : CellBoundary k => (u, closedCellCenter l))
  exact continuous_id.prodMk continuous_const

theorem continuous_beltSphereInclusionBeltRegion (k l : ℕ) :
    Continuous (beltSphereInclusionBeltRegion k l) := by
  change Continuous (fun v : CellBoundary l => (closedCellCenter k, v))
  exact continuous_const.prodMk continuous_id

theorem injective_attachingInclusion (k l : ℕ) : Injective (attachingInclusion k l) := by
  change Injective (Prod.map (cellBoundaryInclusion k) (id : ClosedCell l → ClosedCell l))
  exact Injective.prodMap (injective_cellBoundaryInclusion k)
    (injective_id : Injective (id : ClosedCell l → ClosedCell l))

theorem injective_beltInclusion (k l : ℕ) : Injective (beltInclusion k l) := by
  change Injective (Prod.map (id : ClosedCell k → ClosedCell k) (cellBoundaryInclusion l))
  exact Injective.prodMap (injective_id : Injective (id : ClosedCell k → ClosedCell k))
    (injective_cellBoundaryInclusion l)

theorem injective_cornerInclusion (k l : ℕ) : Injective (cornerInclusion k l) := by
  change Injective (Prod.map (cellBoundaryInclusion k) (cellBoundaryInclusion l))
  exact Injective.prodMap (injective_cellBoundaryInclusion k) (injective_cellBoundaryInclusion l)

theorem injective_attachingCornerInclusion (k l : ℕ) : Injective (attachingCornerInclusion k l) := by
  change Injective (Prod.map (id : CellBoundary k → CellBoundary k) (cellBoundaryInclusion l))
  exact Injective.prodMap (injective_id : Injective (id : CellBoundary k → CellBoundary k))
    (injective_cellBoundaryInclusion l)

theorem injective_beltCornerInclusion (k l : ℕ) : Injective (beltCornerInclusion k l) := by
  change Injective (Prod.map (cellBoundaryInclusion k) (id : CellBoundary l → CellBoundary l))
  exact Injective.prodMap (injective_cellBoundaryInclusion k)
    (injective_id : Injective (id : CellBoundary l → CellBoundary l))

theorem injective_coreDiskInclusion (k l : ℕ) : Injective (coreDiskInclusion k l) := by
  intro x y h
  simpa [coreDiskInclusion] using congrArg Prod.fst h

theorem injective_cocoreDiskInclusion (k l : ℕ) : Injective (cocoreDiskInclusion k l) := by
  intro x y h
  simpa [cocoreDiskInclusion] using congrArg Prod.snd h

theorem injective_attachingSphereInclusion (k l : ℕ) : Injective (attachingSphereInclusion k l) := by
  intro x y h
  apply Subtype.ext
  have hfst := congrArg Prod.fst h
  simpa using congrArg (fun z : ClosedCell k => (z : EuclideanSpace ℝ (Fin k))) hfst

theorem injective_beltSphereInclusion (k l : ℕ) : Injective (beltSphereInclusion k l) := by
  intro x y h
  apply Subtype.ext
  have hsnd := congrArg Prod.snd h
  simpa using congrArg (fun z : ClosedCell l => (z : EuclideanSpace ℝ (Fin l))) hsnd

theorem injective_attachingSphereInclusionAttachingRegion (k l : ℕ) :
    Injective (attachingSphereInclusionAttachingRegion k l) := by
  intro x y h
  simpa [attachingSphereInclusionAttachingRegion] using congrArg Prod.fst h

theorem injective_beltSphereInclusionBeltRegion (k l : ℕ) :
    Injective (beltSphereInclusionBeltRegion k l) := by
  intro x y h
  simpa [beltSphereInclusionBeltRegion] using congrArg Prod.snd h

theorem isClosedEmbedding_attachingInclusion (k l : ℕ) : Topology.IsClosedEmbedding (attachingInclusion k l) := by
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_attachingInclusion k l) (injective_attachingInclusion k l)
    ((continuous_attachingInclusion k l).isClosedMap)

theorem isClosedEmbedding_beltInclusion (k l : ℕ) : Topology.IsClosedEmbedding (beltInclusion k l) := by
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_beltInclusion k l) (injective_beltInclusion k l)
    ((continuous_beltInclusion k l).isClosedMap)

theorem isClosedEmbedding_cornerInclusion (k l : ℕ) : Topology.IsClosedEmbedding (cornerInclusion k l) := by
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_cornerInclusion k l) (injective_cornerInclusion k l)
    ((continuous_cornerInclusion k l).isClosedMap)

theorem isClosedEmbedding_attachingCornerInclusion (k l : ℕ) :
    Topology.IsClosedEmbedding (attachingCornerInclusion k l) := by
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_attachingCornerInclusion k l) (injective_attachingCornerInclusion k l)
    ((continuous_attachingCornerInclusion k l).isClosedMap)

theorem isClosedEmbedding_beltCornerInclusion (k l : ℕ) :
    Topology.IsClosedEmbedding (beltCornerInclusion k l) := by
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_beltCornerInclusion k l) (injective_beltCornerInclusion k l)
    ((continuous_beltCornerInclusion k l).isClosedMap)

theorem isClosedEmbedding_coreDiskInclusion (k l : ℕ) : Topology.IsClosedEmbedding (coreDiskInclusion k l) := by
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_coreDiskInclusion k l) (injective_coreDiskInclusion k l)
    ((continuous_coreDiskInclusion k l).isClosedMap)

theorem isClosedEmbedding_cocoreDiskInclusion (k l : ℕ) : Topology.IsClosedEmbedding (cocoreDiskInclusion k l) := by
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_cocoreDiskInclusion k l) (injective_cocoreDiskInclusion k l)
    ((continuous_cocoreDiskInclusion k l).isClosedMap)

theorem isClosedEmbedding_attachingSphereInclusion (k l : ℕ) :
    Topology.IsClosedEmbedding (attachingSphereInclusion k l) := by
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_attachingSphereInclusion k l) (injective_attachingSphereInclusion k l)
    ((continuous_attachingSphereInclusion k l).isClosedMap)

theorem isClosedEmbedding_beltSphereInclusion (k l : ℕ) :
    Topology.IsClosedEmbedding (beltSphereInclusion k l) := by
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_beltSphereInclusion k l) (injective_beltSphereInclusion k l)
    ((continuous_beltSphereInclusion k l).isClosedMap)

theorem isEmbedding_attachingInclusion (k l : ℕ) : Topology.IsEmbedding (attachingInclusion k l) :=
  (isClosedEmbedding_attachingInclusion k l).isEmbedding

theorem isEmbedding_beltInclusion (k l : ℕ) : Topology.IsEmbedding (beltInclusion k l) :=
  (isClosedEmbedding_beltInclusion k l).isEmbedding

theorem isEmbedding_cornerInclusion (k l : ℕ) : Topology.IsEmbedding (cornerInclusion k l) :=
  (isClosedEmbedding_cornerInclusion k l).isEmbedding

theorem isEmbedding_attachingCornerInclusion (k l : ℕ) : Topology.IsEmbedding (attachingCornerInclusion k l) :=
  (isClosedEmbedding_attachingCornerInclusion k l).isEmbedding

theorem isEmbedding_beltCornerInclusion (k l : ℕ) : Topology.IsEmbedding (beltCornerInclusion k l) :=
  (isClosedEmbedding_beltCornerInclusion k l).isEmbedding

theorem isEmbedding_coreDiskInclusion (k l : ℕ) : Topology.IsEmbedding (coreDiskInclusion k l) :=
  (isClosedEmbedding_coreDiskInclusion k l).isEmbedding

theorem isEmbedding_cocoreDiskInclusion (k l : ℕ) : Topology.IsEmbedding (cocoreDiskInclusion k l) :=
  (isClosedEmbedding_cocoreDiskInclusion k l).isEmbedding

theorem isEmbedding_attachingSphereInclusion (k l : ℕ) : Topology.IsEmbedding (attachingSphereInclusion k l) :=
  (isClosedEmbedding_attachingSphereInclusion k l).isEmbedding

theorem isEmbedding_beltSphereInclusion (k l : ℕ) : Topology.IsEmbedding (beltSphereInclusion k l) :=
  (isClosedEmbedding_beltSphereInclusion k l).isEmbedding

theorem range_attachingInclusion (k l : ℕ) :
    Set.range (attachingInclusion k l) = attachingRegion k l := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    simpa [attachingInclusion, attachingRegion, cellBoundaryInclusion] using q.1.2
  · intro hp
    refine ⟨(⟨(p.1 : EuclideanSpace ℝ (Fin k)), hp⟩, p.2), ?_⟩
    apply Prod.ext
    · simp [attachingInclusion, cellBoundaryInclusion]
    · rfl

theorem range_beltInclusion (k l : ℕ) :
    Set.range (beltInclusion k l) = beltRegion k l := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    simpa [beltInclusion, beltRegion, cellBoundaryInclusion] using q.2.2
  · intro hp
    refine ⟨(p.1, ⟨(p.2 : EuclideanSpace ℝ (Fin l)), hp⟩), ?_⟩
    apply Prod.ext
    · rfl
    · simp [beltInclusion, cellBoundaryInclusion]

theorem range_cornerInclusion (k l : ℕ) :
    Set.range (cornerInclusion k l) = corner k l := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    simpa [cornerInclusion, corner, cellBoundaryInclusion] using ⟨q.1.2, q.2.2⟩
  · intro hp
    refine ⟨(⟨(p.1 : EuclideanSpace ℝ (Fin k)), hp.1⟩, ⟨(p.2 : EuclideanSpace ℝ (Fin l)), hp.2⟩), ?_⟩
    apply Prod.ext
    · simp [cornerInclusion, cellBoundaryInclusion]
    · simp [cornerInclusion, cellBoundaryInclusion]

theorem range_attachingCornerInclusion (k l : ℕ) :
    Set.range (attachingCornerInclusion k l) =
      {p : AttachingRegion k l | ‖(p.2 : EuclideanSpace ℝ (Fin l))‖ = 1} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    simpa [attachingCornerInclusion, cellBoundaryInclusion] using q.2.2
  · intro hp
    refine ⟨(p.1, ⟨(p.2 : EuclideanSpace ℝ (Fin l)), hp⟩), ?_⟩
    apply Prod.ext
    · rfl
    · simp [attachingCornerInclusion, cellBoundaryInclusion]

theorem range_beltCornerInclusion (k l : ℕ) :
    Set.range (beltCornerInclusion k l) =
      {p : BeltRegion k l | ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    simpa [beltCornerInclusion, cellBoundaryInclusion] using q.1.2
  · intro hp
    refine ⟨(⟨(p.1 : EuclideanSpace ℝ (Fin k)), hp⟩, p.2), ?_⟩
    apply Prod.ext
    · simp [beltCornerInclusion, cellBoundaryInclusion]
    · rfl

theorem range_coreDiskInclusion (k l : ℕ) :
    Set.range (coreDiskInclusion k l) = coreDisk k l := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    simp [coreDiskInclusion, coreDisk]
  · intro hp
    simp [coreDisk] at hp
    refine ⟨p.1, ?_⟩
    apply Prod.ext
    · rfl
    · simpa [coreDiskInclusion] using hp.symm

theorem range_cocoreDiskInclusion (k l : ℕ) :
    Set.range (cocoreDiskInclusion k l) = cocoreDisk k l := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    simp [cocoreDiskInclusion, cocoreDisk]
  · intro hp
    simp [cocoreDisk] at hp
    refine ⟨p.2, ?_⟩
    apply Prod.ext
    · simpa [cocoreDiskInclusion] using hp.symm
    · rfl

theorem range_attachingSphereInclusion (k l : ℕ) :
    Set.range (attachingSphereInclusion k l) = attachingSphere k l := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    simpa [attachingSphereInclusion, attachingSphere, cellBoundaryInclusion] using
      And.intro x.2 (rfl : closedCellCenter l = closedCellCenter l)
  · intro hp
    refine ⟨⟨(p.1 : EuclideanSpace ℝ (Fin k)), hp.1⟩, ?_⟩
    apply Prod.ext
    · simp [attachingSphereInclusion, cellBoundaryInclusion]
    · simp [attachingSphereInclusion, hp.2]

theorem range_beltSphereInclusion (k l : ℕ) :
    Set.range (beltSphereInclusion k l) = beltSphere k l := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    simpa [beltSphereInclusion, beltSphere, cellBoundaryInclusion] using
      And.intro (rfl : closedCellCenter k = closedCellCenter k) x.2
  · intro hp
    refine ⟨⟨(p.2 : EuclideanSpace ℝ (Fin l)), hp.2⟩, ?_⟩
    apply Prod.ext
    · simp [beltSphereInclusion, hp.1]
    · simp [beltSphereInclusion, cellBoundaryInclusion]

theorem range_attachingSphereInclusionAttachingRegion (k l : ℕ) :
    Set.range (attachingSphereInclusionAttachingRegion k l) =
      {p : AttachingRegion k l | p.2 = closedCellCenter l} := by
  ext p
  constructor
  · rintro ⟨u, rfl⟩
    rfl
  · intro hp
    refine ⟨p.1, ?_⟩
    apply Prod.ext
    · rfl
    · exact hp.symm

theorem range_beltSphereInclusionBeltRegion (k l : ℕ) :
    Set.range (beltSphereInclusionBeltRegion k l) =
      {p : BeltRegion k l | p.1 = closedCellCenter k} := by
  ext p
  constructor
  · rintro ⟨v, rfl⟩
    rfl
  · intro hp
    refine ⟨p.2, ?_⟩
    apply Prod.ext
    · exact hp.symm
    · rfl

@[simp]
theorem attachingInclusion_comp_attachingCornerInclusion {k l : ℕ} (a : Corner k l) :
    attachingInclusion k l (attachingCornerInclusion k l a) = cornerInclusion k l a := by
  rcases a with ⟨a₁, a₂⟩
  simp [attachingInclusion, attachingCornerInclusion, cornerInclusion]

@[simp]
theorem beltInclusion_comp_beltCornerInclusion {k l : ℕ} (a : Corner k l) :
    beltInclusion k l (beltCornerInclusion k l a) = cornerInclusion k l a := by
  rcases a with ⟨a₁, a₂⟩
  simp [beltInclusion, beltCornerInclusion, cornerInclusion]

@[simp]
theorem coreDiskInclusion_comp_cellBoundaryInclusion {k l : ℕ} (x : CellBoundary k) :
    coreDiskInclusion k l (cellBoundaryInclusion k x) = attachingSphereInclusion k l x := by
  simp [coreDiskInclusion, attachingSphereInclusion]

@[simp]
theorem cocoreDiskInclusion_comp_cellBoundaryInclusion {k l : ℕ} (y : CellBoundary l) :
    cocoreDiskInclusion k l (cellBoundaryInclusion l y) = beltSphereInclusion k l y := by
  simp [cocoreDiskInclusion, beltSphereInclusion]

@[simp]
theorem attachingInclusion_comp_attachingSphereInclusionAttachingRegion {k l : ℕ}
    (u : CellBoundary k) :
    attachingInclusion k l (attachingSphereInclusionAttachingRegion k l u) =
      attachingSphereInclusion k l u := by
  rfl

@[simp]
theorem beltInclusion_comp_beltSphereInclusionBeltRegion {k l : ℕ} (v : CellBoundary l) :
    beltInclusion k l (beltSphereInclusionBeltRegion k l v) = beltSphereInclusion k l v := by
  rfl

@[simp]
theorem mem_attachingRegion {k l : ℕ} {p : StandardHandle k l} :
    p ∈ attachingRegion k l ↔ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1 := by
  rfl

@[simp]
theorem mem_beltRegion {k l : ℕ} {p : StandardHandle k l} :
    p ∈ beltRegion k l ↔ ‖(p.2 : EuclideanSpace ℝ (Fin l))‖ = 1 := by
  rfl

@[simp]
theorem mem_corner {k l : ℕ} {p : StandardHandle k l} :
    p ∈ corner k l ↔ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1 ∧ ‖(p.2 : EuclideanSpace ℝ (Fin l))‖ = 1 := by
  rfl

@[simp]
theorem mem_coreDisk {k l : ℕ} {p : StandardHandle k l} :
    p ∈ coreDisk k l ↔ p.2 = closedCellCenter l := by
  rfl

@[simp]
theorem mem_cocoreDisk {k l : ℕ} {p : StandardHandle k l} :
    p ∈ cocoreDisk k l ↔ p.1 = closedCellCenter k := by
  rfl

@[simp]
theorem mem_attachingSphere {k l : ℕ} {p : StandardHandle k l} :
    p ∈ attachingSphere k l ↔ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1 ∧ p.2 = closedCellCenter l := by
  rfl

@[simp]
theorem mem_beltSphere {k l : ℕ} {p : StandardHandle k l} :
    p ∈ beltSphere k l ↔ p.1 = closedCellCenter k ∧ ‖(p.2 : EuclideanSpace ℝ (Fin l))‖ = 1 := by
  rfl

theorem attachingRegion_inter_beltRegion (k l : ℕ) :
    attachingRegion k l ∩ beltRegion k l = corner k l := by
  ext p
  simp [attachingRegion, beltRegion, corner]

theorem coreDisk_inter_cocoreDisk (k l : ℕ) :
    coreDisk k l ∩ cocoreDisk k l = {(closedCellCenter k, closedCellCenter l)} := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨hp1, hp2⟩
    simp [coreDisk, cocoreDisk] at hp1 hp2
    ext <;> simp [hp1, hp2]
  · intro hp
    simp at hp
    simp [coreDisk, cocoreDisk, hp]

theorem attachingSphere_eq_inter (k l : ℕ) :
    attachingSphere k l = attachingRegion k l ∩ coreDisk k l := by
  ext p
  simp [attachingSphere, attachingRegion, coreDisk]

theorem beltSphere_eq_inter (k l : ℕ) :
    beltSphere k l = beltRegion k l ∩ cocoreDisk k l := by
  ext p
  simp [beltSphere, beltRegion, cocoreDisk, and_comm]

theorem corner_subset_attachingRegion (k l : ℕ) : corner k l ⊆ attachingRegion k l := by
  intro p hp
  simpa [attachingRegion, corner] using hp.1

theorem corner_subset_beltRegion (k l : ℕ) : corner k l ⊆ beltRegion k l := by
  intro p hp
  simpa [beltRegion, corner] using hp.2

theorem attachingSphere_subset_attachingRegion (k l : ℕ) : attachingSphere k l ⊆ attachingRegion k l := by
  intro p hp
  simpa [attachingRegion, attachingSphere] using hp.1

theorem beltSphere_subset_beltRegion (k l : ℕ) : beltSphere k l ⊆ beltRegion k l := by
  intro p hp
  simpa [beltRegion, beltSphere] using hp.2

theorem attachingSphere_subset_coreDisk (k l : ℕ) : attachingSphere k l ⊆ coreDisk k l := by
  intro p hp
  simpa [coreDisk, attachingSphere] using hp.2

theorem beltSphere_subset_cocoreDisk (k l : ℕ) : beltSphere k l ⊆ cocoreDisk k l := by
  intro p hp
  simpa [cocoreDisk, beltSphere] using hp.1

end DifferentialGeometry.Topology.Handle
