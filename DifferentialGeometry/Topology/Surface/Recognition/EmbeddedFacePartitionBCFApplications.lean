import DifferentialGeometry.Topology.Surface.Recognition.EmbeddedFacePartitionBCF
import DifferentialGeometry.Topology.Surface.Recognition.RecognitionApplications

/-!
# Inhabitant and consumers of the embedded face partition (lane B-BCF134)

* `torusFacePartition_BCF`: the torus `S¹ × S¹` as one circle-bundle piece without disks (the
  partition of a cusp torus face `H_b`, BCF03's cusp branch), projection `fst`.
* `torusFacePartition_diskCount_BCF`: its disk count is `0`, as FC40 predicts.
* `no_diskFree_sphere_partition_BCF`: no embedded face partition of `S²` is disk-free.
-/

set_option autoImplicit false

open Set Function Topology

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology

/-- **Inhabitant**: `S¹ × S¹` as one circle-bundle piece without disks. -/
def torusFacePartition_BCF : EmbeddedFacePartition_BCF (Circle × Circle) where
  diskCount := 0
  pieceCount := 1
  disk := fun i => i.elim0
  piece := fun _ => univ
  side := fun i => i.elim0
  isClosed_disk := fun i => i.elim0
  isClosed_piece := fun _ => isClosed_univ
  piece_nonempty := fun _ => univ_nonempty
  cover := by simp [iUnion_const]
  disk_disjoint := fun i => i.elim0
  piece_disjoint := fun i j hij => (hij (Subsingleton.elim i j)).elim
  side_spec := fun i => i.elim0
  degree := fun _ => Or.inl (by simp)
  disk_param := fun i => i.elim0
  annulus_param := fun _ h => by simp at h
  circle_base := fun _ _ => ⟨fun x => x.1.1, continuous_fst.comp continuous_subtype_val,
    isOpenMap_fst.comp (Homeomorph.Set.univ (Circle × Circle)).isOpenMap⟩

/-- **Consumer (torus side)**: the torus partition has no disk (FC40). -/
theorem torusFacePartition_diskCount_BCF : torusFacePartition_BCF.diskCount = 0 :=
  torusFacePartition_BCF.diskCount_eq_zero_of_torus (Homeomorph.refl _)

/-- **Consumer (sphere side)**: an embedded face partition of `S²` has two disks, so it is never
disk-free. -/
theorem no_diskFree_sphere_partition_BCF (P : EmbeddedFacePartition_BCF SphereTwo) :
    P.diskCount ≠ 0 := by
  rw [P.diskCount_eq_two_of_sphere (Homeomorph.refl _)]
  decide

end DifferentialGeometry.Topology.Surface
