import DifferentialGeometry.Topology.Surface.Recognition.EmbeddedFacePartitionOfFamilyBCF
import DifferentialGeometry.Topology.Surface.Recognition.EmbeddedFacePartitionBCFApplications

/-!
# Consumer of the family-to-partition transport (lane S-BCF03b)

`torusFamilyPartition_BCF`: the torus `S¹ × S¹ = ↥(univ)` as the family with no disk and the single
piece `univ` (projection `fst`); the transport returns a partition with `0` disks and `1` piece,
and FC40 (`diskCount_eq_zero_of_torus`) confirms the count on the transported partition.
-/

set_option autoImplicit false

open Set Function Topology

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology

theorem torusFamilyPartition_BCF :
    ∃ Pt : EmbeddedFacePartition_BCF (univ : Set (Circle × Circle)),
      Pt.diskCount = 0 ∧ Pt.pieceCount = 1 := by
  obtain ⟨Pt, -, -, hd, hp, -⟩ := exists_embeddedFacePartition_of_family_BCF
    (Y := (univ : Set (Circle × Circle))) (I := Empty) (J := Unit)
    (fun i => i.elim) (fun _ => univ) (fun i => i.elim) (fun i => i.elim) (fun _ => subset_univ _)
    (fun i => i.elim) (fun _ => isClosed_univ) (fun _ => univ_nonempty)
    (fun y _ => Or.inr (mem_iUnion.mpr ⟨(), mem_univ y⟩)) (fun i => i.elim)
    (fun i j hij => (hij (Subsingleton.elim i j)).elim)
    (fun i => i.elim) (fun _ => Or.inl (by simp)) (fun i => i.elim)
    (fun _ h => by simp at h) (fun _ _ => ⟨fun x => x.1.1,
      continuous_fst.comp continuous_subtype_val,
      isOpenMap_fst.comp (Homeomorph.Set.univ (Circle × Circle)).isOpenMap⟩)
  exact ⟨Pt, by simpa using hd, by simpa using hp⟩

/-- On the transported torus partition FC40 gives no disk (the count is read from the
parametrizations, not from the family). -/
theorem torusFamilyPartition_diskCount_BCF
    (Pt : EmbeddedFacePartition_BCF (univ : Set (Circle × Circle)))
    (φ : (univ : Set (Circle × Circle)) ≃ₜ Circle × Circle) : Pt.diskCount = 0 :=
  Pt.diskCount_eq_zero_of_torus φ

end DifferentialGeometry.Topology.Surface
