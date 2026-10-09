/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteSplittingDisks
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldFaces

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Set

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] {U : Set X}

open Classical in
theorem LocallyFinitePLPieceIn.exists_tetrahedron_superset
    (K : LocallyFinitePLPieceIn E 3 X U)
    (hK : IsCombinatorialManifold 3 K.complex)
    {s : Finset E} (hs : s ∈ K.complex.faces) :
    ∃ t ∈ K.complex.faces, s ⊆ t ∧ t.card = 4 := by
  classical
  obtain ⟨v, hv⟩ := K.complex.nonempty_of_mem_faces hs
  have hvK : ({v} : Finset E) ∈ K.complex.faces :=
    K.complex.down_closed hs (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v)
  let L := SimplicialComplex.geometricLink K.complex {v}
  have _ : Finite L.faces := (K.geometricLink_faces_finite hvK).to_subtype
  have hL : IsPLSphere 2 L.space := hK v hvK
  obtain ⟨t, ht, hst, hcard⟩ :
      ∃ t ∈ L.faces, s.erase v ⊆ t ∧ t.card = 3 := by
    by_cases hne : (s.erase v).Nonempty
    · have hsL : s.erase v ∈ L.faces := by
        apply (SimplicialComplex.mem_geometricLink_singleton K.complex v (s.erase v)).mpr
        refine ⟨hne, Finset.notMem_erase v s, ?_⟩
        rwa [Finset.insert_erase hv]
      exact exists_face_superset_card_eq_of_isPLSphere L hL hsL
    · obtain ⟨x, hx⟩ := hL.nonempty
      obtain ⟨r, hr, _⟩ := L.mem_space_iff.mp hx
      obtain ⟨t, ht, _, hcard⟩ :=
        exists_face_superset_card_eq_of_isPLSphere L hL hr
      refine ⟨t, ht, ?_, hcard⟩
      rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      exact Finset.empty_subset t
  have htL := (SimplicialComplex.mem_geometricLink_singleton K.complex v t).mp ht
  refine ⟨insert v t, htL.2.2, ?_, ?_⟩
  · intro w hw
    by_cases hwv : w = v
    · exact Finset.mem_insert.mpr (Or.inl hwv)
    · exact Finset.mem_insert_of_mem (hst (Finset.mem_erase.mpr ⟨hwv, hw⟩))
  · rw [Finset.card_insert_of_notMem htL.2.1, hcard]

end DifferentialGeometry.Topology.PiecewiseLinear
