import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubdivision

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_face_superset_card_eq {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary n K) {s : Finset E} (hs : s ∈ K.faces) :
    ∃ t ∈ K.faces, s ⊆ t ∧ t.card = n + 1 := by
  classical
  cases n with
  | zero =>
    refine ⟨s, hs, Finset.Subset.rfl, ?_⟩
    have := hK.card_le_one hs
    have := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
    omega
  | succ n =>
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
    have hvK : {v} ∈ K.faces :=
      K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    let L := SimplicialComplex.geometricLink K {v}
    have hL : IsPLBall n L.space ∨ IsPLSphere n L.space := (hK v hvK).symm
    obtain ⟨t, ht, hst, hcard⟩ : ∃ t ∈ L.faces, s.erase v ⊆ t ∧ t.card = n + 1 := by
      by_cases hne : (s.erase v).Nonempty
      · have hsL : s.erase v ∈ L.faces :=
          (SimplicialComplex.mem_geometricLink_singleton K v (s.erase v)).mpr
            ⟨hne, Finset.notMem_erase v s, by rwa [Finset.insert_erase hv]⟩
        exact exists_face_superset_card_eq_of_isPLBall_or_isPLSphere L hL hsL
      · obtain ⟨x, hx⟩ := hL.elim IsPLBall.nonempty IsPLSphere.nonempty
        obtain ⟨r, hr, -⟩ := L.mem_space_iff.mp hx
        obtain ⟨t, ht, -, hcard⟩ :=
          exists_face_superset_card_eq_of_isPLBall_or_isPLSphere L hL hr
        refine ⟨t, ht, ?_, hcard⟩
        rw [Finset.not_nonempty_iff_eq_empty.mp hne]
        exact Finset.empty_subset t
    have htL := (SimplicialComplex.mem_geometricLink_singleton K v t).mp ht
    refine ⟨insert v t, htL.2.2, ?_, ?_⟩
    · intro w hw
      by_cases hwv : w = v
      · exact Finset.mem_insert.mpr (Or.inl hwv)
      · exact Finset.mem_insert_of_mem (hst (Finset.mem_erase.mpr ⟨hwv, hw⟩))
    · rw [Finset.card_insert_of_notMem htL.2.1, hcard]

open Classical in
theorem IsCombinatorialManifold.exists_face_superset_card_eq {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold n K) {s : Finset E} (hs : s ∈ K.faces) :
    ∃ t ∈ K.faces, s ⊆ t ∧ t.card = n + 1 :=
  hK.isCombinatorialManifoldWithBoundary.exists_face_superset_card_eq K hs

end DifferentialGeometry.Topology.PiecewiseLinear
