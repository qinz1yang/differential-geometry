import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldWithBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Geometry.SimplicialComplex ℝ E)

theorem geometricLink_union [DecidableEq E] {s r : Finset E} (hsr : Disjoint s r) :
    SimplicialComplex.geometricLink K (s ∪ r) =
      SimplicialComplex.geometricLink (SimplicialComplex.geometricLink K s) r := by
  ext t
  rw [mem_geometricLink_faces_iff, mem_geometricLink_faces_iff, mem_geometricLink_faces_iff,
    Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.union_assoc]
  constructor
  · rintro ⟨hne, ⟨hst, hrt⟩, hmem⟩
    exact ⟨hne, hrt, hne.mono Finset.subset_union_right, ⟨hsr, hst⟩, hmem⟩
  · rintro ⟨hne, hrt, -, ⟨-, hst⟩, hmem⟩
    exact ⟨hne, ⟨hst, hrt⟩, hmem⟩

variable [FiniteDimensional ℝ E] [Finite K.faces]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLSphere_or_isPLBall_geometricLink {n : ℕ}
    (h : IsCombinatorialManifoldWithBoundary (n + 1) K) {s : Finset E} (hs : s ∈ K.faces) {k : ℕ}
    (hcard : s.card = k + 1) (hk : k ≤ n) :
    IsPLSphere (n - k) (SimplicialComplex.geometricLink K s).space ∨
      IsPLBall (n - k) (SimplicialComplex.geometricLink K s).space := by
  cases k with
  | zero =>
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
    rw [Nat.sub_zero]
    exact h v hs
  | succ k =>
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
    obtain ⟨s', hvs', rfl⟩ : ∃ s', v ∉ s' ∧ s = insert v s' :=
      ⟨s.erase v, Finset.notMem_erase v s, (Finset.insert_erase hv).symm⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hcard' : s'.card = k + 1 := by
      rw [Finset.card_insert_of_notMem hvs'] at hcard
      omega
    have hv' : {v} ∈ K.faces :=
      K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    have hsL : s' ∈ (SimplicialComplex.geometricLink K {v}).faces :=
      (SimplicialComplex.mem_geometricLink_singleton K v s').mpr
        ⟨Finset.card_pos.mp (by omega), hvs', hs⟩
    rw [geometricLink_insert K hvs', show m + 1 - (k + 1) = m - k by omega]
    rcases h v hv' with hL | hL
    · exact Or.inl (isPLSphere_geometricLink_faces_of_isPLSphere _ hL hsL hcard' (by omega))
    · exact isPLSphere_or_isPLBall_geometricLink_faces_of_isPLBall _ hL hsL hcard' (by omega)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.mem_boundaryComplex_faces_iff {n : ℕ}
    (h : IsCombinatorialManifoldWithBoundary (n + 1) K) {s : Finset E} :
    s ∈ (boundaryComplex (n + 1) K).faces ↔ s ∈ K.faces ∧ s.card ≤ n + 1 ∧
      IsPLBall (n + 1 - s.card) (SimplicialComplex.geometricLink K s).space := by
  constructor
  · rintro ⟨hs, t, ht, hst, htn, hball⟩
    have hcardle : s.card ≤ t.card := Finset.card_le_card hst
    refine ⟨hs, by omega, ?_⟩
    obtain ⟨k, hk⟩ : ∃ k, s.card = k + 1 :=
      ⟨s.card - 1, by have := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs); omega⟩
    rcases h.isPLSphere_or_isPLBall_geometricLink K hs hk (by omega) with hsph | hball'
    · exfalso
      rcases (t \ s).eq_empty_or_nonempty with he | hne
      · have hts : t = s := Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp he) hst
        rw [hts, show n + 1 - s.card = n - k by omega] at hball
        exact hball.not_isPLSphere hsph
      · have htu : t = s ∪ t \ s := (Finset.union_sdiff_of_subset hst).symm
        obtain ⟨k', hk'⟩ : ∃ k', (t \ s).card = k' + 1 :=
          ⟨(t \ s).card - 1, by have := Finset.card_pos.mpr hne; omega⟩
        have hcardt : t.card = s.card + (t \ s).card := by
          rw [htu, Finset.card_union_of_disjoint Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hst]
        obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
        rw [hm] at hsph
        have hsub : t \ s ∈ (SimplicialComplex.geometricLink K s).faces :=
          ⟨hne, Finset.disjoint_sdiff, by rwa [Finset.union_sdiff_of_subset hst]⟩
        have hs' := isPLSphere_geometricLink_faces_of_isPLSphere _ hsph hsub hk' (by omega)
        rw [← geometricLink_union K Finset.disjoint_sdiff, ← htu] at hs'
        rw [show n + 1 - t.card = m - k' by omega] at hball
        exact hball.not_isPLSphere hs'
    · rwa [show n + 1 - s.card = n - k by omega]
  · rintro ⟨hs, hsn, hball⟩
    exact ⟨hs, s, hs, subset_rfl, hsn, hball⟩

open Classical in
theorem IsCombinatorialManifold.boundaryComplex_faces_eq_empty {n : ℕ}
    (h : IsCombinatorialManifold (n + 1) K) : (boundaryComplex (n + 1) K).faces = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro s ⟨-, t, ht, -, htn, hball⟩
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces ht
  obtain ⟨t', hvt', rfl⟩ : ∃ t', v ∉ t' ∧ t = insert v t' :=
    ⟨t.erase v, Finset.notMem_erase v t, (Finset.insert_erase hv).symm⟩
  have hv' : {v} ∈ K.faces :=
    K.down_closed ht (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hL := h v hv'
  rw [Finset.card_insert_of_notMem hvt'] at htn hball
  rcases t'.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.insert_empty, Finset.card_empty, show n + 1 - (0 + 1) = n by omega] at hball
    exact hball.not_isPLSphere hL
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := Finset.card_pos.mpr hne; omega⟩
    obtain ⟨k, hk⟩ : ∃ k, t'.card = k + 1 :=
      ⟨t'.card - 1, by have := Finset.card_pos.mpr hne; omega⟩
    have hsL : t' ∈ (SimplicialComplex.geometricLink K {v}).faces :=
      (SimplicialComplex.mem_geometricLink_singleton K v t').mpr ⟨hne, hvt', ht⟩
    have hs := isPLSphere_geometricLink_faces_of_isPLSphere _ hL hsL hk (by omega)
    rw [← geometricLink_insert K hvt'] at hs
    rw [show m + 1 + 1 - (t'.card + 1) = m - k by omega] at hball
    exact hball.not_isPLSphere hs

end DifferentialGeometry.Topology.PiecewiseLinear
