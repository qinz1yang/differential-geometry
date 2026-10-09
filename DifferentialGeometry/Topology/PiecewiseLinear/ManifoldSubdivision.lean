/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFaces
import DifferentialGeometry.Topology.PiecewiseLinear.LinkDimension
import DifferentialGeometry.Topology.PiecewiseLinear.RegularNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.StarJoin

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.card_le_one {K : Geometry.SimplicialComplex ℝ E}
    (h : IsCombinatorialManifoldWithBoundary 0 K) {s : Finset E} (hs : s ∈ K.faces) :
    s.card ≤ 1 := by
  by_contra hcon
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
  have hcard := Finset.card_erase_of_mem hv
  have hne : (s.erase v).Nonempty := Finset.card_pos.mp (by omega)
  have hv' : {v} ∈ K.faces :=
    K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hmem : s.erase v ∈ (SimplicialComplex.geometricLink K {v}).faces :=
    (SimplicialComplex.mem_geometricLink_singleton K v _).mpr
      ⟨hne, Finset.notMem_erase v s, by rwa [Finset.insert_erase hv]⟩
  rw [h v hv'] at hmem
  exact hmem

theorem card_le_one_of_isSubdivision {K K' : Geometry.SimplicialComplex ℝ E}
    (hK' : IsSubdivision K' K) (hK : ∀ u ∈ K.faces, u.card ≤ 1) {s : Finset E}
    (hs : s ∈ K'.faces) : s.card ≤ 1 := by
  obtain ⟨t, ht, hst⟩ := hK'.exists_face_subset hs
  have htcard : t.card = 1 := by
    have := Finset.card_pos.mpr (K.nonempty_of_mem_faces ht)
    have := hK t ht
    omega
  obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp htcard
  rw [Finset.coe_singleton, convexHull_singleton] at hst
  have hsub : s ⊆ {w} := fun u hu =>
    Finset.mem_singleton.mpr (hst (subset_convexHull ℝ _ (Finset.mem_coe.mpr hu)))
  simpa using Finset.card_le_card hsub

open Classical in
theorem IsCombinatorialManifoldWithBoundary.card_le [FiniteDimensional ℝ E] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (h : IsCombinatorialManifoldWithBoundary (n + 1) K) {s : Finset E} (hs : s ∈ K.faces) :
    s.card ≤ n + 2 := by
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
  have hcard := Finset.card_erase_of_mem hv
  have hv' : {v} ∈ K.faces :=
    K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  rcases (s.erase v).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.card_empty] at hcard
    omega
  · have hmem : s.erase v ∈ (SimplicialComplex.geometricLink K {v}).faces :=
      (SimplicialComplex.mem_geometricLink_singleton K v _).mpr
        ⟨hne, Finset.notMem_erase v s, by rwa [Finset.insert_erase hv]⟩
    have hle := card_le_of_isPLBall_or_isPLSphere
      (SimplicialComplex.geometricLink K {v}) (h v hv').symm hmem
    omega

open Classical in
theorem IsCombinatorialManifold.card_le [FiniteDimensional ℝ E] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (h : IsCombinatorialManifold (n + 1) K)
    {s : Finset E} (hs : s ∈ K.faces) : s.card ≤ n + 2 :=
  h.isCombinatorialManifoldWithBoundary.card_le K hs

theorem starAvoiding_eq_simplexBoundary_of_forall_card_le [DecidableEq E] {m : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) (hK : ∀ u ∈ K.faces, u.card ≤ m + 2) {t : Finset E}
    (ht : t ∈ K.faces) (hcard : t.card = m + 2) :
    starAvoiding K t = simplexBoundary t (K.indep ht) := by
  ext s
  rw [mem_starAvoiding_faces_iff, mem_simplexBoundary_faces_iff]
  constructor
  · rintro ⟨hs, hst, hts⟩
    have hle := hK _ hst
    have hsub : t = s ∪ t := Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
    refine ⟨fun w hw => ?_, K.nonempty_of_mem_faces hs, fun hst' => hts ?_⟩
    · rw [hsub]
      exact Finset.mem_union_left t hw
    · subst hst'
      exact Finset.Subset.refl _
  · rintro ⟨hst, hne, hst'⟩
    exact ⟨K.down_closed ht hst hne, by rwa [Finset.union_eq_right.mpr hst],
      fun hh => hst' (Finset.Subset.antisymm hst hh)⟩

theorem isPLSphere_geometricLink_of_forall_card_le [FiniteDimensional ℝ E] [DecidableEq E] {m : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : ∀ u ∈ K.faces, u.card ≤ m + 2)
    {t : Finset E} (ht : t ∈ K.faces) (hcard : t.card = m + 2) {x : E} (hx : x ∈ openSimplex t)
    {K' : Geometry.SimplicialComplex ℝ E} [Finite K'.faces] (hK' : IsSubdivision K' K)
    (hx' : {x} ∈ K'.faces) : IsPLSphere m (SimplicialComplex.geometricLink K' {x}).space := by
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_geometricLink_starAvoiding K ht hx hK' hx'
  rw [starAvoiding_eq_simplexBoundary_of_forall_card_le K hK ht hcard,
    simplexBoundary_space t (K.indep ht) (by omega)] at hf
  exact (isPLSphere_biUnion_erase t (K.indep ht) hcard).of_isPLHomeomorphOn hf.symm

open Classical in
theorem IsCombinatorialManifold.isPLSphere_geometricLink [FiniteDimensional ℝ E] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (h : IsCombinatorialManifold (n + 1) K)
    {s : Finset E} (hs : s ∈ K.faces) {k : ℕ} (hcard : s.card = k + 1) (hk : k ≤ n) :
    IsPLSphere (n - k) (SimplicialComplex.geometricLink K s).space := by
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
    exact isPLSphere_geometricLink_faces_of_isPLSphere _ (h v hv') hsL hcard' (by omega)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.of_isSubdivision [FiniteDimensional ℝ E] {n : ℕ}
    {K K' : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite K'.faces]
    (h : IsCombinatorialManifoldWithBoundary n K) (hK' : IsSubdivision K' K) :
    IsCombinatorialManifoldWithBoundary n K' := by
  cases n with
  | zero =>
    intro x _
    rw [Set.eq_empty_iff_forall_notMem]
    intro u hu
    obtain ⟨hne, hxu, hins⟩ := (SimplicialComplex.mem_geometricLink_singleton K' x u).mp hu
    have hcard := card_le_one_of_isSubdivision hK' (fun w hw => h.card_le_one hw) hins
    rw [Finset.card_insert_of_notMem hxu] at hcard
    have := Finset.card_pos.mpr hne
    omega
  | succ m =>
    intro x hx'
    have hxK : x ∈ K.space := by
      rw [← hK'.space_eq]
      exact K'.convexHull_subset_space hx' (subset_convexHull ℝ _ (by simp))
    obtain ⟨t, ht, hxt⟩ := exists_face_mem_openSimplex K hxK
    have htpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces ht)
    obtain ⟨k, hk⟩ : ∃ k, t.card = k + 1 := ⟨t.card - 1, by omega⟩
    have hcardle := h.card_le K ht
    by_cases hkm : k ≤ m
    · rcases h.isPLSphere_or_isPLBall_geometricLink K ht hk hkm with hsph | hball
      · refine Or.inl ?_
        have hres := isPLSphere_geometricLink_of_isPLSphere_geometricLink K ht hxt hK' hx' hk hsph
        rwa [show k + (m - k) = m by omega] at hres
      · refine Or.inr ?_
        have hres := isPLBall_geometricLink_of_isPLBall_geometricLink K ht hxt hK' hx' hk hball
        rwa [show k + (m - k) = m by omega] at hres
    · exact Or.inl (isPLSphere_geometricLink_of_forall_card_le K (fun w hw => h.card_le K hw) ht
        (by omega) hxt hK' hx')

open Classical in
theorem IsCombinatorialManifold.of_isSubdivision [FiniteDimensional ℝ E] {n : ℕ}
    {K K' : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite K'.faces]
    (h : IsCombinatorialManifold n K) (hK' : IsSubdivision K' K) :
    IsCombinatorialManifold n K' := by
  cases n with
  | zero =>
    intro x _
    rw [Set.eq_empty_iff_forall_notMem]
    intro u hu
    obtain ⟨hne, hxu, hins⟩ := (SimplicialComplex.mem_geometricLink_singleton K' x u).mp hu
    have hcard := card_le_one_of_isSubdivision hK'
      (fun w hw => h.isCombinatorialManifoldWithBoundary.card_le_one hw) hins
    rw [Finset.card_insert_of_notMem hxu] at hcard
    have := Finset.card_pos.mpr hne
    omega
  | succ m =>
    intro x hx'
    have hxK : x ∈ K.space := by
      rw [← hK'.space_eq]
      exact K'.convexHull_subset_space hx' (subset_convexHull ℝ _ (by simp))
    obtain ⟨t, ht, hxt⟩ := exists_face_mem_openSimplex K hxK
    have htpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces ht)
    obtain ⟨k, hk⟩ : ∃ k, t.card = k + 1 := ⟨t.card - 1, by omega⟩
    have hcardle := h.card_le K ht
    by_cases hkm : k ≤ m
    · have hres := isPLSphere_geometricLink_of_isPLSphere_geometricLink K ht hxt hK' hx' hk
        (h.isPLSphere_geometricLink K ht hk hkm)
      rwa [show k + (m - k) = m by omega] at hres
    · exact isPLSphere_geometricLink_of_forall_card_le K (fun w hw => h.card_le K hw) ht
        (by omega) hxt hK' hx'

open Classical in
theorem IsCombinatorialManifoldWithBoundary.barycentricSubdivision [FiniteDimensional ℝ E] {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (h : IsCombinatorialManifoldWithBoundary n K) :
    IsCombinatorialManifoldWithBoundary n
      (DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision K) :=
  h.of_isSubdivision (barycentricSubdivision_isSubdivision K)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.secondDerived [FiniteDimensional ℝ E] {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (h : IsCombinatorialManifoldWithBoundary n K) :
    IsCombinatorialManifoldWithBoundary n
      (DifferentialGeometry.Topology.PiecewiseLinear.secondDerived K) :=
  h.of_isSubdivision (secondDerived_isSubdivision K)

open Classical in
theorem IsCombinatorialManifold.barycentricSubdivision [FiniteDimensional ℝ E] {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] (h : IsCombinatorialManifold n K) :
    IsCombinatorialManifold n
      (DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision K) :=
  h.of_isSubdivision (barycentricSubdivision_isSubdivision K)

open Classical in
theorem IsCombinatorialManifold.secondDerived [FiniteDimensional ℝ E] {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] (h : IsCombinatorialManifold n K) :
    IsCombinatorialManifold n (DifferentialGeometry.Topology.PiecewiseLinear.secondDerived K) :=
  h.of_isSubdivision (secondDerived_isSubdivision K)

end DifferentialGeometry.Topology.PiecewiseLinear
