/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexBallGluing
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem iInter_derivedNeighborhoodCell_space (K : Geometry.SimplicialComplex ℝ E)
    {d : Finset (Finset E)} (hd : IsFlag K d) (hne : d.Nonempty) :
    (⋂ s ∈ d, (derivedNeighborhoodCell K s).space) =
      (dualCell (barycentricSubdivision K) (d.image fun s => s.centroid ℝ id)
        ⟨d, hd, hne, rfl⟩).space := by
  classical
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs⟩ := hne
    have hxs := mem_iInter₂.mp hx s hs
    obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex (derivedNeighborhoodCell K s) hxs
    have huK := derivedNeighborhoodCell_faces_subset K s hu
    have hucell (t : Finset E) (ht : t ∈ d) : u ∈ (derivedNeighborhoodCell K t).faces :=
      mem_faces_of_mem_openSimplex_of_mem_space (derivedNeighborhoodCell_faces_subset K t)
        huK hxu (mem_iInter₂.mp hx t ht)
    obtain ⟨D, hD, hDne, rfl⟩ := huK
    refine (dualCell (barycentricSubdivision K) _ _).convexHull_subset_space ?_
      (openSimplex_subset_convexHull _ hxu)
    apply (mem_dualCell_faces_iff_of_flag _ hD hDne).mpr
    intro e he y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
    exact (mem_derivedNeighborhoodCell_faces_iff_of_flag (hd.mem_faces ht) hD hDne).mp
      (hucell t ht) e he
  · intro x hx
    obtain ⟨u, hu, hxu⟩ := (dualCell (barycentricSubdivision K) _ _).mem_space_iff.mp hx
    obtain ⟨D, hD, hDne, hsub, rfl⟩ := (mem_dualCell_faces_iff _ _).mp hu
    apply mem_iInter₂.mpr
    intro s hs
    apply (derivedNeighborhoodCell K s).convexHull_subset_space ?_ hxu
    exact (mem_derivedNeighborhoodCell_faces_iff_of_flag (hd.mem_faces hs) hD hDne).mpr
      fun e he => hsub e he (Finset.mem_image_of_mem _ hs)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_iInter_derivedNeighborhoodCell
    [FiniteDimensional ℝ E] {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {d : Finset (Finset E)}
    (hd : IsFlag K d) {k : ℕ} (hcard : d.card = k + 1) (hk : k ≤ n) :
    IsPLBall (n - k + 1) (⋂ s ∈ d, (derivedNeighborhoodCell K s).space) := by
  classical
  have hne : d.Nonempty := Finset.card_pos.mp (by omega)
  rw [iInter_derivedNeighborhoodCell_space K hd hne]
  apply hK.barycentricSubdivision.isPLBall_dualCell _ _ (k := k) _ hk
  rw [Finset.card_image_of_injOn (hd.injOn K (centroid_mem_openSimplex_of_mem_faces K)), hcard]

open Classical in
theorem space_subset_iUnion_derivedNeighborhoodCell_space
    (K L : Geometry.SimplicialComplex ℝ E) (hL : L.faces ⊆ K.faces) :
    L.space ⊆ ⋃ s ∈ L.faces, (derivedNeighborhoodCell K s).space := by
  classical
  rw [iUnion_derivedNeighborhoodCell_space K L hL]
  intro x hx
  have hxK : x ∈ (secondDerived K).space :=
    (secondDerived_isSubdivision K).space_eq.symm ▸ space_mono_of_faces_subset hL hx
  obtain ⟨u, hu, hxu⟩ := (secondDerived K).mem_space_iff.mp hxK
  exact closedStar_subset_derivedNeighborhood hL hx (mem_iUnion₂.mpr ⟨u, ⟨hu, hxu⟩, hxu⟩)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_union_derivedNeighborhoodCells
    [FiniteDimensional ℝ E] {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {s : Finset E} (hs : s ∈ K.faces)
    (d : Finset (Finset E))
    (hd : ∀ t ∈ d, t ∈ K.faces) (hds : ∀ t ∈ d, t ≠ s)
    (hcomp : ∀ t ∈ d, s ⊆ t ∨ t ⊆ s)
    (hincomp : ∀ t ∈ d, ∀ u ∈ d, t ≠ u → ¬t ⊆ u ∧ ¬u ⊆ t) :
    IsPLBall 3 ((derivedNeighborhoodCell K s).space ∪
      ⋃ t ∈ d, (derivedNeighborhoodCell K t).space) := by
  classical
  induction d using Finset.induction_on with
  | empty => simpa using hK.isPLBall_derivedNeighborhoodCell hs
  | @insert t d ht ih =>
    have hd' : ∀ u ∈ d, u ∈ K.faces := fun u hu => hd u (Finset.mem_insert_of_mem hu)
    have hds' : ∀ u ∈ d, u ≠ s := fun u hu => hds u (Finset.mem_insert_of_mem hu)
    have hc' : ∀ u ∈ d, s ⊆ u ∨ u ⊆ s := fun u hu => hcomp u (Finset.mem_insert_of_mem hu)
    have hi' : ∀ u ∈ d, ∀ v ∈ d, u ≠ v → ¬u ⊆ v ∧ ¬v ⊆ u :=
      fun u hu v hv huv => hincomp u (Finset.mem_insert_of_mem hu) v (Finset.mem_insert_of_mem hv)
          huv
    have hball := ih hd' hds' hc' hi'
    have htK := hd t (Finset.mem_insert_self _ _)
    have hts := hds t (Finset.mem_insert_self _ _)
    have hinter : ((derivedNeighborhoodCell K s).space ∪
        ⋃ u ∈ d, (derivedNeighborhoodCell K u).space) ∩ (derivedNeighborhoodCell K t).space =
        (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space := by
      apply Subset.antisymm
      · rintro x ⟨hx | hx, hxt⟩
        · exact ⟨hx, hxt⟩
        · obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
          have hut : u ≠ t := ne_of_mem_of_not_mem hu ht
          have hi := hincomp u (Finset.mem_insert_of_mem hu) t (Finset.mem_insert_self _ _) hut
          exact ((disjoint_derivedNeighborhoodCell_space K (hd' u hu) htK hi.1 hi.2).le_bot
            ⟨hxu, hxt⟩).elim
      · rintro x ⟨hxs, hxt⟩
        exact ⟨Or.inl hxs, hxt⟩
    have hI : IsPLBall 2 (((derivedNeighborhoodCell K s).space ∪
        ⋃ u ∈ d, (derivedNeighborhoodCell K u).space) ∩ (derivedNeighborhoodCell K t).space) := by
      rw [hinter]
      exact hK.isPLBall_derivedNeighborhoodCell_inter hs htK hts.symm
        (hcomp t (Finset.mem_insert_self _ _))
    have htball := hK.isPLBall_derivedNeighborhoodCell htK
    have hsub : ((derivedNeighborhoodCell K s).space ∪
        ⋃ u ∈ d, (derivedNeighborhoodCell K u).space) ⊆ K.space :=
      union_subset (derivedNeighborhoodCell_space_subset K s)
        (iUnion₂_subset fun u _ => derivedNeighborhoodCell_space_subset K u)
    have h := hK.isPLBall_union_of_inter_isPLBall_two hball htball hsub
      (derivedNeighborhoodCell_space_subset K t) hI
    simpa only [Finset.set_biUnion_insert, union_assoc, union_left_comm, union_comm] using h

theorem IsCombinatorialManifoldWithBoundary.isPLBall_union_derivedNeighborhoodCells_of_card
    [FiniteDimensional ℝ E] {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {s : Finset E} (hs : s ∈ K.faces)
    (d : Finset (Finset E)) {k : ℕ} (hk : 0 < k)
    (hks : k < s.card) (hsub : ∀ t ∈ d, t ⊆ s) (hcard : ∀ t ∈ d, t.card = k) :
    IsPLBall 3 ((derivedNeighborhoodCell K s).space ∪
      ⋃ t ∈ d, (derivedNeighborhoodCell K t).space) := by
  apply hK.isPLBall_union_derivedNeighborhoodCells hs d
  · intro t ht
    exact K.down_closed hs (hsub t ht) (Finset.card_pos.mp (hcard t ht ▸ hk))
  · intro t ht heq
    have hc := hcard t ht
    rw [heq] at hc
    omega
  · exact fun t ht => Or.inr (hsub t ht)
  · intro t ht u hu hne
    exact ⟨fun h => hne (Finset.eq_of_subset_of_card_le h (by rw [hcard t ht, hcard u hu])),
      fun h => hne (Finset.eq_of_subset_of_card_le h (by rw [hcard t ht, hcard u hu])).symm⟩

end DifferentialGeometry.Topology.PiecewiseLinear
