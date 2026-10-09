/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryOfBall
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_triangle_edges_of_isPLBall_one_subcomplex
    {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : T.card = 3)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLBall 1 K.space) (hKT : K.faces ⊆ (simplexBoundary T hT).faces) :
    ∃ s : Finset E, s ⊆ T ∧ (s.card = 1 ∨ s.card = 2) ∧
      K.space = ⋃ v ∈ s, convexHull ℝ ((T.erase v : Finset E) : Set E) := by
  let s := T.filter (fun v => T.erase v ∈ K.faces)
  have hsT : s ⊆ T := Finset.filter_subset _ _
  have hspace : K.space = ⋃ v ∈ s, convexHull ℝ ((T.erase v : Finset E) : Set E) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨u, hu, hxu⟩ := K.mem_space_iff.mp hx
      obtain ⟨w, hw, huw, hwcard⟩ := exists_face_superset_card_eq_of_isPLBall K hK hu
      have hwT := (hKT hw).1
      have hwproper : w ⊂ T := Finset.ssubset_iff_subset_ne.mpr
        ⟨hwT, fun heq => by rw [heq, hcard] at hwcard; omega⟩
      obtain ⟨v, hv, hwsub⟩ := Finset.ssubset_iff_exists_subset_erase.mp hwproper
      have hwEq : w = T.erase v := Finset.eq_of_subset_of_card_le hwsub (by
        rw [Finset.card_erase_of_mem hv, hcard, hwcard])
      refine mem_iUnion₂.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hwEq ▸ hw⟩, ?_⟩
      rw [← hwEq]
      exact convexHull_mono (Finset.coe_subset.mpr huw) hxu
    · intro x hx
      obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
      exact K.convexHull_subset_space (Finset.mem_filter.mp hv).2 hxv
  have hspos : 0 < s.card := by
    apply Finset.card_pos.mpr
    obtain ⟨x, hx⟩ := hK.nonempty
    rw [hspace] at hx
    obtain ⟨v, hv, _⟩ := mem_iUnion₂.mp hx
    exact ⟨v, hv⟩
  have hslt : s.card < T.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsT, ?_⟩
    intro heq
    have hsphere : IsPLSphere 1 K.space := by
      rw [hspace, heq]
      exact isPLSphere_biUnion_erase T hT hcard
    exact hK.not_isPLSphere hsphere
  exact ⟨s, hsT, by omega, hspace⟩

open Classical in
theorem exists_triangle_edges_of_isPLBall_boundary_inter
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {T : Finset E} (hT : T ∈ K.faces) (hcard : T.card = 3)
    (htrace : IsPLBall 1 ((boundaryComplex 2 K).space ∩ convexHull ℝ (T : Set E))) :
    ∃ s : Finset E, s ⊆ T ∧ (s.card = 1 ∨ s.card = 2) ∧
      (boundaryComplex 2 K).space ∩ convexHull ℝ (T : Set E) =
        ⋃ v ∈ s, convexHull ℝ ((T.erase v : Finset E) : Set E) := by
  let B := boundaryComplex 2 K
  let _ : Finite B.faces :=
    ((Set.toFinite K.faces).subset (boundaryComplex_faces_subset 2 K)).to_subtype
  let L := restrict B (convexHull ℝ (T : Set E))
  let _ : Finite L.faces := (restrict_faces_finite B _).to_subtype
  have hspace : L.space = B.space ∩ convexHull ℝ (T : Set E) := by
    apply Subset.antisymm
    · exact subset_inter (space_mono_of_faces_subset (restrict_faces_subset B _))
        (restrict_space_subset B _)
    · intro x hx
      obtain ⟨u, hu, hxu⟩ := B.mem_space_iff.mp hx.1
      have huK := boundaryComplex_faces_subset 2 K hu
      have hxuT : x ∈ convexHull ℝ ((u ∩ T : Finset E) : Set E) := by
        rw [Finset.coe_inter, ← K.convexHull_inter_convexHull huK hT]
        exact ⟨hxu, hx.2⟩
      have hne : (u ∩ T).Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.coe_empty,
          convexHull_empty] at hxuT
        exact hxuT
      exact L.convexHull_subset_space
        ⟨B.down_closed hu Finset.inter_subset_left hne,
          convexHull_mono (Finset.coe_subset.mpr Finset.inter_subset_right)⟩ hxuT
  have hL : IsPLBall 1 L.space := hspace.symm ▸ htrace
  have hBK : IsPLSphere 1 B.space := isPLSphere_boundaryComplex_space_of_isPLBall K hK
  have hLT : L.faces ⊆ (simplexBoundary T (K.indep hT)).faces := by
    intro u hu
    have huK := boundaryComplex_faces_subset 2 K hu.1
    have hucent : u.centroid ℝ id ∈ openSimplex u :=
      centroid_mem_openSimplex (K.nonempty_of_mem_faces huK)
    have huT : u ⊆ T := face_subset_of_mem_openSimplex_of_mem_convexHull K huK hT
      hucent (hu.2 (openSimplex_subset_convexHull u hucent))
    have hucard := card_le_of_isPLSphere B hBK hu.1
    exact ⟨huT, K.nonempty_of_mem_faces huK, fun heq => by
      rw [heq, hcard] at hucard
      omega⟩
  obtain ⟨s, hsT, hscard, hs⟩ :=
    exists_triangle_edges_of_isPLBall_one_subcomplex (K.indep hT) hcard L hL hLT
  exact ⟨s, hsT, hscard, hspace.symm.trans hs⟩

open Classical in
theorem exists_triangle_boundary_arc_normal_form
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {T : Finset E} (hT : T ∈ K.faces) (hcard : T.card = 3)
    (htrace : IsPLBall 1 ((boundaryComplex 2 K).space ∩ convexHull ℝ (T : Set E))) :
    ∃ a b c : E, a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ T = {c, a, b} ∧
      ((boundaryComplex 2 K).space ∩ convexHull ℝ (T : Set E) = segment ℝ a b ∨
        (boundaryComplex 2 K).space ∩ convexHull ℝ (T : Set E) =
          segment ℝ a c ∪ segment ℝ c b) := by
  obtain ⟨s, hsT, hscard, hs⟩ :=
    exists_triangle_edges_of_isPLBall_boundary_inter K hK hT hcard htrace
  rcases hscard with hc | hc
  · obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp hc
    have hcT := hsT (Finset.mem_singleton_self c)
    have hecard : (T.erase c).card = 2 := by
      rw [Finset.card_erase_of_mem hcT, hcard]
    obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp hecard
    have ha : a ∈ T.erase c := he.symm ▸ Finset.mem_insert_self a {b}
    have hb : b ∈ T.erase c := he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    have hTc : T = {c, a, b} := by rw [← he, Finset.insert_erase hcT]
    refine ⟨a, b, c, hab, (Finset.mem_erase.mp ha).1.symm,
      (Finset.mem_erase.mp hb).1.symm, hTc, Or.inl ?_⟩
    simpa only [Finset.mem_singleton, iUnion_iUnion_eq_left, he, Finset.coe_pair,
      convexHull_pair] using hs
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc
    obtain ⟨c, hcT, hcs⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (by rw [Finset.card_pair hab, hcard]; decide : ({a, b} : Finset E).card < T.card)
    have ⟨hca, hcb⟩ : c ≠ a ∧ c ≠ b := by simpa using hcs
    have hTc : T = {c, a, b} := by
      symm
      apply Finset.eq_of_subset_of_card_le (Finset.insert_subset_iff.mpr ⟨hcT, hsT⟩)
      rw [Finset.card_insert_of_notMem hcs, Finset.card_pair hab, hcard]
    refine ⟨a, b, c, hab, hca, hcb, hTc, Or.inr ?_⟩
    rw [hs, hTc]
    have he₀ : ({c, a, b} : Finset E).erase a = {c, b} := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      aesop
    have he₁ : ({c, a, b} : Finset E).erase b = {c, a} := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      aesop
    simp only [Finset.mem_insert, Finset.mem_singleton, iUnion_iUnion_eq_or_left,
      iUnion_iUnion_eq_left, he₀, he₁, Finset.coe_pair, convexHull_pair]
    rw [segment_symm ℝ c a, union_comm]

end DifferentialGeometry.Topology.PiecewiseLinear
