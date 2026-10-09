/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryLinkGerm
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexCapLink

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem singleton_mem_faces_of_mem_space_of_card_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hcard : ∀ s ∈ K.faces, s.card ≤ 1)
    {x : E} (hx : x ∈ K.space) : {x} ∈ K.faces := by
  obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
  have hsne := K.nonempty_of_mem_faces hs
  have hscard : s.card = 1 := by
    exact le_antisymm (hcard s hs) (Finset.card_pos.mpr hsne)
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hscard
  have hxv : x = v := by
    simpa only [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] using hxs
  rwa [hxv]

theorem boundaryComplex_space_eq_simplexBoundary_of_space_eq_convexHull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [dE : DecidableEq E] (N : Geometry.SimplicialComplex ℝ E) [Finite N.faces]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : T.card = 3)
    (hspace : N.space = convexHull ℝ (T : Set E)) :
    (boundaryComplex 2 N).space = (simplexBoundary T hT).space := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  let S := simplexComplex T hT
  let _ : Finite S.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hSspace : S.space = convexHull ℝ (T : Set E) := by
    apply simplexComplex_space T hT
    apply Finset.card_pos.mp
    rw [hcard]
    norm_num
  have hball : IsPLBall 2 N.space := by
    rw [hspace]
    exact isPLBall_convexHull_of_affineIndependent T hT hcard
  have hid : IsPLHomeomorphOn (id : E → E) N.space S.space := by
    rw [hspace, hSspace]
    exact (isPolyhedron_convexHull_of_affineIndependent T hT).isPLHomeomorphOn_id
  have hboundary := boundaryComplex_space_of_isPLHomeomorphOn
    N S hball.isCombinatorialManifoldWithBoundary hid
  change (boundaryComplex 2 (simplexComplex T hT)).space =
    id '' (boundaryComplex 2 N).space at hboundary
  rw [boundaryComplex_simplexComplex hT hcard] at hboundary
  simpa only [Set.image_id] using hboundary.symm

theorem singleton_mem_boundaryComplex_of_mem_triangle_vertex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] (N : Geometry.SimplicialComplex ℝ E) [Finite N.faces]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : T.card = 3)
    (hspace : N.space = convexHull ℝ (T : Set E)) {q : E} (hq : q ∈ T) :
    {q} ∈ (boundaryComplex 2 N).faces := by
  have hqface : ({q} : Finset E) ∈ (simplexBoundary T hT).faces := by
    refine ⟨Finset.singleton_subset_iff.mpr hq, Finset.singleton_nonempty q, ?_⟩
    intro heq
    have : ({q} : Finset E).card = 3 := heq ▸ hcard
    simp only [Finset.card_singleton] at this
    omega
  have hqspace : q ∈ (boundaryComplex 2 N).space := by
    rw [boundaryComplex_space_eq_simplexBoundary_of_space_eq_convexHull N T hT hcard hspace]
    exact (simplexBoundary T hT).convexHull_subset_space hqface
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_singleton_self q)))
  obtain ⟨s, hs, hqs⟩ := (boundaryComplex 2 N).mem_space_iff.mp hqspace
  obtain ⟨m, -, hm⟩ :=
    exists_linearMap_lt_on_convexHull_sdiff_singleton T hT (by omega) hq
  have hqs' : q ∈ s := by
    by_contra hqnot
    have hslt : (s : Set E) ⊆ {x | m q < m x} := by
      intro v hv
      have hvspace : v ∈ (boundaryComplex 2 N).space :=
        (boundaryComplex 2 N).convexHull_subset_space hs
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))
      have hvT : v ∈ convexHull ℝ (T : Set E) :=
        hspace ▸ boundaryComplex_space_subset 2 N hvspace
      apply hm v
      exact ⟨hvT, fun hvq => hqnot (hvq ▸ hv)⟩
    have hlt := convexHull_min hslt (convex_halfSpace_gt m.isLinear (m q)) hqs
    exact (lt_irrefl (m q) hlt).elim
  exact (boundaryComplex 2 N).down_closed hs
    (Finset.singleton_subset_iff.mpr hqs') (Finset.singleton_nonempty q)

theorem segment_subset_boundaryComplex_of_space_eq_convexHull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] (N : Geometry.SimplicialComplex ℝ E) [Finite N.faces]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : T.card = 3)
    (hspace : N.space = convexHull ℝ (T : Set E)) {p q : E}
    (hp : p ∈ T) (hq : q ∈ T) (hpq : p ≠ q) :
    segment ℝ p q ⊆ (boundaryComplex 2 N).space := by
  rw [boundaryComplex_space_eq_simplexBoundary_of_space_eq_convexHull N T hT hcard hspace,
    ← convexHull_pair]
  have hpair : ({p, q} : Finset E) ∈ (simplexBoundary T hT).faces := by
    refine ⟨?_, Finset.insert_nonempty p {q}, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with hxp | hxq
      · exact hxp ▸ hp
      · exact Finset.mem_singleton.mp hxq ▸ hq
    · intro heq
      have hpaircard : ({p, q} : Finset E).card = 2 := by simp [hpq]
      rw [heq, hcard] at hpaircard
      omega
  simpa only [Finset.coe_pair] using
    (simplexBoundary T hT).convexHull_subset_space hpair

theorem exists_geometricLink_boundary_pair_of_isPLBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [dE : DecidableEq E] (M : Geometry.SimplicialComplex ℝ E) [Finite M.faces]
    (hM : IsPLBall 2 M.space) {q : E} (hqB : {q} ∈ (boundaryComplex 2 M).faces) :
    ∃ a b, a ≠ b ∧
      {a} ∈ (SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).faces ∧
      {b} ∈ (SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).faces ∧
      (SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).space = {a, b} := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  let G := SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}
  let _ : Finite (boundaryComplex 2 M).faces :=
    (boundaryComplex_faces_finite 2 M).to_subtype
  let _ : Finite G.faces :=
    (Set.toFinite G.faces).to_subtype
  have hman : IsCombinatorialManifoldWithBoundary 2 M :=
    hM.isCombinatorialManifoldWithBoundary
  have hlinkBall : IsPLBall 1 (SimplicialComplex.geometricLink M {q}).space := by
    have h := ((hman.mem_boundaryComplex_faces_iff M).mp hqB).2.2
    simpa only [Finset.card_singleton, Nat.reduceSub] using h
  have hsphere : IsPLSphere 0 G.space := by
    rw [show G = SimplicialComplex.geometricLink (boundaryComplex 2 M) {q} from rfl,
      geometricLink_boundaryComplex (n := 1) M q]
    exact isPLSphere_boundaryComplex_space_of_isPLBall
      (SimplicialComplex.geometricLink M {q}) hlinkBall
  obtain ⟨a, b, hab, hspace⟩ := isPLSphere_zero_iff.mp hsphere
  have haS : a ∈ G.space := hspace.symm.subset (Set.mem_insert a {b})
  have hbS : b ∈ G.space := hspace.symm.subset (Set.mem_insert_iff.mpr (Or.inr rfl))
  have hcardG : ∀ s ∈ G.faces, s.card ≤ 1 := fun s hs => by
    simpa only [Nat.zero_add] using card_le_of_isPLSphere G hsphere hs
  exact ⟨a, b, hab,
    singleton_mem_faces_of_mem_space_of_card_le_one G hcardG haS,
    singleton_mem_faces_of_mem_space_of_card_le_one G hcardG hbS, hspace⟩

end DifferentialGeometry.Topology.PiecewiseLinear
