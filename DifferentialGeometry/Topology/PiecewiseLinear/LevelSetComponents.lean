/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallStarring
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFacets
import DifferentialGeometry.Topology.PiecewiseLinear.LevelSetOneManifold
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.OneManifoldComponents

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem singleton_mem_graphComponentComplex_of_mem_space (K : Geometry.SimplicialComplex ℝ E)
    (c : (SimplicialComplex.edgeGraph K).ConnectedComponent) {x : E} (hxK : {x} ∈ K.faces)
    (hxc : x ∈ (graphComponentComplex K c).space) : {x} ∈ (graphComponentComplex K c).faces := by
  obtain ⟨t, ht, hxt⟩ := (graphComponentComplex K c).mem_space_iff.mp hxc
  have hxt' : x ∈ t := mem_of_mem_convexHull_of_singleton_mem K hxK ht.1 hxt
  refine ⟨hxK, ?_⟩
  rw [Finset.coe_singleton, singleton_subset_iff]
  exact ht.2 hxt'

open Classical in
theorem ncard_neighbors_graphComponentComplex (K : Geometry.SimplicialComplex ℝ E)
    (c : (SimplicialComplex.edgeGraph K).ConnectedComponent) {x : E}
    (hx : {x} ∈ (graphComponentComplex K c).faces) :
    {w | w ≠ x ∧ {x, w} ∈ (graphComponentComplex K c).faces}.ncard =
      {w | w ≠ x ∧ {x, w} ∈ K.faces}.ncard := by
  let v : (graphComponentComplex K c).vertices := ⟨x, hx⟩
  let w : c.supp := (graphComponentVertexEquiv K c).symm v
  have hvw : graphComponentVertex K c w = v := (graphComponentVertexEquiv K c).apply_symm_apply v
  have hwx : (w.1 : E) = x := by
    have h := congrArg Subtype.val hvw
    exact h
  have htransfer := graphComponentEdgeGraph_neighborSet_ncard K c w
  rw [hvw, SimplicialComplex.ncard_neighborSet_edgeGraph,
    SimplicialComplex.ncard_neighborSet_edgeGraph, hwx] at htransfer
  exact htransfer

open Classical in
theorem coface_set_singleton_eq (K : Geometry.SimplicialComplex ℝ E) (x : E) :
    {w | w ∉ ({x} : Finset E) ∧ insert w ({x} : Finset E) ∈ K.faces} =
      {w | w ≠ x ∧ {x, w} ∈ K.faces} := by
  ext w
  change (w ∉ ({x} : Finset E) ∧ ({w, x} : Finset E) ∈ K.faces) ↔
    (w ≠ x ∧ ({x, w} : Finset E) ∈ K.faces)
  rw [Finset.mem_singleton, Finset.pair_comm w x]

open Classical in
theorem exists_finite_circle_arc_decomposition_of_neighbors [FiniteDimensional ℝ E]
    (G : Geometry.SimplicialComplex ℝ E) [Finite G.faces] (hcard : ∀ u ∈ G.faces, u.card ≤ 2)
    (W : Set E) (hWv : ∀ x ∈ G.space ∩ W, {x} ∈ G.faces)
    (hdeg : ∀ x, {x} ∈ G.faces →
      (x ∈ W → ∃ a, {y | y ≠ x ∧ {x, y} ∈ G.faces} = {a}) ∧
      (x ∉ W → ∃ a b, a ≠ b ∧ {y | y ≠ x ∧ {x, y} ∈ G.faces} = {a, b})) :
    ∃ C : Set (Set E), C.Finite ∧ C.PairwiseDisjoint id ∧ G.space = ⋃₀ C ∧
      ∀ S ∈ C, (IsPLSphere 1 S ∧ Disjoint S W) ∨
        ∃ q : (Fin 2 → ℝ) → E, IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) S ∧
          q '' stdSimplexBoundary 1 = S ∩ W := by
  have hG : IsCombinatorialManifoldWithBoundary 1 G := by
    apply (isCombinatorialManifoldWithBoundary_one_iff G).mpr
    refine ⟨hcard, fun x hx => ?_⟩
    by_cases hxW : x ∈ W
    · exact Or.inl ((hdeg x hx).1 hxW)
    · exact Or.inr ((hdeg x hx).2 hxW)
  have hncard : ∀ x, {x} ∈ G.faces →
      ({y | y ≠ x ∧ {x, y} ∈ G.faces}.ncard = 1 ↔ x ∈ W) := by
    intro x hx
    constructor
    · intro h1
      by_contra hxW
      obtain ⟨a, b, hab, hpair⟩ := (hdeg x hx).2 hxW
      rw [hpair, Set.ncard_pair hab] at h1
      exact absurd h1 (by norm_num)
    · intro hxW
      obtain ⟨a, ha⟩ := (hdeg x hx).1 hxW
      rw [ha, Set.ncard_singleton]
  let _ : Finite G.vertices := (SimplicialComplex.finite_vertices G).to_subtype
  let F := fun c : (SimplicialComplex.edgeGraph G).ConnectedComponent =>
    (graphComponentComplex G c).space
  refine ⟨range F, Set.finite_range _, ?_, ?_, ?_⟩
  · rintro S ⟨c, rfl⟩ T ⟨d, rfl⟩ hne
    exact pairwise_disjoint_graphComponentComplex_space G (fun hcd => hne (congrArg F hcd))
  · simpa only [sUnion_range] using space_eq_iUnion_graphComponentComplex G
  · rintro S ⟨c, rfl⟩
    let R := graphComponentComplex G c
    have : Finite R.faces := (graphComponentComplex_faces_finite G c).to_subtype
    have hR : IsCombinatorialManifoldWithBoundary 1 R :=
      graphComponentComplex_isManifoldWithBoundary G hG c
    have hRG : R.space ⊆ G.space := graphComponentComplex_space_subset G c
    have hvertW : ∀ x ∈ R.space ∩ W, {x} ∈ R.faces ∧
        {y | y ≠ x ∧ {x, y} ∈ R.faces}.ncard = 1 := by
      rintro x ⟨hxR, hxW⟩
      have hxG : {x} ∈ G.faces := hWv x ⟨hRG hxR, hxW⟩
      have hxRf := singleton_mem_graphComponentComplex_of_mem_space G c hxG hxR
      refine ⟨hxRf, ?_⟩
      rw [ncard_neighbors_graphComponentComplex G c hxRf]
      exact (hncard x hxG).mpr hxW
    have hbd : (boundaryComplex 1 R).space = R.space ∩ W := by
      apply Subset.antisymm
      · intro y hy
        obtain ⟨s, hs, hys⟩ := (boundaryComplex 1 R).mem_space_iff.mp hy
        have hs' := (hR.mem_boundaryComplex_faces_iff (n := 0)).mp hs
        have hscard : s.card = 1 := by
          have := Finset.card_pos.mpr (R.nonempty_of_mem_faces hs'.1)
          omega
        obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hscard
        have hyx : y = x := by
          simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using hys
        subst hyx
        have hcof := (hR.mem_boundaryComplex_iff_unique_coface R (n := 0) hscard).mp hs
        rw [coface_set_singleton_eq R y] at hcof
        obtain ⟨a, ha⟩ := hcof
        have h1 : {w | w ≠ y ∧ {y, w} ∈ R.faces}.ncard = 1 := by
          rw [ha, Set.ncard_singleton]
        have hyG : {y} ∈ G.faces := hs'.1.1
        rw [ncard_neighbors_graphComponentComplex G c hs'.1] at h1
        exact ⟨R.subset_space hs'.1 (Finset.mem_singleton_self y), (hncard y hyG).mp h1⟩
      · intro x hx
        obtain ⟨hxRf, h1⟩ := hvertW x hx
        have hmem : {x} ∈ (boundaryComplex 1 R).faces := by
          apply (hR.mem_boundaryComplex_iff_unique_coface R (n := 0)
            (Finset.card_singleton x)).mpr
          rw [coface_set_singleton_eq R x]
          exact Set.ncard_eq_one.mp h1
        exact (boundaryComplex 1 R).subset_space hmem (Finset.mem_singleton_self x)
    rcases graphComponentComplex_isPLSphere_or_isPLBall G hG c with hsph | hball
    · refine Or.inl ⟨hsph, Set.disjoint_left.mpr fun x hxR hxW => ?_⟩
      have hRm : IsCombinatorialManifold 1 R := hsph.isCombinatorialManifold
      obtain ⟨hxRf, h1⟩ := hvertW x ⟨hxR, hxW⟩
      obtain ⟨a, b, hab, hpair⟩ := (isCombinatorialManifold_one_iff R).mp hRm |>.2 x hxRf
      rw [hpair, Set.ncard_pair hab] at h1
      exact absurd h1 (by norm_num)
    · obtain ⟨q, hq⟩ := hball
      refine Or.inr ⟨q, hq, ?_⟩
      rw [hq.image_stdSimplexBoundary_eq_boundaryComplex (m := 0) R rfl, hbd]

end DifferentialGeometry.Topology.PiecewiseLinear
