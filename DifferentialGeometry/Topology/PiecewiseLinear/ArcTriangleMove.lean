/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexPush
import DifferentialGeometry.Topology.PiecewiseLinear.BallPairArc
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralSeparation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_isPLHomeomorphOn_segment_triangle_move
    {a b c : E} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hind : AffineIndependent ℝ ((↑) : ({c, a, b} : Finset E) → E))
    {C : Set E} (hC : IsPolyhedron C)
    (htri : convexHull ℝ ({c, a, b} : Set E) \ {a, b} ⊆ interior C) :
    ∃ e : E ≃ₜ E, IsPLHomeomorphOn e univ univ ∧ EqOn e id Cᶜ ∧
      EqOn e id (frontier C) ∧ e '' C = C ∧ e a = a ∧ e b = b ∧
      e '' segment ℝ a b = segment ℝ a c ∪ segment ℝ c b := by
  have hc : c ∉ ({a, b} : Finset E) := by simpa using And.intro hca hcb
  have hcard : 2 ≤ ({a, b} : Finset E).card := by rw [Finset.card_pair hab]
  have htri' : convexHull ℝ ((insert c ({a, b} : Finset E) : Finset E) : Set E) \
      (simplexBoundary ({a, b} : Finset E) (affineIndependent_coe_pair hab)).space ⊆
        interior C := by
    simpa only [Finset.coe_insert, Finset.coe_pair, Finset.coe_singleton,
      simplexBoundary_pair_space hab] using htri
  obtain ⟨e, he, hfix, hends, hmove⟩ :=
    exists_isPLHomeomorphOn_push_simplex {a, b} (affineIndependent_coe_pair hab)
      hcard hc hind hC htri'
  rw [simplexBoundary_pair_space hab] at hends
  have hfront : EqOn e id (frontier C) :=
    (hfix.closure e.continuous continuous_id).mono (by
      rw [frontier_eq_closure_inter_closure]
      exact inter_subset_right)
  have hset : e '' C = C := by
    apply compl_injective
    rw [← e.image_compl, hfix.image_eq_self]
  refine ⟨e, he, hfix, hfront, hset, hends (Or.inl rfl), hends (Or.inr rfl), ?_⟩
  have ha : a ∉ ({b} : Finset E) := by simpa using hab
  have hb : b ∉ ({a} : Finset E) := by simpa using hab.symm
  have herase : ({a, b} : Finset E).erase b = {a} := by
    rw [Finset.pair_comm a b, Finset.erase_insert hb]
  simpa only [Finset.coe_pair, convexHull_pair, Finset.mem_insert, Finset.mem_singleton,
    iUnion_iUnion_eq_or_left, iUnion_iUnion_eq_left, Finset.erase_insert ha, herase,
    Finset.coe_insert, Finset.coe_singleton, segment_symm ℝ c a, union_comm] using hmove

open Classical in
theorem exists_isPLHomeomorphOn_segment_triangle_move_fixed_on
    {a b c : E} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hind : AffineIndependent ℝ ((↑) : ({c, a, b} : Finset E) → E))
    {C R : Set E} (hC : IsPolyhedron C) (hR : IsPolyhedron R)
    (htri : convexHull ℝ ({c, a, b} : Set E) \ {a, b} ⊆ interior C)
    (hmeet : convexHull ℝ ({c, a, b} : Set E) ∩ R ⊆ {a, b}) :
    ∃ e : E ≃ₜ E, IsPLHomeomorphOn e univ univ ∧ EqOn e id Cᶜ ∧
      EqOn e id (frontier C) ∧ EqOn e id R ∧ e '' C = C ∧ e a = a ∧ e b = b ∧
      e '' segment ℝ a b = segment ℝ a c ∪ segment ℝ c b := by
  have hT : IsPolyhedron (convexHull ℝ ({c, a, b} : Set E)) := by
    simpa only [Finset.coe_insert, Finset.coe_pair, Finset.coe_singleton] using
      isPolyhedron_convexHull_of_affineIndependent ({c, a, b} : Finset E) hind
  obtain ⟨N, hN, hTN, -, hNR⟩ :=
    exists_isPolyhedron_neighborhood_sdiff hT hR isOpen_univ (subset_univ _)
  have htriN : convexHull ℝ ({c, a, b} : Set E) \ {a, b} ⊆ interior (C ∩ N) := by
    intro x hx
    rw [interior_inter]
    exact ⟨htri hx, hTN ⟨hx.1, fun hxR => hx.2 (hmeet ⟨hx.1, hxR⟩)⟩⟩
  obtain ⟨e, he, hfix, -, -, ha, hb, himage⟩ :=
    exists_isPLHomeomorphOn_segment_triangle_move hab hca hcb hind (hC.inter hN) htriN
  have hfixC : EqOn e id Cᶜ := hfix.mono (by
    intro x hx hCN
    exact hx hCN.1)
  have hfront : EqOn e id (frontier C) :=
    (hfixC.closure e.continuous continuous_id).mono (by
      rw [frontier_eq_closure_inter_closure]
      exact inter_subset_right)
  have hfixR : EqOn e id R := by
    intro x hxR
    by_cases hxN : x ∈ N
    · rcases hmeet (hNR.subset ⟨hxN, hxR⟩) with rfl | hx
      · exact ha
      · exact mem_singleton_iff.mp hx ▸ hb
    · exact hfix (fun hx => hxN hx.2)
  refine ⟨e, he, hfixC, hfront, hfixR, ?_, ha, hb, himage⟩
  apply compl_injective
  rw [← e.image_compl, hfixC.image_eq_self]

end DifferentialGeometry.Topology.PiecewiseLinear
