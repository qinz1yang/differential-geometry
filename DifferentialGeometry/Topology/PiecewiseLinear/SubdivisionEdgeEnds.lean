/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexComplex
import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionEndPoints

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

theorem eq_of_neighbors_on_segment (K : Geometry.SimplicialComplex ℝ E) {a b c d : E}
    (hca : c ≠ a) (hda : d ≠ a) (hac : ({a, c} : Finset E) ∈ K.faces)
    (had : ({a, d} : Finset E) ∈ K.faces) (hc : c ∈ segment ℝ a b)
    (hd : d ∈ segment ℝ a b) : c = d := by
  classical
  have hlink : ∀ z : E, z ≠ a → ({a, z} : Finset E) ∈ K.faces →
      z ∈ (SimplicialComplex.geometricLink K {a}).space := by
    intro z hza haz
    have hz : ({z} : Finset E) ∈ (SimplicialComplex.geometricLink K {a}).faces := by
      apply (SimplicialComplex.mem_geometricLink_singleton K a {z}).mpr
      exact ⟨by simp, by simpa using hza.symm, by simpa using haz⟩
    exact (SimplicialComplex.geometricLink K {a}).convexHull_subset_space hz
      (subset_convexHull ℝ _ (by simp))
  rw [segment_eq_image'] at hc hd
  obtain ⟨α, hα, hc⟩ := hc
  obtain ⟨β, hβ, hd⟩ := hd
  beta_reduce at hc hd
  have hαpos : 0 < α := by
    rcases hα.1.eq_or_lt with h0 | h0
    · exact (hca (by rw [← hc, ← h0, zero_smul, add_zero])).elim
    · exact h0
  have hβpos : 0 < β := by
    rcases hβ.1.eq_or_lt with h0 | h0
    · exact (hda (by rw [← hd, ← h0, zero_smul, add_zero])).elim
    · exact h0
  apply (isRadiallyInjective_geometricLink K).eq_of_add_smul_eq
    (hlink c hca hac) (hlink d hda had) hβpos hαpos
  rw [← hc, ← hd, add_sub_cancel_left, add_sub_cancel_left, smul_smul, smul_smul, mul_comm]

theorem IsSubdivision.exists_unique_neighbor_in_segment
    {K K' : Geometry.SimplicialComplex ℝ E} [Finite K'.faces] (hsub : IsSubdivision K' K)
    {a b : E} (hab : a ≠ b) (he : ({a, b} : Finset E) ∈ K.faces)
    (ha : ({a} : Finset E) ∈ K'.faces) :
    ∃ c, c ≠ a ∧ ({a, c} : Finset E) ∈ K'.faces ∧ c ∈ segment ℝ a b ∧
      ∀ d, d ≠ a → ({a, d} : Finset E) ∈ K'.faces → d ∈ segment ℝ a b → d = c := by
  classical
  let L := simplexComplex ({a, b} : Finset E) (K.indep he)
  have hLK : L.faces ⊆ K.faces := fun s hs => K.down_closed he hs.2 hs.1
  have hLs : L.space = segment ℝ a b := by
    rw [simplexComplex_space _ _ (by simp), Finset.coe_pair, convexHull_pair]
  let R := PiecewiseLinear.restrict K' L.space
  have hRsub : IsSubdivision R L := hsub.restrict L hLK
  have hRs : R.space = segment ℝ a b := hRsub.space_eq.trans hLs
  have : Finite R.faces := (restrict_faces_finite K' L.space).to_subtype
  have hdim : ∀ s ∈ R.faces, s.card ≤ 2 := fun s hs =>
    hRsub.card_le (fun t ht => (Finset.card_le_card ht.2).trans Finset.card_le_two) hs
  have haR : ({a} : Finset E) ∈ R.faces := by
    refine ⟨ha, ?_⟩
    rw [Finset.coe_singleton, convexHull_singleton, singleton_subset_iff, hLs]
    exact left_mem_segment ℝ a b
  have hray : ∀ t ∈ Ioc (0 : ℝ) 1, a + t • (b - a) ∈ R.space := by
    intro t ht
    rw [hRs]
    exact (convex_segment a b).add_smul_sub_mem (left_mem_segment ℝ a b)
      (right_mem_segment ℝ a b) ⟨ht.1.le, ht.2⟩
  obtain ⟨c, _, hca, hac, -⟩ := exists_pair_mem_faces_of_forall_add_smul_mem_space hdim haR
    (sub_ne_zero.mpr hab.symm) one_pos hray
  have hc : c ∈ segment ℝ a b := hLs ▸ hac.2 (subset_convexHull ℝ _ (by simp))
  have hac' : ({a, c} : Finset E) ∈ K'.faces := by
    convert hac.1 using 1
    ext y
    simp only [Finset.mem_insert, Finset.mem_singleton]
  exact ⟨c, hca, hac', hc, fun d hda had hd =>
    eq_of_neighbors_on_segment K' hda hca had hac' hd hc⟩

end DifferentialGeometry.Topology.PiecewiseLinear
