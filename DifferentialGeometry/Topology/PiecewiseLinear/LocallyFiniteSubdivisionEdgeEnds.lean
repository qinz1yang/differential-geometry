/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionEdgeEnds
import DifferentialGeometry.Topology.PiecewiseLinear.DiskBallNeighborhoodImage

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

theorem LocallyFinitePLPieceIn.exists_unique_neighbor_in_segment
    {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] {Y : Set X}
    (T : LocallyFinitePLPieceIn E 3 X Y) {K : Geometry.SimplicialComplex ℝ E}
    (hsub : IsSubdivision T.complex K)
    {a b : E} (hab : a ≠ b) (he : ({a, b} : Finset E) ∈ K.faces)
    (ha : ({a} : Finset E) ∈ T.complex.faces) :
    ∃ c, c ≠ a ∧ ({a, c} : Finset E) ∈ T.complex.faces ∧ c ∈ segment ℝ a b ∧
      ∀ d, d ≠ a → ({a, d} : Finset E) ∈ T.complex.faces → d ∈ segment ℝ a b → d = c := by
  classical
  let L := simplexComplex ({a, b} : Finset E) (K.indep he)
  have hLK : L.faces ⊆ K.faces := fun s hs => K.down_closed he hs.2 hs.1
  have hLs : L.space = segment ℝ a b := by
    rw [simplexComplex_space _ _ (by simp), Finset.coe_pair, convexHull_pair]
  let R := PiecewiseLinear.restrict T.complex L.space
  have hRsub : IsSubdivision R L := hsub.restrict L hLK
  have hRs : R.space = segment ℝ a b := hRsub.space_eq.trans hLs
  have hLc : IsCompact L.space := by
    rw [hLs, ← convexHull_pair]
    exact (Set.toFinite {a, b}).isCompact_convexHull ℝ
  have hLKspace : L.space ⊆ T.complex.space := by
    rw [hsub.space_eq, hLs, ← convexHull_pair, ← Finset.coe_pair]
    exact K.convexHull_subset_space he
  have hRfin : R.faces.Finite := by
    refine (T.finite_faces_inter_of_isCompact hLc hLKspace).subset ?_
    rintro σ ⟨hσ, hσL⟩
    obtain ⟨z, hz⟩ := T.complex.nonempty_of_mem_faces hσ
    exact ⟨hσ, z, subset_convexHull ℝ _ (Finset.mem_coe.mpr hz),
      hσL (subset_convexHull ℝ _ (Finset.mem_coe.mpr hz))⟩
  have : Finite R.faces := hRfin.to_subtype
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
  have hac' : ({a, c} : Finset E) ∈ T.complex.faces := by
    convert hac.1 using 1
    ext y
    simp only [Finset.mem_insert, Finset.mem_singleton]
  exact ⟨c, hca, hac', hc, fun d hda had hd =>
    eq_of_neighbors_on_segment T.complex hda hca had hac' hd hc⟩

end DifferentialGeometry.Topology.PiecewiseLinear
