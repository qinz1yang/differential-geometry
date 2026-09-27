import DifferentialGeometry.Analysis.Convex.AffineBasis
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Set Metric

namespace AffineBasis

theorem triangle_complement_sides {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : AffineBasis (Fin 3) ℝ E) {S B : Set E} (hB : IsClosed B)
    (hS : S = B ∪ convexHull ℝ (range b))
    (hattach : B ∩ convexHull ℝ (range b) =
      segment ℝ (b 0) (b 2) ∪ segment ℝ (b 1) (b 2)) :
    let N := (interior S ∩ {p | 0 < b.coord 2 p}) ∪
      (Bᶜ ∩ {p | 0 < b.coord 0 p ∧ 0 < b.coord 1 p})
    IsOpen N ∧ ∀ p ∈ N,
      (p ∈ B ↔ min (b.coord 0 p) (b.coord 1 p) ≤ 0) ∧
      (p ∈ interior B ↔ min (b.coord 0 p) (b.coord 1 p) < 0) ∧
      (p ∈ frontier B ↔ min (b.coord 0 p) (b.coord 1 p) = 0) := by
  let : FiniteDimensional ℝ E := b.finiteDimensional
  let N := (interior S ∩ {p | 0 < b.coord 2 p}) ∪
    (Bᶜ ∩ {p | 0 < b.coord 0 p ∧ 0 < b.coord 1 p})
  have hN : IsOpen N :=
    (isOpen_interior.inter
      (isOpen_lt continuous_const (b.coord 2).continuous_of_finiteDimensional)).union
      (hB.isOpen_compl.inter
        ((isOpen_lt continuous_const (b.coord 0).continuous_of_finiteDimensional).inter
          (isOpen_lt continuous_const (b.coord 1).continuous_of_finiteDimensional)))
  have hweak (p : E) (hpN : p ∈ N) : p ∈ B ↔ min (b.coord 0 p) (b.coord 1 p) ≤ 0 := by
    rcases hpN with hp | hp
    · constructor
      · intro hpB
        by_contra! hpos
        have hpC : p ∈ convexHull ℝ (range b) := by
          rw [b.convexHull_eq_nonneg_coord]
          intro i
          fin_cases i
          · exact (hpos.trans_le (min_le_left _ _)).le
          · exact (hpos.trans_le (min_le_right _ _)).le
          · exact hp.2.le
        have hseg := hattach ▸ (show p ∈ B ∩ convexHull ℝ (range b) from ⟨hpB, hpC⟩)
        rcases hseg with hseg | hseg
        · have hz := ((b.mem_segment_iff_coord 0 2).mp hseg).2 1 (by decide) (by decide)
          exact (hpos.trans_le (min_le_right _ _)).ne' hz
        · have hz := ((b.mem_segment_iff_coord 1 2).mp hseg).2 0 (by decide) (by decide)
          exact (hpos.trans_le (min_le_left _ _)).ne' hz
      · intro hmin
        by_cases hpC : p ∈ convexHull ℝ (range b)
        · have hc : ∀ j, 0 ≤ b.coord j p := by
            rw [b.convexHull_eq_nonneg_coord] at hpC
            exact hpC
          have hseg : p ∈ segment ℝ (b 0) (b 2) ∪ segment ℝ (b 1) (b 2) := by
            rcases min_le_iff.mp hmin with h₀ | h₁
            · exact Or.inr (b.mem_segment_of_coord_eq_zero hc 0 (le_antisymm h₀ (hc 0)))
            · have h := b.mem_segment_of_coord_eq_zero hc 1 (le_antisymm h₁ (hc 1))
              exact Or.inl (by simpa only [Fin.reduceAdd, segment_symm] using h)
          exact ((hattach.symm ▸ hseg) : p ∈ B ∩ convexHull ℝ (range b)).1
        · exact (hS ▸ interior_subset hp.1).resolve_right hpC
    · exact iff_of_false hp.1 (not_le.mpr (lt_min hp.2.1 hp.2.2))
  have hstrict (p : E) (hpN : p ∈ N) :
      p ∈ interior B ↔ min (b.coord 0 p) (b.coord 1 p) < 0 := by
    constructor
    · intro hpB
      by_contra! hmge
      have hpcoords : 0 ≤ b.coord 0 p ∧ 0 ≤ b.coord 1 p :=
        ⟨hmge.trans (min_le_left _ _), hmge.trans (min_le_right _ _)⟩
      let q := AffineMap.lineMap (b 0) (b 1) (1 / 2 : ℝ)
      have hq₀ : b.coord 0 q = 1 / 2 := by
        norm_num [q, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring, b.coord_apply]
      have hq₁ : b.coord 1 q = 1 / 2 := by
        norm_num [q, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring, b.coord_apply]
      have hp : (0 : ℝ) ∈ (AffineMap.lineMap p q) ⁻¹' (N ∩ interior B) := by
        change AffineMap.lineMap p q 0 ∈ N ∩ interior B
        rw [AffineMap.lineMap_apply_zero]
        exact ⟨hpN, hpB⟩
      obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp
        ((hN.inter isOpen_interior).preimage AffineMap.lineMap_continuous) 0 hp
      let t := min (δ / 2) (1 / 2)
      have ht : 0 < t := lt_min (half_pos hδ) (by norm_num)
      have ht1 : t ≤ 1 := (min_le_right _ _).trans (by norm_num)
      have htδ : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
      have hv := hδV (show t ∈ ball (0 : ℝ) δ from by
        simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using htδ)
      have hpos : 0 < min (b.coord 0 (AffineMap.lineMap p q t))
          (b.coord 1 (AffineMap.lineMap p q t)) := by
        rw [AffineMap.apply_lineMap, hq₀, AffineMap.apply_lineMap, hq₁,
          AffineMap.lineMap_apply_ring, AffineMap.lineMap_apply_ring]
        exact lt_min
          (add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht1) hpcoords.1)
            (mul_pos ht (by norm_num)))
          (add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht1) hpcoords.2)
            (mul_pos ht (by norm_num)))
      exact (not_le_of_gt hpos) ((hweak _ hv.1).mp (interior_subset hv.2))
    · intro hpmin
      have hV : IsOpen (N ∩ {p | min (b.coord 0 p) (b.coord 1 p) < 0}) :=
        hN.inter (isOpen_lt
          ((b.coord 0).continuous_of_finiteDimensional.min
            (b.coord 1).continuous_of_finiteDimensional) continuous_const)
      have hVB : N ∩ {p | min (b.coord 0 p) (b.coord 1 p) < 0} ⊆ B :=
        fun x hx => (hweak x hx.1).mpr hx.2.le
      exact (hV.subset_interior_iff.mpr hVB) ⟨hpN, hpmin⟩
  refine ⟨hN, fun p hp => ⟨hweak p hp, hstrict p hp, ?_⟩⟩
  rw [hB.frontier_eq]
  change (p ∈ B ∧ p ∉ interior B) ↔ min (b.coord 0 p) (b.coord 1 p) = 0
  rw [hweak p hp, hstrict p hp, not_lt]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

end AffineBasis
