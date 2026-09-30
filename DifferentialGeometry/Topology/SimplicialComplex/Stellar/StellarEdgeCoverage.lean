import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic

namespace DifferentialGeometry.Topology.Engulfing

open Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem segment_eq_union_at_point {a b p : E} (hp : p ∈ segment ℝ a b) :
    segment ℝ a b = segment ℝ a p ∪ segment ℝ p b := by
  have hprange : p ∈ range (AffineMap.lineMap a b : ℝ → E) := by
    rw [segment_eq_image_lineMap] at hp
    exact image_subset_range _ _ hp
  apply Subset.antisymm
  · apply (openSegment_subset_iff_segment_subset (𝕜 := ℝ)
      (s := segment ℝ a p ∪ segment ℝ p b)
      (Or.inl (left_mem_segment ℝ a p)) (Or.inr (right_mem_segment ℝ p b))).mp
    intro x hx
    rcases openSegment_subset_union a b hprange hx with hxp | hxp
    · exact Or.inl (hxp ▸ right_mem_segment ℝ a p)
    · exact hxp.imp (fun h => openSegment_subset_segment ℝ a p h)
        (fun h => openSegment_subset_segment ℝ p b h)
  · exact union_subset
      ((convex_segment (𝕜 := ℝ) a b).segment_subset (left_mem_segment ℝ a b) hp)
      ((convex_segment (𝕜 := ℝ) a b).segment_subset hp (right_mem_segment ℝ a b))

theorem convexHull_eq_union_of_edge_point {S : Set E} {a b p : E}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (hp : p ∈ segment ℝ a b) :
    convexHull ℝ S = convexHull ℝ (insert p (S \ {a})) ∪
      convexHull ℝ (insert p (S \ {b})) := by
  let R : Set E := (S \ {a, b}) ∪ {p}
  have hR : R.Nonempty := ⟨p, Or.inr rfl⟩
  have hwhole : ({a, b} : Set E) ∪ R = insert p S := by
    ext x
    by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all [R]
  have hleft : ({a, p} : Set E) ∪ R = insert p (S \ {b}) := by
    ext x
    by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all [R]
  have hright : ({p, b} : Set E) ∪ R = insert p (S \ {a}) := by
    ext x
    by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all [R]
  have hpS : p ∈ convexHull ℝ S := segment_subset_convexHull ha hb hp
  have hinsert : convexHull ℝ (insert p S) = convexHull ℝ S := by
    apply Subset.antisymm
    · exact convexHull_min (insert_subset_iff.mpr ⟨hpS, subset_convexHull ℝ S⟩)
        (convex_convexHull ℝ S)
    · exact convexHull_mono (subset_insert p S)
  calc
    convexHull ℝ S = convexHull ℝ (({a, b} : Set E) ∪ R) := by rw [hwhole, hinsert]
    _ = convexJoin ℝ (segment ℝ a b) (convexHull ℝ R) := by
      rw [convexHull_union (insert_nonempty a {b}) hR, convexHull_pair]
    _ = convexJoin ℝ (segment ℝ a p) (convexHull ℝ R) ∪
        convexJoin ℝ (segment ℝ p b) (convexHull ℝ R) := by
      rw [segment_eq_union_at_point hp, convexJoin_union_left]
    _ = convexHull ℝ (({a, p} : Set E) ∪ R) ∪
        convexHull ℝ (({p, b} : Set E) ∪ R) := by
      rw [convexHull_union (insert_nonempty a {p}) hR,
        convexHull_union (insert_nonempty p {b}) hR, convexHull_pair, convexHull_pair]
    _ = convexHull ℝ (insert p (S \ {a})) ∪ convexHull ℝ (insert p (S \ {b})) := by
      rw [hleft, hright, union_comm]

theorem convexHull_eq_union_stellar_edge [DecidableEq E] {V : Finset E} {a b p : E}
    (ha : a ∈ V) (hb : b ∈ V) (hab : a ≠ b) (hp : p ∈ segment ℝ a b) :
    convexHull ℝ (V : Set E) = convexHull ℝ ((insert p (V.erase a) : Finset E) : Set E) ∪
      convexHull ℝ ((insert p (V.erase b) : Finset E) : Set E) := by
  simpa only [Finset.coe_insert, Finset.coe_erase] using
    convexHull_eq_union_of_edge_point ha hb hab hp

end DifferentialGeometry.Topology.Engulfing
