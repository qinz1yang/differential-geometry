import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem segment_union_segment_of_mem_segment {E : Type*} [AddCommGroup E] [Module ℝ E]
    {z w q : E} (hq : q ∈ segment ℝ z w) :
    segment ℝ q z ∪ segment ℝ q w = segment ℝ z w := by
  refine Subset.antisymm (union_subset ?_ ?_) ?_
  · exact (convex_segment z w).segment_subset hq (left_mem_segment ℝ z w)
  · exact (convex_segment z w).segment_subset hq (right_mem_segment ℝ z w)
  · obtain ⟨c, d, hc, hd, hcd, hqe⟩ := hq
    have hc' : c = 1 - d := by linarith
    subst hc'
    rintro x ⟨a, b, ha, hb, hab, rfl⟩
    have ha' : a = 1 - b := by linarith
    subst ha'
    rcases le_total b d with h | h
    · refine Or.inl ?_
      rcases eq_or_lt_of_le hd with hd0 | hd0
      · have hb0 : b = 0 := by linarith
        rw [hb0]
        simpa using right_mem_segment ℝ q z
      · refine ⟨b / d, 1 - b / d, div_nonneg hb hd, ?_, by ring, ?_⟩
        · rw [sub_nonneg, div_le_one hd0]
          exact h
        · rw [← hqe]
          have hd' : d ≠ 0 := ne_of_gt hd0
          match_scalars <;> (field_simp; try ring)
    · refine Or.inr ?_
      rcases eq_or_lt_of_le hc with hc0 | hc0
      · have hb1 : b = 1 := by linarith
        rw [hb1]
        simpa using right_mem_segment ℝ q w
      · refine ⟨(1 - b) / (1 - d), 1 - (1 - b) / (1 - d), div_nonneg ha hc, ?_, by ring, ?_⟩
        · rw [sub_nonneg, div_le_one hc0]
          linarith
        · rw [← hqe]
          have hc' : (1 : ℝ) - d ≠ 0 := ne_of_gt hc0
          match_scalars <;> (field_simp; try ring)

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem segment_inter_le_eq_singleton {z w : E} {ℓ : E →ₗ[ℝ] ℝ} {r : ℝ} (hz : ℓ z = r)
    (hw : r < ℓ w) : segment ℝ z w ∩ {x | ℓ x ≤ r} = {z} := by
  apply Subset.antisymm
  · rintro x ⟨⟨a, b, ha, hb, hab, rfl⟩, hx⟩
    simp only [Set.mem_ofPred_eq, map_add, map_smul, hz, smul_eq_mul] at hx
    have hb0 : b = 0 := by
      rcases eq_or_lt_of_le hb with h | h
      · exact h.symm
      · exfalso
        have ha' : a = 1 - b := by linarith
        rw [ha'] at hx
        nlinarith [mul_pos h (sub_pos.mpr hw)]
    have ha1 : a = 1 := by linarith
    rw [hb0, ha1, one_smul, zero_smul, add_zero]
    rfl
  · rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨left_mem_segment ℝ x w, by simp [hz]⟩

theorem segment_inter_ge_eq_singleton {z p : E} {ℓ : E →ₗ[ℝ] ℝ} {r : ℝ} (hz : ℓ z = r)
    (hp : ℓ p < r) : segment ℝ z p ∩ {x | r ≤ ℓ x} = {z} := by
  have h := segment_inter_le_eq_singleton (z := z) (w := p) (ℓ := -ℓ) (r := -r)
    (by simp [hz]) (by simp only [LinearMap.neg_apply]; linarith)
  simpa only [LinearMap.neg_apply, neg_le_neg_iff] using h

theorem segment_inter_le_eq_segment {p w z : E} {ℓ : E →ₗ[ℝ] ℝ} {r : ℝ}
    (hzs : z ∈ segment ℝ p w) (hz : ℓ z = r) (hp : ℓ p ≤ r) (hw : r < ℓ w) :
    segment ℝ p w ∩ {x | ℓ x ≤ r} = segment ℝ p z := by
  rw [← segment_union_segment_of_mem_segment hzs, Set.union_inter_distrib_right,
    segment_inter_le_eq_singleton hz hw]
  have h1 : segment ℝ z p ∩ {x : E | ℓ x ≤ r} = segment ℝ z p := by
    rw [Set.inter_eq_left]
    exact (convex_halfSpace_le ℓ.isLinear r).segment_subset (by simp [hz]) hp
  rw [h1, Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr (left_mem_segment ℝ z p)),
    segment_symm]

theorem segment_inter_ge_eq_segment {p w z : E} {ℓ : E →ₗ[ℝ] ℝ} {r : ℝ}
    (hzs : z ∈ segment ℝ p w) (hz : ℓ z = r) (hp : ℓ p < r) (hw : r ≤ ℓ w) :
    segment ℝ p w ∩ {x | r ≤ ℓ x} = segment ℝ z w := by
  have hzs' : z ∈ segment ℝ w p := by rwa [segment_symm]
  have h := segment_inter_le_eq_segment (p := w) (w := p) (z := z) (ℓ := -ℓ) (r := -r) hzs'
    (by simp [hz]) (by simp only [LinearMap.neg_apply]; linarith)
    (by simp only [LinearMap.neg_apply]; linarith)
  rw [segment_symm ℝ w p] at h
  simpa only [LinearMap.neg_apply, neg_le_neg_iff, segment_symm ℝ w z] using h

theorem segment_inter_eq_singleton {p w z : E} {ℓ : E →ₗ[ℝ] ℝ} {r : ℝ}
    (hzs : z ∈ segment ℝ p w) (hz : ℓ z = r) (hp : ℓ p < r) (hw : r < ℓ w) :
    segment ℝ p w ∩ {x | ℓ x = r} = {z} := by
  have hset : {x : E | ℓ x = r} = {x : E | ℓ x ≤ r} ∩ {x : E | r ≤ ℓ x} := by
    ext x
    exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩
  rw [hset, ← Set.inter_assoc, segment_inter_le_eq_segment hzs hz hp.le hw, segment_symm,
    segment_inter_ge_eq_singleton hz hp]

theorem segment_subset_of_mem_segment {p d z : E} (hzs : z ∈ segment ℝ p d) :
    segment ℝ p z ⊆ segment ℝ p d :=
  (convex_segment p d).segment_subset (left_mem_segment ℝ p d) hzs

theorem segment_right_subset_of_mem_segment {p d z : E} (hzs : z ∈ segment ℝ p d) :
    segment ℝ z d ⊆ segment ℝ p d :=
  (convex_segment p d).segment_subset hzs (right_mem_segment ℝ p d)

theorem segment_subset_halfSpace_lt {p c : E} {ℓ : E →ₗ[ℝ] ℝ} {r : ℝ} (hp : ℓ p < r)
    (hc : ℓ c < r) : segment ℝ p c ⊆ {x : E | ℓ x < r} :=
  (convex_halfSpace_lt ℓ.isLinear r).segment_subset hp hc

theorem inter_arc_of_subset_halfSpace_le {P : Set E} {ℓ : E →ₗ[ℝ] ℝ} {r : ℝ} {p c d z : E}
    (hP : P ⊆ {x : E | ℓ x ≤ r}) (hpc : segment ℝ p c ⊆ P) (hpzP : segment ℝ p z ⊆ P)
    (hzs : z ∈ segment ℝ p d) (hz : ℓ z = r) (hp : ℓ p ≤ r) (hd : r < ℓ d) :
    P ∩ (segment ℝ p c ∪ segment ℝ p d) = segment ℝ p c ∪ segment ℝ p z := by
  rw [Set.inter_union_distrib_left, Set.inter_eq_right.mpr hpc]
  congr 1
  apply Subset.antisymm
  · rintro x ⟨hxP, hxd⟩
    have hx : x ∈ segment ℝ p d ∩ {y : E | ℓ y ≤ r} := ⟨hxd, hP hxP⟩
    rwa [segment_inter_le_eq_segment hzs hz hp hd] at hx
  · exact fun x hx => ⟨hpzP hx, segment_subset_of_mem_segment hzs hx⟩

theorem inter_arc_of_subset_halfSpace_ge {P : Set E} {ℓ : E →ₗ[ℝ] ℝ} {r : ℝ} {p c d z : E}
    (hP : P ⊆ {x : E | r ≤ ℓ x}) (hzdP : segment ℝ z d ⊆ P) (hzs : z ∈ segment ℝ p d)
    (hz : ℓ z = r) (hp : ℓ p < r) (hc : ℓ c < r) (hd : r ≤ ℓ d) :
    P ∩ (segment ℝ p c ∪ segment ℝ p d) = segment ℝ z d := by
  have hempty : P ∩ segment ℝ p c = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxP, hxc⟩
    have h1 : r ≤ ℓ x := hP hxP
    have h2 : ℓ x < r := segment_subset_halfSpace_lt hp hc hxc
    linarith
  rw [Set.inter_union_distrib_left, hempty, Set.empty_union]
  apply Subset.antisymm
  · rintro x ⟨hxP, hxd⟩
    have hx : x ∈ segment ℝ p d ∩ {y : E | r ≤ ℓ y} := ⟨hxd, hP hxP⟩
    rwa [segment_inter_ge_eq_segment hzs hz hp hd] at hx
  · exact fun x hx => ⟨hzdP hx, segment_right_subset_of_mem_segment hzs hx⟩

theorem inter_arc_of_subset_hyperplane {P : Set E} {ℓ : E →ₗ[ℝ] ℝ} {r : ℝ} {p c d z : E}
    (hP : P ⊆ {x : E | ℓ x = r}) (hzP : z ∈ P) (hzs : z ∈ segment ℝ p d) (hz : ℓ z = r)
    (hp : ℓ p < r) (hc : ℓ c < r) (hd : r < ℓ d) :
    P ∩ (segment ℝ p c ∪ segment ℝ p d) = {z} := by
  have hempty : P ∩ segment ℝ p c = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxP, hxc⟩
    have h1 : ℓ x = r := hP hxP
    have h2 : ℓ x < r := segment_subset_halfSpace_lt hp hc hxc
    linarith
  rw [Set.inter_union_distrib_left, hempty, Set.empty_union]
  apply Subset.antisymm
  · rintro x ⟨hxP, hxd⟩
    have hx : x ∈ segment ℝ p d ∩ {y : E | ℓ y = r} := ⟨hxd, hP hxP⟩
    rwa [segment_inter_eq_singleton hzs hz hp hd] at hx
  · rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨hzP, hzs⟩

end DifferentialGeometry.Topology.PiecewiseLinear
