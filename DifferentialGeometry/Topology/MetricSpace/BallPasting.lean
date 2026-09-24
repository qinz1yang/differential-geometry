import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Lipschitz

section

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped NNReal ENNReal

namespace DifferentialGeometry.Analysis

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoEMetricSpace X]

private theorem exists_sphere_point_between {p x y : E} {r : ℝ}
    (hx : x ∈ closedBall p r) (hy : r ≤ dist y p) :
    ∃ z : E, dist z p = r ∧ dist x z ≤ dist x y ∧ dist z y ≤ dist x y := by
  let c : ℝ → E := AffineMap.lineMap x y
  have hc : Continuous (fun t => dist (c t) p) :=
    (AffineMap.lineMap_continuous (p := x) (q := y)).dist continuous_const
  have hends : r ∈ Icc (dist (c 0) p) (dist (c 1) p) := by
    simpa only [c, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
      mem_closedBall, mem_Icc] using
      And.intro hx hy
  obtain ⟨t, ht, htr⟩ := intermediate_value_Icc zero_le_one hc.continuousOn hends
  have hzseg : c t ∈ segment ℝ x y := lineMap_mem_segment ℝ x y ht
  have hd := dist_add_dist_of_mem_segment hzseg
  exact ⟨c t, htr, by linarith [dist_nonneg (x := c t) (y := y)],
    by linarith [dist_nonneg (x := x) (y := c t)]⟩

theorem lipschitzWith_piecewise_closedBall_of_eqOn_sphere
    {p : E} {r : ℝ} {f g : E → X} {K L : ℝ≥0}
    (hf : LipschitzOnWith K f (closedBall p r))
    (hg : LipschitzOnWith L g {x | r ≤ dist x p})
    (heq : EqOn f g (sphere p r)) :
    letI : DecidablePred (· ∈ closedBall p r) := Classical.decPred _
    LipschitzWith (K + L) ((closedBall p r).piecewise f g) := by
  classical
  have hcross (x y : E) (hx : x ∈ closedBall p r) (hy : y ∉ closedBall p r) :
      edist (f x) (g y) ≤ ((K + L : ℝ≥0) : ℝ≥0∞) * edist x y := by
    have hyr : r ≤ dist y p := (not_le.mp (by simpa only [mem_closedBall, mem_Icc] using hy)).le
    obtain ⟨z, hz, hzx, hzy⟩ := exists_sphere_point_between hx hyr
    have hzball : z ∈ closedBall p r := mem_closedBall.mpr hz.le
    have hzsphere : z ∈ sphere p r := mem_sphere.mpr hz
    calc
      edist (f x) (g y) ≤ edist (f x) (f z) + edist (f z) (g y) := edist_triangle _ _ _
      _ = edist (f x) (f z) + edist (g z) (g y) := by rw [heq hzsphere]
      _ ≤ (K : ℝ≥0∞) * edist x z + (L : ℝ≥0∞) * edist z y :=
        add_le_add (hf hx hzball) (hg hz.ge hyr)
      _ ≤ (K : ℝ≥0∞) * edist x y + (L : ℝ≥0∞) * edist x y := by
        apply add_le_add <;> apply mul_le_mul_right
        · simpa only [edist_dist] using ENNReal.ofReal_le_ofReal hzx
        · simpa only [edist_dist] using ENNReal.ofReal_le_ofReal hzy
      _ = _ := by rw [ENNReal.coe_add, add_mul]
  intro x y
  by_cases hx : x ∈ closedBall p r
  · by_cases hy : y ∈ closedBall p r
    · rw [piecewise_eq_of_mem _ _ _ hx, piecewise_eq_of_mem _ _ _ hy]
      exact (hf hx hy).trans
        (mul_le_mul_left (by exact_mod_cast le_add_of_nonneg_right L.coe_nonneg) _)
    · rw [piecewise_eq_of_mem _ _ _ hx, piecewise_eq_of_notMem _ _ _ hy]
      exact hcross x y hx hy
  · by_cases hy : y ∈ closedBall p r
    · rw [piecewise_eq_of_notMem _ _ _ hx, piecewise_eq_of_mem _ _ _ hy, edist_comm, edist_comm x y]
      exact hcross y x hy hx
    · rw [piecewise_eq_of_notMem _ _ _ hx, piecewise_eq_of_notMem _ _ _ hy]
      have hxr : r ≤ dist x p := (not_le.mp (by simpa only [mem_closedBall, mem_Icc] using hx)).le
      have hyr : r ≤ dist y p := (not_le.mp (by simpa only [mem_closedBall, mem_Icc] using hy)).le
      exact (hg hxr hyr).trans
        (mul_le_mul_left (by exact_mod_cast le_add_of_nonneg_left K.coe_nonneg) _)

end DifferentialGeometry.Analysis

end

end

section

noncomputable section

open Set Metric
open scoped NNReal ENNReal

namespace DifferentialGeometry.Analysis

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoEMetricSpace X]

theorem lipschitzOnWith_piecewise_closedBall_of_eqOn_sphere
    {S : Set E} (hS : Convex ℝ S) {p : E} {r : ℝ} {f g : E → X} {K L : ℝ≥0}
    (hf : LipschitzOnWith K f (S ∩ closedBall p r))
    (hg : LipschitzOnWith L g (S ∩ {x | r ≤ dist x p}))
    (heq : EqOn f g (S ∩ sphere p r)) :
    letI : DecidablePred (· ∈ closedBall p r) := Classical.decPred _
    LipschitzOnWith (K + L) ((closedBall p r).piecewise f g) S := by
  classical
  have hcross (x y : E) (hxS : x ∈ S) (hyS : y ∈ S)
      (hx : x ∈ closedBall p r) (hy : y ∉ closedBall p r) :
      edist (f x) (g y) ≤ ((K + L : ℝ≥0) : ℝ≥0∞) * edist x y := by
    have hyr : r ≤ dist y p := (not_le.mp hy).le
    let c : ℝ → E := AffineMap.lineMap x y
    have hc : Continuous (fun t => dist (c t) p) :=
      (AffineMap.lineMap_continuous (p := x) (q := y)).dist continuous_const
    have hends : r ∈ Icc (dist (c 0) p) (dist (c 1) p) := by
      simpa only [c, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
        mem_closedBall, mem_Icc] using And.intro hx hyr
    obtain ⟨t, ht, htr⟩ := intermediate_value_Icc zero_le_one hc.continuousOn hends
    have hzseg : c t ∈ segment ℝ x y := lineMap_mem_segment ℝ x y ht
    have hzS : c t ∈ S := hS.segment_subset hxS hyS hzseg
    have hd := dist_add_dist_of_mem_segment hzseg
    have hzx : dist x (c t) ≤ dist x y := by linarith [dist_nonneg (x := c t) (y := y)]
    have hzy : dist (c t) y ≤ dist x y := by linarith [dist_nonneg (x := x) (y := c t)]
    calc
      edist (f x) (g y) ≤ edist (f x) (f (c t)) + edist (f (c t)) (g y) :=
        edist_triangle _ _ _
      _ = edist (f x) (f (c t)) + edist (g (c t)) (g y) := by rw [heq ⟨hzS, htr⟩]
      _ ≤ (K : ℝ≥0∞) * edist x (c t) + (L : ℝ≥0∞) * edist (c t) y :=
        add_le_add (hf ⟨hxS, hx⟩ ⟨hzS, htr.le⟩) (hg ⟨hzS, htr.ge⟩ ⟨hyS, hyr⟩)
      _ ≤ (K : ℝ≥0∞) * edist x y + (L : ℝ≥0∞) * edist x y := by
        apply add_le_add <;> apply mul_le_mul' le_rfl
        · simpa only [edist_dist] using ENNReal.ofReal_le_ofReal hzx
        · simpa only [edist_dist] using ENNReal.ofReal_le_ofReal hzy
      _ = _ := by rw [ENNReal.coe_add, add_mul]
  intro x hxS y hyS
  by_cases hx : x ∈ closedBall p r
  · by_cases hy : y ∈ closedBall p r
    · rw [piecewise_eq_of_mem _ _ _ hx, piecewise_eq_of_mem _ _ _ hy]
      exact (hf ⟨hxS, hx⟩ ⟨hyS, hy⟩).trans
        (mul_le_mul' (by exact_mod_cast le_add_of_nonneg_right L.coe_nonneg) le_rfl)
    · rw [piecewise_eq_of_mem _ _ _ hx, piecewise_eq_of_notMem _ _ _ hy]
      exact hcross x y hxS hyS hx hy
  · by_cases hy : y ∈ closedBall p r
    · rw [piecewise_eq_of_notMem _ _ _ hx, piecewise_eq_of_mem _ _ _ hy,
        edist_comm, edist_comm x y]
      exact hcross y x hyS hxS hy hx
    · rw [piecewise_eq_of_notMem _ _ _ hx, piecewise_eq_of_notMem _ _ _ hy]
      have hxr : r ≤ dist x p := (not_le.mp hx).le
      have hyr : r ≤ dist y p := (not_le.mp hy).le
      exact (hg ⟨hxS, hxr⟩ ⟨hyS, hyr⟩).trans
        (mul_le_mul' (by exact_mod_cast le_add_of_nonneg_left K.coe_nonneg) le_rfl)

end DifferentialGeometry.Analysis

end

end
