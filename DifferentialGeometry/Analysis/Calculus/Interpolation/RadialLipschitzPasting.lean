import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Lipschitz







noncomputable section

open Set Metric
open scoped Convex NNReal

namespace DifferentialGeometry.Analysis

variable {V Q : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [PseudoMetricSpace Q]


theorem exists_sphere_point_on_segment {x y : V} {r : ℝ}
    (hx : ‖x‖ ≤ r) (hy : r ≤ ‖y‖) :
    ∃ z ∈ segment ℝ x y, ‖z‖ = r := by
  let f : ℝ → ℝ := fun t => ‖AffineMap.lineMap x y t‖
  have hf : Continuous f := AffineMap.lineMap_continuous.norm
  have hr : r ∈ Icc (f 0) (f 1) := by simpa [f] using And.intro hx hy
  obtain ⟨t, ht, htr⟩ := intermediate_value_Icc (zero_le_one : (0 : ℝ) ≤ 1) hf.continuousOn hr
  exact ⟨AffineMap.lineMap x y t, lineMap_mem_segment ℝ x y ht, htr⟩



theorem lipschitzOnWith_of_radial_pieces {f : V → Q} {S : Set V} {r : ℝ} {K : ℝ≥0}
    (hS : Convex ℝ S)
    (hin : LipschitzOnWith K f (S ∩ {z | ‖z‖ ≤ r}))
    (hout : LipschitzOnWith K f (S ∩ {z | r ≤ ‖z‖})) : LipschitzOnWith K f S := by
  have hcross (x : V) (hxS : x ∈ S) (hx : ‖x‖ ≤ r)
      (y : V) (hyS : y ∈ S) (hy : r ≤ ‖y‖) :
      dist (f x) (f y) ≤ (K : ℝ) * dist x y := by
    obtain ⟨z, hz, hzr⟩ := exists_sphere_point_on_segment hx hy
    have hzS := hS.segment_subset hxS hyS hz
    calc
      _ ≤ dist (f x) (f z) + dist (f z) (f y) := dist_triangle _ _ _
      _ ≤ (K : ℝ) * dist x z + (K : ℝ) * dist z y := add_le_add
        (hin.dist_le_mul x ⟨hxS, hx⟩ z ⟨hzS, hzr.le⟩)
        (hout.dist_le_mul z ⟨hzS, hzr.ge⟩ y ⟨hyS, hy⟩)
      _ = _ := by rw [← mul_add, dist_add_dist_of_mem_segment hz]
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  by_cases hxr : ‖x‖ ≤ r
  · by_cases hyr : ‖y‖ ≤ r
    · exact hin.dist_le_mul x ⟨hx, hxr⟩ y ⟨hy, hyr⟩
    · exact hcross x hx hxr y hy (le_of_not_ge hyr)
  · by_cases hyr : ‖y‖ ≤ r
    · simpa only [dist_comm] using hcross y hy hyr x hx (le_of_not_ge hxr)
    · exact hout.dist_le_mul x ⟨hx, le_of_not_ge hxr⟩ y ⟨hy, le_of_not_ge hyr⟩

end DifferentialGeometry.Analysis
