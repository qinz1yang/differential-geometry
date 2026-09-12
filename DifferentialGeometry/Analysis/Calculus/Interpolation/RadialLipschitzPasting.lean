import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Lipschitz







noncomputable section

open Set Metric
open scoped Convex NNReal ENNReal

namespace DifferentialGeometry.Analysis

variable {V Q : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [PseudoEMetricSpace Q]


theorem exists_sphere_point_on_segment {x y : V} {r : ℝ}
    (hx : ‖x‖ ≤ r) (hy : r ≤ ‖y‖) :
    ∃ z ∈ segment ℝ x y, ‖z‖ = r := by
  let f : ℝ → ℝ := fun t => ‖AffineMap.lineMap x y t‖
  have hf : Continuous f := AffineMap.lineMap_continuous.norm
  have hr : r ∈ Icc (f 0) (f 1) := by simpa [f] using And.intro hx hy
  obtain ⟨t, ht, htr⟩ := intermediate_value_Icc (zero_le_one : (0 : ℝ) ≤ 1) hf.continuousOn hr
  exact ⟨AffineMap.lineMap x y t, lineMap_mem_segment ℝ x y ht, htr⟩



theorem edist_add_edist_of_mem_segment {x y z : V} (h : z ∈ segment ℝ x y) :
    edist x z + edist z y = edist x y := by
  rw [edist_dist, edist_dist, edist_dist, ← ENNReal.ofReal_add (dist_nonneg) (dist_nonneg),
    dist_add_dist_of_mem_segment h]


theorem lipschitzOnWith_of_radial_pieces {f : V → Q} {S : Set V} {r : ℝ} {K : ℝ≥0}
    (hS : Convex ℝ S)
    (hin : LipschitzOnWith K f (S ∩ {z | ‖z‖ ≤ r}))
    (hout : LipschitzOnWith K f (S ∩ {z | r ≤ ‖z‖})) : LipschitzOnWith K f S := by
  have hcross (x : V) (hxS : x ∈ S) (hx : ‖x‖ ≤ r)
      (y : V) (hyS : y ∈ S) (hy : r ≤ ‖y‖) :
      edist (f x) (f y) ≤ (K : ℝ≥0∞) * edist x y := by
    obtain ⟨z, hz, hzr⟩ := exists_sphere_point_on_segment hx hy
    have hzS := hS.segment_subset hxS hyS hz
    calc
      _ ≤ edist (f x) (f z) + edist (f z) (f y) := edist_triangle _ _ _
      _ ≤ (K : ℝ≥0∞) * edist x z + (K : ℝ≥0∞) * edist z y := add_le_add
        (hin ⟨hxS, hx⟩ ⟨hzS, hzr.le⟩)
        (hout ⟨hzS, hzr.ge⟩ ⟨hyS, hy⟩)
      _ = _ := by rw [← mul_add, edist_add_edist_of_mem_segment hz]
  intro x hx y hy
  by_cases hxr : ‖x‖ ≤ r
  · by_cases hyr : ‖y‖ ≤ r
    · exact hin ⟨hx, hxr⟩ ⟨hy, hyr⟩
    · exact hcross x hx hxr y hy (le_of_not_ge hyr)
  · by_cases hyr : ‖y‖ ≤ r
    · simpa only [edist_comm] using hcross y hy hyr x hx (le_of_not_ge hxr)
    · exact hout ⟨hx, le_of_not_ge hxr⟩ ⟨hy, le_of_not_ge hyr⟩

end DifferentialGeometry.Analysis
