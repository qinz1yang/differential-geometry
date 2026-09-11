import DifferentialGeometry.Geometry.Neck.PointwiseChart

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace DifferentialGeometry.Geometry.Neck
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1

theorem compact_subset_openCylinder {K : Set (S2 × ℝ)} (hK : IsCompact K) :
    ∃ L : ℝ, 0 < L ∧ K ⊆ (openCylinder L : Set (S2 × ℝ)) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn continuous_snd.continuousOn
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro q hq
  have hb : |q.2| ≤ C := by simpa only [Real.norm_eq_abs] using hC q hq
  change -(max C 0 + 1) < q.2 ∧ q.2 < max C 0 + 1
  exact ⟨by linarith [neg_abs_le q.2, le_max_left C 0],
    by linarith [le_abs_self q.2, le_max_left C 0]⟩

theorem openCylinder_nat_exhaustion :
    Monotone (fun k : ℕ => (openCylinder ((k : ℝ) + 1) : Set (S2 × ℝ))) ∧
      (⋃ k : ℕ, (openCylinder ((k : ℝ) + 1) : Set (S2 × ℝ))) = univ := by
  constructor
  · intro i j hij q hq
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    change -((j : ℝ) + 1) < q.2 ∧ q.2 < (j : ℝ) + 1
    exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
  · apply eq_univ_of_forall
    intro q
    obtain ⟨k, hk⟩ := exists_nat_gt |q.2|
    apply mem_iUnion.mpr
    refine ⟨k, ?_⟩
    change -((k : ℝ) + 1) < q.2 ∧ q.2 < (k : ℝ) + 1
    exact ⟨by linarith [neg_abs_le q.2], by linarith [le_abs_self q.2]⟩

end DifferentialGeometry.Geometry.Neck
end
