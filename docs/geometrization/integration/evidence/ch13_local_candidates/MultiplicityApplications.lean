import DifferentialGeometry.Geometry.Metric.LipschitzScaleMultiplicity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Count

set_option autoImplicit false
open Set Metric MeasureTheory GC.MetricGeometry
open scoped ENNReal

example : (({(0 : ℝ), 2} : Finset ℝ).card : ℝ) ≤ 26 := by
  refine card_le_of_lipschitz_scale_ball_overlap volume {(0 : ℝ), 2}
    (ρ := fun _ => 1) (Λ := 0) (LipschitzWith.const 1) (by intro _ _; norm_num)
    (a := 1 / 4) (C := 2) (b := 26) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_ 1 ?_
  · intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (hij rfl).elim
    · apply ball_disjoint_ball; norm_num [Real.dist_eq]
    · apply ball_disjoint_ball; norm_num [Real.dist_eq]
    · exact (hij rfl).elim
  · intro i _; norm_num [Measure.real]
  · intro i _; norm_num
  · intro i _; norm_num [Measure.real]
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> norm_num [mem_ball, Real.dist_eq]

private abbrev Two := {x : ℝ // x ∈ ({0, 2} : Set ℝ)}
private instance : Finite Two := ((Set.finite_singleton (2 : ℝ)).insert 0).to_subtype
private instance : MeasurableSpace Two := borel Two
private instance : BorelSpace Two := ⟨rfl⟩

private theorem small_ball (i : Two) : ball i (1 / 4) = {i} := by
  ext y
  have hi : (i : ℝ) = 0 ∨ (i : ℝ) = 2 := by simpa only [mem_insert_iff, mem_singleton_iff] using i.property
  have hy : (y : ℝ) = 0 ∨ (y : ℝ) = 2 := by simpa only [mem_insert_iff, mem_singleton_iff] using y.property
  rcases hi with hi | hi <;> rcases hy with hy | hy <;>
    norm_num [mem_ball, mem_singleton_iff, Subtype.ext_iff, Subtype.dist_eq, Real.dist_eq, hi, hy]

private theorem large_ball (i : Two) : ball i (13 / 2) = univ := by
  ext y
  have hi : (i : ℝ) = 0 ∨ (i : ℝ) = 2 := by simpa only [mem_insert_iff, mem_singleton_iff] using i.property
  have hy : (y : ℝ) = 0 ∨ (y : ℝ) = 2 := by simpa only [mem_insert_iff, mem_singleton_iff] using y.property
  rcases hi with hi | hi <;> rcases hy with hy | hy <;>
    norm_num [mem_ball, Subtype.dist_eq, Real.dist_eq, hi, hy]

private theorem card_two : Nat.card Two = 2 := by
  rw [Nat.card_coe_set_eq]
  simp

example : ∃ I : Set Two, I.Finite ∧
    (∀ p : Two, ∃ i ∈ I, ball p (3 / 4) ⊆ ball i (3 / 2)) ∧
    ∀ x : Two, ((I ∩ {i | x ∈ ball i 2}).ncard : ℝ) ≤ 2 := by
  have hsingle (i : Two) : ball i ((3 / 4 : ℝ) * 1 / 3) = {i} := by norm_num; exact small_ball i
  have hwhole (i : Two) : ball i ((3 * 2 + 2 * ((3 / 4) / 3 : ℝ)) * 1) = univ := by
    norm_num; exact large_ball i
  obtain ⟨I, _, hfin, _, hc, hm⟩ := exists_finite_scale_cover_with_multiplicity
    (μ := Measure.count) univ (ρ := fun _ : Two => 1) (Λ := 0) (Δ := 3 / 4) (C := 2) (b := 2)
    (LipschitzWith.const 1) (by intro _; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by intro i _; rw [hsingle]; simp [Measure.real])
    (by intro i _; rw [hwhole]; simp [Measure.count_univ])
    (by intro i _; rw [hwhole, hsingle]; norm_num [Measure.real, Measure.count_univ, card_two])
  refine ⟨I, hfin, ?_, ?_⟩
  · intro p
    simpa only [mul_one, show 2 * (3 / 4 : ℝ) = 3 / 2 by ring] using hc p (mem_univ p)
  · simpa using hm
