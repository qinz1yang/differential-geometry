import DifferentialGeometry.Topology.MetricSpace.LipschitzBallSelection

set_option autoImplicit false
open Set Metric

example :
    let X := Icc (0 : ℝ) 1
    let E : Set X := {x | 0 < x.val ∧ x.val < 1}
    ∃ I : Set X, I ⊆ E ∧ I.Finite ∧ I.Nonempty ∧
      I.PairwiseDisjoint (fun i => ball i (1 / 3)) ∧ E ⊆ ⋃ i ∈ I, ball i 2 := by
  let X := Icc (0 : ℝ) 1
  let E : Set X := {x | 0 < x.val ∧ x.val < 1}
  obtain ⟨I, hIE, hfin, hdisj, hcover⟩ := exists_finite_disjoint_lipschitz_scale_selection
    E (ρ := fun _ => (1 : ℝ)) (Λ := 0) (Δ := 1) (LipschitzWith.const 1)
    (fun _ => by norm_num) (by norm_num) (by norm_num)
  have hne : I.Nonempty := by
    let p : X := ⟨1 / 2, by norm_num [X]⟩
    obtain ⟨i, hi, _⟩ := hcover p (by change 0 < (1 : ℝ) / 2 ∧ (1 : ℝ) / 2 < 1; norm_num)
    exact ⟨i, hi⟩
  refine ⟨I, hIE, hfin, hne, ?_, ?_⟩
  · simpa only [mul_one] using hdisj
  · intro p hp
    obtain ⟨i, hi, hd, _⟩ := hcover p hp
    refine mem_iUnion₂.mpr ⟨i, hi, ?_⟩
    change dist p i < 2
    linarith only [hd]

example :
    ∃ I : Set (Icc (0 : ℝ) 1), I = ∅ ∧ I.Finite ∧
      I.PairwiseDisjoint (fun i => ball i (1 / 3)) := by
  obtain ⟨I, hI, hfin, hdisj, _⟩ := exists_finite_disjoint_lipschitz_scale_selection
    (∅ : Set (Icc (0 : ℝ) 1)) (ρ := fun _ => (1 : ℝ)) (Λ := 0) (Δ := 1)
    (LipschitzWith.const 1) (fun _ => by norm_num) (by norm_num) (by norm_num)
  exact ⟨I, subset_empty_iff.mp hI, hfin, by simpa only [mul_one] using hdisj⟩
