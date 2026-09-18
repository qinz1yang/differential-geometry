import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies

open Set Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem mem_Icc_uniform_partition {n : ℕ} {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ j ≤ n, x ∈ Icc ((j : ℝ) / ((n : ℝ) + 1)) (((j : ℝ) + 1) / ((n : ℝ) + 1)) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlow : (⌊x * ((n : ℝ) + 1)⌋₊ : ℝ) ≤ x * ((n : ℝ) + 1) := Nat.floor_le (by positivity)
  have hhigh : x * ((n : ℝ) + 1) < (⌊x * ((n : ℝ) + 1)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  rcases Nat.lt_or_ge (⌊x * ((n : ℝ) + 1)⌋₊) (n + 1) with hmn | hmn
  · refine ⟨⌊x * ((n : ℝ) + 1)⌋₊, by omega, ?_, ?_⟩
    · rw [div_le_iff₀ hpos]
      linarith
    · rw [le_div_iff₀ hpos]
      linarith
  · have hmge : ((n : ℝ) + 1) ≤ (⌊x * ((n : ℝ) + 1)⌋₊ : ℝ) := by
      have hcast : ((n + 1 : ℕ) : ℝ) ≤ (⌊x * ((n : ℝ) + 1)⌋₊ : ℝ) := Nat.cast_le.mpr hmn
      push_cast at hcast
      linarith
    refine ⟨n, le_rfl, ?_, ?_⟩
    · rw [div_le_iff₀ hpos]
      nlinarith
    · rw [le_div_iff₀ hpos]
      nlinarith

theorem exists_subordinate_chain_of_isPLBall_one {S : Set E} (hS : IsPLBall 1 S)
    {ι : Type*} {U : ι → Set E} (hU : ∀ i, IsOpen (U i)) (hcover : S ⊆ ⋃ i, U i) :
    ∃ (n : ℕ) (γ : ℝ → E), IsPLHomeomorphOn γ (Icc (0 : ℝ) 1) S ∧
      (∀ j ≤ n, ∃ i : ι,
        γ '' Icc ((j : ℝ) / ((n : ℝ) + 1)) (((j : ℝ) + 1) / ((n : ℝ) + 1)) ⊆ U i) ∧
      S = ⋃ j ∈ Finset.range (n + 1),
        γ '' Icc ((j : ℝ) / ((n : ℝ) + 1)) (((j : ℝ) + 1) / ((n : ℝ) + 1)) := by
  classical
  obtain ⟨γ, hγ⟩ := exists_isPLHomeomorphOn_Icc_of_isPLBall_one hS
  have hγcont : ContinuousOn γ (Icc (0 : ℝ) 1) := hγ.2.1.continuousOn
  have hγimage : γ '' Icc (0 : ℝ) 1 = S := hγ.image_eq
  choose O hOopen hOeq using fun i : ι => continuousOn_iff'.mp hγcont (U i) (hU i)
  have hcover' : Icc (0 : ℝ) 1 ⊆ ⋃ i, O i := by
    intro x hx
    have hγx : γ x ∈ S := hγimage ▸ mem_image_of_mem γ hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hγx)
    have hmem : x ∈ γ ⁻¹' U i ∩ Icc (0 : ℝ) 1 := ⟨hi, hx⟩
    rw [hOeq i] at hmem
    exact mem_iUnion.mpr ⟨i, hmem.1⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hOopen hcover'
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hstep : ∀ j : ℕ, ((j : ℝ) + 1) / ((n : ℝ) + 1) - (j : ℝ) / ((n : ℝ) + 1) =
      1 / ((n : ℝ) + 1) := by
    intro j
    field_simp
    ring
  have hsubIcc : ∀ j ≤ n, Icc ((j : ℝ) / ((n : ℝ) + 1)) (((j : ℝ) + 1) / ((n : ℝ) + 1)) ⊆
      Icc (0 : ℝ) 1 := by
    intro j hj y hy
    have hjn : (j : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hj
    refine ⟨le_trans (by positivity) hy.1, le_trans hy.2 ?_⟩
    rw [div_le_one hpos]
    linarith
  refine ⟨n, γ, hγ, ?_, ?_⟩
  · intro j hj
    have hstart : (j : ℝ) / ((n : ℝ) + 1) ∈
        Icc ((j : ℝ) / ((n : ℝ) + 1)) (((j : ℝ) + 1) / ((n : ℝ) + 1)) := by
      have hone : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have := hstep j
      exact ⟨le_rfl, by linarith⟩
    obtain ⟨i, hball⟩ := hleb _ (hsubIcc j hj hstart)
    refine ⟨i, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    have hyIcc : y ∈ Icc (0 : ℝ) 1 := hsubIcc j hj hy
    have hydist : dist y ((j : ℝ) / ((n : ℝ) + 1)) < δ := by
      have hd : dist y ((j : ℝ) / ((n : ℝ) + 1)) = y - (j : ℝ) / ((n : ℝ) + 1) := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hy.1])]
      have hlen := hstep j
      have hyle := hy.2
      rw [hd]
      linarith
    have hmem : y ∈ O i ∩ Icc (0 : ℝ) 1 := ⟨hball (mem_ball.mpr hydist), hyIcc⟩
    rw [← hOeq i] at hmem
    exact hmem.1
  · apply Subset.antisymm
    · intro z hz
      rw [← hγimage] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨j, hj, hyj⟩ := mem_Icc_uniform_partition (n := n) hy
      exact mem_biUnion (Finset.mem_range.mpr (by omega)) (mem_image_of_mem γ hyj)
    · intro z hz
      simp only [mem_iUnion] at hz
      obtain ⟨j, hj, y, hy, rfl⟩ := hz
      have hjle : j ≤ n := by
        have := Finset.mem_range.mp hj
        omega
      rw [← hγimage]
      exact mem_image_of_mem γ (hsubIcc j hjle hy)

end DifferentialGeometry.Topology.PiecewiseLinear
