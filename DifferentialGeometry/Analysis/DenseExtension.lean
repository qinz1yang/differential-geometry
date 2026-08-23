import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.CompleteSeparated

noncomputable section

open Filter Set
open scoped NNReal Topology

namespace DifferentialGeometry.Analysis

theorem cont_of_lipBalls {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {D : Set X} (F : D → Y) (x₀ : X)
    (hball : ∀ R : ℝ, ∃ K : ℝ≥0,
      LipschitzOnWith K F {x : D | dist (x : X) x₀ ≤ R}) :
    Continuous F := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨K, hK⟩ := hball (dist (x : X) x₀ + 1)
  refine hK.continuousOn.continuousAt ?_
  have hmem : Metric.closedBall x₀ (dist (x : X) x₀ + 1) ∈ 𝓝 (x : X) :=
    Metric.closedBall_mem_nhds_of_mem
      (by simpa only [Metric.mem_ball] using lt_add_one (dist (x : X) x₀))
  exact continuous_subtype_val.continuousAt.preimage_mem_nhds hmem

theorem cont_extend_lip {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompleteSpace Y] [T0Space Y] {D : Set X} (hD : Dense D) (F : D → Y) (x₀ : X)
    (hball : ∀ R : ℝ, ∃ K : ℝ≥0,
      LipschitzOnWith K F {x : D | dist (x : X) x₀ ≤ R}) :
    Continuous (Dense.extend hD F) := by
  apply hD.isDenseInducing_val.continuous_extend_of_cauchy
  intro x
  let l : Filter D := comap ((↑) : D → X) (𝓝 x)
  have hl : Cauchy l :=
    cauchy_nhds.comap'
      (le_of_eq isUniformEmbedding_subtype_val.isUniformInducing.comap_uniformity)
      (hD.comap_val_nhds_neBot x)
  let R : ℝ := dist x x₀ + 1
  let S : Set D := {d | dist (d : X) x₀ ≤ R}
  obtain ⟨K, hK⟩ := hball R
  have hclosed : Metric.closedBall x₀ R ∈ 𝓝 x :=
    Metric.closedBall_mem_nhds_of_mem
      (by simpa only [Metric.mem_ball, R] using lt_add_one (dist x x₀))
  have hlS : l ≤ 𝓟 S := by
    rw [le_principal_iff]
    have hpre : ((↑) : D → X) ⁻¹' Metric.closedBall x₀ R ∈ l :=
      preimage_mem_comap hclosed
    simpa only [S, Metric.mem_closedBall, Set.mem_setOf_eq] using hpre
  exact hl.map_of_le hK.uniformContinuousOn hlS

theorem eq_of_lipPair {ι X Y : Type*} [SeminormedAddCommGroup X]
    [NormedAddCommGroup Y] {j : ι → X} {f : ι → Y}
    (hpair : ∀ R : ℝ, ∃ K : ℝ, ∀ v w : ι, ‖j v‖ ≤ R → ‖j w‖ ≤ R →
      ‖f v - f w‖ ≤ K * ‖j v - j w‖)
    {v w : ι} (h : j v = j w) : f v = f w := by
  obtain ⟨K, hK⟩ := hpair ‖j v‖
  have hle := hK v w le_rfl (by rw [← h])
  rw [h, sub_self, norm_zero, mul_zero] at hle
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hle)

private theorem lipBalls_of_pair {ι X Y : Type*} [SeminormedAddCommGroup X]
    [NormedAddCommGroup Y] {j : ι → X} (F : ↥(Set.range j) → Y) (f : ι → Y)
    (hval : ∀ v : ι, F ⟨j v, ⟨v, rfl⟩⟩ = f v)
    (hpair : ∀ R : ℝ, ∃ K : ℝ, ∀ v w : ι, ‖j v‖ ≤ R → ‖j w‖ ≤ R →
      ‖f v - f w‖ ≤ K * ‖j v - j w‖) :
    ∀ R : ℝ, ∃ K : ℝ≥0,
      LipschitzOnWith K F {x : ↥(Set.range j) | dist (x : X) 0 ≤ R} := by
  intro R
  obtain ⟨K, hK⟩ := hpair R
  refine ⟨⟨max K 0, le_max_right _ _⟩, ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  obtain ⟨v, hv⟩ := x.2
  obtain ⟨w, hw⟩ := y.2
  have hvR : ‖j v‖ ≤ R := by
    have hx' : dist (x : X) 0 ≤ R := hx
    rwa [dist_zero_right, ← hv] at hx'
  have hwR : ‖j w‖ ≤ R := by
    have hy' : dist (y : X) 0 ≤ R := hy
    rwa [dist_zero_right, ← hw] at hy'
  have hxv : x = ⟨j v, ⟨v, rfl⟩⟩ := Subtype.ext hv.symm
  have hyw : y = ⟨j w, ⟨w, rfl⟩⟩ := Subtype.ext hw.symm
  rw [hxv, hyw, hval, hval]
  simp only [Subtype.dist_eq, dist_eq_norm, NNReal.coe_mk]
  exact (hK v w hvR hwR).trans
    (mul_le_mul_of_nonneg_right (le_max_left K 0) (norm_nonneg _))

theorem cont_extend_pair {ι X Y : Type*} [SeminormedAddCommGroup X]
    [NormedAddCommGroup Y] [CompleteSpace Y] {j : ι → X} (hj : DenseRange j)
    (F : ↥(Set.range j) → Y) (f : ι → Y)
    (hval : ∀ v : ι, F ⟨j v, ⟨v, rfl⟩⟩ = f v)
    (hpair : ∀ R : ℝ, ∃ K : ℝ, ∀ v w : ι, ‖j v‖ ≤ R → ‖j w‖ ≤ R →
      ‖f v - f w‖ ≤ K * ‖j v - j w‖) :
    Continuous (Dense.extend hj F) :=
  cont_extend_lip hj F 0 (lipBalls_of_pair F f hval hpair)

theorem extend_pair_apply {ι X Y : Type*} [SeminormedAddCommGroup X]
    [NormedAddCommGroup Y] {j : ι → X} (hj : DenseRange j)
    (F : ↥(Set.range j) → Y) (f : ι → Y)
    (hval : ∀ v : ι, F ⟨j v, ⟨v, rfl⟩⟩ = f v)
    (hpair : ∀ R : ℝ, ∃ K : ℝ, ∀ v w : ι, ‖j v‖ ≤ R → ‖j w‖ ≤ R →
      ‖f v - f w‖ ≤ K * ‖j v - j w‖)
    (v : ι) : Dense.extend hj F (j v) = f v :=
  (Dense.extend_eq hj (cont_of_lipBalls F 0 (lipBalls_of_pair F f hval hpair))
    ⟨j v, ⟨v, rfl⟩⟩).trans (hval v)

theorem exists_extend_pair {ι X Y : Type*} [SeminormedAddCommGroup X]
    [NormedAddCommGroup Y] [CompleteSpace Y] {j : ι → X} (hj : DenseRange j)
    (f : ι → Y)
    (hpair : ∀ R : ℝ, ∃ K : ℝ, ∀ v w : ι, ‖j v‖ ≤ R → ‖j w‖ ≤ R →
      ‖f v - f w‖ ≤ K * ‖j v - j w‖) :
    ∃ F : X → Y, Continuous F ∧ ∀ v : ι, F (j v) = f v := by
  classical
  have hval : ∀ v : ι, (f ∘ Set.rangeSplitting j) ⟨j v, ⟨v, rfl⟩⟩ = f v := by
    intro v
    exact eq_of_lipPair hpair (Set.apply_rangeSplitting j ⟨j v, ⟨v, rfl⟩⟩)
  exact ⟨Dense.extend hj (f ∘ Set.rangeSplitting j),
    cont_extend_pair hj _ f hval hpair,
    fun v => extend_pair_apply hj _ f hval hpair v⟩

theorem norm_extend_le {ι X Y : Type*} [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y] {j : ι → X} (hj : DenseRange j) {f : ι → Y}
    {F : X → Y} {Φ : ℝ → ℝ} (hF : Continuous F) (hΦ : Continuous Φ)
    (hval : ∀ v : ι, F (j v) = f v) (hbd : ∀ v : ι, ‖f v‖ ≤ Φ ‖j v‖) (x : X) :
    ‖F x‖ ≤ Φ ‖x‖ := by
  refine hj.induction_on x (isClosed_le hF.norm (hΦ.comp continuous_norm)) ?_
  intro v
  rw [hval v]
  exact hbd v

theorem exists_extend_le {ι X Y : Type*} [SeminormedAddCommGroup X]
    [NormedAddCommGroup Y] [CompleteSpace Y] {j : ι → X} (hj : DenseRange j)
    (f : ι → Y) {Φ : ℝ → ℝ} (hΦ : Continuous Φ)
    (hpair : ∀ R : ℝ, ∃ K : ℝ, ∀ v w : ι, ‖j v‖ ≤ R → ‖j w‖ ≤ R →
      ‖f v - f w‖ ≤ K * ‖j v - j w‖)
    (hbd : ∀ v : ι, ‖f v‖ ≤ Φ ‖j v‖) :
    ∃ F : X → Y, Continuous F ∧ (∀ v : ι, F (j v) = f v) ∧
      ∀ x : X, ‖F x‖ ≤ Φ ‖x‖ := by
  obtain ⟨F, hFc, hFv⟩ := exists_extend_pair hj f hpair
  exact ⟨F, hFc, hFv, fun x => norm_extend_le hj hFc hΦ hFv hbd x⟩

end DifferentialGeometry.Analysis

end
