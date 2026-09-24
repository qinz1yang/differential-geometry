import Mathlib.Topology.MetricSpace.Sequences

section

open Filter Metric Set
open scoped Topology

theorem DenseRange.tendsto_of_tendsto_dist
    {A I X : Type*} [PseudoMetricSpace X] {a : I → X} (ha : DenseRange a)
    {l : Filter A} {u : A → X} {x : X}
    (hu : ∀ i, Tendsto (fun n => dist (u n) (a i)) l (𝓝 (dist x (a i)))) :
    Tendsto u l (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨i, hi⟩ := ha.exists_dist_lt x (half_pos hε)
  have hnear : ∀ᶠ n in l, dist (u n) (a i) < ε - dist x (a i) :=
    (hu i).eventually (Iio_mem_nhds (by linarith : dist x (a i) < ε - dist x (a i)))
  filter_upwards [hnear] with n hn
  exact (dist_triangle_right (u n) x (a i)).trans_lt (by linarith)

theorem DenseRange.exists_tendsto_of_tendsto_dist
    {I X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    {a : I → X} (ha : DenseRange a) {u : ℕ → X}
    (hu : ∀ i, ∃ r : ℝ, Tendsto (fun n => dist (u n) (a i)) atTop (𝓝 r)) :
    ∃ x : X, Tendsto u atTop (𝓝 x) := by
  obtain ⟨i, _⟩ := ha.exists_dist_lt (u 0) zero_lt_one
  obtain ⟨r, hr⟩ := hu i
  have hbounded : ∀ᶠ n in atTop, u n ∈ closedBall (a i) (r + 1) := by
    have hlt : ∀ᶠ n in atTop, dist (u n) (a i) < r + 1 :=
      hr.eventually (Iio_mem_nhds (lt_add_one r))
    filter_upwards [hlt] with n hn
    exact hn.le
  obtain ⟨x, _, φ, hφ, hx⟩ :=
    (isCompact_closedBall (a i) (r + 1)).tendsto_subseq' hbounded.frequently
  refine ⟨x, ha.tendsto_of_tendsto_dist ?_⟩
  intro j
  obtain ⟨s, hs⟩ := hu j
  have hsub : Tendsto (fun n => dist (u (φ n)) (a j)) atTop (𝓝 (dist x (a j))) :=
    hx.dist tendsto_const_nhds
  have heq : s = dist x (a j) := tendsto_nhds_unique (hs.comp hφ.tendsto_atTop) hsub
  rwa [heq] at hs

end
