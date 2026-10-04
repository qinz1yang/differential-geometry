import DifferentialGeometry.Topology.MetricSpace.LipschitzBallSelection

/-!
# LFR44: a finite strong-edge family covering the nonslim stratum and the weak points

Blueprint 207A, LFR44 (`thm:collapse-strong-edge-density-cover`, A:28614–28752), finite-selection
paragraph (A:28700–28720). From the two density items (every point of `N` is within `Δρ(q)` of some
`q ∈ E`, every point of `W` within `ρ(q)`), a compact space with a positive `Λ`-Lipschitz scale,
`ΛΔ ≤ 1/100`, has a finite family `q_i ∈ E` with pairwise disjoint `B(q_i, Δρ(q_i)/3)` whose balls
`B(q_i, 2Δρ(q_i))` cover `N ∪ W` (the blueprint states radius `3Δρ(q_i)` and remarks that `2` holds)
and whose balls `B(q_i, Δρ(q_i))` cover `E`. The selection is LC63's finite Vitali selection
(`Metric.exists_finite_disjoint_lipschitz_scale_selection`), a valid alternative to the source's
maximal-cardinality choice. An empty `E` gives the empty family.
-/

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

variable {X : Type*} [MetricSpace X]

/-- **LFR44, finite selection.** -/
theorem exists_finite_strong_edge_selection [CompactSpace X] {E N W : Set X} {ρ : X → ℝ}
    {Λ : NNReal} {Δ : ℝ} (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) (hΔ : 1 ≤ Δ)
    (hsmall : (Λ : ℝ) * Δ ≤ 1 / 100)
    (hN : ∀ p ∈ N, ∃ q ∈ E, dist p q < Δ * ρ q) (hW : ∀ p ∈ W, ∃ q ∈ E, dist p q < ρ q) :
    ∃ I : Set X, I ⊆ E ∧ I.Finite ∧ I.PairwiseDisjoint (fun i => ball i (Δ * ρ i / 3)) ∧
      (∀ p ∈ N ∪ W, ∃ i ∈ I, dist p i < 2 * Δ * ρ i) ∧
      ∀ q ∈ E, ∃ i ∈ I, dist q i < Δ * ρ i := by
  have hΔpos : 0 < Δ := by linarith
  obtain ⟨I, hIE, hfin, hdisj, hcov⟩ :=
    exists_finite_disjoint_lipschitz_scale_selection E hρ hρpos hΔpos hsmall
  refine ⟨I, hIE, hfin, hdisj, ?_, ?_⟩
  · have hnear (p : X) (q : X) (hq : q ∈ E) (hpq : dist p q < Δ * ρ q) :
        ∃ i ∈ I, dist p i < 2 * Δ * ρ i := by
      obtain ⟨i, hi, _, _, hball⟩ := hcov q hq
      exact ⟨i, hi, hball hpq⟩
    rintro p (hp | hp)
    · obtain ⟨q, hq, hpq⟩ := hN p hp
      exact hnear p q hq hpq
    · obtain ⟨q, hq, hpq⟩ := hW p hp
      exact hnear p q hq (hpq.trans_le (le_mul_of_one_le_left (hρpos q).le hΔ))
  · intro q hq
    obtain ⟨i, hi, hd, _, _⟩ := hcov q hq
    refine ⟨i, hi, hd.trans_le ?_⟩
    have := mul_pos hΔpos (hρpos i)
    nlinarith

end GC.MetricGeometry
