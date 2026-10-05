import DifferentialGeometry.Geometry.Collapse.SublevelCore.CompactTransfer

/-!
# LC57 (3) / LC61 for a compact finite model (LFR49, compact branch)

Frozen blueprint master207A, LFR49 (A:29096), compact branch: "If the limit is compact, eventual
exhaustion includes the WHOLE model. Its smooth embedding is open and closed in connected `M_i`,
hence a diffeomorphism. Choose the fixed scale large enough for LC43's diameter bound".

`exists_scale_eventually_compact_model_type_finite` (statement T2 of lane LFR49): for smooth
comparison maps `j i : N ⇀ M i` from a compact model that eventually exhaust it, with pointed
distortion tending to zero, there is `R₀ > 0` such that for every `R ≥ R₀` one tail has every open
ball `B(j_i n, ρ R)`, `ρ ∈ [1/5, 2]`, diffeomorphic to the model. Only the distance of the model is
used (no metric tensor, so the finite-order metric of LFR14 is enough): the distortion `< 1` on
`B(n, D + 1)` (`D` a diameter bound) gives `d(j_i n, ·) < D + 1 < ρ R` on all of `M i`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]

/-- **LC57 (3) / LC61 for a compact finite model.** Smooth comparison maps from a compact model
that eventually exhaust it, with pointed distortion `→ 0`: there is `R₀ > 0` such that for every
`R ≥ R₀` one tail has every open ball `B(j_i n, ρ R)`, `ρ ∈ [1/5, 2]`, diffeomorphic to the model
(the ball is the whole source, the map a global diffeomorphism). -/
theorem exists_scale_eventually_compact_model_type_finite
    {N : Type*} [MetricSpace N] [ChartedSpace H N] [CompactSpace N]
    [∀ i, ConnectedSpace (M i)] (n : N) (j : ∀ i, PartialDiffeomorph I I N (M i) ∞)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball n R, ∀ y ∈ ball n R,
      |dist (j i x) (j i y) - dist x y| < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ᶠ i in atTop, ∀ ρ ∈ Icc (1 / 5 : ℝ) 2,
      ∃ Ψ : PartialDiffeomorph I I (M i) N ∞,
        Ψ.source = Metric.ball (j i n) (ρ * R) ∧ Ψ.target = univ := by
  have : Nonempty N := ⟨n⟩
  obtain ⟨D₀, hD₀⟩ := (isCompact_univ (X := N)).isBounded.subset_closedBall n
  set D : ℝ := max D₀ 0 with hDdef
  have hD0 : 0 ≤ D := le_max_right _ _
  have hball : ∀ x : N, x ∈ ball n (D + 1) := fun x => by
    rw [mem_ball]
    linarith [(mem_closedBall.mp (hD₀ (mem_univ x))).trans (le_max_left D₀ 0)]
  refine ⟨5 * (D + 2), by positivity, fun R hR => ?_⟩
  filter_upwards [hexh univ isCompact_univ, hdist (D + 1) 1 one_pos] with i hsrc hdi ρ hρ
  have hsrc' : (j i).source = univ := eq_univ_of_univ_subset hsrc
  obtain ⟨d, hd⟩ := DifferentialGeometry.exists_diffeomorph_of_compactSpace (j i) hsrc'
  refine ⟨d.symm.toPartialDiffeomorph, ?_, rfl⟩
  symm
  apply eq_univ_of_forall
  intro y
  obtain ⟨x, rfl⟩ : ∃ x, d x = y := ⟨d.symm y, d.apply_symm_apply y⟩
  rw [hd x, mem_ball, dist_comm]
  have h1 := (abs_lt.mp (hdi n (hball n) x (hball x))).2
  have h2 : dist n x < D + 1 := by rw [dist_comm]; exact mem_ball.mp (hball x)
  have hρR : D + 2 ≤ ρ * R := by nlinarith [hρ.1]
  linarith

end DifferentialGeometry.Geometry.Collapse
