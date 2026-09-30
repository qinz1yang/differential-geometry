import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottConvergence

set_option autoImplicit false

namespace GC.MetricGeometry

open Set Filter Metric
open scoped Topology

universe u v w
variable {X : ℕ → Type u} {Y : ℕ → Type v} {Z : Type w}
variable [∀ i, MetricSpace (X i)] [∀ i, MetricSpace (Y i)] [MetricSpace Z]
variable {p : ∀ i, X i} {q : ∀ i, Y i} {z : Z}

private theorem pointed_convergence_of_eventually_approximate_models
    (h : PointedGHConverges q z)
    (hf : ∀ R ε : ℝ, 0 < ε → ε < R →
      ∀ᶠ i in atTop, Nonempty (PointedBallApprox (p i) (q i) R ε)) :
    PointedGHConverges p z := by
  refine ⟨h.complete_space, fun R ε hε hεR => ?_⟩
  have hsmall : 0 < ε / 8 := by linarith
  have hlarge : ε / 8 < 2 * R + 2 := by linarith
  filter_upwards [hf (2 * R + 2) (ε / 8) hsmall hlarge,
    h.eventually_approx hsmall hlarge] with i hfi hgi
  obtain ⟨f⟩ := hfi
  obtain ⟨g⟩ := hgi
  exact ⟨(f.comp g (s := R) (by linarith) (by linarith) (by linarith)).enlargeError
    (by linarith) hεR⟩

theorem pointedGHConverges_iff_of_kleinerLott_sequence {ε : ℕ → ℝ}
    (f : ∀ i, KleinerLottApprox (p i) (q i) (ε i))
    (hε : Tendsto ε atTop (𝓝 0)) :
    PointedGHConverges p z ↔ PointedGHConverges q z := by
  have hpairs : ∀ R η : ℝ, 0 < η → η < R →
      ∀ᶠ i in atTop, Nonempty (PointedBallApprox (p i) (q i) R η) := by
    intro R η hη hηR
    have hη3 : 0 < η / 3 := by linarith
    have hRinv : 0 < (R + 1)⁻¹ := inv_pos.mpr (by linarith)
    filter_upwards [hε.eventually (eventually_lt_nhds hη3),
      hε.eventually (eventually_lt_nhds hRinv)] with i hiη hiR
    have hinv : R < (ε i)⁻¹ := by
      have ht := (inv_lt_inv₀ hRinv (f i).error_pos).mpr hiR
      rw [inv_inv] at ht
      linarith
    exact ⟨((f i).toClosedBall (by linarith) hinv).enlargeError (by linarith) hηR⟩
  have hreverse : ∀ R η : ℝ, 0 < η → η < R →
      ∀ᶠ i in atTop, Nonempty (PointedBallApprox (q i) (p i) R η) := by
    intro R η hη hηR
    filter_upwards [hpairs (R + η) (η / 4) (by linarith) (by linarith)] with i hi
    obtain ⟨g⟩ := hi
    have hh := g.quasiInverse (s := R) (by linarith) (by linarith)
    have he : 4 * (η / 4) = η := by ring
    rw [he] at hh
    exact ⟨hh⟩
  exact ⟨fun h => pointed_convergence_of_eventually_approximate_models h hreverse,
    fun h => pointed_convergence_of_eventually_approximate_models h hpairs⟩

end GC.MetricGeometry
