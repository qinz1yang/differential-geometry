import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottConvergence

open Filter
open scoped Topology

namespace GC.MetricGeometry.PointedGHConverges

universe u v w
variable {X : ℕ → Type u} {Y : ℕ → Type v} {Z : Type w}
variable [∀ i, MetricSpace (X i)] [∀ i, MetricSpace (Y i)] [MetricSpace Z]
variable {p : ∀ i, X i} {q : ∀ i, Y i} {z : Z} {δ : ℕ → ℝ}

theorem of_approximate_sources (h : PointedGHConverges q z)
    (f : ∀ i, KleinerLottApprox (p i) (q i) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) : PointedGHConverges p z := by
  refine ⟨h.complete_space, fun R ε hε hεR => ?_⟩
  have hR : 0 < R := hε.trans hεR
  filter_upwards [h.eventually_approx (R := R + ε) (ε := ε / 4)
    (by linarith) (by linarith),
    hδ.eventually (eventually_lt_nhds (show 0 < ε / 12 by positivity)),
    hδ.eventually (eventually_lt_nhds (show 0 < (R + ε + 1)⁻¹ by positivity))]
    with i hi hiε hiR
  obtain ⟨g⟩ := hi
  have hinv : R + ε < (δ i)⁻¹ := by
    have hh := (inv_lt_inv₀ (show 0 < (R + ε + 1)⁻¹ by positivity) (f i).error_pos).mpr hiR
    rw [inv_inv] at hh
    linarith
  let F : PointedBallApprox (p i) (q i) (R + ε) (ε / 4) :=
    ((f i).toClosedBall (by linarith) hinv).enlargeError (by linarith) (by linarith)
  have H := F.comp g (s := R) (by linarith) (by linarith) (by linarith)
  have he : 2 * (ε / 4 + ε / 4) = ε := by ring
  rw [he] at H
  exact ⟨H⟩

end GC.MetricGeometry.PointedGHConverges
