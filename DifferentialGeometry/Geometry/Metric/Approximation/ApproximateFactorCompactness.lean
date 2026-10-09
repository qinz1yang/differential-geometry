import DifferentialGeometry.Geometry.Metric.Approximation.FactorNetTransfer
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottConvergence
import DifferentialGeometry.Geometry.Metric.Approximation.PointedPrecompactness

set_option autoImplicit false

open Set Metric Filter
open scoped Topology

namespace GC.MetricGeometry

universe u v w z
variable {X : ℕ → Type u} {E : ℕ → Type v} {Z : ℕ → Type w} {Y : Type z}
variable [∀ i, MetricSpace (X i)] [∀ i, MetricSpace (E i)] [∀ i, MetricSpace (Z i)]
variable [MetricSpace Y] [ProperSpace Y]
variable {p : ∀ i, X i} {a : ∀ i, E i} {q : Y} {b : ∀ i, Z i} {δ : ℕ → ℝ}

theorem PointedGHConverges.eventual_factor_nets_of_approximate_products
    (h : PointedGHConverges p q)
    (f : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a i, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → ∃ N I : ℕ, ∀ i : ℕ, I ≤ i →
      ∃ T : Finset (Z i), T.card ≤ N ∧
        (∀ y ∈ T, dist y (b i) ≤ R) ∧
        ∀ y : Z i, dist y (b i) ≤ R → ∃ z ∈ T, dist y z ≤ η := by
  intro R hR η hη
  let ε : ℝ := min (1 / 100) (η / 100)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hεone : ε ≤ 1 / 100 := min_le_left _ _
  have hεη : ε ≤ η / 100 := min_le_right _ _
  obtain ⟨F, hFin, hnet⟩ := exists_finset_net_of_isCompact (isCompact_closedBall q (R + 1))
    (by positivity : 0 < η / 4)
  have htail : ∀ᶠ i in atTop, ∃ T : Finset (Z i), T.card ≤ F.card ∧
      (∀ y ∈ T, dist y (b i) ≤ R) ∧
      ∀ y : Z i, dist y (b i) ≤ R → ∃ z ∈ T, dist y z ≤ η := by
    filter_upwards [h.eventually_reverse_approx (R := R + 4) hε (by linarith),
      hδ.eventually (eventually_lt_nhds (show 0 < ε / 3 by positivity)),
      hδ.eventually (eventually_lt_nhds (show 0 < (R + 5)⁻¹ by positivity))] with i hg hiε hiR
    obtain ⟨g⟩ := hg
    have hinv : R + 4 < (δ i)⁻¹ := by
      have hi := (inv_lt_inv₀ (show 0 < (R + 5)⁻¹ by positivity) (f i).error_pos).mpr hiR
      rw [inv_inv] at hi
      linarith
    let A : PointedBallApprox (p i) (WithLp.toLp 2 (a i, b i)) (R + 4) ε :=
      ((f i).toClosedBall (by linarith) hinv).enlargeError (by linarith) (by linarith)
    have B : PointedBallApprox q (WithLp.toLp 2 (a i, b i)) (R + 2) (4 * ε) := by
      simpa only [show 2 * (ε + ε) = 4 * ε by ring] using
        g.comp A (s := R + 2) (by linarith) (by linarith) (by linarith)
    obtain ⟨T, hcard, hT, hcover⟩ := B.exists_internal_finset_net_factor hR hη
      (by linarith) (by linarith) F hFin hnet
    refine ⟨T, hcard, hT, fun y hy => ?_⟩
    obtain ⟨z, hz, hd⟩ := hcover y hy
    exact ⟨z, hz, hd.le⟩
  obtain ⟨I, hI⟩ := eventually_atTop.mp htail
  exact ⟨F.card, I, hI⟩

theorem PointedGHConverges.exists_factor_limit_of_approximate_products
    (h : PointedGHConverges p q)
    (f : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a i, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    ∃ (W : Type) (m : MetricSpace W), letI := m
      ∃ (w : W) (φ : ℕ → ℕ), StrictMono φ ∧ ProperSpace W ∧ CompleteSpace W ∧
        PointedGHConverges (fun i => b (φ i)) w ∧
        PointedGHConverges (fun i => p (φ i)) q := by
  obtain ⟨W, m, w, φ, hφ, hproper, hconv⟩ :=
    exists_pointedGHConverges_of_eventual_finite_nets b
      (h.eventual_factor_nets_of_approximate_products f hδ)
  exact ⟨W, m, w, φ, hφ, hproper, hconv.complete_space, hconv, h.subsequence hφ⟩

end GC.MetricGeometry
