import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Topology.Sequences.EventualDiagonal
import Mathlib.Analysis.SpecificLimits.Basic

namespace GC.MetricGeometry.PointedGHConverges

open Filter
open scoped Topology

universe u v
variable {X : ℕ → Type u} [∀ n, MetricSpace (X n)]
variable {Y : Type v} [MetricSpace Y] {p : ∀ n, X n} {q : Y}

theorem eventually_kleinerLott_approx (h : PointedGHConverges p q) {δ : ℝ}
    (hδ : 0 < δ) (hδone : δ < 1) :
    ∀ᶠ n in atTop, Nonempty (KleinerLottApprox (p n) q δ) := by
  have hε : 0 < δ / 4 := by linarith
  have hR : δ / 4 < δ⁻¹ + δ := by linarith [inv_pos.mpr hδ]
  filter_upwards [h.eventually_approx hε hR] with n hn
  obtain ⟨f⟩ := hn
  exact ⟨f.toKleinerLott hδ hδone⟩

theorem of_kleinerLott_sequence [CompleteSpace Y] {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0))
    (happrox : ∀ᶠ n in atTop, Nonempty (KleinerLottApprox (p n) q (δ n))) :
    PointedGHConverges p q := by
  refine ⟨inferInstance, fun R ε hε hεR => ?_⟩
  have hRpos : 0 < R := hε.trans hεR
  have hε3 : 0 < ε / 3 := by linarith
  have hRinv : 0 < (R + 1)⁻¹ := inv_pos.mpr (by linarith)
  filter_upwards [happrox, hδ.eventually (eventually_lt_nhds hε3),
    hδ.eventually (eventually_lt_nhds hRinv)] with n hn hnε hnR
  obtain ⟨f⟩ := hn
  have hinv : R < (δ n)⁻¹ := by
    have ht := (inv_lt_inv₀ hRinv f.error_pos).mpr hnR
    rw [inv_inv] at ht
    linarith
  exact ⟨(f.toClosedBall (by linarith) hinv).enlargeError (by linarith) hεR⟩

theorem exists_kleinerLott_sequence (h : PointedGHConverges p q) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 < δ n ∧ δ n < 1) ∧
      Tendsto δ atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, Nonempty (KleinerLottApprox (p n) q (δ n)) := by
  let ε : ℕ → ℝ := fun k => (1 / ((k : ℝ) + 1)) / 2
  have hε (k : ℕ) : 0 < ε k ∧ ε k < 1 := by
    have hn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hinv : 1 / ((k : ℝ) + 1) ≤ 1 :=
      (div_le_iff₀ (by positivity)).mpr (by linarith)
    dsimp only [ε]
    exact ⟨by positivity, by linarith⟩
  have hzero : Tendsto ε atTop (𝓝 0) := by
    simpa only [zero_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
  obtain ⟨j, hj, hjapprox⟩ := exists_tendsto_atTop_eventually_diagonal
    (fun k => h.eventually_kleinerLott_approx (hε k).1 (hε k).2)
  exact ⟨fun n => ε (j n), fun n => hε (j n), hzero.comp hj, hjapprox⟩

theorem iff_exists_kleinerLott_sequence [CompleteSpace Y] :
    PointedGHConverges p q ↔
      ∃ δ : ℕ → ℝ, (∀ n, 0 < δ n ∧ δ n < 1) ∧
        Tendsto δ atTop (𝓝 0) ∧
        ∀ᶠ n in atTop, Nonempty (KleinerLottApprox (p n) q (δ n)) :=
  ⟨exists_kleinerLott_sequence, fun ⟨_, _, hzero, happrox⟩ =>
    of_kleinerLott_sequence hzero happrox⟩

end GC.MetricGeometry.PointedGHConverges
