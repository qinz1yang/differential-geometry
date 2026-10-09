import DifferentialGeometry.Geometry.Metric.Approximation.Transport
import DifferentialGeometry.Geometry.Metric.Approximation.RealBallExamples
import DifferentialGeometry.Geometry.Metric.Approximation.OpenBallApproximation
import Mathlib.Order.Filter.AtTopBot.Basic

namespace GC.MetricGeometry

open Filter

universe u v

variable {X : ℕ → Type u} [∀ n, MetricSpace (X n)]
variable {Y : Type v} [MetricSpace Y]

def PointedGHConverges (p : ∀ n, X n) (q : Y) : Prop :=
  CompleteSpace Y ∧ ∀ R ε : ℝ, 0 < ε → ε < R →
    ∀ᶠ n in atTop, Nonempty (PointedBallApprox (p n) q R ε)

namespace PointedGHConverges

variable {p : ∀ n, X n} {q : Y}

theorem complete_space (h : PointedGHConverges p q) : CompleteSpace Y := h.1

theorem eventually_approx (h : PointedGHConverges p q) {R ε : ℝ}
    (hε : 0 < ε) (hR : ε < R) :
    ∀ᶠ n in atTop, Nonempty (PointedBallApprox (p n) q R ε) := h.2 R ε hε hR

theorem subsequence (h : PointedGHConverges p q) {φ : ℕ → ℕ}
    (hφ : StrictMono φ) : PointedGHConverges (fun n => p (φ n)) q := by
  refine ⟨h.1, fun R ε hε hR => ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h.eventually_approx hε hR)
  exact eventually_atTop.mpr ⟨N, fun n hn => hN (φ n) (hn.trans (hφ.id_le n))⟩

theorem eventually_reverse_approx (h : PointedGHConverges p q) {R ε : ℝ}
    (hε : 0 < ε) (hR : ε < R) :
    ∀ᶠ n in atTop, Nonempty (PointedBallApprox q (p n) R ε) := by
  filter_upwards [h.eventually_approx (R := R + ε) (ε := ε / 4)
    (by linarith) (by linarith)] with n hn
  obtain ⟨f⟩ := hn
  have hf := f.quasiInverse (s := R) (by linarith) (by linarith)
  have he : 4 * (ε / 4) = ε := by ring
  rw [he] at hf
  exact ⟨hf⟩

theorem of_eventually_reverse_approx [CompleteSpace Y]
    (h : ∀ R ε : ℝ, 0 < ε → ε < R →
      ∀ᶠ n in atTop, Nonempty (PointedBallApprox q (p n) R ε)) :
    PointedGHConverges p q := by
  refine ⟨inferInstance, fun R ε hε hR => ?_⟩
  filter_upwards [h (R + ε) (ε / 4) (by linarith) (by linarith)] with n hn
  obtain ⟨f⟩ := hn
  have hf := f.quasiInverse (s := R) (by linarith) (by linarith)
  have he : 4 * (ε / 4) = ε := by ring
  rw [he] at hf
  exact ⟨hf⟩

theorem iff_eventually_reverse_approx [CompleteSpace Y] :
    PointedGHConverges p q ↔
      ∀ R ε : ℝ, 0 < ε → ε < R →
        ∀ᶠ n in atTop, Nonempty (PointedBallApprox q (p n) R ε) :=
  ⟨fun h _ _ hε hR => h.eventually_reverse_approx hε hR,
    of_eventually_reverse_approx⟩

theorem const [CompleteSpace Y] (q : Y) :
    PointedGHConverges (fun _ : ℕ => q) q :=
  ⟨inferInstance, fun _ _ hε hR => Eventually.of_forall
    (fun _ => ⟨identityApprox q hε hR⟩)⟩

theorem eventually_open_approx (h : PointedGHConverges p q) {R ε : ℝ}
    (hε : 0 < ε) (hR : ε < R) :
    ∀ᶠ n in atTop, Nonempty (PointedOpenBallApprox (p n) q R ε) := by
  filter_upwards [h.eventually_approx (R := R + 1) (ε := ε / 2)
    (by linarith) (by linarith)] with n hn
  obtain ⟨f⟩ := hn
  have hf := f.toOpenBall (s := R) (by linarith) (by linarith)
  have he : 2 * (ε / 2) = ε := by ring
  rw [he] at hf
  exact ⟨hf⟩

theorem of_eventually_open_approx [CompleteSpace Y]
    (h : ∀ R ε : ℝ, 0 < ε → ε < R →
      ∀ᶠ n in atTop, Nonempty (PointedOpenBallApprox (p n) q R ε)) :
    PointedGHConverges p q := by
  refine ⟨inferInstance, fun R ε hε hR => ?_⟩
  filter_upwards [h (R + 1) (ε / 2) (by linarith) (by linarith)] with n hn
  obtain ⟨f⟩ := hn
  have hf := f.toClosedBall (s := R) (by linarith) (by linarith)
  have he : 2 * (ε / 2) = ε := by ring
  rw [he] at hf
  exact ⟨hf⟩

theorem iff_eventually_open_approx [CompleteSpace Y] :
    PointedGHConverges p q ↔
      ∀ R ε : ℝ, 0 < ε → ε < R →
        ∀ᶠ n in atTop, Nonempty (PointedOpenBallApprox (p n) q R ε) :=
  ⟨fun h _ _ hε hR => h.eventually_open_approx hε hR,
    of_eventually_open_approx⟩

end PointedGHConverges

end GC.MetricGeometry
