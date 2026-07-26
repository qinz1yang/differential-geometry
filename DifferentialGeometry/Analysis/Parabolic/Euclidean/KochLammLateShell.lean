import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLateCover

/-!
# Parameterized shell bound for the late Koch--Lamm potential

The `k`-th spatial shell has inner radius `kR` and outer radius `(k+1)R`.
This file proves its measurable geometry and applies the finite-cover estimate
under exactly the cardinality and covering conclusions supplied by the
canonical quantitative-cover theorem.  It does not choose a cover itself.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The half-open shell of radii `[kR, (k+1)R)`. -/
def klLateShell (x : V) (R : ℝ) (k : ℕ) : Set V :=
  Metric.ball x (((k + 1 : ℕ) : ℝ) * R) \
    Metric.ball x ((k : ℝ) * R)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V] in
/-- Every late shell is measurable. -/
theorem klLateShell_mble (x : V) (R : ℝ) (k : ℕ) :
    MeasurableSet (klLateShell x R k) := by
  unfold klLateShell
  exact Metric.isOpen_ball.measurableSet.diff
    Metric.isOpen_ball.measurableSet

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- A shell lies in its outer closed ball. -/
theorem klLateShell_sub (x : V) (R : ℝ) (k : ℕ) :
    klLateShell x R k ⊆
      Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) := by
  exact diff_subset.trans Metric.ball_subset_closedBall

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- Membership outside the inner open ball gives the lower distance used by
the Gaussian tail estimate. -/
theorem klLateShell_far (x : V) (R : ℝ) (k : ℕ) :
    ∀ y ∈ klLateShell x R k, (k : ℝ) * R ≤ ‖x - y‖ := by
  intro y hy
  have hnot : y ∉ Metric.ball x ((k : ℝ) * R) := hy.2
  rw [Metric.mem_ball] at hnot
  have hdist : (k : ℝ) * R ≤ dist y x := le_of_not_gt hnot
  simpa only [dist_comm, dist_eq_norm] using hdist

omit [CompleteSpace F] in
/-- A finite shell cover with the canonical polynomial cardinality bound
inherits the Gaussian late-source estimate. -/
theorem klLateShell_norm {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (k : ℕ) (s : Finset V)
    (hcard : s.card ≤ (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s, Metric.ball c R) :
    ‖klLatePiece0 R f x (klLateShell x R k)‖ ≤
      (((5 * (k + 1)) ^ Module.finrank ℝ V : ℕ) : ℝ) *
        (Real.exp (-((k : ℝ) ^ 2) / 4) *
          (klLateTailC V * (A_q : ℝ))) := by
  have hnorm := klLateCover_norm (V := V) h x hR
    (Nat.cast_nonneg k) hRT s (klLateShell_mble (V := V) x R k)
    (fun _ hy ↦ hcover (klLateShell_sub (V := V) x R k hy))
    (klLateShell_far (V := V) x R k)
  have hc : 0 < klLateTailC V := by
    unfold klLateTailC klTailRoot
    exact Real.rpow_pos_of_pos (klTailCore_pos (V := V) one_pos) _
  have hD : 0 ≤ Real.exp (-((k : ℝ) ^ 2) / 4) *
      (klLateTailC V * (A_q : ℝ)) :=
    mul_nonneg (Real.exp_pos _).le
      (mul_nonneg hc.le (NNReal.coe_nonneg A_q))
  have hcardR : (s.card : ℝ) ≤
      (((5 * (k + 1)) ^ Module.finrank ℝ V : ℕ) : ℝ) := by
    exact_mod_cast hcard
  exact hnorm.trans (mul_le_mul_of_nonneg_right hcardR hD)

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
