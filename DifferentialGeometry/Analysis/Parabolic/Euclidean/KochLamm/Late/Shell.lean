import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Late.Cover

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

def kochLammLateShell (x : V) (R : ℝ) (k : ℕ) : Set V :=
  Metric.ball x (((k + 1 : ℕ) : ℝ) * R) \
    Metric.ball x ((k : ℝ) * R)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V] in
theorem kochLammLateShell_mble (x : V) (R : ℝ) (k : ℕ) :
    MeasurableSet (kochLammLateShell x R k) := by
  unfold kochLammLateShell
  exact Metric.isOpen_ball.measurableSet.diff
    Metric.isOpen_ball.measurableSet

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem kochLammLateShell_sub (x : V) (R : ℝ) (k : ℕ) :
    kochLammLateShell x R k ⊆
      Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) := by
  exact sdiff_subset.trans Metric.ball_subset_closedBall

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem kochLammLateShell_far (x : V) (R : ℝ) (k : ℕ) :
    ∀ y ∈ kochLammLateShell x R k, (k : ℝ) * R ≤ ‖x - y‖ := by
  intro y hy
  have hnot : y ∉ Metric.ball x ((k : ℝ) * R) := hy.2
  rw [Metric.mem_ball] at hnot
  have hdist : (k : ℝ) * R ≤ dist y x := le_of_not_gt hnot
  simpa only [dist_comm, dist_eq_norm] using hdist

omit [CompleteSpace F] in
theorem kochLammLateShell_norm {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceZero T A₁ A_q f) (x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (k : ℕ) (s : Finset V)
    (hcard : s.card ≤ (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s, Metric.ball c R) :
    ‖kochLammLatePiece0 R f x (kochLammLateShell x R k)‖ ≤
      (((5 * (k + 1)) ^ Module.finrank ℝ V : ℕ) : ℝ) *
        (Real.exp (-((k : ℝ) ^ 2) / 4) *
          (kochLammLateTailC V * (A_q : ℝ))) := by
  have hnorm := kochLammLateCover_norm (V := V) h x hR
    (Nat.cast_nonneg k) hRT s (kochLammLateShell_mble (V := V) x R k)
    (fun _ hy ↦ hcover (kochLammLateShell_sub (V := V) x R k hy))
    (kochLammLateShell_far (V := V) x R k)
  have hc : 0 < kochLammLateTailC V := by
    unfold kochLammLateTailC kochLammTailRoot
    exact Real.rpow_pos_of_pos (kochLammTailCore_pos (V := V) one_pos) _
  have hD : 0 ≤ Real.exp (-((k : ℝ) ^ 2) / 4) *
      (kochLammLateTailC V * (A_q : ℝ)) :=
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
