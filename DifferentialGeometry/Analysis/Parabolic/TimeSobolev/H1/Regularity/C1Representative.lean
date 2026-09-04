import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {T : ℝ}

theorem toFun_c1_of_rep
    (hT : 0 < T) (u : timeH1 X T) (w : ℝ → X)
    (hw : ContinuousOn w (Icc (0 : ℝ) T))
    (hrep : u.deriv =ᵐ[timeMeasure T] w) :
    ContDiffOn ℝ 1 u.toFun (Icc (0 : ℝ) T) ∧
      EqOn (derivWithin u.toFun (Icc (0 : ℝ) T)) w (Icc (0 : ℝ) T) := by
  have hd : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt u.toFun (w t) (Icc (0 : ℝ) T) t :=
    fun t ht ↦ u.hasDerivWithinAt_toFun_of_continuousOn hw hrep ht
  have huniq : UniqueDiffOn ℝ (Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  have heq : EqOn (derivWithin u.toFun (Icc (0 : ℝ) T)) w
      (Icc (0 : ℝ) T) := by
    intro t ht
    exact (hd t ht).derivWithin (huniq.uniqueDiffWithinAt ht)
  refine ⟨?_, heq⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
    contDiffOn_succ_iff_derivWithin huniq]
  refine ⟨fun t ht ↦ (hd t ht).differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  exact hw.congr fun _ ht ↦ heq ht

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
