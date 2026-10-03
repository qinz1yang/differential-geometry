import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Multiplication

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1

variable {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K] {T : ℝ}

theorem exists_lift_of_initial_and_deriv
    (J : H →L[ℝ] K) (u : timeH1 K T) (a : H) (z : timeL2 H T)
    (ha : J a = u.initial)
    (hz : ∀ᵐ t ∂timeMeasure T, J (z t) = u.deriv t) :
    ∃ w : timeH1 H T, w.initial = a ∧ w.deriv = z ∧
      ∀ t ∈ Icc (0 : ℝ) T, J (w.toFun t) = u.toFun t := by
  let w := timeH1.mk a z
  obtain ⟨v, hvi, hv, hvd⟩ := exists_timeH1_comp_clm J w
  have hvu : v = u := by
    apply timeH1.ext
    · exact hvi.trans ha
    · apply Lp.ext
      exact hvd.trans hz
  refine ⟨w, rfl, rfl, ?_⟩
  intro t ht
  rw [← hv t ht, hvu]

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1
