import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeOperatorH1
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Regularity.C1Representative

noncomputable section

open MeasureTheory Filter Set

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  {T : ℝ}

theorem timeH1.exists_timeH1_deriv_of_eq_timeOp
    (u : timeH1 Y T) (v : timeH1 X T) (f : timeH1 Y T)
    (A : ℝ → X →L[ℝ] Y) (hA : ContDiffOn ℝ 1 A (Icc (0 : ℝ) T))
    (hAm : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal) (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (heq : u.deriv = timeOp A hAm C hC v.toFunL2 + f.toFunL2) :
    ∃ w : timeH1 Y T,
      w.toFunL2 = u.deriv ∧
      (∀ t ∈ Icc (0 : ℝ) T, w.toFun t = A t (v.toFun t) + f.toFun t) ∧
      (w.deriv =ᵐ[timeMeasure T]
        fun t => _root_.deriv A t (v.toFun t) + A t (v.deriv t) + f.deriv t) ∧
      ContDiffOn ℝ 1 u.toFun (Icc (0 : ℝ) T) ∧
      (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt u.toFun
        (A t (v.toFun t) + f.toFun t) (Icc (0 : ℝ) T) t) := by
  let w := timeOpH1 A hA v + f
  have hw : w.toFunL2 = u.deriv := by
    have hp := congrArg (fun L : timeH1 X T →L[ℝ] timeL2 Y T => L v)
      (toTimeL2_comp_timeOpH1 A hA hAm C hC)
    change (timeOpH1 A hA v).toFunL2 = timeOp A hAm C hC v.toFunL2 at hp
    change timeH1.toTimeL2 Y T (timeOpH1 A hA v + f) = _
    rw [map_add, timeH1.toTimeL2_apply, timeH1.toTimeL2_apply, hp, heq]
  have hpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      w.toFun t = A t (v.toFun t) + f.toFun t := by
    rw [timeH1.toFun_add _ _ ht, timeOpH1_toFun A hA v ht]
  have hrep : u.deriv =ᵐ[timeMeasure T] w.toFun := by
    rw [← hw]
    exact coeFn_ofContinuousOn w.continuousOn_toFun
  have hC1 : ContDiffOn ℝ 1 u.toFun (Icc (0 : ℝ) T) := by
    rcases lt_trichotomy T 0 with hT | rfl | hT
    · rw [Icc_eq_empty (not_le.mpr hT)]
      exact contDiffOn_empty
    · intro t ht
      have ht0 : t = 0 := le_antisymm ht.2 ht.1
      subst t
      simpa only [Icc_self] using
        (contDiffWithinAt_singleton : ContDiffWithinAt ℝ 1 u.toFun {0} 0)
    · exact (toFun_c1_of_rep hT u w.toFun w.continuousOn_toFun hrep).1
  refine ⟨w, hw, hpoint, ?_, hC1, ?_⟩
  · change (timeOpH1 A hA v).deriv + f.deriv =ᵐ[timeMeasure T] _
    filter_upwards [Lp.coeFn_add (timeOpH1 A hA v).deriv f.deriv,
      timeOpH1_deriv_ae A hA v] with t hsum ht
    rw [hsum, Pi.add_apply, ht]
  · intro t ht
    rw [← hpoint t ht]
    exact u.hasDerivWithinAt_toFun_of_continuousOn w.continuousOn_toFun hrep ht

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
