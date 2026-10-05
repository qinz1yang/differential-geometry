import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

section

variable {X : Type*} [NormedAddCommGroup X] [CompleteSpace X]

theorem deriv_ae_of_eqOn [NormedSpace ℝ X]
    {T : ℝ} (hT : 0 < T) (u : timeH1 X T)
    (f : ℝ → X) (hf : ContDiff ℝ 1 f)
    (heq : EqOn u.toFun f (Icc (0 : ℝ) T)) :
    u.deriv =ᵐ[timeMeasure T] _root_.deriv f := by
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Ioo (0 : ℝ) T := by
    unfold timeMeasure
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [u.ae_hasDerivWithinAt_toFun, hmem] with t hu ht
  have htIcc : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
  have huniq := (uniqueDiffOn_Icc hT).uniqueDiffWithinAt htIcc
  have hfAt : HasDerivAt f (_root_.deriv f t) t :=
    ((hf.differentiable (by norm_num)) t).hasDerivAt
  calc
    u.deriv t = derivWithin u.toFun (Icc (0 : ℝ) T) t :=
      (hu.derivWithin huniq).symm
    _ = derivWithin f (Icc (0 : ℝ) T) t :=
      derivWithin_congr heq (heq htIcc)
    _ = _root_.deriv f t :=
      hfAt.hasDerivWithinAt.derivWithin huniq

end

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
