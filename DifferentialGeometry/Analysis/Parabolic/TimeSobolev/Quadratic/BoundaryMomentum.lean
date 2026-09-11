import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.C1Regularity

set_option autoImplicit false

noncomputable section

open Set intervalIntegral
open scoped Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} {T : ℝ}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X]

private theorem mom_ramp_ftc
    (hT : 0 < T) (P F r r' : ℝ → X)
    (hP : ContDiffOn ℝ 1 P (Icc (0 : ℝ) T))
    (hPF : EqOn (derivWithin P (Icc (0 : ℝ) T)) F
      (Icc (0 : ℝ) T))
    (hr : ContDiffOn ℝ 1 r (Icc (0 : ℝ) T))
    (hr' : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt r (r' t) (Icc (0 : ℝ) T) t) :
    ∫ t in (0 : ℝ)..T,
        (inner ℝ (F t) (r t) + inner ℝ (P t) (r' t)) =
      inner ℝ (P T) (r T) - inner ℝ (P 0) (r 0) := by
  let φ : ℝ → ℝ := fun t ↦ inner ℝ (P t) (r t)
  have hφ : ContDiffOn ℝ 1 φ (Icc (0 : ℝ) T) := hP.inner ℝ hr
  have huniq : UniqueDiffOn ℝ (Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  have hφd : ∀ t ∈ Icc (0 : ℝ) T,
      derivWithin φ (Icc (0 : ℝ) T) t =
        inner ℝ (F t) (r t) + inner ℝ (P t) (r' t) := by
    intro t ht
    have hPd : HasDerivWithinAt P
        (derivWithin P (Icc (0 : ℝ) T) t) (Icc (0 : ℝ) T) t :=
      ((hP t ht).differentiableWithinAt one_ne_zero).hasDerivWithinAt
    have hd := (hPd.inner ℝ (hr' t ht)).derivWithin
      (huniq.uniqueDiffWithinAt ht)
    rw [hPF ht] at hd
    simpa only [φ, add_comm] using hd
  calc
    ∫ t in (0 : ℝ)..T,
        (inner ℝ (F t) (r t) + inner ℝ (P t) (r' t)) =
        ∫ t in (0 : ℝ)..T,
          derivWithin φ (Icc (0 : ℝ) T) t := by
            apply intervalIntegral.integral_congr
            intro t ht
            rw [uIcc_of_le hT.le] at ht
            exact (hφd t ht).symm
    _ = φ T - φ 0 :=
      intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc hφ hT.le
    _ = inner ℝ (P T) (r T) - inner ℝ (P 0) (r 0) := rfl

theorem mom_ramp_up
    (hT : 0 < T) (P F : ℝ → X)
    (hP : ContDiffOn ℝ 1 P (Icc (0 : ℝ) T))
    (hPF : EqOn (derivWithin P (Icc (0 : ℝ) T)) F
      (Icc (0 : ℝ) T)) (z : X) :
    ∫ t in (0 : ℝ)..T,
        (inner ℝ (F t) ((t / T) • z) +
          inner ℝ (P t) ((1 / T) • z)) =
      inner ℝ (P T) z := by
  have hr : ContDiffOn ℝ 1 (fun t : ℝ ↦ (t / T) • z)
      (Icc (0 : ℝ) T) :=
    ((contDiff_id.div_const T).smul_const z).contDiffOn
  have hr' : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s : ℝ ↦ (s / T) • z) ((1 / T) • z)
        (Icc (0 : ℝ) T) t := by
    intro t _
    exact (((hasDerivAt_id t).div_const T).smul_const z).hasDerivWithinAt
  have hTT : T / T = 1 := div_self hT.ne'
  simpa only [hTT, one_smul, zero_div, zero_smul, inner_zero_right,
    sub_zero] using
    mom_ramp_ftc hT P F (fun t : ℝ ↦ (t / T) • z)
      (fun _ ↦ (1 / T) • z) hP hPF hr hr'

theorem mom_ramp_down
    (hT : 0 < T) (P F : ℝ → X)
    (hP : ContDiffOn ℝ 1 P (Icc (0 : ℝ) T))
    (hPF : EqOn (derivWithin P (Icc (0 : ℝ) T)) F
      (Icc (0 : ℝ) T)) (z : X) :
    ∫ t in (0 : ℝ)..T,
        (inner ℝ (F t) (((T - t) / T) • z) +
          inner ℝ (P t) ((-(1 / T)) • z)) =
      -inner ℝ (P 0) z := by
  have hr : ContDiffOn ℝ 1 (fun t : ℝ ↦ ((T - t) / T) • z)
      (Icc (0 : ℝ) T) :=
    (((contDiff_const.sub contDiff_id).div_const T).smul_const z).contDiffOn
  have hr' : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s : ℝ ↦ ((T - s) / T) • z)
        ((-(1 / T)) • z) (Icc (0 : ℝ) T) t := by
    intro t _
    simpa only [Pi.sub_apply, id_eq, zero_sub, neg_div, one_div] using
      ((((hasDerivAt_const t T).sub (hasDerivAt_id t)).div_const T).smul_const z).hasDerivWithinAt
  have hTT : T / T = 1 := div_self hT.ne'
  simpa only [sub_self, sub_zero, zero_div, zero_smul, inner_zero_right, zero_sub,
    hTT, one_smul] using
    mom_ramp_ftc hT P F (fun t : ℝ ↦ ((T - t) / T) • z)
      (fun _ ↦ (-(1 / T)) • z) hP hPF hr hr'

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
