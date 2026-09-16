import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace DifferentialGeometry.Analysis.ODE

theorem sub_le_integral_of_dominated_subsolutions
    {a b K : ℝ} (hab : a ≤ b)
    {u u' r : ℕ → ℝ → ℝ} {v G H : ℝ → ℝ}
    (hcont : ∀ n, ContinuousOn (u n) (Icc a b))
    (hderiv : ∀ n, ∀ t ∈ Ioo a b, HasDerivWithinAt (u n) (u' n t) (Ioi t) t)
    (hsub : ∀ n, ∀ t ∈ Ioo a b, u' n t ≤ K * u n t + r n t)
    (hrmeas : ∀ n, AEStronglyMeasurable (r n) (volume.restrict (Icc a b)))
    (hG : IntervalIntegrable G volume a b) (hH : IntervalIntegrable H volume a b)
    (huG : ∀ n, ∀ᵐ t ∂volume.restrict (Icc a b), ‖u n t‖ ≤ G t)
    (hrH : ∀ n, ∀ᵐ t ∂volume.restrict (Icc a b), ‖r n t‖ ≤ H t)
    (hu : ∀ t ∈ Icc a b, Tendsto (fun n => u n t) atTop (𝓝 (v t)))
    (hr : ∀ᵐ t ∂volume.restrict (Icc a b), Tendsto (fun n => r n t) atTop (𝓝 0)) :
    v b - v a ≤ K * ∫ t in a..b, v t := by
  have hGint : IntegrableOn G (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hG
  have hHint : IntegrableOn H (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hH
  have huit (n : ℕ) : IntegrableOn (u n) (Icc a b) := (hcont n).integrableOn_Icc
  have hrit (n : ℕ) : IntegrableOn (r n) (Icc a b) :=
    hHint.mono' (hrmeas n) (hrH n)
  have hlimit : ∀ᵐ t ∂volume.restrict (Icc a b),
      Tendsto (fun n => u n t) atTop (𝓝 (v t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hu t ht
  have hulim := tendsto_integral_of_dominated_convergence G
    (fun n => (huit n).aestronglyMeasurable) hGint huG hlimit
  have hrlim := tendsto_integral_of_dominated_convergence H hrmeas hHint hrH hr
  have huleft : Tendsto (fun n => u n b - u n a) atTop (𝓝 (v b - v a)) :=
    (hu b ⟨hab, le_rfl⟩).sub (hu a ⟨le_rfl, hab⟩)
  have huright : Tendsto (fun n => K * (∫ t in a..b, u n t) + ∫ t in a..b, r n t)
      atTop (𝓝 (K * ∫ t in a..b, v t)) := by
    simp_rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    simpa only [integral_zero, add_zero] using (hulim.const_mul K).add hrlim
  apply le_of_tendsto_of_tendsto huleft huright
  filter_upwards [] with n
  have hn := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
    hab (hcont n) (hderiv n) ((huit n).const_mul K |>.add (hrit n)) (hsub n)
  change u n b - u n a ≤ ∫ t in a..b, K * u n t + r n t at hn
  rw [intervalIntegral.integral_add
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr ((huit n).const_mul K))
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr (hrit n)),
    intervalIntegral.integral_const_mul] at hn
  exact hn

end DifferentialGeometry.Analysis.ODE
