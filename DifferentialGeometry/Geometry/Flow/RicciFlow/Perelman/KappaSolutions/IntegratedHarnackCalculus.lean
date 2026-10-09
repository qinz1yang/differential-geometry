import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.TangentCone.Real

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter MeasureTheory Set
open scoped _root_.Topology Interval

theorem compensated_monotoneOn_of_pointwise_of_uniform_bound
    {a b : ℝ} (scalar energy : ℕ → ℝ → ℝ) (scalarLimit energyLimit : ℝ → ℝ)
    (B : ℝ)
    (henergy : ∀ i, ContinuousOn (energy i) (Icc a b))
    (hbound : ∀ i, ∀ t ∈ Icc a b, ‖energy i t‖ ≤ B)
    (hscalar : ∀ t ∈ Icc a b,
      Tendsto (fun i => scalar i t) atTop (𝓝 (scalarLimit t)))
    (hlimit : ∀ t ∈ Icc a b,
      Tendsto (fun i => energy i t) atTop (𝓝 (energyLimit t)))
    (hmono : ∀ i, MonotoneOn
      (fun t => scalar i t + (1 / 2 : ℝ) * ∫ s in a..t, energy i s) (Icc a b)) :
    MonotoneOn
      (fun t => scalarLimit t + (1 / 2 : ℝ) * ∫ s in a..t, energyLimit s)
      (Icc a b) := by
  apply monotoneOn_of_frequently_monotoneOn_of_tendsto (l := (atTop : Filter ℕ))
    (Eventually.of_forall hmono).frequently
  intro t ht
  have hsub : Ι a t ⊆ Icc a b := by
    rw [uIoc_of_le ht.1]
    intro s hs
    exact ⟨hs.1.le, hs.2.trans ht.2⟩
  have hintegral : Tendsto (fun i => ∫ s in a..t, energy i s)
      atTop (𝓝 (∫ s in a..t, energyLimit s)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => B)
    · exact Eventually.of_forall (fun i =>
        ((henergy i).mono hsub).aestronglyMeasurable measurableSet_uIoc)
    · exact Eventually.of_forall (fun i =>
        ae_of_all volume (fun s hs => hbound i s (hsub hs)))
    · exact intervalIntegrable_const
    · exact ae_of_all volume (fun s hs => hlimit s (hsub hs))
  exact (hscalar t ht).add (hintegral.const_mul (1 / 2 : ℝ))

theorem nonnegative_compensated_derivative_on_closed_interval
    {a b t d : ℝ} (hab : a < b) (ht : t ∈ Icc a b)
    (scalar energy : ℝ → ℝ)
    (hscalar : HasDerivWithinAt scalar d (Icc a b) t)
    (henergy : ContinuousOn energy (Icc a b))
    (hmono : MonotoneOn
      (fun s => scalar s + (1 / 2 : ℝ) * ∫ u in a..s, energy u) (Icc a b)) :
    0 ≤ d + (1 / 2 : ℝ) * energy t := by
  let _ : Fact (t ∈ Icc a b) := ⟨ht⟩
  have hint : IntervalIntegrable energy volume a t :=
    (henergy.mono (uIcc_subset_Icc ⟨le_rfl, hab.le⟩ ht)).intervalIntegrable
  have hderiv : HasDerivWithinAt (fun s => ∫ u in a..s, energy u)
      (energy t) (Icc a b) t :=
    intervalIntegral.integral_hasDerivWithinAt_right hint
      (henergy.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t)
      (henergy t ht)
  have htotal := hscalar.add (hderiv.const_mul (1 / 2 : ℝ))
  have hacc : AccPt t (𝓟 (Icc a b)) :=
    uniqueDiffWithinAt_iff_accPt.mp (uniqueDiffOn_Icc hab t ht)
  exact HasDerivWithinAt.nonneg_of_monotoneOn hacc htotal hmono

theorem terminal_harnack_of_endpoint_differences
    (spatial temporal energy : ℝ → ℝ) {tau ds dt e : ℝ}
    (hspace : HasDerivAt spatial ds 0)
    (htime : HasDerivWithinAt temporal dt (Iic tau) tau)
    (henergy : Tendsto energy (𝓝[>] (0 : ℝ)) (𝓝 e))
    (hineq : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      temporal (tau - h) ≤ spatial h - spatial 0 + temporal tau +
        (1 / 2 : ℝ) * h * energy h) :
    0 ≤ dt + ds + (1 / 2 : ℝ) * e := by
  have htime0 : HasDerivWithinAt temporal dt (Iic tau) (tau - 0) := by
    simpa only [sub_zero] using htime
  have hback := htime0.comp 0
    ((hasDerivAt_id (0 : ℝ)).const_sub tau).hasDerivWithinAt (s := Ici (0 : ℝ))
    (by
      intro h hh
      change 0 ≤ h at hh
      change tau - h ≤ tau
      linarith)
  have hdiff : HasDerivWithinAt (fun h => spatial h - temporal (tau - h))
      (ds + dt) (Ici (0 : ℝ)) 0 := by
    simpa only [mul_neg_one, sub_neg_eq_add, Pi.sub_apply, Function.comp_apply] using!
      (hspace.hasDerivWithinAt (s := Ici (0 : ℝ))).sub hback
  have hslope := (hasDerivWithinAt_iff_tendsto_slope'
    (by simp : (0 : ℝ) ∉ Ioi 0)).mp hdiff.Ioi_of_Ici
  have hlim := hslope.add (henergy.const_mul (1 / 2 : ℝ))
  have hnonneg : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      0 ≤ slope (fun q => spatial q - temporal (tau - q)) 0 h +
        (1 / 2 : ℝ) * energy h := by
    filter_upwards [hineq, self_mem_nhdsWithin] with h hh hpos
    change 0 < h at hpos
    have hnum : 0 ≤ ((spatial h - temporal (tau - h)) -
        (spatial 0 - temporal tau)) + (1 / 2 : ℝ) * h * energy h := by
      linarith
    have hdiv := div_nonneg hnum hpos.le
    have heq : (((spatial h - temporal (tau - h)) -
        (spatial 0 - temporal tau)) + (1 / 2 : ℝ) * h * energy h) / h =
        slope (fun q => spatial q - temporal (tau - q)) 0 h +
          (1 / 2 : ℝ) * energy h := by
      rw [slope_def_field]
      simp only [sub_zero]
      field_simp [ne_of_gt hpos]
    rw [heq] at hdiv
    exact hdiv
  have h := ge_of_tendsto hlim hnonneg
  simpa only [add_comm dt ds] using h

theorem short_diagonal_average_tendsto
    (energy : ℝ × ℝ → ℝ) (tau : ℝ)
    (hcont : ContinuousWithinAt energy (Iic tau ×ˢ Ici (0 : ℝ)) (tau, 0))
    (hint : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      IntervalIntegrable (fun s => energy (s, s - (tau - h))) volume (tau - h) tau) :
    Tendsto (fun h => (∫ s in tau - h..tau, energy (s, s - (tau - h))) / h)
      (𝓝[>] (0 : ℝ)) (𝓝 (energy (tau, 0))) := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  obtain ⟨delta, hdelta, hnear⟩ :=
    Metric.continuousWithinAt_iff.mp hcont (eps / 2) (half_pos heps)
  have hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo 0 delta :=
    Ioo_mem_nhdsGT hdelta
  filter_upwards [hsmall, hint] with h hh hInt
  have hab : tau - h ≤ tau := sub_le_self _ hh.1.le
  have hpointwise : ∀ s ∈ Ι (tau - h) tau,
      ‖energy (s, s - (tau - h)) - energy (tau, 0)‖ ≤ eps / 2 := by
    intro s hs
    rw [uIoc_of_le hab] at hs
    have hfirst : |s - tau| ≤ h := by
      rw [abs_of_nonpos (sub_nonpos.mpr hs.2)]
      linarith [hs.1]
    have hsecond : |s - (tau - h) - 0| ≤ h := by
      rw [sub_zero, abs_of_nonneg (sub_nonneg.mpr hs.1.le)]
      linarith [hs.2]
    have hdist : dist (s, s - (tau - h)) (tau, 0) < delta := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_lt (hfirst.trans_lt hh.2) (hsecond.trans_lt hh.2)
    have h := hnear (x := (s, s - (tau - h)))
      ⟨hs.2, sub_nonneg.mpr hs.1.le⟩ hdist
    simpa only [Real.dist_eq, Real.norm_eq_abs] using h.le
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hpointwise
  have hidentity :
      (∫ s in tau - h..tau, energy (s, s - (tau - h))) / h - energy (tau, 0) =
        (∫ s in tau - h..tau, energy (s, s - (tau - h)) - energy (tau, 0)) / h := by
    rw [intervalIntegral.integral_sub hInt intervalIntegrable_const, sub_div,
      intervalIntegral.integral_const]
    simp only [sub_sub_cancel, smul_eq_mul, mul_div_cancel_left₀ _ hh.1.ne']
  rw [Real.dist_eq, ← Real.norm_eq_abs, hidentity, norm_div,
    Real.norm_eq_abs h, abs_of_pos hh.1]
  apply lt_of_le_of_lt _ (half_lt_self heps)
  apply (div_le_iff₀ hh.1).2
  simpa only [sub_sub_cancel, abs_of_pos hh.1] using hbound

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
