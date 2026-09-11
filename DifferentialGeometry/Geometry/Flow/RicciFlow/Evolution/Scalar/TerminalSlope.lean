import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul


set_option autoImplicit false
open Filter Set
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood


theorem abs_derivWithin_Iic_le_of_interior_bound
    (f : ℝ → ℝ) {a b C : ℝ} (hab : a < b) (hC : 0 ≤ C)
    (hcont : ContinuousOn f (Icc a b))
    (hdiff : ∀ r ∈ Ioo a b, DifferentiableAt ℝ f r)
    (hbound : ∀ r ∈ Ioo a b, |deriv f r| ≤ C) :
    |derivWithin f (Iic b) b| ≤ C := by
  by_cases hd : DifferentiableWithinAt ℝ f (Iic b) b
  · have hlim : Tendsto (slope f b) (𝓝[<] b) (𝓝 (derivWithin f (Iic b) b)) :=
      (hasDerivWithinAt_iff_tendsto_slope' (by simp : b ∉ Iio b)).mp
        (hd.hasDerivWithinAt.mono Iio_subset_Iic_self)
    apply le_of_tendsto hlim.abs
    filter_upwards [Ioo_mem_nhdsLT hab] with r hr
    have hsub : Icc r b ⊆ Icc a b := fun s hs => ⟨hr.1.le.trans hs.1, hs.2⟩
    have hmv := norm_image_sub_le_of_norm_deriv_right_le_segment
      (hcont.mono hsub)
      (fun s hs => (hdiff s ⟨hr.1.trans_le hs.1, hs.2⟩).hasDerivAt.hasDerivWithinAt)
      (fun s hs => by simpa only [Real.norm_eq_abs] using hbound s ⟨hr.1.trans_le hs.1, hs.2⟩)
      b ⟨hr.2.le, le_rfl⟩
    rw [slope_def_field, abs_div, abs_sub_comm (f r) (f b), abs_of_neg (sub_neg.mpr hr.2), neg_sub]
    exact (div_le_iff₀ (sub_pos.mpr hr.2)).mpr (by simpa only [Real.norm_eq_abs] using hmv)
  · rw [derivWithin_zero_of_not_differentiableWithinAt hd, abs_zero]
    exact hC


theorem derivWithin_parabolic_scalar_Iic
    (f : ℝ → ℝ) (t Q : ℝ) (hQ : 0 < Q)
    (hf : DifferentiableWithinAt ℝ f (Iic t) t) :
    derivWithin (fun s => Q⁻¹ * f (t + s / Q)) (Iic 0) 0 =
      Q⁻¹ ^ 2 * derivWithin f (Iic t) t := by
  have htime : HasDerivAt (fun s : ℝ => t + s / Q) Q⁻¹ 0 := by
    have hh : HasDerivAt (fun s : ℝ => s / Q) (1 / Q) 0 :=
      (hasDerivAt_id (0 : ℝ)).div_const Q
    rw [one_div] at hh
    exact hh.const_add t
  have hmaps : MapsTo (fun s : ℝ => t + s / Q) (Iic 0) (Iic t) := by
    intro s hs
    exact add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs hQ.le)
  have hd : HasDerivWithinAt (fun s : ℝ => f (t + s / Q))
      (derivWithin f (Iic t) t * Q⁻¹) (Iic 0) 0 :=
    hf.hasDerivWithinAt.comp_of_eq 0 htime.hasDerivWithinAt hmaps (by simp)
  have hh := (hd.const_mul Q⁻¹).derivWithin (uniqueDiffWithinAt_Iic (0 : ℝ))
  calc
    _ = Q⁻¹ * (derivWithin f (Iic t) t * Q⁻¹) := hh
    _ = _ := by ring

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
