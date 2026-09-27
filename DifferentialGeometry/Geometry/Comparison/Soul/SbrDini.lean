import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace DifferentialGeometry.Geometry.Topology

theorem eventually_right_slope_lt_of_upper_support
    {f phi : ℝ → ℝ} {t d : ℝ}
    (hphi : HasDerivWithinAt phi d (Ici t) t)
    (hcontact : phi t = f t)
    (hupper : ∀ᶠ s in 𝓝[>] t, f s ≤ phi s)
    {r : ℝ} (hr : d < r) :
    ∀ᶠ s in 𝓝[>] t, slope f t s < r := by
  have hder := hphi.Ioi_of_Ici.limsup_slope_le' (lt_irrefl t) hr
  filter_upwards [hupper, hder, self_mem_nhdsWithin] with s hu hd hs
  have hts : t < s := hs
  rw [slope_def_field] at hd ⊢
  rw [← hcontact]
  exact lt_of_le_of_lt
    (div_le_div_of_nonneg_right (sub_le_sub_right hu (phi t))
      (sub_pos.mpr hts).le) hd

theorem image_le_affine_of_upper_right_slope_le
    {f : ℝ → ℝ} {a b c : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hbound : ∀ t ∈ Ico a b, ∀ r : ℝ, c < r →
      ∀ᶠ s in 𝓝[>] t, slope f t s < r) :
    ∀ x ∈ Icc a b, f x ≤ f a + c * (x - a) := by
  have hB : ∀ t : ℝ,
      HasDerivAt (fun x : ℝ => f a + c * (x - a)) c t := by
    intro t
    convert! (((hasDerivAt_id t).sub_const a).const_mul c).const_add (f a) using 1
    simp only [mul_one]
  intro x hx
  exact image_le_of_liminf_slope_right_le_deriv_boundary hf
    (B := fun x : ℝ => f a + c * (x - a)) (B' := fun _ : ℝ => c)
    (by simp) (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt)
    (fun t ht r hr => (hbound t ht r hr).frequently) hx

theorem antitoneOn_of_upper_right_slope_nonpos
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hbound : ∀ t ∈ Ico a b, ∀ r : ℝ, 0 < r →
      ∀ᶠ s in 𝓝[>] t, slope f t s < r) :
    AntitoneOn f (Icc a b) := by
  intro x hx y hy hxy
  have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  have hlocal : ∀ t ∈ Ico x y, ∀ r : ℝ, 0 < r →
      ∀ᶠ s in 𝓝[>] t, slope f t s < r := by
    intro t ht r hr
    exact hbound t ⟨hx.1.trans ht.1, ht.2.trans_le hy.2⟩ r hr
  simpa only [zero_mul, add_zero] using
    image_le_affine_of_upper_right_slope_le (c := 0) (hf.mono hsub)
      hlocal y ⟨hxy, le_rfl⟩

end DifferentialGeometry.Geometry.Topology
