import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

open Filter Set
open scoped Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem HasDerivWithinAt.norm_le_of_eventually_norm_deriv_le
    {f : ℝ → F} {f' : F} {g : ℝ → ℝ} {b : ℝ}
    (hf : HasDerivWithinAt f f' (Iic b) b)
    (hdiff : ∀ᶠ t in 𝓝[<] b, DifferentiableAt ℝ f t)
    (hg : ContinuousWithinAt g (Iio b) b)
    (hbound : ∀ᶠ t in 𝓝[<] b, ‖_root_.deriv f t‖ ≤ g t) :
    ‖f'‖ ≤ g b := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro C hC
  have hbnd : ∀ᶠ t in 𝓝[<] b, DifferentiableAt ℝ f t ∧ ‖_root_.deriv f t‖ ≤ C := by
    filter_upwards [hdiff, hbound, hg.eventually (gt_mem_nhds hC)] with t ht ht' htC
    exact ⟨ht, ht'.trans htC.le⟩
  obtain ⟨a, hab, ha⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hbnd
  have hlim : Tendsto (slope f b) (𝓝[<] b) (𝓝 f') :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : b ∉ Iio b)).mp
      (hf.mono Iio_subset_Iic_self)
  apply le_of_tendsto hlim.norm
  filter_upwards [Ioo_mem_nhdsLT hab] with r hr
  have hcont : ContinuousOn f (Icc r b) := by
    intro s hs
    rcases hs.2.eq_or_lt with hsb | hsb
    · subst s
      exact hf.continuousWithinAt.mono (fun _ hu => hu.2)
    · exact (ha ⟨hr.1.trans_le hs.1, hsb⟩).1.continuousAt.continuousWithinAt
  have hmv := norm_image_sub_le_of_norm_deriv_right_le_segment hcont
    (fun s hs => (ha ⟨hr.1.trans_le hs.1, hs.2⟩).1.hasDerivAt.hasDerivWithinAt)
    (fun s hs => (ha ⟨hr.1.trans_le hs.1, hs.2⟩).2)
    b ⟨hr.2.le, le_rfl⟩
  rw [slope_def_module, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_neg (sub_neg.mpr hr.2), neg_sub, norm_sub_rev,
    mul_comm, ← div_eq_mul_inv]
  exact (div_le_iff₀ (sub_pos.mpr hr.2)).mpr hmv

theorem HasDerivAt.norm_le_of_eventually_norm_deriv_le
    {f : ℝ → F} {f' : F} {g : ℝ → ℝ} {b : ℝ}
    (hf : HasDerivAt f f' b)
    (hdiff : ∀ᶠ t in 𝓝[<] b, DifferentiableAt ℝ f t)
    (hg : ContinuousWithinAt g (Iio b) b)
    (hbound : ∀ᶠ t in 𝓝[<] b, ‖_root_.deriv f t‖ ≤ g t) :
    ‖f'‖ ≤ g b :=
  hf.hasDerivWithinAt.norm_le_of_eventually_norm_deriv_le hdiff hg hbound

namespace DifferentialGeometry.Analysis

theorem norm_deriv_le_of_finite_exception
    {f : ℝ → F} {g : ℝ → ℝ} {s E : Set ℝ} (hs : IsOpen s) (hE : E.Finite)
    (hdiff : ∀ t ∈ s, DifferentiableAt ℝ f t) (hg : ContinuousOn g s)
    (hbound : ∀ t ∈ s, t ∉ E → ‖deriv f t‖ ≤ g t) :
    ∀ t ∈ s, ‖deriv f t‖ ≤ g t := by
  intro t ht
  have hs' : ∀ᶠ r in 𝓝[<] t, r ∈ s :=
    mem_nhdsWithin_of_mem_nhds (hs.mem_nhds ht)
  have hE' : ∀ᶠ r in 𝓝[<] t, r ∉ E :=
    ((nhdsLT_le_nhdsNE t).trans (nhdsNE_le_cofinite t)) hE.compl_mem_cofinite
  apply (hdiff t ht).hasDerivAt.norm_le_of_eventually_norm_deriv_le
  · exact hs'.mono fun r hr => hdiff r hr
  · exact ((hg t ht).continuousAt (hs.mem_nhds ht)).continuousWithinAt
  · filter_upwards [hs', hE'] with r hr hrE
    exact hbound r hr hrE

theorem abs_deriv_le_quadratic_of_finite_exception
    {f : ℝ → ℝ} {a b C q : ℝ} {E : Set ℝ} (hE : E.Finite)
    (hdiff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hbound : ∀ t ∈ Ioo a b, t ∉ E → q < f t → |deriv f t| ≤ C * (f t) ^ 2) :
    ∀ t ∈ Ioo a b, q < f t → |deriv f t| ≤ C * (f t) ^ 2 := by
  intro t ht hqt
  have hs : ∀ᶠ r in 𝓝[<] t, r ∈ Ioo a b :=
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds ht.1 ht.2)
  have hE' : ∀ᶠ r in 𝓝[<] t, r ∉ E :=
    ((nhdsLT_le_nhdsNE t).trans (nhdsNE_le_cofinite t)) hE.compl_mem_cofinite
  have hq : ∀ᶠ r in 𝓝[<] t, q < f r :=
    ((hdiff t ht).continuousAt.eventually (lt_mem_nhds hqt)).filter_mono nhdsWithin_le_nhds
  have hg : ContinuousAt (fun r => C * (f r) ^ 2) t :=
    continuousAt_const.mul ((hdiff t ht).continuousAt.pow 2)
  have hb : ∀ᶠ r in 𝓝[<] t, ‖deriv f r‖ ≤ C * (f r) ^ 2 := by
    filter_upwards [hs, hE', hq] with r hr hrE hqr
    simpa only [Real.norm_eq_abs] using hbound r hr hrE hqr
  simpa only [Real.norm_eq_abs] using
    (hdiff t ht).hasDerivAt.norm_le_of_eventually_norm_deriv_le
      (hs.mono fun r hr => hdiff r hr) hg.continuousWithinAt hb

end DifferentialGeometry.Analysis
