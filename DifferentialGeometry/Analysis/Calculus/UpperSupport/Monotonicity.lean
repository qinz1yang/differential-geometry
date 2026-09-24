import Mathlib.Analysis.Calculus.MeanValue

namespace DifferentialGeometry

open Set Filter
open scoped _root_.Topology

theorem image_le_of_deriv_upper_support
    {f B B' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (ha : f a ≤ B a)
    (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ t ∈ Ico a b, HasDerivWithinAt B (B' t) (Ici t) t)
    (hsupport : ∀ t ∈ Ico a b,
      ∃ phi : ℝ → ℝ, ∃ d : ℝ,
        phi t = f t ∧ f ≤ᶠ[𝓝[>] t] phi ∧
        HasDerivAt phi d t ∧ d ≤ B' t) :
    ∀ t ∈ Icc a b, f t ≤ B t := by
  intro x hx
  refine image_le_of_liminf_slope_right_le_deriv_boundary hf ha hB hB' ?_ hx
  intro t ht r hr
  obtain ⟨phi, d, heq, hupper, hderiv, hd⟩ := hsupport t ht
  have hslope : ∀ᶠ z in 𝓝[>] t, slope phi t z < r :=
    (hderiv.tendsto_slope.mono_left (nhdsGT_le_nhdsNE t)).eventually_lt_const
      (hd.trans_lt hr)
  have hbound : ∀ᶠ z in 𝓝[>] t, slope f t z < r := by
    filter_upwards [hupper, hslope, self_mem_nhdsWithin] with z hz hs htz
    have hle : slope f t z ≤ slope phi t z := by
      rw [slope_def_field, slope_def_field, heq]
      exact div_le_div_of_nonneg_right (sub_le_sub_right hz _) (sub_pos.mpr htz).le
    exact hle.trans_lt hs
  exact hbound.frequently

theorem antitoneOn_of_deriv_upper_support_nonpos
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hsupport : ∀ t ∈ Ico a b,
      ∃ phi : ℝ → ℝ, ∃ d : ℝ,
        phi t = f t ∧ f ≤ᶠ[𝓝[>] t] phi ∧
        HasDerivAt phi d t ∧ d ≤ 0) :
    AntitoneOn f (Icc a b) := by
  intro x hx y hy hxy
  refine image_le_of_deriv_upper_support
    (f := f) (B := fun _ ↦ f x) (B' := fun _ ↦ 0)
    (hf.mono (Icc_subset_Icc hx.1 hy.2)) le_rfl continuousOn_const
    (fun t _ ↦ (hasDerivAt_const t (f x)).hasDerivWithinAt) ?_ y ⟨hxy, le_rfl⟩
  intro t ht
  exact hsupport t ⟨hx.1.trans ht.1, ht.2.trans_le hy.2⟩

theorem monotoneOn_of_deriv_upper_support_nonneg
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hsupport : ∀ t ∈ Ioc a b,
      ∃ phi : ℝ → ℝ, ∃ d : ℝ,
        phi t = f t ∧ f ≤ᶠ[𝓝[<] t] phi ∧
        HasDerivAt phi d t ∧ 0 ≤ d) :
    MonotoneOn f (Icc a b) := by
  have hfneg : ContinuousOn (fun t ↦ f (-t)) (Icc (-b) (-a)) := by
    apply hf.comp continuous_neg.continuousOn
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hanti : AntitoneOn (fun t ↦ f (-t)) (Icc (-b) (-a)) := by
    apply antitoneOn_of_deriv_upper_support_nonpos hfneg
    intro t ht
    have hmem : -t ∈ Ioc a b := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    obtain ⟨phi, d, heq, hupper, hderiv, hd⟩ := hsupport (-t) hmem
    have hneg : Tendsto (fun z : ℝ ↦ -z) (𝓝[>] t) (𝓝[<] (-t)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact continuous_neg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact neg_lt_neg (show t < z from hz)
    refine ⟨fun z ↦ phi (-z), -d, heq, hneg.eventually hupper, ?_, neg_nonpos.mpr hd⟩
    simpa only [Function.comp_def, mul_neg, mul_one] using
      hderiv.comp t (hasDerivAt_neg t)
  intro x hx y hy hxy
  have hnx : -x ∈ Icc (-b) (-a) := ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩
  have hny : -y ∈ Icc (-b) (-a) := ⟨neg_le_neg hy.2, neg_le_neg hy.1⟩
  simpa only [neg_neg] using hanti hny hnx (neg_le_neg hxy)

end DifferentialGeometry
