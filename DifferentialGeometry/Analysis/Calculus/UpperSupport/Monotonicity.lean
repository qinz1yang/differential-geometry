import Mathlib.Analysis.Calculus.MeanValue

namespace DifferentialGeometry

open Set Filter
open scoped _root_.Topology

theorem image_le_of_deriv_upper_support_le_add_pos
    {f B B' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (ha : f a ≤ B a)
    (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ t ∈ Ico a b, HasDerivWithinAt B (B' t) (Ici t) t)
    (hsupport : ∀ t ∈ Ico a b, ∀ ε : ℝ, 0 < ε →
      ∃ phi : ℝ → ℝ, ∃ d : ℝ,
        phi t = f t ∧ f ≤ᶠ[𝓝[>] t] phi ∧
        HasDerivWithinAt phi d (Ioi t) t ∧ d ≤ B' t + ε) :
    ∀ t ∈ Icc a b, f t ≤ B t := by
  intro x hx
  refine image_le_of_liminf_slope_right_le_deriv_boundary hf ha hB hB' ?_ hx
  intro t ht r hr
  obtain ⟨phi, d, heq, hupper, hderiv, hd⟩ :=
    hsupport t ht ((r - B' t) / 2) (by linarith)
  have hdr : d < r := by linarith
  have hslope : ∀ᶠ z in 𝓝[>] t, slope phi t z < r :=
    ((hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).mp hderiv).eventually_lt_const hdr
  have hbound : ∀ᶠ z in 𝓝[>] t, slope f t z < r := by
    filter_upwards [hupper, hslope, self_mem_nhdsWithin] with z hz hs htz
    have hle : slope f t z ≤ slope phi t z := by
      rw [slope_def_field, slope_def_field, heq]
      exact div_le_div_of_nonneg_right (sub_le_sub_right hz _) (sub_pos.mpr htz).le
    exact hle.trans_lt hs
  exact hbound.frequently

theorem antitoneOn_Ioc_of_deriv_upper_support_le_pos
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Ioc a b))
    (hsupport : ∀ t ∈ Ioo a b, ∀ ε : ℝ, 0 < ε →
      ∃ phi : ℝ → ℝ, ∃ d : ℝ,
        phi t = f t ∧ f ≤ᶠ[𝓝[>] t] phi ∧
        HasDerivWithinAt phi d (Ioi t) t ∧ d ≤ ε) :
    AntitoneOn f (Ioc a b) := by
  intro x hx y hy hxy
  refine image_le_of_deriv_upper_support_le_add_pos
    (f := f) (B := fun _ ↦ f x) (B' := fun _ ↦ 0)
    (hf.mono (fun _ ht ↦ ⟨hx.1.trans_le ht.1, ht.2.trans hy.2⟩))
    le_rfl continuousOn_const
    (fun t _ ↦ (hasDerivAt_const t (f x)).hasDerivWithinAt) ?_ y ⟨hxy, le_rfl⟩
  intro t ht ε hε
  simpa only [zero_add] using
    hsupport t ⟨hx.1.trans_le ht.1, ht.2.trans_le hy.2⟩ ε hε

theorem antitoneOn_of_deriv_upper_support_le_pos
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hsupport : ∀ t ∈ Ioo a b, ∀ ε : ℝ, 0 < ε →
      ∃ phi : ℝ → ℝ, ∃ d : ℝ,
        phi t = f t ∧ f ≤ᶠ[𝓝[>] t] phi ∧
        HasDerivWithinAt phi d (Ioi t) t ∧ d ≤ ε) :
    AntitoneOn f (Icc a b) := by
  have hanti := antitoneOn_Ioc_of_deriv_upper_support_le_pos
    (hf.mono Ioc_subset_Icc_self) hsupport
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | hxy
  · exact le_rfl
  have hlim : Tendsto f (𝓝[>] x) (𝓝 (f x)) :=
    (hf x hx).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGT_of_mem ⟨hx.1, hxy.trans_le hy.2⟩)
  apply ge_of_tendsto hlim
  filter_upwards [Ioc_mem_nhdsGT hxy] with z hz
  exact hanti ⟨hx.1.trans_lt hz.1, hz.2.trans hy.2⟩
    ⟨hx.1.trans_lt hxy, hy.2⟩ hz.2

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
  apply image_le_of_deriv_upper_support_le_add_pos hf ha hB hB'
  intro t ht ε hε
  obtain ⟨phi, d, heq, hupper, hderiv, hd⟩ := hsupport t ht
  exact ⟨phi, d, heq, hupper, hderiv.hasDerivWithinAt,
    hd.trans (le_add_of_nonneg_right hε.le)⟩

theorem antitoneOn_of_deriv_upper_support_nonpos
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hsupport : ∀ t ∈ Ico a b,
      ∃ phi : ℝ → ℝ, ∃ d : ℝ,
        phi t = f t ∧ f ≤ᶠ[𝓝[>] t] phi ∧
        HasDerivAt phi d t ∧ d ≤ 0) :
    AntitoneOn f (Icc a b) := by
  apply antitoneOn_of_deriv_upper_support_le_pos hf
  intro t ht ε hε
  obtain ⟨phi, d, heq, hupper, hderiv, hd⟩ := hsupport t ⟨ht.1.le, ht.2⟩
  exact ⟨phi, d, heq, hupper, hderiv.hasDerivWithinAt, hd.trans hε.le⟩

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
