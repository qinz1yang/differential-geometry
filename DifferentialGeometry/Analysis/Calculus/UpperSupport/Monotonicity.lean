import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Semicontinuity.Basic

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

open Set Filter
open scoped Topology

namespace DifferentialGeometry

theorem le_initial_of_lowerSemicontinuousOn_of_liminf_slope_right_nonpos
    {f : ℝ → ℝ} {a b c : ℝ}
    (hf : LowerSemicontinuousOn f (Icc a b)) (ha : f a < c)
    (hslope : ∀ t ∈ Ico a b, f t < c → ∀ ε : ℝ, 0 < ε →
      ∃ᶠ z in 𝓝[>] t, slope f t z < ε) :
    ∀ t ∈ Icc a b, f t ≤ f a := by
  intro t ht
  have hab : a ≤ b := ht.1.trans ht.2
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  let L := b - a + 1
  have hL : 0 < L := by dsimp [L]; linarith
  let ε := min (δ / L) ((c - f a) / (2 * L))
  have hε : 0 < ε := lt_min (div_pos hδ hL) (div_pos (sub_pos.mpr ha) (by positivity))
  have hεδ : ε * L ≤ δ := (le_div_iff₀ hL).mp (min_le_left _ _)
  have hεc : ε * L ≤ (c - f a) / 2 := by
    have hh := (le_div_iff₀ (show 0 < 2 * L by positivity)).mp (min_le_right (δ / L) ((c - f a) / (2 * L)))
    change ε * (2 * L) ≤ c - f a at hh
    nlinarith
  let B := fun x : ℝ => f a + ε * (x - a)
  let s := {x : ℝ | f x ≤ B x}
  have hB : ContinuousOn B (Icc a b) := by dsimp [B]; fun_prop
  have hclosed : IsClosed (s ∩ Icc a b) := by
    have hsub : LowerSemicontinuousOn (fun x => f x - B x) (Icc a b) := by
      simpa only [sub_eq_add_neg, Pi.neg_apply] using hf.add hB.neg.lowerSemicontinuousOn
    have hh := (hsub.isCompact_inter_preimage_Iic isCompact_Icc 0).isClosed
    convert hh using 1
    ext x
    simp only [s, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_Iic, sub_nonpos]
    exact and_comm
  have hinitial : a ∈ s := by simp only [s, mem_ofPred_eq, B, sub_self, mul_zero, add_zero, le_refl]
  have hall : Icc a b ⊆ s := by
    apply hclosed.Icc_subset_of_forall_exists_gt hinitial
    rintro x ⟨hx, hxab⟩ y hxy
    have hxB : f x ≤ B x := hx
    have hxL : x - a ≤ L := by dsimp [L]; linarith [hxab.2]
    have hnegative : f x < c := by
      have hh := mul_le_mul_of_nonneg_left hxL hε.le
      dsimp only [B] at hxB
      linarith
    obtain ⟨z, hz, hzy⟩ := ((hslope x hxab hnegative ε hε).and_eventually
      (Ioc_mem_nhdsGT hxy)).exists
    refine ⟨z, ?_, hzy⟩
    have hzbound : f z - f x < ε * (z - x) := by
      rw [slope_def_field] at hz
      exact (div_lt_iff₀ (sub_pos.mpr hzy.1)).mp hz
    change f z ≤ B z
    dsimp only [B] at hxB ⊢
    nlinarith
  have hh := hall ht
  have htL : t - a ≤ L := by dsimp [L]; linarith [ht.2]
  have hterm := (mul_le_mul_of_nonneg_left htL hε.le).trans hεδ
  change f t ≤ B t at hh
  dsimp only [B] at hh
  linarith


theorem le_initial_of_lowerSemicontinuousOn_of_upper_support
    {f : ℝ → ℝ} {a b c : ℝ}
    (hf : LowerSemicontinuousOn f (Icc a b)) (ha : f a < c)
    (hsupport : ∀ t ∈ Ico a b, f t < c → ∀ ε : ℝ, 0 < ε →
      ∃ φ : ℝ → ℝ, ∃ d : ℝ,
        φ t = f t ∧ f ≤ᶠ[𝓝[>] t] φ ∧ HasDerivAt φ d t ∧ d ≤ ε) :
    ∀ t ∈ Icc a b, f t ≤ f a := by
  apply le_initial_of_lowerSemicontinuousOn_of_liminf_slope_right_nonpos hf ha
  intro t ht htc ε hε
  obtain ⟨φ, d, hφ, hupper, hderiv, hd⟩ := hsupport t ht htc (ε / 2) (by linarith)
  have hds : d < ε := lt_of_le_of_lt hd (by linarith)
  have hslope : ∀ᶠ z in 𝓝[>] t, slope φ t z < ε :=
    (hderiv.tendsto_slope.mono_left (nhdsGT_le_nhdsNE t)).eventually_lt_const hds
  apply Filter.Eventually.frequently
  filter_upwards [hupper, hslope, self_mem_nhdsWithin] with z hz hzs hzt
  have hle : slope f t z ≤ slope φ t z := by
    rw [slope_def_field, slope_def_field, hφ]
    exact div_le_div_of_nonneg_right (sub_le_sub_right hz _) (sub_pos.mpr hzt).le
  exact hle.trans_lt hzs

end DifferentialGeometry
