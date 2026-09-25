import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis.ODE

theorem inv_sub_inv_le_mul_sub_of_deriv_le_sq
    {f : ℝ → ℝ} {a b A B C : ℝ}
    (hab : a ≤ b) (hA : 0 < A) (hAB : A < B)
    (hf : ContinuousOn f (Icc a b)) (ha : f a ≤ A) (hb : B ≤ f b)
    (hderiv : ∀ t ∈ Ioo a b, A < f t →
      DifferentiableAt ℝ f t ∧ deriv f t ≤ C * f t ^ 2) :
    A⁻¹ - B⁻¹ ≤ C * (b - a) := by
  let K : Set ℝ := Icc a b ∩ f ⁻¹' {A}
  have hKclosed : IsClosed K :=
    hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hKcompact : IsCompact K :=
    isCompact_Icc.of_isClosed_subset hKclosed inter_subset_left
  have hKnonempty : K.Nonempty := by
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf ⟨ha, hAB.le.trans hb⟩
    exact ⟨t, ht, hft⟩
  obtain ⟨c, hc, hmax⟩ := hKcompact.exists_isMaxOn hKnonempty continuousOn_id
  have hfc : f c = A := hc.2
  have hcb : c < b := lt_of_le_of_ne hc.1.2 (fun h => by
    have : f b = A := h ▸ hfc
    linarith)
  have hhigh : ∀ t ∈ Ioc c b, A < f t := by
    intro t ht
    by_contra h
    have hft : f t ≤ A := le_of_not_gt h
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc ht.2
      (hf.mono (Icc_subset_Icc (hc.1.1.trans ht.1.le) le_rfl))
      ⟨hft, hAB.le.trans hb⟩
    have hsK : s ∈ K := ⟨⟨(hc.1.1.trans ht.1.le).trans hs.1, hs.2⟩, hfs⟩
    have hsc : s ≤ c := hmax hsK
    linarith [hs.1, ht.1]
  have hpos : ∀ t ∈ Icc c b, 0 < f t := by
    intro t ht
    rcases ht.1.eq_or_lt with hct | hct
    · simpa only [← hct, hfc] using hA
    · exact hA.trans (hhigh t ⟨hct, ht.2⟩)
  have hcont : ContinuousOn (fun t => (f t)⁻¹) (Icc c b) :=
    (hf.mono (Icc_subset_Icc hc.1.1 le_rfl)).inv₀ (fun t ht => (hpos t ht).ne')
  have hdiff : ∀ t ∈ Ioo c b,
      HasDerivAt (fun s => (f s)⁻¹) (-(deriv f t) / f t ^ 2) t := by
    intro t ht
    exact (hderiv t ⟨hc.1.1.trans_lt ht.1, ht.2⟩
      (hhigh t ⟨ht.1, ht.2.le⟩)).1.hasDerivAt.inv (hpos t ⟨ht.1.le, ht.2.le⟩).ne'
  have hbound : ∀ t ∈ interior (Icc c b),
      -C ≤ deriv (fun s => (f s)⁻¹) t := by
    intro t ht
    rw [interior_Icc] at ht
    rw [(hdiff t ht).deriv]
    apply (le_div_iff₀ (sq_pos_of_pos (hpos t ⟨ht.1.le, ht.2.le⟩))).mpr
    have h := (hderiv t ⟨hc.1.1.trans_lt ht.1, ht.2⟩
      (hhigh t ⟨ht.1, ht.2.le⟩)).2
    nlinarith
  have hdrop := (convex_Icc c b).mul_sub_le_image_sub_of_le_deriv hcont
    (fun t ht => by
      rw [interior_Icc] at ht
      exact (hdiff t ht).differentiableAt.differentiableWithinAt)
    hbound c ⟨le_rfl, hcb.le⟩ b ⟨hcb.le, le_rfl⟩ hcb.le
  have hinv : (f b)⁻¹ ≤ B⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (hA.trans hAB) hb
  rw [hfc] at hdrop
  have hgap : B⁻¹ < A⁻¹ := by
    simpa only [one_div] using one_div_lt_one_div_of_lt hA hAB
  have hC : 0 ≤ C := by
    by_contra h
    have hprod : C * (b - c) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) (sub_pos.mpr hcb).le
    nlinarith
  have htime : C * (b - c) ≤ C * (b - a) :=
    mul_le_mul_of_nonneg_left (by linarith [hc.1.1]) hC
  linarith

theorem inv_le_mul_sub_of_unbounded_sequence
    {f : ℝ → ℝ} {a b A C : ℝ} {time : ℕ → ℝ}
    (hA : 0 < A) (hC : 0 ≤ C)
    (hf : ContinuousOn f (Ico a b)) (ha : f a ≤ A)
    (hderiv : ∀ t ∈ Ioo a b, A < f t →
      DifferentiableAt ℝ f t ∧ deriv f t ≤ C * f t ^ 2)
    (htime : ∀ n, time n ∈ Ico a b)
    (hblow : Tendsto (fun n => f (time n)) atTop atTop) :
    A⁻¹ ≤ C * (b - a) := by
  have hinv : Tendsto (fun n => (f (time n))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hblow
  have hbound : ∀ᶠ n in atTop, A⁻¹ - (f (time n))⁻¹ ≤ C * (b - a) := by
    filter_upwards [hblow.eventually (eventually_gt_atTop A)] with n hn
    have hsub : Icc a (time n) ⊆ Ico a b :=
      fun s hs => ⟨hs.1, hs.2.trans_lt (htime n).2⟩
    exact (inv_sub_inv_le_mul_sub_of_deriv_le_sq (htime n).1 hA hn
      (hf.mono hsub) ha le_rfl (fun t ht hAt =>
        hderiv t ⟨ht.1, ht.2.trans (htime n).2⟩ hAt)).trans
      (mul_le_mul_of_nonneg_left (by linarith [(htime n).2]) hC)
  simpa only [sub_zero] using le_of_tendsto ((tendsto_const_nhds (x := A⁻¹)).sub hinv) hbound

end DifferentialGeometry.Analysis.ODE
