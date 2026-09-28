import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.OrderClosed

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

open Set Filter
open scoped Topology

theorem exists_tendsto_nhdsLT_of_bounded_deriv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f f' : ℝ → F} {a b C : ℝ} (hab : a < b)
    (hderiv : ∀ s : ℝ, s ∈ Set.Ioo a b → HasDerivAt f (f' s) s)
    (hbound : ∀ s : ℝ, s ∈ Set.Ioo a b → ‖f' s‖ ≤ C) :
    ∃ L : F, Tendsto f (𝓝[<] b) (𝓝 L) := by
  have hNB : (𝓝[<] b).NeBot := nhdsWithin_Iio_neBot (le_refl b)
  suffices hcauchy : Cauchy (Filter.map f (𝓝[<] b)) by
    exact cauchy_map_iff_exists_tendsto.mp hcauchy
  refine Metric.cauchy_iff.mpr ⟨Filter.map_neBot, ?_⟩
  have hC_nn : 0 ≤ C := by
    have hmid : (a + b) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
    exact le_trans (norm_nonneg _) (hbound _ hmid)
  intro ε hε
  have hCC_pos : 0 < C + 1 := by linarith
  set η : ℝ := ε / (C + 1) with hη_def
  have hη_pos : 0 < η := div_pos hε hCC_pos
  set lo : ℝ := max a (b - η) with hlo_def
  have hlo_lt_b : lo < b := max_lt hab (by linarith)
  have ha_le_lo : a ≤ lo := le_max_left _ _
  have hsub : Set.Ioo lo b ⊆ Set.Ioo a b :=
    fun τ hτ => ⟨lt_of_le_of_lt ha_le_lo hτ.1, hτ.2⟩
  have hIoo_mem : f '' Set.Ioo lo b ∈ Filter.map f (𝓝[<] b) :=
    Filter.image_mem_map (Ioo_mem_nhdsLT hlo_lt_b)
  refine ⟨f '' Set.Ioo lo b, hIoo_mem, ?_⟩
  rintro x ⟨sx, hsx, rfl⟩ y ⟨sy, hsy, rfl⟩
  set s : ℝ := min sx sy with hs_def
  set t : ℝ := max sx sy with ht_def
  have hst : s ≤ t := min_le_max
  have ht_hi : t < b := max_lt hsx.2 hsy.2
  have hs_lo : lo < s := lt_min hsx.1 hsy.1
  have ht_sub_s_lt : t - s < η := by
    have hlo_ge : b - η ≤ lo := le_max_right _ _
    rcases le_total sx sy with h | h
    · rw [hs_def, ht_def, min_eq_left h, max_eq_right h]; linarith [hsy.2, hsx.1]
    · rw [hs_def, ht_def, min_eq_right h, max_eq_left h]; linarith [hsx.2, hsy.1]
  have hmvt : ‖f t - f s‖ ≤ C * (t - s) := by
    have hIcc_sub : Set.Icc s t ⊆ Set.Ioo a b := by
      intro τ hτ
      exact hsub ⟨lt_of_lt_of_le hs_lo hτ.1, lt_of_le_of_lt hτ.2 ht_hi⟩
    have hderivW : ∀ x ∈ Set.Icc s t, HasDerivWithinAt f (f' x) (Set.Icc s t) x :=
      fun x hx => (hderiv x (hIcc_sub hx)).hasDerivWithinAt
    have hboundW : ∀ x ∈ Set.Ico s t, ‖f' x‖ ≤ C :=
      fun x hx => hbound x (hIcc_sub (Set.Ico_subset_Icc_self hx))
    exact norm_image_sub_le_of_norm_deriv_le_segment' hderivW hboundW t
      (right_mem_Icc.mpr hst)
  have h_dist_eq : dist (f sx) (f sy) = ‖f t - f s‖ := by
    rcases le_total sx sy with h | h
    · rw [hs_def, ht_def, min_eq_left h, max_eq_right h, dist_eq_norm, norm_sub_rev]
    · rw [hs_def, ht_def, min_eq_right h, max_eq_left h, dist_eq_norm]
  rw [h_dist_eq]
  calc ‖f t - f s‖ ≤ C * (t - s) := hmvt
    _ ≤ C * η := mul_le_mul_of_nonneg_left ht_sub_s_lt.le hC_nn
    _ < ε := by
        rw [hη_def]
        have hrw : C * (ε / (C + 1)) = ε * (C / (C + 1)) := by ring
        rw [hrw]
        have hfrac : C / (C + 1) < 1 := by rw [div_lt_one hCC_pos]; linarith
        have := mul_lt_mul_of_pos_left hfrac hε
        rwa [mul_one] at this

end DifferentialGeometry.Analysis
