import DifferentialGeometry.Analysis.ODE.Gronwall.Integral

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace DifferentialGeometry.Analysis.ODE

theorem eq_zero_of_nonneg_of_le_mul_integral
    {a b K : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hint : IntervalIntegrable f volume a b)
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hbound : ∀ t ∈ Icc a b, f t ≤ K * ∫ s in a..t, f s) :
    ∀ t ∈ Icc a b, f t = 0 := by
  let F : ℝ → ℝ := fun t => ∫ s in a..t, f s
  let k : ℝ := max K 0
  have hk : 0 ≤ k := le_max_right _ _
  have hFcont : ContinuousOn F (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      intervalIntegral.continuousOn_primitive_interval' hint (left_mem_uIcc : a ∈ uIcc a b)
  have hFnonneg (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ F t :=
    intervalIntegral.integral_nonneg ht.1 fun s hs => hnonneg s ⟨hs.1, hs.2.trans ht.2⟩
  have hfbound (t : ℝ) (ht : t ∈ Icc a b) : f t ≤ k * F t :=
    (hbound t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hFnonneg t ht))
  have hFbound (t : ℝ) (ht : t ∈ Icc a b) : F t ≤ k * ∫ s in a..t, F s := by
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
    have hfint : IntervalIntegrable f volume a t := hint.mono_set (by
      simpa only [uIcc_of_le ht.1, uIcc_of_le hab] using hsub)
    have hFintOn : IntegrableOn F (uIcc a t) volume := by
      rw [uIcc_of_le ht.1]
      exact (hFcont.mono hsub).integrableOn_Icc
    have hFint : IntervalIntegrable F volume a t := hFintOn.intervalIntegrable
    have h := intervalIntegral.integral_mono_on ht.1 hfint (hFint.const_mul k)
      (fun s hs => hfbound s (hsub hs))
    rwa [intervalIntegral.integral_const_mul] at h
  have hshiftcont : ContinuousOn (fun t => F (a + t)) (Icc 0 (b - a)) :=
    hFcont.comp (continuous_const.add continuous_id).continuousOn (by
      intro t ht
      constructor <;> linarith [ht.1, ht.2])
  have hshiftbound : ∀ t ∈ Icc 0 (b - a),
      F (a + t) ≤ (0 : ℝ) + k * ∫ s in (0 : ℝ)..t, F (a + s) := by
    intro t ht
    rw [zero_add, intervalIntegral.integral_comp_add_left, add_zero]
    exact hFbound (a + t) (by constructor <;> linarith [ht.1, ht.2])
  have hgr := gronwall_integral_le (sub_nonneg.mpr hab) hk hshiftcont hshiftbound
  intro t ht
  have hFle : F t ≤ 0 := by
    have h := hgr (t - a) (by constructor <;> linarith [ht.1, ht.2])
    simpa only [add_sub_cancel, zero_mul] using h
  have hFzero : F t = 0 := le_antisymm hFle (hFnonneg t ht)
  have hf := hfbound t ht
  rw [hFzero, mul_zero] at hf
  exact le_antisymm hf (hnonneg t ht)

open Filter in
theorem eq_zero_of_nonneg_of_sub_le_mul_integral_of_tendsto
    {a b K : ℝ} {f : ℝ → ℝ} (hK : 0 ≤ K)
    (hnonneg : ∀ t ∈ Ioo a b, 0 ≤ f t)
    (hint : ∀ c ∈ Ioo a b, IntervalIntegrable f volume a c)
    (htend : Tendsto f (𝓝[>] a) (𝓝 0))
    (hbound : ∀ s ∈ Ioo a b, ∀ t ∈ Ico s b,
      f t - f s ≤ K * ∫ u in s..t, f u) :
    ∀ t ∈ Ioo a b, f t = 0 := by
  have hbound₀ : ∀ t ∈ Ioo a b, f t ≤ K * ∫ u in a..t, f u := by
    intro t ht
    have hev : ∀ᶠ s in 𝓝[>] a, f t ≤ f s + K * ∫ u in a..t, f u := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds ht.1)] with s hsa hst
      have hi := hbound s ⟨hsa, hst.trans ht.2⟩ t ⟨hst.le, ht.2⟩
      have hm : (∫ u in s..t, f u) ≤ ∫ u in a..t, f u := by
        apply intervalIntegral.integral_mono_interval hsa.le hst.le le_rfl
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
          exact hnonneg u ⟨hu.1, hu.2.trans_lt ht.2⟩
        · exact hint t ht
      have hmK := mul_le_mul_of_nonneg_left hm hK
      linarith
    have hlimit := htend.add_const (K * ∫ u in a..t, f u)
    simpa only [zero_add] using ge_of_tendsto hlimit hev
  intro t ht
  let F : ℝ → ℝ := fun s => if s = a then 0 else f s
  have hFint : IntervalIntegrable F volume a t := by
    apply (hint t ht).congr
    intro s hs
    rw [uIoc_of_le ht.1.le] at hs
    simp only [F, ite_eq_right (ne_of_gt hs.1)]
  have hFeq (s : ℝ) (hs : a ≤ s) : (∫ u in a..s, F u) = ∫ u in a..s, f u := by
    apply intervalIntegral.integral_congr_ae'
    · filter_upwards [] with u hu
      simp only [F, ite_eq_right (ne_of_gt hu.1)]
    · filter_upwards [] with u hu
      exact False.elim (not_lt_of_ge (hu.2.trans hs) hu.1)
  have hFzero := eq_zero_of_nonneg_of_le_mul_integral ht.1.le hFint
    (fun s hs => by
      by_cases hsa : s = a
      · simp only [F, ite_eq_left hsa, le_refl]
      · simpa only [F, ite_eq_right hsa] using hnonneg s ⟨lt_of_le_of_ne hs.1 (Ne.symm hsa), hs.2.trans_lt ht.2⟩)
    (fun s hs => by
      rw [hFeq s hs.1]
      by_cases hsa : s = a
      · subst s
        simp [F]
      · simpa only [F, ite_eq_right hsa] using hbound₀ s
          ⟨lt_of_le_of_ne hs.1 (Ne.symm hsa), hs.2.trans_lt ht.2⟩)
    t ⟨ht.1.le, le_rfl⟩
  simpa only [F, ite_eq_right (ne_of_gt ht.1)] using hFzero

end DifferentialGeometry.Analysis.ODE
