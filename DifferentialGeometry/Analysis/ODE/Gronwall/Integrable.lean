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

end DifferentialGeometry.Analysis.ODE
