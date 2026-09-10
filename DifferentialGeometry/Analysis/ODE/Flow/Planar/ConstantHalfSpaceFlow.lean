import DifferentialGeometry.Analysis.ODE.Flow.GlobalSliceSmoothness
import Mathlib.Analysis.Calculus.Deriv.Add

noncomputable section
open Set Topology
open scoped ContDiff

namespace Poincare.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem integralCurve_eq_translation_in_constant_halfSpace
    {v : E → E} (hv : ContDiff ℝ ∞ v) (ℓ : E →L[ℝ] ℝ) (c : E) {b : ℝ}
    (hc : 0 ≤ ℓ c) (hfixed : ∀ x, b ≤ ℓ x → v x = c)
    {γ : ℝ → E} (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    {t : ℝ} (ht : b ≤ ℓ (γ t)) {s : ℝ} (hs : 0 ≤ s) :
    γ (t + s) = γ t + s • c := by
  let η : ℝ → E := fun r ↦ γ t + r • c
  have hηmem (r : ℝ) (hr : 0 ≤ r) : b ≤ ℓ (η r) := by
    have he : ℓ (η r) = ℓ (γ t) + r * ℓ c := by simp [η]
    rw [he]
    exact ht.trans (le_add_of_nonneg_right (mul_nonneg hr hc))
  have hηd (r : ℝ) (hr : 0 ≤ r) : HasDerivAt η (v (η r)) r := by
    rw [hfixed _ (hηmem r hr)]
    simpa only [η, one_smul, id_eq] using ((hasDerivAt_id r).smul_const c).const_add (γ t)
  have hshift (r : ℝ) : HasDerivAt (fun r ↦ γ (t + r)) (v (γ (t + r))) r := by
    simpa only [one_smul, zero_add, Pi.add_apply, id_eq, Function.comp_def] using
      (hγ (t + r)).scomp r ((hasDerivAt_const r t).add (hasDerivAt_id r))
  have he := DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_Icc hv
    (a := 0) (b := s) (fun r _ ↦ (hshift r).hasDerivWithinAt)
    (fun r hr ↦ (hηd r hr.1).hasDerivWithinAt) (by simp [η])
  exact he ⟨hs, le_rfl⟩

theorem eq_of_integralCurve_constant_halfSpace_crossings
    {v : E → E} (hv : ContDiff ℝ ∞ v) (ℓ : E →L[ℝ] ℝ) (c : E) {b : ℝ}
    (hc : 0 < ℓ c) (hfixed : ∀ x, b ≤ ℓ x → v x = c)
    {γ : ℝ → E} (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    {s t : ℝ} (hs : ℓ (γ s) = b) (ht : ℓ (γ t) = b) : s = t := by
  have hle (s t : ℝ) (hs : ℓ (γ s) = b) (ht : ℓ (γ t) = b) (hst : s ≤ t) : s = t := by
    have he := integralCurve_eq_translation_in_constant_halfSpace hv ℓ c hc.le hfixed hγ
      hs.ge (sub_nonneg.mpr hst)
    rw [add_sub_cancel] at he
    have hlevel := congrArg ℓ he
    simp only [map_add, map_smul, smul_eq_mul, hs, ht] at hlevel
    have hz : (t - s) * ℓ c = 0 := by linarith
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hc.ne')).symm
  rcases le_total s t with hst | hts
  · exact hle s t hs ht hst
  · exact (hle t s ht hs hts).symm

theorem pos_of_integralCurve_constant_halfSpace_crossing
    {v : E → E} (hv : ContDiff ℝ ∞ v) (ℓ : E →L[ℝ] ℝ) (c : E) {b : ℝ}
    (hc : 0 ≤ ℓ c) (hfixed : ∀ x, b ≤ ℓ x → v x = c)
    {γ : ℝ → E} (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    (hzero : ℓ (γ 0) < b) {t : ℝ} (ht : ℓ (γ t) = b) : 0 < t := by
  by_contra h
  have hn : 0 ≤ -t := neg_nonneg.mpr (not_lt.mp h)
  have he := integralCurve_eq_translation_in_constant_halfSpace hv ℓ c hc hfixed hγ ht.ge hn
  rw [add_neg_cancel] at he
  have hlevel := congrArg ℓ he
  simp only [map_add, map_smul, smul_eq_mul, ht] at hlevel
  have : 0 ≤ -t * ℓ c := mul_nonneg hn hc
  linarith

theorem le_of_integralCurve_constant_incoming_halfSpace
    {v : E → E} (hv : ContDiff ℝ ∞ v) (ℓ : E →L[ℝ] ℝ) (c : E) {b : ℝ}
    (hc : 0 ≤ ℓ c) (hfixed : ∀ x, ℓ x ≤ b → v x = c)
    {γ : ℝ → E} (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    (hzero : b ≤ ℓ (γ 0)) {t : ℝ} (ht : 0 ≤ t) : b ≤ ℓ (γ t) := by
  by_contra h
  have hlt : ℓ (γ t) < b := lt_of_not_ge h
  let η : ℝ → E := fun s ↦ γ (-s)
  have hη (s : ℝ) : HasDerivAt η (-v (η s)) s := by
    simpa only [η, Function.comp_def, neg_one_smul] using
      (hγ (-s)).scomp s (hasDerivAt_neg s)
  have hfixed' (x : E) (hx : -b ≤ (-ℓ) x) : -v x = -c := by
    rw [hfixed x (by simpa only [neg_apply, neg_le_neg_iff] using hx)]
  have he := integralCurve_eq_translation_in_constant_halfSpace hv.neg (-ℓ) (-c)
    (b := -b) (by simpa only [map_neg, neg_apply, neg_neg] using hc)
    hfixed' hη (t := -t)
    (by simpa only [η, neg_neg, neg_apply, neg_le_neg_iff] using hlt.le) ht
  have he0 : γ 0 = γ t + t • (-c) := by
    simpa only [η, neg_add_cancel, neg_neg, neg_zero] using he
  have hlevel := congrArg ℓ he0
  simp only [map_add, map_smul, map_neg, smul_eq_mul, mul_neg] at hlevel
  linarith [mul_nonneg ht hc]

theorem eq_of_integralCurve_constant_incoming_halfSpace_crossings
    {v : E → E} (hv : ContDiff ℝ ∞ v) (ℓ : E →L[ℝ] ℝ) (c : E) {b : ℝ}
    (hc : 0 < ℓ c) (hfixed : ∀ x, ℓ x ≤ b → v x = c)
    {γ : ℝ → E} (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    {s t : ℝ} (hs : ℓ (γ s) = b) (ht : ℓ (γ t) = b) : s = t := by
  let η : ℝ → E := fun r ↦ γ (-r)
  have hη (r : ℝ) : HasDerivAt η (-v (η r)) r := by
    simpa only [η, Function.comp_def, neg_one_smul] using
      (hγ (-r)).scomp r (hasDerivAt_neg r)
  have hfixed' (x : E) (hx : -b ≤ (-ℓ) x) : -v x = -c := by
    rw [hfixed x (by simpa only [neg_apply, neg_le_neg_iff] using hx)]
  have he := eq_of_integralCurve_constant_halfSpace_crossings hv.neg (-ℓ) (-c)
    (b := -b) (by simpa only [map_neg, neg_apply, neg_neg] using hc) hfixed' hη
    (s := -s) (t := -t)
    (by simpa only [η, neg_neg, neg_apply, neg_inj] using hs)
    (by simpa only [η, neg_neg, neg_apply, neg_inj] using ht)
  exact neg_injective he

end Poincare.Analysis
