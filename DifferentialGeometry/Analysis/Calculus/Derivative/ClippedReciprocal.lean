import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open Set Filter
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis

theorem lipschitzOnWith_inv_max_of_quadratic_deriv_bound
    {r r' : ℝ → ℝ} {s : Set ℝ} {q : ℝ} {C : ℝ≥0}
    (hq : 0 < q) (hs : OrdConnected s) (hc : ContinuousOn r s)
    (hd : ∀ t ∈ s, q < r t → HasDerivWithinAt r (r' t) s t)
    (hb : ∀ t ∈ s, q < r t → |r' t| ≤ C * r t ^ 2) :
    LipschitzOnWith C (fun t => (max q (r t))⁻¹) s := by
  let f : ℝ → ℝ := fun t => (max q (r t))⁻¹
  have hf : ContinuousOn f s :=
    (continuous_max.comp_continuousOn (continuousOn_const.prodMk hc)).inv₀
      fun t _ => ne_of_gt (hq.trans_le (le_max_left _ _))
  have hsegment {u v : ℝ} (hu : u ∈ s) (hv : v ∈ s) (huv : u ≤ v)
      (hhigh : ∀ t ∈ Ioo u v, q < r t) :
      |f v - f u| ≤ C * (v - u) := by
    rcases huv.eq_or_lt with heq | hlt
    · subst v
      simp
    have hsub : Icc u v ⊆ s := hs.out hu hv
    have hdiff (t : ℝ) (ht : t ∈ Ioo u v) :
        HasDerivAt f (-r' t / r t ^ 2) t := by
      have hrt := hhigh t ht
      have hdr : HasDerivAt r (r' t) t :=
        ((hd t (hsub ⟨ht.1.le, ht.2.le⟩) hrt).mono hsub).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2)
      apply (hdr.inv (ne_of_gt (hq.trans hrt))).congr_of_eventuallyEq
      filter_upwards [hdr.continuousAt.eventually (Ioi_mem_nhds hrt)] with z hz
      simp only [f, max_eq_right hz.le, Pi.inv_apply]
    obtain ⟨t, ht, heq⟩ := exists_hasDerivAt_eq_slope f
      (fun t => -r' t / r t ^ 2) hlt (hf.mono hsub) hdiff
    have hrpos : 0 < r t := hq.trans (hhigh t ht)
    have hsq : 0 < r t ^ 2 := sq_pos_of_pos hrpos
    have hderiv : |-r' t / r t ^ 2| ≤ C := by
      rw [abs_div, abs_neg, abs_of_pos hsq, div_le_iff₀ hsq]
      exact hb t (hsub ⟨ht.1.le, ht.2.le⟩) (hhigh t ht)
    rw [heq, abs_div, abs_of_pos (sub_pos.mpr hlt), div_le_iff₀ (sub_pos.mpr hlt)] at hderiv
    exact hderiv
  have hordered {u v : ℝ} (hu : u ∈ s) (hv : v ∈ s) (huv : u ≤ v) :
      |f v - f u| ≤ C * (v - u) := by
    let A := Icc u v ∩ r ⁻¹' Iic q
    have hsub : Icc u v ⊆ s := hs.out hu hv
    have hclosed : IsClosed A :=
      (hc.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hcompact : IsCompact A := isCompact_Icc.of_isClosed_subset hclosed inter_subset_left
    rcases A.eq_empty_or_nonempty with he | hn
    · apply hsegment hu hv huv
      intro t ht
      by_contra h
      have hm : t ∈ A := ⟨⟨ht.1.le, ht.2.le⟩, le_of_not_gt h⟩
      rw [he] at hm
      exact hm.elim
    obtain ⟨c, hcA, hcmin⟩ := hcompact.exists_isMinOn hn continuousOn_id
    obtain ⟨d, hdA, hdmax⟩ := hcompact.exists_isMaxOn hn continuousOn_id
    have hcd : c ≤ d := isMaxOn_iff.mp hdmax c hcA
    have hfc : f c = q⁻¹ := by simp only [f, max_eq_left (show r c ≤ q from hcA.2)]
    have hfd : f d = q⁻¹ := by simp only [f, max_eq_left (show r d ≤ q from hdA.2)]
    have hleft : |f c - f u| ≤ C * (c - u) := by
      apply hsegment hu (hsub hcA.1) hcA.1.1
      intro t ht
      by_contra h
      have htA : t ∈ A := ⟨⟨ht.1.le, ht.2.le.trans hcA.1.2⟩, le_of_not_gt h⟩
      have := isMinOn_iff.mp hcmin t htA
      exact (not_le_of_gt ht.2) this
    have hright : |f v - f d| ≤ C * (v - d) := by
      apply hsegment (hsub hdA.1) hv hdA.1.2
      intro t ht
      by_contra h
      have htA : t ∈ A := ⟨⟨hdA.1.1.trans ht.1.le, ht.2.le⟩, le_of_not_gt h⟩
      have := isMaxOn_iff.mp hdmax t htA
      exact (not_le_of_gt ht.1) this
    have htri := abs_sub_le (f v) (f c) (f u)
    rw [hfc] at hleft htri
    rw [hfd] at hright
    nlinarith [C.coe_nonneg]
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro u hu v hv
  change |f u - f v| ≤ C * |u - v|
  rcases le_total u v with huv | hvu
  · rw [abs_sub_comm (f u), abs_sub_comm u, abs_of_nonneg (sub_nonneg.mpr huv)]
    exact hordered hu hv huv
  · rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact hordered hv hu hvu


theorem lipschitzOnWith_inv_max_of_quadratic_deriv_bound_Icc
    {r r' : ℝ → ℝ} {a b q : ℝ} {C : ℝ≥0}
    (hq : 0 < q) (hc : ContinuousOn r (Icc a b))
    (hd : ∀ t ∈ Ioo a b, q < r t → HasDerivAt r (r' t) t)
    (hb : ∀ t ∈ Ioo a b, q < r t → |r' t| ≤ C * r t ^ 2) :
    LipschitzOnWith C (fun t => (max q (r t))⁻¹) (Icc a b) := by
  by_cases hab : a < b
  · have hi := lipschitzOnWith_inv_max_of_quadratic_deriv_bound hq ordConnected_Ioo
      (hc.mono Ioo_subset_Icc_self)
      (fun t ht hqt => (hd t ht hqt).hasDerivWithinAt) hb
    have hcont : ContinuousOn (fun t => (max q (r t))⁻¹) (Icc a b) :=
      (continuous_max.comp_continuousOn (continuousOn_const.prodMk hc)).inv₀
        (fun t _ => ne_of_gt (hq.trans_le (le_max_left _ _)))
    rw [← closure_Ioo hab.ne] at hcont ⊢
    exact LipschitzOnWith.closure hcont hi
  · rw [lipschitzOnWith_iff_dist_le_mul]
    intro t ht u hu
    have heq : t = u := by
      have := le_of_not_gt hab
      rcases ht with ⟨hat, htb⟩
      rcases hu with ⟨hau, hub⟩
      linarith
    simp only [heq, dist_self, mul_zero, le_refl]

end DifferentialGeometry.Analysis
