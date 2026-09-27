import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Analysis

theorem monotoneOn_max_of_deriv_nonneg_above
    {f : ℝ → ℝ} {s : Set ℝ} {q : ℝ} (hs : OrdConnected s)
    (hc : ContinuousOn f s)
    (hd : ∀ t ∈ interior s, q < f t → DifferentiableAt ℝ f t ∧ 0 ≤ deriv f t) :
    MonotoneOn (fun t => max q (f t)) s := by
  have hsegment {u v : ℝ} (hu : u ∈ s) (hv : v ∈ s) (huv : u ≤ v)
      (hhigh : ∀ t ∈ Ioo u v, q < f t) : f u ≤ f v := by
    have hsub : Icc u v ⊆ s := hs.out hu hv
    have hint : Ioo u v ⊆ interior s := by
      rw [← interior_Icc]
      exact interior_mono hsub
    have hmono : MonotoneOn f (Icc u v) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc u v)
      · exact hc.mono hsub
      · intro t ht
        rw [interior_Icc] at ht
        exact (hd t (hint ht)
          (hhigh t ht)).1.differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (hd t (hint ht) (hhigh t ht)).2
    exact hmono ⟨le_rfl,huv⟩ ⟨huv,le_rfl⟩ huv
  intro u hu v hv huv
  change max q (f u) ≤ max q (f v)
  by_cases hqu : f u ≤ q
  · rw [max_eq_left hqu]
    exact le_max_left _ _
  have hqu : q < f u := lt_of_not_ge hqu
  let A := Icc u v ∩ f ⁻¹' Iic q
  have hsub : Icc u v ⊆ s := hs.out hu hv
  have hclosed : IsClosed A :=
    (hc.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hcompact : IsCompact A := isCompact_Icc.of_isClosed_subset hclosed inter_subset_left
  rcases A.eq_empty_or_nonempty with he | hn
  · apply max_le_max_left q
    apply hsegment hu hv huv
    intro t ht
    by_contra h
    have hm : t ∈ A := ⟨⟨ht.1.le,ht.2.le⟩,le_of_not_gt h⟩
    rw [he] at hm
    exact hm.elim
  · obtain ⟨c, hcA, hmin⟩ := hcompact.exists_isMinOn hn continuousOn_id
    have huc : u ≤ c := hcA.1.1
    have hfc : f c ≤ q := hcA.2
    have hfu : f u ≤ f c := by
      apply hsegment hu (hsub hcA.1) huc
      intro t ht
      by_contra h
      have htA : t ∈ A := ⟨⟨ht.1.le,ht.2.le.trans hcA.1.2⟩,le_of_not_gt h⟩
      exact (not_le_of_gt ht.2) (hmin htA)
    exact (not_le_of_gt hqu (hfu.trans hfc)).elim

theorem le_max_endpoint_of_deriv_nonneg_above
    {f : ℝ → ℝ} {a b q : ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, q < f t → DifferentiableAt ℝ f t ∧ 0 ≤ deriv f t)
    {t : ℝ} (ht : t ∈ Icc a b) : f t ≤ max q (f b) :=
  (le_max_right _ _).trans
    (monotoneOn_max_of_deriv_nonneg_above ordConnected_Icc hc
      (by simpa only [interior_Icc] using hd) ht ⟨ht.1.trans ht.2,le_rfl⟩ ht.2)

end DifferentialGeometry.Analysis
