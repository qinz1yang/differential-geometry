import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

private theorem le_of_deriv_nonpos_Icc {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ x ∈ Ioo a b, ∃ d ≤ 0, HasDerivAt f d x)
    (ha : ContinuousWithinAt f (Ici a) a) (hb : ContinuousWithinAt f (Iic b) b) :
    f b ≤ f a := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  have hcont : ContinuousOn f (Icc a b) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hxa
    · exact ha.mono Icc_subset_Ici_self
    rcases eq_or_lt_of_le hx.2 with rfl | hxb
    · exact hb.mono Icc_subset_Iic_self
    obtain ⟨d, -, hdx⟩ := hd x ⟨hxa, hxb⟩
    exact hdx.continuousAt.continuousWithinAt
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc a b) hcont (fun x hx => by
    rw [interior_Icc] at hx
    obtain ⟨d, -, hdx⟩ := hd x hx
    exact hdx.differentiableAt.differentiableWithinAt) (fun x hx => by
    rw [interior_Icc] at hx
    obtain ⟨d, hd0, hdx⟩ := hd x hx
    rw [hdx.deriv]
    exact hd0)
  exact hanti (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab

theorem le_of_hasDerivAt_nonpos_off_finite {f : ℝ → ℝ} {S : Set ℝ} (hS : S.Finite) :
    ∀ (N : ℕ) (a b : ℝ), a ≤ b → (S ∩ Ioo a b).ncard ≤ N →
      (∀ x ∈ Ioo a b, x ∉ S → ∃ d ≤ 0, HasDerivAt f d x) →
      (∀ x ∈ Ioo a b, x ∈ S → ∃ L, Tendsto f (𝓝[<] x) (𝓝 L) ∧ Tendsto f (𝓝[>] x) (𝓝 L)) →
      ContinuousWithinAt f (Ici a) a → ContinuousWithinAt f (Iic b) b → f b ≤ f a := by
  intro N
  induction N with
  | zero =>
    intro a b hab hN hd _ ha hb
    have hempty : S ∩ Ioo a b = ∅ :=
      (Set.ncard_eq_zero (hS.subset inter_subset_left)).1 (Nat.le_zero.1 hN)
    refine le_of_deriv_nonpos_Icc hab (fun x hx => hd x hx fun hxS => ?_) ha hb
    exact (Set.eq_empty_iff_forall_notMem.1 hempty x) ⟨hxS, hx⟩
  | succ N ih =>
    intro a b hab hN hd hlim ha hb
    by_cases hne : (S ∩ Ioo a b).Nonempty
    swap
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      refine le_of_deriv_nonpos_Icc hab (fun x hx => hd x hx fun hxS => ?_) ha hb
      exact (Set.eq_empty_iff_forall_notMem.1 hne x) ⟨hxS, hx⟩
    obtain ⟨s, hsS, hs⟩ := hne
    obtain ⟨L, hL₁, hL₂⟩ := hlim s hs hsS
    have hfin : (S ∩ Ioo a b).Finite := hS.subset inter_subset_left
    have hcard : ∀ c d, Ioo c d ⊆ Ioo a b → s ∉ Ioo c d → (S ∩ Ioo c d).ncard ≤ N := by
      intro c d hsub hsn
      have hlt : (S ∩ Ioo c d).ncard < (S ∩ Ioo a b).ncard :=
        Set.ncard_lt_ncard ⟨fun x hx => ⟨hx.1, hsub hx.2⟩, fun h => hsn (h ⟨hsS, hs⟩).2⟩ hfin
      omega
    have hSs : ∀ᶠ x in 𝓝 s, x ≠ s → x ∉ S := by
      have hcl : IsClosed (S \ {s}) := (hS.subset sdiff_subset).isClosed
      filter_upwards [hcl.isOpen_compl.mem_nhds (by simp)] with x hx hxs hxS
      exact hx ⟨hxS, hxs⟩
    have hleft : L ≤ f a := by
      refine le_of_tendsto hL₁ ?_
      filter_upwards [nhdsWithin_le_nhds hSs, Ioo_mem_nhdsLT hs.1, self_mem_nhdsWithin]
        with x hxS hx hxs
      have hxS' := hxS (ne_of_lt hxs)
      obtain ⟨d, -, hdx⟩ := hd x ⟨hx.1, hx.2.trans hs.2⟩ hxS'
      exact ih a x hx.1.le (hcard a x (Ioo_subset_Ioo le_rfl (hx.2.trans hs.2).le)
        (fun h => (lt_irrefl s) (h.2.trans hx.2)))
        (fun y hy hyS => hd y ⟨hy.1, hy.2.trans (hx.2.trans hs.2)⟩ hyS)
        (fun y hy hyS => hlim y ⟨hy.1, hy.2.trans (hx.2.trans hs.2)⟩ hyS) ha
        hdx.continuousAt.continuousWithinAt
    have hright : f b ≤ L := by
      refine ge_of_tendsto hL₂ ?_
      filter_upwards [nhdsWithin_le_nhds hSs, Ioo_mem_nhdsGT hs.2, self_mem_nhdsWithin]
        with y hyS hy hys
      have hyS' := hyS (ne_of_gt hys)
      obtain ⟨d, -, hdy⟩ := hd y ⟨hs.1.trans hy.1, hy.2⟩ hyS'
      exact ih y b hy.2.le (hcard y b (Ioo_subset_Ioo (hs.1.trans hy.1).le le_rfl)
        (fun h => (lt_irrefl s) (hy.1.trans h.1)))
        (fun z hz hzS => hd z ⟨(hs.1.trans hy.1).trans hz.1, hz.2⟩ hzS)
        (fun z hz hzS => hlim z ⟨(hs.1.trans hy.1).trans hz.1, hz.2⟩ hzS)
        hdy.continuousAt.continuousWithinAt hb
    linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
