import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open Set Filter
open scoped Topology

namespace OpenPartialHomeomorph

variable {N M : Type*} [TopologicalSpace N] [TopologicalSpace M]

theorem exists_signed_germ_of_segment
    (T : OpenPartialHomeomorph (N × ℝ) M) {a b : ℝ} (hab : a < b)
    (γ : ℝ → M) (hγ : ContinuousOn γ (Icc a b))
    (htarget : ∀ t ∈ Icc a b, γ t ∈ T.target)
    (hbase : (T.symm (γ a)).2 = 0) {V : Set M}
    (htail : ∀ t ∈ Ioc a b, γ t ∈ V)
    (havoid : Disjoint V (range fun q : N => T (q,0))) :
    ∃ ν : ℝ, (ν = 1 ∨ ν = -1) ∧
      (∀ t ∈ Ioc a b, 0 < ν * (T.symm (γ t)).2) ∧
      ∀ r : ℝ, 0 < r → ∃ q : N, ∃ t ∈ Ioo (0 : ℝ) r, T (q,ν*t) ∈ V := by
  let f : ℝ → ℝ := fun t => (T.symm (γ t)).2
  have hf : ContinuousOn f (Icc a b) := continuous_snd.continuousOn.comp
    (T.continuousOn_symm.comp hγ htarget) (fun _ _ => mem_univ _)
  have hnonzero : ∀ t ∈ Ioc a b, f t ≠ 0 := by
    intro t ht heq
    apply disjoint_left.mp havoid (htail t ht)
    refine ⟨(T.symm (γ t)).1,?_⟩
    change T ((T.symm (γ t)).1,0) = γ t
    rw [← heq]
    exact T.right_inv (htarget t ⟨ht.1.le,ht.2⟩)
  have hend : f b ≠ 0 := hnonzero b ⟨hab,le_rfl⟩
  have hsign : (∀ t ∈ Ioc a b, 0 < f t) ∨ (∀ t ∈ Ioc a b, f t < 0) := by
    rcases lt_or_gt_of_ne hend with hbneg | hbpos
    · right
      intro t ht
      by_contra hn
      have hft := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm (hnonzero t ht))
      obtain ⟨c,hc,hfc⟩ := isPreconnected_Ioc.intermediate_value
        (show b ∈ Ioc a b from ⟨hab,le_rfl⟩) ht
        (hf.mono Ioc_subset_Icc_self) ⟨hbneg.le,hft.le⟩
      exact hnonzero c hc hfc
    · left
      intro t ht
      by_contra hn
      have hft := lt_of_le_of_ne (le_of_not_gt hn) (hnonzero t ht)
      obtain ⟨c,hc,hfc⟩ := isPreconnected_Ioc.intermediate_value ht
        (show b ∈ Ioc a b from ⟨hab,le_rfl⟩)
        (hf.mono Ioc_subset_Icc_self) ⟨hft.le,hbpos.le⟩
      exact hnonzero c hc hfc
  have hsmall (r : ℝ) (hr : 0 < r) : ∃ t ∈ Ioc a b, |f t| < r := by
    have hfcont := hf a ⟨le_rfl,hab.le⟩
    change Tendsto f (𝓝[Icc a b] a) (𝓝 (f a)) at hfcont
    have hfa : f a = 0 := hbase
    have hI : Ioo (-r) r ∈ 𝓝 (f a) := by rw [hfa]; exact Ioo_mem_nhds (by linarith) hr
    have hnear := hfcont hI
    have hwithin : 𝓝[>] a ≤ 𝓝[Icc a b] a := by
      apply nhdsWithin_le_of_mem
      filter_upwards [Ioo_mem_nhdsGT hab] with t ht
      exact ⟨ht.1.le,ht.2.le⟩
    have hfsmall : ∀ᶠ t in 𝓝[>] a, f t ∈ Ioo (-r) r := hwithin hnear
    obtain ⟨t,ht,hft⟩ := ((show ∀ᶠ t in 𝓝[>] a, t ∈ Ioo a b from Ioo_mem_nhdsGT hab).and hfsmall).exists
    exact ⟨t,⟨ht.1,ht.2.le⟩,abs_lt.mpr hft⟩
  rcases hsign with hsign | hsign
  · refine ⟨1,Or.inl rfl,?_,?_⟩
    · simpa only [one_mul] using hsign
    · intro r hr
      obtain ⟨t,ht,hft⟩ := hsmall r hr
      refine ⟨(T.symm (γ t)).1,f t,⟨hsign t ht,(abs_lt.mp hft).2⟩,?_⟩
      change T ((T.symm (γ t)).1,1 * (T.symm (γ t)).2) ∈ V
      rw [one_mul]
      exact (T.right_inv (htarget t ⟨ht.1.le,ht.2⟩)).symm ▸ htail t ht
  · refine ⟨-1,Or.inr rfl,?_,?_⟩
    · intro t ht
      have h := hsign t ht
      change 0 < -1 * f t
      linarith
    · intro r hr
      obtain ⟨t,ht,hft⟩ := hsmall r hr
      refine ⟨(T.symm (γ t)).1,-f t,⟨neg_pos.mpr (hsign t ht),by linarith [(abs_lt.mp hft).1]⟩,?_⟩
      change T ((T.symm (γ t)).1,-1 * -(T.symm (γ t)).2) ∈ V
      rw [neg_mul,one_mul,neg_neg]
      exact (T.right_inv (htarget t ⟨ht.1.le,ht.2⟩)).symm ▸ htail t ht

end OpenPartialHomeomorph
