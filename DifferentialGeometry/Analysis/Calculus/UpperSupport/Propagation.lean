import DifferentialGeometry.Analysis.Calculus.UpperSupport.Monotonicity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Compact
namespace DifferentialGeometry

open Set Filter
open scoped _root_.Topology

theorem image_le_initial_of_deriv_upper_support_nonpos_below
    {f : ℝ → ℝ} {a b C : ℝ}
    (hf : ContinuousOn f (Icc a b)) (ha : f a < C)
    (hsupport : ∀ t ∈ Ioo a b, f t < C →
      ∃ phi : ℝ → ℝ, ∃ d : ℝ,
        phi t = f t ∧ f ≤ᶠ[𝓝[>] t] phi ∧
        HasDerivAt phi d t ∧ d ≤ 0) :
    ∀ t ∈ Icc a b, f t ≤ f a := by
  intro t ht
  by_contra hft
  obtain ⟨q, haq, hq⟩ := exists_between (lt_min (lt_of_not_ge hft) ha)
  have hqt : q < f t := hq.trans_le (min_le_left _ _)
  have hq0 : q < C := hq.trans_le (min_le_right _ _)
  let K := Icc a t ∩ f ⁻¹' Ici q
  have hclosed : IsClosed K :=
    (hf.mono (Icc_subset_Icc le_rfl ht.2)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Ici
  have hcompact : IsCompact K := isCompact_Icc.of_isClosed_subset hclosed inter_subset_left
  obtain ⟨c, hc, hmin⟩ := hcompact.exists_isMinOn
    (show K.Nonempty from ⟨t, ⟨⟨ht.1, le_rfl⟩, hqt.le⟩⟩) continuousOn_id
  have hac : a < c := by
    refine lt_of_le_of_ne hc.1.1 ?_
    intro hca
    exact (not_le_of_gt haq) (hca ▸ hc.2)
  have := left_nhdsWithin_Ioo_neBot hac
  have hsmall : ∀ᶠ x in 𝓝[Ioo a c] a, f x < q :=
    ((hf a ⟨le_rfl, ht.1.trans ht.2⟩).mono
      (show Ioo a c ⊆ Icc a b from fun x hx =>
        ⟨hx.1.le, hx.2.le.trans (hc.1.2.trans ht.2)⟩)).eventually_lt_const haq
  have hboth : ∀ᶠ x in 𝓝[Ioo a c] a, x ∈ Ioo a c ∧ f x < q :=
    (show ∀ᶠ x in 𝓝[Ioo a c] a, x ∈ Ioo a c from self_mem_nhdsWithin).and hsmall
  obtain ⟨x, hx, hxq⟩ := hboth.exists
  have hbound : f c ≤ f x := by
    apply image_le_of_deriv_upper_support
      (f := f) (B := fun _ => f x) (B' := fun _ => 0)
      (hf.mono (Icc_subset_Icc hx.1.le (hc.1.2.trans ht.2))) le_rfl continuousOn_const
      (fun r _ => (hasDerivAt_const r (f x)).hasDerivWithinAt) ?_ c ⟨hx.2.le, le_rfl⟩
    intro r hr
    have hfr : f r < q := by
      by_contra h
      have hrK : r ∈ K := ⟨⟨hx.1.le.trans hr.1, hr.2.le.trans hc.1.2⟩, le_of_not_gt h⟩
      exact (not_le_of_gt hr.2) (hmin hrK)
    exact hsupport r ⟨hx.1.trans_le hr.1, hr.2.trans_le (hc.1.2.trans ht.2)⟩
      (hfr.trans hq0)
  exact (not_le_of_gt hxq) (hc.2.trans hbound)

end DifferentialGeometry
