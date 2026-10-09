import DifferentialGeometry.Topology.MetricSpace.SegmentNeighborhood

set_option autoImplicit false

open Set Metric

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem exists_segment_endpoint_on_curve_of_exit {a b : ℝ} (hab : a ≤ b)
    {σ : Icc a b → X} (hσ : Isometry σ)
    (ho : IsOpen (σ '' {t | a < (t : ℝ) ∧ (t : ℝ) < b}))
    {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    {f : T → X} (hf : Continuous f)
    (hmeet : (range f ∩ σ '' {t | a < (t : ℝ) ∧ (t : ℝ) < b}).Nonempty)
    (hout : ∃ t, f t ∉ range σ) :
    ∃ t, f t = σ ⟨a, le_rfl, hab⟩ ∨ f t = σ ⟨b, hab, le_rfl⟩ := by
  by_contra hn
  have havoid (t : T) (s : Icc a b) (heq : f t = σ s) :
      a < (s : ℝ) ∧ (s : ℝ) < b := by
    constructor
    · apply lt_of_le_of_ne s.property.1
      intro hs
      exact hn ⟨t, Or.inl (heq.trans (congrArg σ (Subtype.ext hs.symm)))⟩
    · apply lt_of_le_of_ne s.property.2
      intro hs
      exact hn ⟨t, Or.inr (heq.trans (congrArg σ (Subtype.ext hs)))⟩
  have hsub : range f ⊆ σ '' {t | a < (t : ℝ) ∧ (t : ℝ) < b} := by
    apply (isPreconnected_range hf).subset_of_closure_inter_subset ho hmeet
    rintro x ⟨hx, t, rfl⟩
    have hclosed : IsClosed (range σ) := (isCompact_range hσ.continuous).isClosed
    have hc : closure (σ '' {s | a < (s : ℝ) ∧ (s : ℝ) < b}) ⊆ range σ :=
      closure_minimal (image_subset_range _ _) hclosed
    obtain ⟨s, hs⟩ := hc hx
    exact ⟨s, havoid t s hs.symm, hs⟩
  obtain ⟨t, ht⟩ := hout
  exact ht ((image_subset_range _ _) (hsub (mem_range_self t)))

theorem dist_to_segment_of_not_mem_range
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {D : ℝ} (hD : 0 ≤ D) {σ : Icc (0 : ℝ) D → X} (hσ : Isometry σ)
    (ho : IsOpen (σ '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < D}))
    {x : X} (hx : x ∉ range σ) (t : Icc (0 : ℝ) D) :
    dist x (σ t) = min (dist x (σ ⟨0, le_rfl, hD⟩) + (t : ℝ))
      (dist x (σ ⟨D, hD, le_rfl⟩) + (D - (t : ℝ))) := by
  let p := σ ⟨0, le_rfl, hD⟩
  let q := σ ⟨D, hD, le_rfl⟩
  have hpt : dist p (σ t) = (t : ℝ) := by
    rw [hσ.dist_eq]
    simp only [Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg t.property.1]
  have hqt : dist q (σ t) = D - (t : ℝ) := by
    rw [hσ.dist_eq]
    exact abs_of_nonneg (sub_nonneg.mpr t.property.2)
  have hupper : dist x (σ t) ≤ min (dist x p + (t : ℝ)) (dist x q + (D - (t : ℝ))) := by
    apply le_min
    · simpa only [hpt] using dist_triangle x p (σ t)
    · simpa only [hqt] using dist_triangle x q (σ t)
  obtain ⟨f, hf, hf0, hf1, hfd⟩ := hsegments x (σ t)
  have hhit : ∃ u, f u = p ∨ f u = q := by
    by_cases ht0 : (t : ℝ) = 0
    · exact ⟨⟨1, by norm_num⟩, Or.inl (hf1.trans (congrArg σ (Subtype.ext ht0)))⟩
    by_cases htD : (t : ℝ) = D
    · exact ⟨⟨1, by norm_num⟩, Or.inr (hf1.trans (congrArg σ (Subtype.ext htD)))⟩
    exact exists_segment_endpoint_on_curve_of_exit hD hσ ho hf
      ⟨σ t, ⟨⟨1, by norm_num⟩, hf1⟩, t,
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0), lt_of_le_of_ne t.property.2 htD⟩, rfl⟩
      ⟨⟨0, by norm_num⟩, hf0 ▸ hx⟩
  obtain ⟨u, hu⟩ := hhit
  have heq : dist x (f u) + dist (f u) (σ t) = dist x (σ t) := by
    have hl := hfd ⟨0, by norm_num⟩ u
    have hr := hfd u ⟨1, by norm_num⟩
    rw [hf0] at hl
    rw [hf1] at hr
    simp only [Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg u.property.1] at hl
    simp only [Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr u.property.2), neg_sub] at hr
    linarith
  apply le_antisymm hupper
  rcases hu with hu | hu
  · rw [hu, hpt] at heq
    exact (min_le_left _ _).trans_eq heq
  · rw [hu, hqt] at heq
    exact (min_le_right _ _).trans_eq heq

end Metric
