import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamCorrectionPlacement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem inter_initial_arcs_of_common_ends
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ ε : ℝ → E} {A B : Set E}
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) A) (hε : IsPLHomeomorphOn ε (Icc 0 1) B)
    (hεzero : ε 0 = δ 0) (hεone : ε 1 = δ 1) (hAB : A ∩ B = {δ 0, δ 1}) :
    (ε '' Icc (0 : ℝ) (1 / 4) ∪ δ '' Icc (0 : ℝ) (1 / 4)) ∩ A =
      δ '' Icc (0 : ℝ) (1 / 4) ∧
    (ε '' Icc (0 : ℝ) (1 / 4) ∪ δ '' Icc (0 : ℝ) (1 / 4)) ∩ B =
      ε '' Icc (0 : ℝ) (1 / 4) ∧
    Disjoint (δ '' Icc (1 / 2 : ℝ) (3 / 4)) B := by
  have hs : Icc (0 : ℝ) (1 / 4) ⊆ Icc (0 : ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hz : (0 : ℝ) ∈ Icc 0 (1 / 4) := by norm_num
  have ho : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  have hzI : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hδs := (image_mono hs).trans hδ.image_eq.subset
  have hεs := (image_mono hs).trans hε.image_eq.subset
  refine ⟨Subset.antisymm ?_ (fun x hx => ⟨Or.inr hx, hδs hx⟩),
    Subset.antisymm ?_ (fun x hx => ⟨Or.inl hx, hεs hx⟩), ?_⟩
  · rintro x ⟨hx | hx, hxA⟩
    · have he := hAB.subset ⟨hxA, hεs hx⟩
      rcases he with he | he
      · exact he.symm ▸ mem_image_of_mem δ hz
      · obtain ⟨t, ht, htε⟩ := hx
        have hti := hε.bijOn.injOn (hs ht) ho (htε.trans (he.trans hεone.symm))
        linarith [ht.2]
    · exact hx
  · rintro x ⟨hx | hx, hxB⟩
    · exact hx
    · have he := hAB.subset ⟨hδs hx, hxB⟩
      rcases he with he | he
      · exact (he.trans hεzero.symm).symm ▸ mem_image_of_mem ε hz
      · obtain ⟨t, ht, htδ⟩ := hx
        have hti := hδ.bijOn.injOn (hs ht) ho (htδ.trans he)
        linarith [ht.2]
  · apply disjoint_left.mpr
    rintro x ⟨t, ht, rfl⟩ hxB
    have htI : t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
    have he := hAB.subset ⟨hδ.bijOn.mapsTo htI, hxB⟩
    rcases he with he | he
    · have hti := hδ.bijOn.injOn htI hzI he
      linarith [ht.1]
    · have hti := hδ.bijOn.injOn htI ho he
      linarith [ht.2]

end DifferentialGeometry.Topology.PiecewiseLinear
