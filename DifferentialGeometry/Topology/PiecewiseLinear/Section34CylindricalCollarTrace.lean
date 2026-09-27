import DifferentialGeometry.Topology.PiecewiseLinear.Section34SynchronizedShellTraces

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem cylindrical_trace_of_collar_level_traces
    {E M X ι : Type*} {u : E → M} {ρ : E × ℝ → E} {F : X × ℝ → M}
    {R W S : Set E} {A : Set M} {B : Set X} {η : ι → ℝ → X} {c : ℝ}
    (hSR : S ⊆ R) (hW : ρ '' (S ×ˢ Icc (0 : ℝ) c) = W)
    (hzero : ∀ x ∈ S, ρ (x, 0) = x)
    (htrace : u '' R ∩ A = F '' (B ×ˢ Icc (0 : ℝ) 1)) (hcore : ∀ k, η k 0 ∈ B)
    (hlevels : ∀ t ∈ Ioc (0 : ℝ) c, (u ∘ ρ) '' (S ×ˢ {t}) ∩ A =
      ⋃ k, F '' ({η k t} ×ˢ Icc (0 : ℝ) 1)) :
    u '' (R ∪ W) ∩ A = F '' ((B ∪ ⋃ k, η k '' Icc (0 : ℝ) c) ×ˢ Icc (0 : ℝ) 1) := by
  have hbase : u '' R ∩ A ⊆
      F '' ((B ∪ ⋃ k, η k '' Icc (0 : ℝ) c) ×ˢ Icc (0 : ℝ) 1) := by
    rw [htrace]
    exact image_mono (prod_mono_left subset_union_left)
  apply Subset.antisymm
  · rintro y ⟨⟨x, hx, rfl⟩, hxA⟩
    rcases hx with hx | hx
    · exact hbase ⟨mem_image_of_mem u hx, hxA⟩
    · obtain ⟨⟨p, t⟩, ⟨hp, ht⟩, rfl⟩ := hW.symm.subset hx
      by_cases ht0 : t = 0
      · rw [ht0, hzero p hp] at hxA ⊢
        exact hbase ⟨mem_image_of_mem u (hSR hp), hxA⟩
      · have htp : t ∈ Ioc (0 : ℝ) c := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩
        have hm := (hlevels t htp).subset
          ⟨⟨(p, t), ⟨hp, rfl⟩, rfl⟩, hxA⟩
        obtain ⟨k, ⟨⟨q, s⟩, ⟨hq, hs⟩, heq⟩⟩ := mem_iUnion.mp hm
        refine ⟨(q, s), ⟨Or.inr (mem_iUnion.mpr ⟨k, ?_⟩), hs⟩, heq⟩
        exact ⟨t, ht, hq.symm⟩
  · rintro y ⟨⟨q, s⟩, ⟨hq, hs⟩, rfl⟩
    rcases hq with hq | hq
    · obtain ⟨hyR, hyA⟩ := htrace.symm.subset (mem_image_of_mem F ⟨hq, hs⟩)
      exact ⟨image_mono subset_union_left hyR, hyA⟩
    · obtain ⟨k, ⟨t, ht, rfl⟩⟩ := mem_iUnion.mp hq
      by_cases ht0 : t = 0
      · subst t
        obtain ⟨hyR, hyA⟩ := htrace.symm.subset (mem_image_of_mem F ⟨hcore k, hs⟩)
        exact ⟨image_mono subset_union_left hyR, hyA⟩
      · have htp : t ∈ Ioc (0 : ℝ) c := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩
        have hm := (hlevels t htp).symm.subset
          (mem_iUnion.mpr ⟨k, (η k t, s), ⟨rfl, hs⟩, rfl⟩)
        obtain ⟨⟨⟨p, r⟩, ⟨hp, hr⟩, heq⟩, hyA⟩ := hm
        have hrt : r = t := hr
        subst r
        exact ⟨⟨ρ (p, t), Or.inr (hW.subset (mem_image_of_mem ρ ⟨hp, ht⟩)), heq⟩, hyA⟩

end DifferentialGeometry.Topology.PiecewiseLinear
