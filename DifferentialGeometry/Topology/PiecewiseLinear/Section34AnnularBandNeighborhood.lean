import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandComponents

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsAnnulusOn.mem_nhdsWithin_of_not_mem_ends
    {M : Type*} [TopologicalSpace M] [T2Space M] {S A A₀ A₁ : Set M}
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (hA : IsAnnulusOn A A₀ A₁) (hAS : A ⊆ S) {x : M}
    (hx : x ∈ A) (hxend : x ∉ A₀ ∪ A₁) : A ∈ 𝓝[S] x := by
  have hann := hA.preimage_subtype hAS
  have hint : (⟨x, hAS hx⟩ : S) ∈ interior ((Subtype.val : S → M) ⁻¹' A) := by
    apply (mem_interior_iff_notMem_frontier
      (show (⟨x, hAS hx⟩ : S) ∈ (Subtype.val : S → M) ⁻¹' A from hx)).mpr
    intro hf
    exact hxend (hann.frontier_subset hf)
  exact preimage_coe_mem_nhds_subtype.mp (mem_interior_iff_mem_nhds.mp hint)

theorem IsPLCellOn.annulus_mem_nhdsWithin_of_not_mem_ends
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {S B A A₀ A₁ : Set M}
    (hS : IsPLCellOn 3 S B) (hA : IsAnnulusOn A A₀ A₁) (hAB : A ⊆ B) {x : M}
    (hx : x ∈ A) (hxend : x ∉ A₀ ∪ A₁) : A ∈ 𝓝[B] x := by
  obtain ⟨hc⟩ := hS.nonempty_chartedSpace_boundary
  let _ := hc
  exact hA.mem_nhdsWithin_of_not_mem_ends hAB hx hxend

theorem inter_caps_eq_union_of_ordered_caps
    {X ι : Type*} [Preorder ι] {S : Set X} {D₀ D₁ : ι → Set X}
    (hU : ∀ i, D₀ i ∪ D₁ i = S) (h₀ : Monotone D₀) (h₁ : Antitone D₁)
    {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) :
    D₁ i ∩ D₀ k = (D₁ i ∩ D₀ j) ∪ (D₁ j ∩ D₀ k) := by
  apply Subset.antisymm
  · rintro x ⟨hxi, hxk⟩
    rcases (hU j).superset ((hU k).subset (Or.inl hxk)) with hxj | hxj
    · exact Or.inl ⟨hxi, hxj⟩
    · exact Or.inr ⟨hxj, hxk⟩
  · rintro x (hx | hx)
    · exact ⟨hx.1, h₀ hjk hx.2⟩
    · exact ⟨h₁ hij hx.1, hx.2⟩

theorem exists_neighborhood_lateral_pair_cover
    {M : Type*} [TopologicalSpace M] [T2Space M] {S A₀ A₁ T : Set M}
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {f g : (Fin 3 → ℝ) × ℝ → M}
    (hf : InjOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hg : InjOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hann : IsAnnulusOn
      (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∪
        g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) A₀ A₁)
    (hS : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∪
      g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ S)
    (hfends : f '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
      f '' (stdSimplexBoundary 2 ×ˢ {1}) ⊆ T)
    (hgends : g '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
      g '' (stdSimplexBoundary 2 ×ˢ {1}) ⊆ T) {x : M}
    (hx : x ∈ f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∪
      g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hxend : x ∉ A₀ ∪ A₁) :
    ∃ V : Set M, V ∈ 𝓝 x ∧ V ∩ S ⊆
      f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ∪
        g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ∪ T := by
  have hnhds := hann.mem_nhdsWithin_of_not_mem_ends hS hx hxend
  obtain ⟨V, hV, hcover⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hnhds
  refine ⟨V, hV, ?_⟩
  intro y hy
  rcases hcover hy with hyf | hyg
  · by_cases hyt : y ∈ f '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
        f '' (stdSimplexBoundary 2 ×ˢ {1})
    · exact Or.inr (hfends hyt)
    · exact Or.inl (Or.inl ((image_lateral_open_eq_sdiff_ends hf).superset ⟨hyf, hyt⟩))
  · by_cases hyt : y ∈ g '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
        g '' (stdSimplexBoundary 2 ×ˢ {1})
    · exact Or.inr (hgends hyt)
    · exact Or.inl (Or.inr ((image_lateral_open_eq_sdiff_ends hg).superset ⟨hyg, hyt⟩))

end DifferentialGeometry.Topology.PiecewiseLinear
