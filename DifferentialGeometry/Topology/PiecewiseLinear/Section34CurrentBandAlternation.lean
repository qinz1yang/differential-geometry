import DifferentialGeometry.Topology.PiecewiseLinear.Section34OrderedBandAlternation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.opposite_lateral_band_sides_of_chart_crossing
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {X S Y B : Set M}
    (hX : IsPLCellOn 3 X S) (hY : IsPLCellOn 3 Y B)
    {f g : (Fin 3 → ℝ) × ℝ → M}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfi : InjOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hgi : InjOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) {J L : Set M}
    (hann : IsAnnulusOn (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∪
      g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) J L)
    (hB : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∪
      g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ B)
    (hfends : f '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
      f '' (stdSimplexBoundary 2 ×ˢ {1}) ⊆ S)
    (hgends : g '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
      g '' (stdSimplexBoundary 2 ×ˢ {1}) ⊆ S)
    (hfempty : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) S)
    (hgempty : Disjoint (g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) S)
    {x : M} (hxS : x ∈ S)
    (hx : x ∈ f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∪
      g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) (hxend : x ∉ J ∪ L)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))) (hxc : x ∈ c.source)
    (hcross : HasPLCrossingAt (c '' (B ∩ c.source)) (c '' (S ∩ c.source)) (c x)) :
    (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆ interior X ∧
      g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆ Xᶜ) ∨
    (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆ Xᶜ ∧
      g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆ interior X) := by
  obtain ⟨hchart⟩ := hY.nonempty_chartedSpace_boundary
  let _ := hchart
  have hball (N : Set M) (hN : N ∈ 𝓝 x) :=
    exists_ball_chart_of_mem_nhdsWithin_surface (hB hx) self_mem_nhdsWithin hN
  have hreg : closure (interior X) = X := by
    rw [← hX.sdiff_boundary_eq_interior]
    exact hX.closure_sdiff_boundary
  have hcross' : HasPLCrossingAt (c '' (B ∩ c.source))
      (c '' (frontier X ∩ c.source)) (c x) := hX.boundary_eq_frontier ▸ hcross
  have hxF : x ∈ frontier X := hX.boundary_eq_frontier ▸ hxS
  have hxreg : x ∈ closure (interior X) := by
    rw [hreg]
    exact hX.boundary_subset hxS
  obtain ⟨V₀, -, -, -, hin⟩ := exists_connected_inside_slice_of_chart_crossing
    hX.isCompact.isClosed hxreg c hxc hcross' hball
  obtain ⟨V₁, -, -, -, hout⟩ := exists_connected_outside_slice_of_chart_crossing
    hX.isCompact.isClosed hreg c hxc hcross' hxF hball
  obtain ⟨V, hV, hcover⟩ := exists_neighborhood_lateral_pair_cover hfi hgi hann hB
    hfends hgends hx hxend
  have hconn := (isConnected_stdSimplexBoundary 0).prod
    (isConnected_Ioo (zero_lt_one : (0 : ℝ) < 1))
  rw [hX.boundary_eq_frontier] at hfempty hgempty hcover
  exact opposite_sides_of_local_two_set_cover hX.isCompact.isClosed
    (hconn.image f (hf.mono (prod_mono_right Ioo_subset_Icc_self))).isPreconnected
    (hconn.image g (hg.mono (prod_mono_right Ioo_subset_Icc_self))).isPreconnected
    hfempty hgempty (closure_mono inter_subset_left hin)
    (closure_mono inter_subset_left hout) hV hcover

theorem IsPLCellOn.opposite_ordered_band_sides_of_chart_crossings
    {M ι : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [Preorder ι]
    {X S Y B : Set M} (hX : IsPLCellOn 3 X S) (hY : IsPLCellOn 3 Y B)
    {J D₀ D₁ : ι → Set M}
    (hcap : ∀ r, IsPLCellOn 2 (D₀ r) (J r) ∧ IsPLCellOn 2 (D₁ r) (J r) ∧
      D₀ r ∪ D₁ r = B ∧ D₀ r ∩ D₁ r = J r)
    (hmono : Monotone D₀) (hanti : Antitone D₁)
    (hdis : ∀ r s, r < s → Disjoint (D₀ r) (D₁ s))
    (hJ : ∀ r, J r ⊆ S) (hJdis : Pairwise fun i j => Disjoint (J i) (J j))
    {i j k : ι} (hij : i < j) (hjk : j < k)
    {f g : (Fin 3 → ℝ) × ℝ → M}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfi : InjOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hgi : InjOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (himagef : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) = D₁ i ∩ D₀ j)
    (himageg : g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) = D₁ j ∩ D₀ k)
    (hfzero : f '' (stdSimplexBoundary 2 ×ˢ {0}) = J i)
    (hfone : f '' (stdSimplexBoundary 2 ×ˢ {1}) = J j)
    (hgzero : g '' (stdSimplexBoundary 2 ×ˢ {0}) = J j)
    (hgone : g '' (stdSimplexBoundary 2 ×ˢ {1}) = J k)
    (hfempty : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) S)
    (hgempty : Disjoint (g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) S)
    (hcross : ∀ x ∈ J j, ∃ c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)),
      x ∈ c.source ∧
        HasPLCrossingAt (c '' (B ∩ c.source)) (c '' (S ∩ c.source)) (c x)) :
    (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆ interior X ∧
      g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆ Xᶜ) ∨
    (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆ Xᶜ ∧
      g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆ interior X) := by
  have hann : IsAnnulusOn (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∪
      g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) (J i) (J k) := by
    rw [himagef, himageg]
    exact hY.isAnnulusOn_union_of_ordered_caps hcap hmono hanti hdis hij hjk
  have hB : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∪
      g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ B := by
    rw [himagef, himageg]
    exact union_subset (inter_subset_left.trans (subset_union_right.trans (hcap i).2.2.1.subset))
      (inter_subset_left.trans (subset_union_right.trans (hcap j).2.2.1.subset))
  obtain ⟨x, hx⟩ : (J j).Nonempty := hfone ▸
    ((isConnected_stdSimplexBoundary 0).nonempty.prod (singleton_nonempty (1 : ℝ))).image f
  have hxf : x ∈ f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) :=
    image_mono (prod_mono_right (by simp)) (hfone.symm ▸ hx)
  have hxend : x ∉ J i ∪ J k := by
    rintro (hxi | hxk)
    · exact disjoint_left.mp (hJdis hij.ne') hx hxi
    · exact disjoint_left.mp (hJdis hjk.ne) hx hxk
  obtain ⟨c, hxc, hcross⟩ := hcross x hx
  apply hX.opposite_lateral_band_sides_of_chart_crossing hY hf hfi hg hgi hann hB
    (by rw [hfzero, hfone]; exact union_subset (hJ i) (hJ j))
    (by rw [hgzero, hgone]; exact union_subset (hJ j) (hJ k))
    hfempty hgempty (hJ j hx) (Or.inl hxf) hxend c hxc hcross

end DifferentialGeometry.Topology.PiecewiseLinear
