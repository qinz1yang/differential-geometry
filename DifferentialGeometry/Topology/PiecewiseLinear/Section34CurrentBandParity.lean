import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentBandAlternation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34OrderedBandSideParity

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.current_band_sides_eq_of_parity
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {n : ℕ}
    {X S Y B : Set M} (hX : IsPLCellOn 3 X S) (hY : IsPLCellOn 3 Y B)
    {J D₀ D₁ : Fin n → Set M}
    (hcap : ∀ r, IsPLCellOn 2 (D₀ r) (J r) ∧ IsPLCellOn 2 (D₁ r) (J r) ∧
      D₀ r ∪ D₁ r = B ∧ D₀ r ∩ D₁ r = J r)
    (hmono : Monotone D₀) (hanti : Antitone D₁)
    (hdis : ∀ r s, r < s → Disjoint (D₀ r) (D₁ s))
    (hJ : ∀ r, J r ⊆ S) (hJdis : Pairwise fun i j => Disjoint (J i) (J j))
    (hcross : ∀ r, ∀ x ∈ J r,
      ∃ c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)), x ∈ c.source ∧
        HasPLCrossingAt (c '' (B ∩ c.source)) (c '' (S ∩ c.source)) (c x))
    {f : ℕ → (Fin 3 → ℝ) × ℝ → M}
    (hbands : ∀ r (hr : r + 1 < n),
      ContinuousOn (f r) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
      InjOn (f r) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
      f r '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) =
        D₁ ⟨r, by omega⟩ ∩ D₀ ⟨r + 1, hr⟩ ∧
      f r '' (stdSimplexBoundary 2 ×ˢ {0}) = J ⟨r, by omega⟩ ∧
      f r '' (stdSimplexBoundary 2 ×ˢ {1}) = J ⟨r + 1, hr⟩ ∧
      Disjoint (f r '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) S)
    {i j : ℕ} (hi : i + 1 < n) (hj : j + 1 < n) (hpar : i % 2 = j % 2) :
    (f i '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆ interior X ∧
      f j '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆ interior X) ∨
    (f i '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆ Xᶜ ∧
      f j '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆ Xᶜ) := by
  apply Set.same_side_of_local_alternation (n := n - 1)
    (disjoint_compl_right.mono_left interior_subset) ?_ ?_ ?_ (by omega) (by omega) hpar
  · intro r _
    exact ((isConnected_stdSimplexBoundary 0).nonempty.prod
      (nonempty_Ioo.mpr (zero_lt_one : (0 : ℝ) < 1))).image (f r)
  · intro r hr
    obtain ⟨hf, -, -, -, -, hempty⟩ := hbands r (by omega)
    exact lateral_open_subset_one_side hX.isCompact.isClosed hf
      (hX.boundary_eq_frontier ▸ hempty)
  · intro r hr
    obtain ⟨hf, hfi, himagef, hfzero, hfone, hfempty⟩ := hbands r (by omega)
    obtain ⟨hg, hgi, himageg, hgzero, hgone, hgempty⟩ := hbands (r + 1) (by omega)
    exact hX.opposite_ordered_band_sides_of_chart_crossings hY hcap hmono hanti hdis hJ hJdis
      (i := ⟨r, by omega⟩) (j := ⟨r + 1, by omega⟩) (k := ⟨r + 1 + 1, by omega⟩)
      (by exact_mod_cast Nat.lt_succ_self r) (by exact_mod_cast Nat.lt_succ_self (r + 1))
      hf hfi hg hgi himagef himageg hfzero hfone hgzero hgone hfempty hgempty (hcross _)

end DifferentialGeometry.Topology.PiecewiseLinear
