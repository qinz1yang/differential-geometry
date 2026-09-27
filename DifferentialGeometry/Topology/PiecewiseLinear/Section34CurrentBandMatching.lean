import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentBandNoncrossing
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentBandParity
import DifferentialGeometry.Topology.PiecewiseLinear.Section34LateralBandReversal
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CircleOrderAdjacency

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_ordered_lateral_ends {M ι : Type*} [TopologicalSpace M] [LinearOrder ι]
    {f : (Fin 3 → ℝ) × ℝ → M} {J : ι → Set M} {i j : ι}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfi : InjOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hzero : f '' (stdSimplexBoundary 2 ×ˢ {0}) = J i)
    (hone : f '' (stdSimplexBoundary 2 ×ˢ {1}) = J j) :
    ∃ f' : (Fin 3 → ℝ) × ℝ → M,
      ContinuousOn f' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
      InjOn f' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
      f' '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) =
        f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
      f' '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) =
        f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ∧
      f' '' (stdSimplexBoundary 2 ×ˢ {0}) = J (min i j) ∧
      f' '' (stdSimplexBoundary 2 ×ˢ {1}) = J (max i j) := by
  rcases le_total i j with hij | hji
  · exact ⟨f, hf, hfi, rfl, rfl, by simpa only [min_eq_left hij] using hzero,
      by simpa only [max_eq_right hij] using hone⟩
  · obtain ⟨f', hf', hfi', hfc, hfo, hfz, hfon⟩ := exists_lateral_band_reversal hf hfi
    exact ⟨f', hf', hfi', hfc, hfo,
      by simpa only [min_eq_right hji] using hfz.trans hone,
      by simpa only [max_eq_left hji] using hfon.trans hzero⟩

theorem IsPLCellOn.not_interleaved_of_sorted_current_bands
    {M ι : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [LinearOrder ι]
    {X S Y B : Set M} (hX : IsPLCellOn 3 X S) (hY : IsPLCellOn 3 Y B)
    (hcross : ∀ x ∈ S ∩ B, ∃ c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)),
      x ∈ c.source ∧
        HasPLCrossingAt (c '' (B ∩ c.source)) (c '' (S ∩ c.source)) (c x))
    {J : ι → Set M} (hJ : ∀ r, J r ⊆ S)
    (hJdis : Pairwise fun i j => Disjoint (J i) (J j)) {i j k l : ι}
    {f g : (Fin 3 → ℝ) × ℝ → M}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfi : InjOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hgi : InjOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfB : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ B)
    (hgB : g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ B)
    (hfzero : f '' (stdSimplexBoundary 2 ×ˢ {0}) = J k)
    (hfone : f '' (stdSimplexBoundary 2 ×ˢ {1}) = J l)
    (hgzero : g '' (stdSimplexBoundary 2 ×ˢ {0}) = J i)
    (hgone : g '' (stdSimplexBoundary 2 ×ˢ {1}) = J j)
    (hfempty : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) S)
    (hgempty : Disjoint (g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) S)
    {C F : Set M} (hC : closure (interior C) = C)
    (hfront : frontier C = g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∪ F)
    (hfirst : S ∩ C = F) (hCside : C ⊆ X ∨ C ∩ X ⊆ S)
    (hinterval : ∀ r, J r ⊆ F ↔ min i j ≤ r ∧ r ≤ max i j)
    (hbands : (g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆ interior X ∧
      f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆ interior X) ∨
      (g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆ Xᶜ ∧
        f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆ Xᶜ)) :
    ¬ (min i j < min k l ∧ min k l < max i j ∧ max i j < max k l) := by
  obtain ⟨f', hf', hfi', hfc, hfo, hfz, hfon⟩ := exists_ordered_lateral_ends hf hfi hfzero hfone
  obtain ⟨g', hg', hgi', hgc, hgo, hgz, hgon⟩ := exists_ordered_lateral_ends hg hgi hgzero hgone
  exact hX.not_interleaved_of_current_matching_bands hY hcross hJ hJdis hf' hfi' hg' hgi'
    (hfc.subset.trans hfB) (hgc.subset.trans hgB) hfz hfon hgz hgon
    (by rwa [hfo]) (by rwa [hgo]) hC (by rwa [hgc]) hfirst hCside hinterval
    (by rwa [hgo, hfo])

theorem IsPLCellOn.exists_common_adjacent_pair_of_current_bands
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {n : ℕ} (hn : 1 < n)
    {X S Y B : Set M} (hX : IsPLCellOn 3 X S) (hY : IsPLCellOn 3 Y B)
    (hcross : ∀ x ∈ S ∩ B, ∃ c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)),
      x ∈ c.source ∧
        HasPLCrossingAt (c '' (B ∩ c.source)) (c '' (S ∩ c.source)) (c x))
    {J D₀ D₁ : Fin n → Set M} (p : Fin n ≃ Fin n)
    (hJ : ∀ r, J r ⊆ S) (hJdis : Pairwise fun i j => Disjoint (J i) (J j))
    (hcap : ∀ r, IsPLCellOn 2 (D₀ r) (J (p r)) ∧
      IsPLCellOn 2 (D₁ r) (J (p r)) ∧ D₀ r ∪ D₁ r = B ∧ D₀ r ∩ D₁ r = J (p r))
    (hmono : Monotone D₀) (hanti : Antitone D₁)
    (hdis : ∀ r s, r < s → Disjoint (D₀ r) (D₁ s))
    {f : ℕ → (Fin 3 → ℝ) × ℝ → M}
    (hbands : ∀ r (hr : r + 1 < n),
      ContinuousOn (f r) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
      InjOn (f r) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
      f r '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) =
        D₁ ⟨r, by omega⟩ ∩ D₀ ⟨r + 1, hr⟩ ∧
      f r '' (stdSimplexBoundary 2 ×ˢ {0}) = J (p ⟨r, by omega⟩) ∧
      f r '' (stdSimplexBoundary 2 ×ˢ {1}) = J (p ⟨r + 1, hr⟩) ∧
      Disjoint (f r '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) S)
    (hregions : ∀ r (hr : r + 1 < n), ∃ C F : Set M,
      closure (interior C) = C ∧
      frontier C = f r '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∪ F ∧
      S ∩ C = F ∧ (C ⊆ X ∨ C ∩ X ⊆ S) ∧
      ∀ t, J t ⊆ F ↔ min (p ⟨r, by omega⟩) (p ⟨r + 1, hr⟩) ≤ t ∧
        t ≤ max (p ⟨r, by omega⟩) (p ⟨r + 1, hr⟩)) :
    ∃ i j : Fin n, i.val + 1 = j.val ∧
      ((p i).val + 1 = (p j).val ∨ (p j).val + 1 = (p i).val) := by
  apply Fin.exists_common_adjacent_pair_of_same_parity_noninterleaving hn p
  intro i j k l hij hkl hpar
  have hi : i.val + 1 < n := hij ▸ j.isLt
  have hk : k.val + 1 < n := hkl ▸ l.isLt
  obtain ⟨hfi, hfii, himagei, hfzi, hfoni, hemptyi⟩ := hbands i.val hi
  obtain ⟨hfk, hfik, himagek, hfzk, hfonk, hemptyk⟩ := hbands k.val hk
  have hji : (⟨i.val + 1, hi⟩ : Fin n) = j := Fin.ext hij
  have hlk : (⟨k.val + 1, hk⟩ : Fin n) = l := Fin.ext hkl
  obtain ⟨C, F, hC, hfront, hfirst, hside, hint⟩ := hregions i.val hi
  have hB (r : Fin n) (hr : r.val + 1 < n) :
      f r.val '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ B := by
    rw [(hbands r.val hr).2.2.1]
    exact inter_subset_left.trans ((hcap r).2.2.1 ▸ subset_union_right)
  have hsame := hX.current_band_sides_eq_of_parity hY hcap hmono hanti hdis
    (fun r => hJ (p r)) (fun r s hrs => hJdis (p.injective.ne hrs))
    (fun r x hx => hcross x ⟨hJ (p r) hx,
      ((hcap r).2.2.1 ▸ subset_union_left) ((hcap r).2.2.2.superset hx).1⟩)
    hbands hi hk hpar
  simp only [Fin.eta, hji] at hfoni hint
  simp only [hlk] at hfonk
  exact hX.not_interleaved_of_sorted_current_bands hY hcross hJ hJdis
    hfk hfik hfi hfii (hB k hk) (hB i hi) hfzk hfonk hfzi hfoni
    hemptyk hemptyi hC hfront hfirst hside hint hsame

end DifferentialGeometry.Topology.PiecewiseLinear
