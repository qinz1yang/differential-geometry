import DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedCellSides
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalLocalChart

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem signs_of_frontier_reading
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F]
    {D : Set E} {X : Set F} {f : E → F} (ℓ : E →ₗ[ℝ] ℝ)
    (hD : Convex ℝ D) (hf : ContinuousOn f D) (hX : IsClosed X)
    (hzero : ∀ p ∈ D, f p ∈ frontier X ↔ ℓ p = 0)
    {a b : E} (ha : a ∈ D) (hb : b ∈ D) (hap : 0 < ℓ a) (hbn : ℓ b < 0)
    (haX : f a ∈ X) (hbX : f b ∉ interior X) :
    ∀ p ∈ D, (f p ∈ interior X ↔ 0 < ℓ p) ∧ (f p ∈ X ↔ 0 ≤ ℓ p) := by
  have hdis (T : Set ℝ) (hT : 0 ∉ T) : Disjoint (f '' (D ∩ ℓ ⁻¹' T)) (frontier X) := by
    refine disjoint_left.mpr ?_
    rintro y ⟨p, hp, rfl⟩ hy
    exact hT ((hzero p hp.1).mp hy ▸ hp.2)
  have hapos : f a ∈ interior X := (mem_interior_iff_notMem_frontier haX).mpr
    (fun h => hap.ne' ((hzero a ha).mp h))
  have hbneg : f b ∈ Xᶜ := fun h => hbX ((mem_interior_iff_notMem_frontier h).mpr
    (fun h => hbn.ne ((hzero b hb).mp h)))
  have hpos : f '' (D ∩ ℓ ⁻¹' Ioi 0) ⊆ interior X :=
    DifferentialGeometry.Topology.subset_interior_of_isPreconnected_of_disjoint_frontier
      ((hD.inter ((convex_Ioi (0 : ℝ)).linear_preimage ℓ)).isPreconnected.image f
        (hf.mono inter_subset_left)) (hdis _ (by simp))
      ⟨f a, ⟨a, ⟨ha, hap⟩, rfl⟩, hapos⟩
  have hneg : f '' (D ∩ ℓ ⁻¹' Iio 0) ⊆ Xᶜ := by
    have h := DifferentialGeometry.Topology.subset_interior_of_isPreconnected_of_disjoint_frontier
      ((hD.inter ((convex_Iio (0 : ℝ)).linear_preimage ℓ)).isPreconnected.image f
        (hf.mono inter_subset_left))
      (show Disjoint (f '' (D ∩ ℓ ⁻¹' Iio 0)) (frontier Xᶜ) by
        rw [frontier_compl]; exact hdis _ (by simp))
      ⟨f b, ⟨b, ⟨hb, hbn⟩, rfl⟩, hX.isOpen_compl.interior_eq.symm ▸ hbneg⟩
    rwa [hX.isOpen_compl.interior_eq] at h
  intro p hp
  constructor
  · constructor
    · intro h
      by_contra hn
      rcases lt_or_eq_of_le (le_of_not_gt hn) with hn | hn
      · exact hneg ⟨p, ⟨hp, hn⟩, rfl⟩ (interior_subset h)
      · exact disjoint_left.mp disjoint_interior_frontier h ((hzero p hp).mpr hn)
    · exact fun h => hpos ⟨p, ⟨hp, h⟩, rfl⟩
  · constructor
    · intro h
      by_contra hn
      exact hneg ⟨p, ⟨hp, lt_of_not_ge hn⟩, rfl⟩ h
    · intro h
      rcases lt_or_eq_of_le h with h | h
      · exact interior_subset (hpos ⟨p, ⟨hp, h⟩, rfl⟩)
      · exact hX.frontier_subset ((hzero p hp).mpr h.symm)

private theorem horizontal_spokes_iff {p : ℝ × ℝ} (hp : p ∈ spliceSquare) :
    p ∈ segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 0) ∪
      segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 2) ↔ p.2 = 0 := by
  constructor
  · intro h
    rcases h with h | h <;>
      obtain ⟨t, -, -, -, ht⟩ := mem_segment_zero_prod_iff.mp h <;>
      simpa [fourSpokeModelLeaf] using ht
  · intro h
    by_cases hp0 : 0 ≤ p.1
    · exact Or.inl (mem_segment_zero_prod_iff.mpr
        ⟨p.1, hp0, hp.1.2, by simp [fourSpokeModelLeaf], by simpa [fourSpokeModelLeaf]⟩)
    · refine Or.inr (mem_segment_zero_prod_iff.mpr ⟨-p.1, by linarith, ?_, ?_, ?_⟩)
      · linarith [hp.1.1]
      · simp [fourSpokeModelLeaf]
      · simpa [fourSpokeModelLeaf]

private theorem vertical_spokes_iff {p : ℝ × ℝ} (hp : p ∈ spliceSquare) :
    p ∈ segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 1) ∪
      segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 3) ↔ p.1 = 0 := by
  constructor
  · intro h
    rcases h with h | h <;>
      obtain ⟨t, -, -, ht, -⟩ := mem_segment_zero_prod_iff.mp h <;>
      simpa [fourSpokeModelLeaf] using ht
  · intro h
    by_cases hp0 : 0 ≤ p.2
    · exact Or.inl (mem_segment_zero_prod_iff.mpr
        ⟨p.2, hp0, hp.2.2, by simpa [fourSpokeModelLeaf], by simp [fourSpokeModelLeaf]⟩)
    · refine Or.inr (mem_segment_zero_prod_iff.mpr ⟨-p.2, by linarith, ?_, ?_, ?_⟩)
      · linarith [hp.2.1]
      · simpa [fourSpokeModelLeaf]
      · simp [fourSpokeModelLeaf]

theorem IsCylindricalDiagram.crossing_neighborhood_sign_readings
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {C X Y : Set E}
    (hf : IsCylindricalDiagram f spliceSquare C)
    (hends : ∀ x ∈ spliceSquare, f (x, 0) = f (x, 1))
    (hfirst : f '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2) = C ∩ frontier X)
    (hsecond : f '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3) = C ∩ frontier Y)
    (hpages : ∀ i : Fin 4, f '' section34MarkedRibbon i = C ∩
      ![frontier X ∩ Y, frontier Y ∩ X, frontier X \ interior Y, frontier Y \ interior X] i)
    (hX : IsClosed X) (hY : IsClosed Y) :
    ∀ p ∈ spliceCylinder,
      (f p ∈ interior X ↔ 0 < p.1.2) ∧ (f p ∈ X ↔ 0 ≤ p.1.2) ∧
      (f p ∈ interior Y ↔ 0 < p.1.1) ∧ (f p ∈ Y ↔ 0 ≤ p.1.1) := by
  have hreading (i j : Fin 4) (p : (ℝ × ℝ) × ℝ) (hp : p ∈ spliceCylinder) :
      f p ∈ f '' (section34MarkedRibbon i ∪ section34MarkedRibbon j) ↔
        p.1 ∈ segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ∪
          segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf j) := by
    rw [section34MarkedRibbon, section34MarkedRibbon, ← union_prod]
    exact hf.mem_image_base_iff_of_equal_ends hends hp (union_subset
      (segment_zero_fourSpokeModelLeaf_subset i) (segment_zero_fourSpokeModelLeaf_subset j))
  have hzeroX (p) (hp : p ∈ spliceCylinder) : f p ∈ frontier X ↔ p.1.2 = 0 := by
    have h := (hreading 0 2 p hp).trans (horizontal_spokes_iff hp.1)
    rwa [hfirst, mem_inter_iff, and_iff_right (hf.image_eq ▸ mem_image_of_mem f hp)] at h
  have hzeroY (p) (hp : p ∈ spliceCylinder) : f p ∈ frontier Y ↔ p.1.1 = 0 := by
    have h := (hreading 1 3 p hp).trans (vertical_spokes_iff hp.1)
    rwa [hsecond, mem_inter_iff, and_iff_right (hf.image_eq ▸ mem_image_of_mem f hp)] at h
  have hpoint (i : Fin 4) : (fourSpokeModelLeaf i, (1 / 2 : ℝ)) ∈
      section34MarkedRibbon i := ⟨right_mem_segment ℝ _ _, by norm_num, by norm_num⟩
  have hpointC (i : Fin 4) : (fourSpokeModelLeaf i, (1 / 2 : ℝ)) ∈ spliceCylinder :=
    section34_marked_ribbon_subset_cylinder i (hpoint i)
  have hpointP (i : Fin 4) := (hpages i).subset (mem_image_of_mem f (hpoint i))
  have hconvex : Convex ℝ spliceCylinder :=
    (convex_Icc _ _ |>.prod (convex_Icc _ _)).prod (convex_Icc _ _)
  have hreadX := signs_of_frontier_reading
    ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ))
    hconvex hf.isPiecewiseAffineOn.continuousOn hX hzeroX
    (hpointC 1) (hpointC 3) (by norm_num [fourSpokeModelLeaf])
    (by norm_num [fourSpokeModelLeaf]) (hpointP 1).2.2 (hpointP 3).2.2
  have hreadY := signs_of_frontier_reading
    ((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ))
    hconvex hf.isPiecewiseAffineOn.continuousOn hY hzeroY
    (hpointC 0) (hpointC 2) (by norm_num [fourSpokeModelLeaf])
    (by norm_num [fourSpokeModelLeaf]) (hpointP 0).2.2 (hpointP 2).2.2
  exact fun p hp => ⟨(hreadX p hp).1, (hreadX p hp).2, hreadY p hp⟩

end DifferentialGeometry.Topology.PiecewiseLinear
