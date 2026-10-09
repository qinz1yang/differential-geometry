import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingNeighborhoodQuadrants
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FillingCrossingSides

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private def section34StrictQuadrant (a b : Bool) : Set (ℝ × ℝ) :=
  (if a then Ioc (0 : ℝ) 1 else Ico (-1 : ℝ) 0) ×ˢ
    (if b then Ioc (0 : ℝ) 1 else Ico (-1 : ℝ) 0)

private theorem strict_quadrant_subset (a b : Bool) :
    section34StrictQuadrant a b ⊆ section34CrossingQuadrant a b := by
  cases a <;> cases b <;>
    rintro ⟨x, y⟩ ⟨⟨hx₀, hx₁⟩, ⟨hy₀, hy₁⟩⟩ <;>
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

private theorem strict_quadrant_nonzero {a b : Bool} {p : ℝ × ℝ}
    (hp : p ∈ section34StrictQuadrant a b) : p.1 ≠ 0 ∧ p.2 ≠ 0 := by
  cases a <;> cases b <;> rcases hp with ⟨⟨hx₀, hx₁⟩, ⟨hy₀, hy₁⟩⟩ <;>
    constructor <;> intro h <;> simp_all only <;> linarith

private theorem mem_strict_quadrant_of_nonzero {a b : Bool} {p : ℝ × ℝ}
    (hp : p ∈ section34CrossingQuadrant a b) (hx : p.1 ≠ 0) (hy : p.2 ≠ 0) :
    p ∈ section34StrictQuadrant a b := by
  cases a <;> cases b
  · exact ⟨⟨hp.1.1, lt_of_le_of_ne hp.1.2 hx⟩, hp.2.1, lt_of_le_of_ne hp.2.2 hy⟩
  · exact ⟨⟨hp.1.1, lt_of_le_of_ne hp.1.2 hx⟩, lt_of_le_of_ne hp.2.1 hy.symm, hp.2.2⟩
  · exact ⟨⟨lt_of_le_of_ne hp.1.1 hx.symm, hp.1.2⟩, hp.2.1, lt_of_le_of_ne hp.2.2 hy⟩
  · exact ⟨⟨lt_of_le_of_ne hp.1.1 hx.symm, hp.1.2⟩,
      lt_of_le_of_ne hp.2.1 hy.symm, hp.2.2⟩

private theorem strict_quadrant_convex (a b : Bool) :
    Convex ℝ (section34StrictQuadrant a b) := by
  cases a <;> cases b
  · exact (convex_Ico _ _).prod (convex_Ico _ _)
  · exact (convex_Ico _ _).prod (convex_Ioc _ _)
  · exact (convex_Ioc _ _).prod (convex_Ico _ _)
  · exact (convex_Ioc _ _).prod (convex_Ioc _ _)

private theorem strict_quadrant_closure (a b : Bool) :
    closure (section34StrictQuadrant a b ×ˢ Icc (0 : ℝ) 1) =
      section34CrossingQuadrant a b ×ˢ Icc (0 : ℝ) 1 := by
  cases a <;> cases b <;>
    simp [section34StrictQuadrant, section34CrossingQuadrant, closure_prod_eq,
      closure_Ioc (by norm_num : (0 : ℝ) ≠ 1), closure_Ico (by norm_num : (-1 : ℝ) ≠ 0)]

theorem IsCylindricalDiagram.exists_filling_quadrant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {C X Y R : Set E}
    (hf : IsCylindricalDiagram f spliceSquare C)
    (hends : ∀ x ∈ spliceSquare, f (x, 0) = f (x, 1))
    (hfirst : f '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2) = C ∩ frontier X)
    (hsecond : f '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3) = C ∩ frontier Y)
    (hpages : ∀ i : Fin 4, f '' section34MarkedRibbon i = C ∩
      ![frontier X ∩ Y, frontier Y ∩ X, frontier X \ interior Y, frontier Y \ interior X] i)
    (hX : IsClosed X) (hY : IsClosed Y)
    (haxisC : f '' section34MarkedAxis ⊆ interior C)
    (haxisR : f '' section34MarkedAxis ⊆ R)
    (hR : IsClosed R) (hregR : closure (interior R) = R)
    (hconnR : IsPreconnected (interior R))
    (hcontactX : R ∩ frontier X ⊆ frontier R)
    (hcontactY : R ∩ frontier Y ⊆ frontier R)
    (hfrontR : frontier R ⊆ frontier X ∪ frontier Y) :
    ∃ a b : Bool, R ⊆ (if b then X else (interior X)ᶜ) ∧
      R ⊆ (if a then Y else (interior Y)ᶜ) ∧
      f '' (section34CrossingQuadrant a b ×ˢ Icc (0 : ℝ) 1) = C ∩ R := by
  obtain ⟨b, hRX⟩ := exists_closed_side_of_frontier_contact hX hregR hconnR hcontactX
  obtain ⟨a, hRY⟩ := exists_closed_side_of_frontier_contact hY hregR hconnR hcontactY
  have hread := hf.crossing_neighborhood_sign_readings hends hfirst hsecond hpages hX hY
  have hzeroX (p) (hp : p ∈ spliceCylinder) (hx : f p ∈ frontier X) : p.1.2 = 0 :=
    le_antisymm (le_of_not_gt fun h => hx.2 ((hread p hp).1.mpr h))
      ((hread p hp).2.1.mp (hX.frontier_subset hx))
  have hzeroY (p) (hp : p ∈ spliceCylinder) (hy : f p ∈ frontier Y) : p.1.1 = 0 :=
    le_antisymm (le_of_not_gt fun h => hy.2 ((hread p hp).2.2.1.mpr h))
      ((hread p hp).2.2.2.mp (hY.frontier_subset hy))
  have hQsub : section34StrictQuadrant a b ×ˢ Icc (0 : ℝ) 1 ⊆ spliceCylinder :=
    prod_mono ((strict_quadrant_subset a b).trans
      (section34_crossing_quadrant_subset_square a b)) Subset.rfl
  have hdis : Disjoint (f '' (section34StrictQuadrant a b ×ˢ Icc (0 : ℝ) 1))
      (frontier R) := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨p, hp, rfl⟩ hfr
    rcases hfrontR hfr with hx | hy
    · exact (strict_quadrant_nonzero hp.1).2 (hzeroX p (hQsub hp) hx)
    · exact (strict_quadrant_nonzero hp.1).1 (hzeroY p (hQsub hp) hy)
  have hmeet : (f '' (section34StrictQuadrant a b ×ˢ Icc (0 : ℝ) 1) ∩ R).Nonempty := by
    have hzero : ((0, 0), (0 : ℝ)) ∈ section34MarkedAxis := by
      norm_num [section34MarkedAxis]
    have hzaxis := mem_image_of_mem f hzero
    have hzR : f ((0, 0), 0) ∈ closure (interior R) := hregR.symm ▸ haxisR hzaxis
    obtain ⟨y, hyC, hyR⟩ := mem_closure_iff_nhds.mp hzR (interior C)
      (isOpen_interior.mem_nhds (haxisC hzaxis))
    have hyimage : y ∈ f '' (section34CrossingQuadrant a b ×ˢ Icc (0 : ℝ) 1) := by
      rw [hf.crossing_neighborhood_quadrant_images hends hfirst hsecond hpages hX hY]
      exact ⟨⟨interior_subset hyC, hRX (interior_subset hyR)⟩, hRY (interior_subset hyR)⟩
    obtain ⟨p, hp, rfl⟩ := hyimage
    have hpC : p ∈ spliceCylinder :=
      ⟨section34_crossing_quadrant_subset_square a b hp.1, hp.2⟩
    have hx : p.1.1 ≠ 0 := by
      intro hz
      have hfY : f p ∈ frontier Y := ⟨subset_closure ((hread p hpC).2.2.2.mpr hz.ge),
        fun h => lt_irrefl (0 : ℝ) (hz ▸ (hread p hpC).2.2.1.mp h)⟩
      exact (hcontactY ⟨interior_subset hyR, hfY⟩).2 hyR
    have hy : p.1.2 ≠ 0 := by
      intro hz
      have hfX : f p ∈ frontier X := ⟨subset_closure ((hread p hpC).2.1.mpr hz.ge),
        fun h => lt_irrefl (0 : ℝ) (hz ▸ (hread p hpC).1.mp h)⟩
      exact (hcontactX ⟨interior_subset hyR, hfX⟩).2 hyR
    exact ⟨f p, ⟨p, ⟨mem_strict_quadrant_of_nonzero hp.1 hx hy, hp.2⟩, rfl⟩,
      interior_subset hyR⟩
  have hQR : f '' (section34StrictQuadrant a b ×ˢ Icc (0 : ℝ) 1) ⊆ R :=
    IsPreconnected.subset_of_disjoint_frontier
      (((strict_quadrant_convex a b).prod (convex_Icc _ _)).isPreconnected.image f
        (hf.isPiecewiseAffineOn.continuousOn.mono hQsub)) hmeet hdis
  have hmap : MapsTo f (section34CrossingQuadrant a b ×ˢ Icc (0 : ℝ) 1) R := by
    have hcont : ContinuousOn f
        (closure (section34StrictQuadrant a b ×ˢ Icc (0 : ℝ) 1)) := by
      rw [strict_quadrant_closure]
      exact hf.isPiecewiseAffineOn.continuousOn.mono
        (prod_mono (section34_crossing_quadrant_subset_square a b) Subset.rfl)
    have hm : MapsTo f (section34StrictQuadrant a b ×ˢ Icc (0 : ℝ) 1) R :=
      fun p hp => hQR (mem_image_of_mem f hp)
    simpa only [strict_quadrant_closure, hR.closure_eq] using hm.closure_of_continuousOn hcont
  refine ⟨a, b, hRX, hRY, Subset.antisymm ?_ ?_⟩
  · rintro y ⟨p, hp, rfl⟩
    exact ⟨hf.image_eq ▸ mem_image_of_mem f
      ⟨section34_crossing_quadrant_subset_square a b hp.1, hp.2⟩, hmap hp⟩
  · rintro y ⟨hyC, hyR⟩
    rw [hf.crossing_neighborhood_quadrant_images hends hfirst hsecond hpages hX hY]
    exact ⟨⟨hyC, hRX hyR⟩, hRY hyR⟩

end DifferentialGeometry.Topology.PiecewiseLinear
