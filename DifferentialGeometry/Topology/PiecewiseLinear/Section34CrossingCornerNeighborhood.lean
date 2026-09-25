import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCornerCollarModel

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem mem_corner_of_small_of_zero {a b : Bool} {p : ℝ × ℝ}
    (hp : p ∈ section34CrossingQuadrant a b)
    (hsmall : p ∈ Ioo (-1 / 2 : ℝ) (1 / 2) ×ˢ Ioo (-1 / 2 : ℝ) (1 / 2))
    (hzero : p.1 = 0 ∨ p.2 = 0) : p ∈ section34CornerBase a b := by
  rcases hzero with hx | hy
  · right
    refine ⟨hx, ?_⟩
    have hy := hp.2
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, mem_Icc] at hy ⊢ <;>
      exact ⟨by linarith [hsmall.2.1], by linarith [hsmall.2.2]⟩
  · left
    refine ⟨?_, hy⟩
    have hx := hp.1
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte, mem_Icc] at hx ⊢ <;>
      exact ⟨by linarith [hsmall.1.1], by linarith [hsmall.1.2]⟩

theorem IsCylindricalDiagram.crossing_corner_base_mem_nhdsSetWithin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {C X Y R : Set E}
    (hf : IsCylindricalDiagram f spliceSquare C)
    (hends : ∀ p ∈ spliceSquare, f (p, 0) = f (p, 1)) (a b : Bool)
    (hfirst : f '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2) = C ∩ frontier X)
    (hsecond : f '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3) = C ∩ frontier Y)
    (hpages : ∀ i : Fin 4, f '' section34MarkedRibbon i = C ∩
      ![frontier X ∩ Y, frontier Y ∩ X, frontier X \ interior Y, frontier Y \ interior X] i)
    (hX : IsClosed X) (hY : IsClosed Y) (hR : IsClosed R)
    (hquad : f '' (section34CrossingQuadrant a b ×ˢ Icc (0 : ℝ) 1) = C ∩ R)
    (hfrontR : frontier R ⊆ frontier X ∪ frontier Y)
    (haxisC : f '' section34MarkedAxis ⊆ interior C) :
    f '' (section34CornerBase a b ×ˢ Icc (0 : ℝ) 1) ∈
      𝓝ˢ[frontier R] (f '' section34MarkedAxis) := by
  let V := Ioo (-1 / 2 : ℝ) (1 / 2) ×ˢ Ioo (-1 / 2 : ℝ) (1 / 2)
  let Z := (spliceSquare \ V) ×ˢ Icc (0 : ℝ) 1
  have hV : IsOpen V := isOpen_Ioo.prod isOpen_Ioo
  have hZ : IsCompact Z :=
    ((isCompact_Icc.prod isCompact_Icc).diff hV).prod isCompact_Icc
  have hZC : Z ⊆ spliceCylinder := prod_mono sdiff_subset subset_rfl
  have himage : IsClosed (f '' Z) :=
    (hZ.image_of_continuousOn (hf.isPiecewiseAffineOn.continuousOn.mono hZC)).isClosed
  let O := interior C \ f '' Z
  have hO : IsOpen O := isOpen_interior.sdiff himage
  have haxisO : f '' section34MarkedAxis ⊆ O := by
    intro x hx
    refine ⟨haxisC hx, ?_⟩
    obtain ⟨p, hp, rfl⟩ := hx
    rintro ⟨q, hq, heq⟩
    have hpC := section34_marked_ribbon_subset_cylinder 0
      (section34_marked_axis_subset_ribbon 0 hp)
    have hqp := hf.fst_eq_of_eq_of_equal_ends hends (hZC hq) hpC heq
    have hp0 : p.1 = 0 := hp.1
    have hq0 : q.1 = 0 := hqp.trans hp0
    apply hq.1.2
    rw [hq0]
    norm_num [V]
  refine mem_nhdsSetWithin.mpr ⟨O, hO, haxisO, ?_⟩
  rintro x ⟨hxO, hxR⟩
  obtain ⟨p, hp, rfl⟩ := hquad.symm.subset ⟨interior_subset hxO.1, hR.frontier_subset hxR⟩
  have hpC : p ∈ spliceCylinder :=
    ⟨section34_crossing_quadrant_subset_square a b hp.1, hp.2⟩
  have hpV : p.1 ∈ V := by
    by_contra hn
    exact hxO.2 ⟨p, ⟨⟨hpC.1, hn⟩, hp.2⟩, rfl⟩
  have hread := hf.crossing_neighborhood_sign_readings hends hfirst hsecond hpages hX hY p hpC
  have hzero : p.1.1 = 0 ∨ p.1.2 = 0 := by
    rcases hfrontR hxR with hx | hy
    · right
      exact le_antisymm (le_of_not_gt fun h => hx.2 (hread.1.mpr h))
        (hread.2.1.mp (hX.frontier_subset hx))
    · left
      exact le_antisymm (le_of_not_gt fun h => hy.2 (hread.2.2.1.mpr h))
        (hread.2.2.2.mp (hY.frontier_subset hy))
  exact ⟨p, ⟨mem_corner_of_small_of_zero hp.1 hpV hzero, hp.2⟩, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
