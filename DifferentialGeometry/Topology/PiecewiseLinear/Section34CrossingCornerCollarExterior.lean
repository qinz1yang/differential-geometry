import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCornerCollar
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCornerCollarExteriorModel

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.exists_crossing_corner_exterior_collar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {C : Set E} (hf : IsCylindricalDiagram f spliceSquare C)
    (hends : ∀ p ∈ spliceSquare, f (p, 0) = f (p, 1)) (a b : Bool) :
    let L := section34CornerBase a b
    let B := f '' (L ×ˢ Icc (0 : ℝ) 1)
    let Q := section34CornerExteriorPush a b '' (L ×ˢ Icc (0 : ℝ) 1)
    ∃ ρ : E × ℝ → E,
      IsPLHomeomorphOn ρ (B ×ˢ Icc (0 : ℝ) 1) (f '' (Q ×ˢ Icc (0 : ℝ) 1)) ∧
      (∀ y ∈ B, ρ (y, 0) = y) ∧
      (∀ p ∈ L, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        ρ (f (p, s), t) = f (section34CornerExteriorPush a b (p, t), s)) ∧
      f '' (Q ×ˢ Icc (0 : ℝ) 1) ⊆ C := by
  dsimp only
  have hL := section34_corner_base_isPolyhedron a b
  have hLP := (section34_corner_base_subset a b).trans
    (section34_crossing_quadrant_subset_square a b)
  apply hf.exists_collar_of_base_embedding hends hL hLP
    (section34_corner_exterior_push_isPLHomeomorphOn a b)
  · rintro _ ⟨z, hz, rfl⟩
    exact section34_corner_exterior_push_mapsTo a b hz
  · exact fun p _ => section34_corner_exterior_push_zero a b p

theorem IsCylindricalDiagram.exists_crossing_corner_collar_outside_filling
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {C X Y R : Set E}
    (hf : IsCylindricalDiagram f spliceSquare C)
    (hends : ∀ p ∈ spliceSquare, f (p, 0) = f (p, 1)) (a b : Bool)
    (hfirst : f '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2) = C ∩ frontier X)
    (hsecond : f '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3) = C ∩ frontier Y)
    (hpages : ∀ i : Fin 4, f '' section34MarkedRibbon i = C ∩
      ![frontier X ∩ Y, frontier Y ∩ X, frontier X \ interior Y, frontier Y \ interior X] i)
    (hX : IsClosed X) (hY : IsClosed Y) (hR : IsClosed R)
    (hquad : f '' (section34CrossingQuadrant a b ×ˢ Icc (0 : ℝ) 1) = C ∩ R)
    (hcontactX : R ∩ frontier X ⊆ frontier R)
    (hcontactY : R ∩ frontier Y ⊆ frontier R) :
    let L := section34CornerBase a b
    let B := f '' (L ×ˢ Icc (0 : ℝ) 1)
    let Q := section34CornerExteriorPush a b '' (L ×ˢ Icc (0 : ℝ) 1)
    let W := f '' (Q ×ˢ Icc (0 : ℝ) 1)
    ∃ ρ : E × ℝ → E, IsPLHomeomorphOn ρ (B ×ˢ Icc (0 : ℝ) 1) W ∧
      (∀ y ∈ B, ρ (y, 0) = y) ∧
      (∀ p ∈ L, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        ρ (f (p, s), t) = f (section34CornerExteriorPush a b (p, t), s)) ∧
      W ⊆ C ∩ closure Rᶜ ∧ W ∩ R = B ∧ W ∩ frontier R = B ∧
      ∀ p ∈ L, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        (ρ (f (p, s), t) ∈ frontier X ↔ p.2 = (if b then t / 2 else -t / 2)) ∧
        (ρ (f (p, s), t) ∈ frontier Y ↔ p.1 = (if a then t / 2 else -t / 2)) := by
  dsimp only
  let L := section34CornerBase a b
  let B := f '' (L ×ˢ Icc (0 : ℝ) 1)
  let Q := section34CornerExteriorPush a b '' (L ×ˢ Icc (0 : ℝ) 1)
  let W := f '' (Q ×ˢ Icc (0 : ℝ) 1)
  obtain ⟨ρ, hρ, hzero, hconj, hWC⟩ := hf.exists_crossing_corner_exterior_collar hends a b
  have hread := hf.crossing_neighborhood_sign_readings hends hfirst hsecond hpages hX hY
  have hXread (p) (hp : p ∈ spliceCylinder) : f p ∈ frontier X ↔ p.1.2 = 0 := by
    rw [frontier, hX.closure_eq, mem_sdiff, (hread p hp).2.1, (hread p hp).1]
    exact ⟨fun h => le_antisymm (le_of_not_gt h.2) h.1, fun h => by simp [h]⟩
  have hYread (p) (hp : p ∈ spliceCylinder) : f p ∈ frontier Y ↔ p.1.1 = 0 := by
    rw [frontier, hY.closure_eq, mem_sdiff, (hread p hp).2.2.2, (hread p hp).2.2.1]
    exact ⟨fun h => le_antisymm (le_of_not_gt h.2) h.1, fun h => by simp [h]⟩
  have hLP := (section34_corner_base_subset a b).trans
    (section34_crossing_quadrant_subset_square a b)
  have hBW : B ⊆ W := by
    rintro _ ⟨⟨p, s⟩, ⟨hp, hs⟩, rfl⟩
    exact ⟨(p, s), ⟨⟨(p, 0), ⟨hp, by norm_num⟩,
      section34_corner_exterior_push_zero a b p⟩, hs⟩, rfl⟩
  have hBR : B ⊆ R := by
    rintro _ ⟨⟨p, s⟩, ⟨hp, hs⟩, rfl⟩
    exact (hquad.subset ⟨(p, s), ⟨section34_corner_base_subset a b hp, hs⟩, rfl⟩).2
  have hBfront : B ⊆ frontier R := by
    rintro _ ⟨⟨p, s⟩, ⟨hp, hs⟩, rfl⟩
    have hRp := hBR (mem_image_of_mem f ⟨hp, hs⟩)
    have hpC : (p, s) ∈ spliceCylinder := ⟨hLP hp, hs⟩
    rcases hp with ⟨-, hp⟩ | ⟨hp, -⟩
    · exact hcontactX ⟨hRp, (hXread _ hpC).mpr hp⟩
    · exact hcontactY ⟨hRp, (hYread _ hpC).mpr hp⟩
  have hWR : W ∩ R ⊆ B := by
    rintro y ⟨⟨⟨q, s⟩, ⟨⟨⟨p, t⟩, ⟨hp, ht⟩, rfl⟩, hs⟩, rfl⟩, hyR⟩
    have hpC : (section34CornerExteriorPush a b (p, t), s) ∈ spliceCylinder :=
      ⟨section34_corner_exterior_push_mapsTo a b ⟨hp, ht⟩, hs⟩
    have hyQ := hquad.symm.subset ⟨hf.image_eq ▸ mem_image_of_mem f hpC, hyR⟩
    have hbase := (hf.mem_image_base_iff_of_equal_ends hends hpC
      (section34_crossing_quadrant_subset_square a b)).mp hyQ
    have ht0 := (section34_corner_exterior_push_mem_quadrant a b hp ht).mp hbase
    change t = 0 at ht0
    subst t
    simpa only [section34_corner_exterior_push_zero] using
      (show f (p, s) ∈ B from ⟨(p, s), ⟨hp, hs⟩, rfl⟩)
  have hWout : W ⊆ closure Rᶜ := by
    intro y hy
    by_cases hyR : y ∈ R
    · have hh : y ∈ frontier Rᶜ := (frontier_compl R).symm ▸ hBfront (hWR ⟨hy, hyR⟩)
      exact hh.1
    · exact subset_closure hyR
  refine ⟨ρ, hρ, hzero, hconj, subset_inter hWC hWout,
    Subset.antisymm hWR (subset_inter hBW hBR),
    Subset.antisymm (fun _ hy => hWR ⟨hy.1, hR.frontier_subset hy.2⟩)
      (subset_inter hBW hBfront), ?_⟩
  intro p hp s hs t ht
  rw [hconj p hp s hs t ht]
  have hpC : (section34CornerExteriorPush a b (p, t), s) ∈ spliceCylinder :=
    ⟨section34_corner_exterior_push_mapsTo a b ⟨hp, ht⟩, hs⟩
  exact ⟨(hXread _ hpC).trans (section34_corner_exterior_push_sheet_contacts a b p t).2,
    (hYread _ hpC).trans (section34_corner_exterior_push_sheet_contacts a b p t).1⟩

end DifferentialGeometry.Topology.PiecewiseLinear
