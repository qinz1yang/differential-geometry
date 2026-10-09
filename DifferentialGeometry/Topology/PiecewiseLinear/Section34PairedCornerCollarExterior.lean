import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCornerCollarExterior
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCornerNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.CellMapTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_paired_crossing_corner_exterior_collar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : Fin 2 → (ℝ × ℝ) × ℝ → E} {C : Fin 2 → Set E} {X Y R : Set E}
    (hf : ∀ k, IsCylindricalDiagram (f k) spliceSquare (C k))
    (hends : ∀ k, ∀ p ∈ spliceSquare, f k (p, 0) = f k (p, 1)) (a b : Fin 2 → Bool)
    (hfirst : ∀ k, f k '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2) =
      C k ∩ frontier X)
    (hsecond : ∀ k, f k '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3) =
      C k ∩ frontier Y)
    (hpages : ∀ k, ∀ i : Fin 4, f k '' section34MarkedRibbon i = C k ∩
      ![frontier X ∩ Y, frontier Y ∩ X, frontier X \ interior Y, frontier Y \ interior X] i)
    (hX : IsClosed X) (hY : IsClosed Y) (hR : IsClosed R)
    (hquad : ∀ k, f k '' (section34CrossingQuadrant (a k) (b k) ×ˢ Icc (0 : ℝ) 1) = C k ∩ R)
    (hcontactX : R ∩ frontier X ⊆ frontier R)
    (hcontactY : R ∩ frontier Y ⊆ frontier R)
    (hfrontR : frontier R ⊆ frontier X ∪ frontier Y)
    (haxisC : ∀ k, f k '' section34MarkedAxis ⊆ interior (C k))
    (hdis : Disjoint (C 0) (C 1)) :
    let L := fun k => section34CornerBase (a k) (b k)
    let B := fun k => f k '' (L k ×ˢ Icc (0 : ℝ) 1)
    let Q := fun k => section34CornerExteriorPush (a k) (b k) '' (L k ×ˢ Icc (0 : ℝ) 1)
    let W := fun k => f k '' (Q k ×ˢ Icc (0 : ℝ) 1)
    ∃ ρ : E × ℝ → E,
      IsPLHomeomorphOn ρ ((B 0 ∪ B 1) ×ˢ Icc (0 : ℝ) 1) (W 0 ∪ W 1) ∧
      IsPolyhedron (B 0 ∪ B 1) ∧ IsPolyhedron (W 0 ∪ W 1) ∧
      (∀ y ∈ B 0 ∪ B 1, ρ (y, 0) = y) ∧
      (∀ k, ∀ p ∈ L k, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        ρ (f k (p, s), t) = f k (section34CornerExteriorPush (a k) (b k) (p, t), s)) ∧
      (∀ k, ρ '' (B k ×ˢ Icc (0 : ℝ) 1) = W k) ∧
      W 0 ∪ W 1 ⊆ (C 0 ∪ C 1) ∩ closure Rᶜ ∧ B 0 ∪ B 1 ⊆ frontier R ∧
      (W 0 ∪ W 1) ∩ R = B 0 ∪ B 1 ∧
      (W 0 ∪ W 1) ∩ frontier R = B 0 ∪ B 1 ∧
      (∀ y ∈ B 0 ∪ B 1, ∀ t ∈ Ioc (0 : ℝ) 1, ρ (y, t) ∉ R) ∧
      (∀ k, ∀ p ∈ L k, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        (ρ (f k (p, s), t) ∈ frontier X ↔ p.2 = (if b k then t / 2 else -t / 2)) ∧
        (ρ (f k (p, s), t) ∈ frontier Y ↔ p.1 = (if a k then t / 2 else -t / 2))) ∧
      B 0 ∪ B 1 ∈ 𝓝ˢ[frontier R]
        ((f 0 '' section34MarkedAxis) ∪ (f 1 '' section34MarkedAxis)) := by
  let L := fun k => section34CornerBase (a k) (b k)
  let B := fun k => f k '' (L k ×ˢ Icc (0 : ℝ) 1)
  let Q := fun k => section34CornerExteriorPush (a k) (b k) '' (L k ×ˢ Icc (0 : ℝ) 1)
  let W := fun k => f k '' (Q k ×ˢ Icc (0 : ℝ) 1)
  have hex (k : Fin 2) := (hf k).exists_crossing_corner_collar_outside_filling (hends k)
    (a k) (b k) (hfirst k) (hsecond k) (hpages k) hX hY hR (hquad k)
    hcontactX hcontactY
  choose η hη hzero hconj hWC hWR hWbd hread using hex
  have hBpoly (k : Fin 2) : IsPolyhedron (B k) := by
    have hp : IsPolyhedron (L k ×ˢ Icc (0 : ℝ) 1) :=
      (section34_corner_base_isPolyhedron (a k) (b k)).prod
      isHPolytope_Icc.isPolyhedron
    have hsub : L k ×ˢ Icc (0 : ℝ) 1 ⊆ spliceCylinder :=
      prod_mono_left ((section34_corner_base_subset (a k) (b k)).trans
        (section34_crossing_quadrant_subset_square (a k) (b k)))
    exact ((hf k).isPiecewiseAffineOn.mono_of_isPolyhedron hp hsub).isPolyhedron_image hp
  have hBW (k : Fin 2) : B k ⊆ W k := by
    intro y hy
    exact hzero k y hy ▸ (hη k).bijOn.mapsTo ⟨hy, by norm_num⟩
  have hBd : Disjoint (B 0 ×ˢ Icc (0 : ℝ) 1) (B 1 ×ˢ Icc (0 : ℝ) 1) := by
    refine disjoint_left.mpr fun z hz hz' => ?_
    exact disjoint_left.mp hdis (hWC 0 (hBW 0 hz.1)).1 (hWC 1 (hBW 1 hz'.1)).1
  have hWd : Disjoint (W 0) (W 1) :=
    hdis.mono ((hWC 0).trans inter_subset_left) ((hWC 1).trans inter_subset_left)
  obtain ⟨ρ, hρ, hρ₀, hρ₁⟩ := exists_isPLHomeomorphOn_union
    ((hBpoly 0).prod isHPolytope_Icc.isPolyhedron)
    ((hBpoly 1).prod isHPolytope_Icc.isPolyhedron) (hη 0) (hη 1)
    (by rw [hBd.inter_eq]; exact eqOn_empty _ _)
    (by intro y hy; rw [hWd.inter_eq] at hy; exact hy.elim)
  rw [← union_prod] at hρ
  have heq (k : Fin 2) : EqOn ρ (η k) (B k ×ˢ Icc (0 : ℝ) 1) := by
    fin_cases k
    · exact hρ₀
    · exact hρ₁
  have hρzero (y : E) (hy : y ∈ B 0 ∪ B 1) : ρ (y, 0) = y := by
    rcases hy with hy | hy
    · exact (hρ₀ ⟨hy, by norm_num⟩).trans (hzero 0 y hy)
    · exact (hρ₁ ⟨hy, by norm_num⟩).trans (hzero 1 y hy)
  have hWsub : W 0 ∪ W 1 ⊆ (C 0 ∪ C 1) ∩ closure Rᶜ := by
    rintro x (hx | hx)
    · exact ⟨Or.inl (hWC 0 hx).1, (hWC 0 hx).2⟩
    · exact ⟨Or.inr (hWC 1 hx).1, (hWC 1 hx).2⟩
  have hWfront : (W 0 ∪ W 1) ∩ frontier R = B 0 ∪ B 1 := by
    rw [union_inter_distrib_right, hWbd 0, hWbd 1]
  have hWcontact : (W 0 ∪ W 1) ∩ R = B 0 ∪ B 1 := by
    rw [union_inter_distrib_right, hWR 0, hWR 1]
  have hBfront : B 0 ∪ B 1 ⊆ frontier R :=
    hWfront.symm.subset.trans inter_subset_right
  have hBunion := (hBpoly 0).union (hBpoly 1)
  have hWpoly : IsPolyhedron (W 0 ∪ W 1) := by
    rw [← hρ.image_eq]
    exact (hBunion.prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
      hρ.isPiecewiseAffineOn hρ.bijOn.injOn
  refine ⟨ρ, hρ, hBunion, hWpoly, hρzero, ?_, ?_, hWsub, hBfront, hWcontact,
    hWfront, ?_, ?_, ?_⟩
  · intro k p hp s hs t ht
    exact (heq k (show (f k (p, s), t) ∈ B k ×ˢ Icc (0 : ℝ) 1 from
      ⟨mem_image_of_mem (f k) ⟨hp, hs⟩, ht⟩)).trans
      (hconj k p hp s hs t ht)
  · exact fun k => (heq k).image_eq.trans (hη k).image_eq
  · intro y hy t ht
    have hyW := hρ.bijOn.mapsTo
      (show (y, t) ∈ (B 0 ∪ B 1) ×ˢ Icc (0 : ℝ) 1 from ⟨hy, ht.1.le, ht.2⟩)
    intro hyR
    have hyB := hWcontact.subset ⟨hyW, hyR⟩
    have he := hρ.bijOn.injOn ⟨hy, ht.1.le, ht.2⟩
      (show (ρ (y, t), 0) ∈ (B 0 ∪ B 1) ×ˢ Icc (0 : ℝ) 1 from
        ⟨hyB, by norm_num⟩) (hρzero _ hyB).symm
    exact ht.1.ne' (congrArg Prod.snd he)
  · intro k p hp s hs t ht
    rw [heq k (show (f k (p, s), t) ∈ B k ×ˢ Icc (0 : ℝ) 1 from
      ⟨mem_image_of_mem (f k) ⟨hp, hs⟩, ht⟩)]
    exact hread k p hp s hs t ht
  · have hn (k : Fin 2) := (hf k).crossing_corner_base_mem_nhdsSetWithin (hends k)
      (a k) (b k) (hfirst k) (hsecond k) (hpages k) hX hY hR (hquad k) hfrontR (haxisC k)
    obtain ⟨V₀, hV₀, haxis₀, hVB₀⟩ := mem_nhdsSetWithin.mp (hn 0)
    obtain ⟨V₁, hV₁, haxis₁, hVB₁⟩ := mem_nhdsSetWithin.mp (hn 1)
    refine mem_nhdsSetWithin.mpr ⟨V₀ ∪ V₁, hV₀.union hV₁,
      union_subset_union haxis₀ haxis₁, ?_⟩
    rintro x ⟨hx | hx, hxR⟩
    · exact Or.inl (hVB₀ ⟨hx, hxR⟩)
    · exact Or.inr (hVB₁ ⟨hx, hxR⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
