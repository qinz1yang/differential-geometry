import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentFillingRibbonTraces
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CollaredFillingCylinderExpanded

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_collared_filling_cylinder_of_cell_contacts
    {M : Type*} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {A As B Bs D F J₀ J₁ S : Set M}
    (hcellA : IsPLCellOn 3 A As) (hcellB : IsPLCellOn 3 B Bs)
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hP : IsPLBall 3 P) (hu : IsPLHomeomorphInto 3 u P)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 3 R)
    (hsolid : IsTopologicalSolidTorus R.space) (hRint : R.space ⊆ interior P)
    (hRS : u '' R.space ⊆ interior S)
    (hfront : u '' frontier R.space = D ∪ F)
    (hcontactA : As ∩ u '' R.space = F)
    (hcontactB : Bs ∩ u '' R.space = D)
    (hJDF : J₀ ∪ J₁ ⊆ D ∩ F)
    (hF : IsAnnulusOn F J₀ J₁) (hD : IsAnnulusOn D J₀ J₁)
    (hDF : D ∩ F = J₀ ∪ J₁)
    {C : Fin 2 → Set (EuclideanSpace ℝ (Fin 3))}
    {f : Fin 2 → (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hC : ∀ k, IsPolyhedron (C k)) (hCP : ∀ k, C k ⊆ interior P)
    (hf : ∀ k, IsCylindricalDiagram (f k) spliceSquare (C k))
    (haxis : ∀ k, u '' (f k '' section34MarkedAxis) = ![J₀, J₁] k)
    (hfirst : ∀ k, u '' (f k '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2)) =
      u '' C k ∩ As)
    (hsecond : ∀ k, u '' (f k '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3)) =
      u '' C k ∩ Bs)
    (hpages : ∀ k, ∀ l : Fin 4, u '' (f k '' section34MarkedRibbon l) = u '' C k ∩
      ![As ∩ B,
        Bs ∩ A,
        As \ interior (B),
        Bs \ interior (A)] l)
    (hJC : ∀ k, ![J₀, J₁] k ⊆ interior (u '' C k))
    (hends : ∀ k, ∀ p ∈ spliceSquare, f k (p, 0) = f k (p, 1)) (a b : Fin 2 → Bool)
    (hquad : ∀ k, f k '' (section34CrossingQuadrant (a k) (b k) ×ˢ Icc (0 : ℝ) 1) =
      C k ∩ R.space) (hdis : Disjoint (C 0) (C 1))
    {g : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hg : IsCylindricalDiagram g (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) R.space)
    (hgends : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, g (p, 0) = g (p, 1))
    (hgfront : frontier R.space =
      g '' (frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1)) :
    let J := (f 0 '' section34MarkedAxis) ∪ (f 1 '' section34MarkedAxis)
    let B := fun k => f k '' (section34CornerBase (a k) (b k) ×ˢ Icc (0 : ℝ) 1)
    ∃ (c : ℝ) (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (W : Set (EuclideanSpace ℝ (Fin 3)))
      (ρ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3))
      (H : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
      let V := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
      let D := Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c)
      IsPLBall 2 D ∧ IsCylindricalDiagram H D (R.space ∪ W) ∧
      (∀ z ∈ D, H (z, 0) = H (z, 1)) ∧
      EqOn H g (V ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ p ∈ frontier V, ∀ t ∈ Icc (0 : ℝ) c, ∀ s ∈ Icc (0 : ℝ) 1,
        H (section34SquareShellFlatten c (p, t), s) = ρ (g (p, s), t)) ∧
      u '' (R.space ∪ W) ⊆ interior S ∧
      0 < c ∧ c ≤ 1 ∧ L.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 L ∧
      L.space ⊆ frontier R.space ∩ (B 0 ∪ B 1) ∧ J ⊆ L.space ∧
      (∀ x ∈ J, L.space ∈ 𝓝[frontier R.space] x) ∧
      J = Function.invFunOn u P '' (J₀ ∪ J₁) ∧
      IsPolyhedron W ∧ W ⊆ interior P ∧ u '' W ⊆ interior S ∧
      IsPLHomeomorphOn ρ (frontier R.space ×ˢ Icc (0 : ℝ) c) W ∧
      (∀ x ∈ frontier R.space, ρ (x, 0) = x) ∧ W ∩ R.space = frontier R.space ∧
      MapsTo ρ (frontier R.space ×ˢ Ioc (0 : ℝ) c) (interior P \ R.space) ∧
      (∀ k, ∀ p ∈ section34CornerBase (a k) (b k), ∀ s ∈ Icc (0 : ℝ) 1,
        f k (p, s) ∈ L.space → ∀ t ∈ Icc (0 : ℝ) c,
          ρ (f k (p, s), t) = f k (section34CornerExteriorPush (a k) (b k) (p, t), s) ∧
          (u (ρ (f k (p, s), t)) ∈ As ↔
            p.2 = (if b k then t / 2 else -t / 2)) ∧
          (u (ρ (f k (p, s), t)) ∈ Bs ↔
            p.1 = (if a k then t / 2 else -t / 2))) ∧
      (∀ x ∈ frontier R.space, ∀ t ∈ Ioc (0 : ℝ) c,
        (u (ρ (x, t)) ∈ As ↔
          ∃ k p s, p ∈ section34CornerBase (a k) (b k) ∧ s ∈ Icc (0 : ℝ) 1 ∧
            x = f k (p, s) ∧ x ∈ L.space ∧ p.2 = (if b k then t / 2 else -t / 2)) ∧
        (u (ρ (x, t)) ∈ Bs ↔
          ∃ k p s, p ∈ section34CornerBase (a k) (b k) ∧ s ∈ Icc (0 : ℝ) 1 ∧
            x = f k (p, s) ∧ x ∈ L.space ∧ p.1 = (if a k then t / 2 else -t / 2))) ∧
      ∀ t ∈ Ioc (0 : ℝ) c,
        (u ∘ ρ) '' (frontier R.space ×ˢ {t}) ∩ As =
          ⋃ k, (u ∘ f k) ''
            ({((if a k then -t / 2 else t / 2), 0)} ×ˢ Icc (0 : ℝ) 1) ∧
        (u ∘ ρ) '' (frontier R.space ×ˢ {t}) ∩ Bs =
          ⋃ k, (u ∘ f k) ''
            ({(0, if b k then -t / 2 else t / 2)} ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨c, L, W, ρ, hc, hc1, hLfin, hL, hLB, hJL, hLnhds, haxisModel,
      hW, hWP, hWSp, hρ, hzero, htrace, hpositive, hread, hfull, hlevels⟩ :=
    exists_filling_ribbon_traces_of_cell_contacts hcellA hcellB hP hu
      R hR hsolid hRint hRS hfront hcontactA hcontactB hJDF hF hD hDF hC hCP hf haxis
      hfirst hsecond hpages hJC hends a b hquad hdis
  obtain ⟨hD, H, hH, hHends, hHbottom, hHshell⟩ :=
    hg.exists_expanded_square_of_outward_collar hgends hgfront hc hρ hzero htrace
  refine ⟨c, L, W, ρ, H, hD, hH, hHends, hHbottom, hHshell, ?_,
    hc, hc1, hLfin, hL, hLB, hJL, hLnhds, haxisModel,
    hW, hWP, hWSp, hρ, hzero, htrace, hpositive, hread, hfull, hlevels⟩
  rw [image_union]
  exact union_subset hRS hWSp

end DifferentialGeometry.Topology.PiecewiseLinear
