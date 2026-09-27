import DifferentialGeometry.Topology.PiecewiseLinear.Section34ActualFillingRibbonTraces
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CollaredFillingCylinderExpanded

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem exists_section34_actual_collared_filling_cylinder
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M₂}
    (hP : IsPLBall 3 P) (hu : IsPLHomeomorphInto 3 u P)
    (hmodel : u '' P = G (ends e).1 '' Cc (ends e).1)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 3 R)
    (hsolid : IsTopologicalSolidTorus R.space) (hRP : R.space ⊆ P)
    (hRT : u '' R.space ⊆ Tp e) {D F : Set M₂}
    (hfront : u '' frontier R.space = D ∪ F)
    (hcontactA : G (ends e).1 '' CpBd (ends e).1 ∩ u '' R.space = F)
    (hcontactB : G (ends e).2 '' CpBd (ends e).2 ∩ u '' R.space = D)
    {i j : ℕ} (hJDF : Pg e i ∪ Pg e j ⊆ D ∩ F)
    (hfill : Section34FaceAlignedBandFilling
      (G (ends e).1 '' Cc (ends e).1) (G (ends e).1 '' Cp (ends e).1)
      (G (ends e).1 '' CpBd (ends e).1) (G (ends e).2 '' CpBd (ends e).2) (Tp e) D F
      (Pg e i) (Pg e j))
    {C : Fin 2 → Set (EuclideanSpace ℝ (Fin 3))}
    {f : Fin 2 → (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hC : ∀ k, IsPolyhedron (C k)) (hCP : ∀ k, C k ⊆ interior P)
    (hf : ∀ k, IsCylindricalDiagram (f k) spliceSquare (C k))
    (haxis : ∀ k, u '' (f k '' section34MarkedAxis) = ![Pg e i, Pg e j] k)
    (hfirst : ∀ k, u '' (f k '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2)) =
      u '' C k ∩ G (ends e).1 '' CpBd (ends e).1)
    (hsecond : ∀ k, u '' (f k '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3)) =
      u '' C k ∩ G (ends e).2 '' CpBd (ends e).2)
    (hpages : ∀ k, ∀ l : Fin 4, u '' (f k '' section34MarkedRibbon l) = u '' C k ∩
      ![G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' Cp (ends e).2,
        G (ends e).2 '' CpBd (ends e).2 ∩ G (ends e).1 '' Cp (ends e).1,
        G (ends e).1 '' CpBd (ends e).1 \ interior (G (ends e).2 '' Cp (ends e).2),
        G (ends e).2 '' CpBd (ends e).2 \ interior (G (ends e).1 '' Cp (ends e).1)] l)
    (hJC : ∀ k, ![Pg e i, Pg e j] k ⊆ interior (u '' C k))
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
      u '' (R.space ∪ W) ⊆ interior (Sp e) ∧
      0 < c ∧ c ≤ 1 ∧ L.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 L ∧
      L.space ⊆ frontier R.space ∩ (B 0 ∪ B 1) ∧ J ⊆ L.space ∧
      (∀ x ∈ J, L.space ∈ 𝓝[frontier R.space] x) ∧
      J = Function.invFunOn u P '' (Pg e i ∪ Pg e j) ∧
      IsPolyhedron W ∧ W ⊆ interior P ∧ u '' W ⊆ interior (Sp e) ∧
      IsPLHomeomorphOn ρ (frontier R.space ×ˢ Icc (0 : ℝ) c) W ∧
      (∀ x ∈ frontier R.space, ρ (x, 0) = x) ∧ W ∩ R.space = frontier R.space ∧
      MapsTo ρ (frontier R.space ×ˢ Ioc (0 : ℝ) c) (interior P \ R.space) ∧
      (∀ k, ∀ p ∈ section34CornerBase (a k) (b k), ∀ s ∈ Icc (0 : ℝ) 1,
        f k (p, s) ∈ L.space → ∀ t ∈ Icc (0 : ℝ) c,
          ρ (f k (p, s), t) = f k (section34CornerExteriorPush (a k) (b k) (p, t), s) ∧
          (u (ρ (f k (p, s), t)) ∈ G (ends e).1 '' CpBd (ends e).1 ↔
            p.2 = (if b k then t / 2 else -t / 2)) ∧
          (u (ρ (f k (p, s), t)) ∈ G (ends e).2 '' CpBd (ends e).2 ↔
            p.1 = (if a k then t / 2 else -t / 2))) ∧
      (∀ x ∈ frontier R.space, ∀ t ∈ Ioc (0 : ℝ) c,
        (u (ρ (x, t)) ∈ G (ends e).1 '' CpBd (ends e).1 ↔
          ∃ k p s, p ∈ section34CornerBase (a k) (b k) ∧ s ∈ Icc (0 : ℝ) 1 ∧
            x = f k (p, s) ∧ x ∈ L.space ∧ p.2 = (if b k then t / 2 else -t / 2)) ∧
        (u (ρ (x, t)) ∈ G (ends e).2 '' CpBd (ends e).2 ↔
          ∃ k p s, p ∈ section34CornerBase (a k) (b k) ∧ s ∈ Icc (0 : ℝ) 1 ∧
            x = f k (p, s) ∧ x ∈ L.space ∧ p.1 = (if a k then t / 2 else -t / 2))) ∧
      ∀ t ∈ Ioc (0 : ℝ) c,
        (u ∘ ρ) '' (frontier R.space ×ˢ {t}) ∩ G (ends e).1 '' CpBd (ends e).1 =
          ⋃ k, (u ∘ f k) ''
            ({((if a k then -t / 2 else t / 2), 0)} ×ˢ Icc (0 : ℝ) 1) ∧
        (u ∘ ρ) '' (frontier R.space ×ˢ {t}) ∩ G (ends e).2 '' CpBd (ends e).2 =
          ⋃ k, (u ∘ f k) ''
            ({(0, if b k then -t / 2 else t / 2)} ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨c, L, W, ρ, hc, hc1, hLfin, hL, hLB, hJL, hLnhds, haxisModel,
      hW, hWP, hWSp, hρ, hzero, htrace, hpositive, hread, hfull, hlevels⟩ :=
    exists_section34_actual_filling_ribbon_traces hprep hpack e hP hu hmodel
      R hR hsolid hRP hRT hfront hcontactA hcontactB hJDF hfill hC hCP hf haxis
      hfirst hsecond hpages hJC hends a b hquad hdis
  obtain ⟨hD, H, hH, hHends, hHbottom, hHshell⟩ :=
    hg.exists_expanded_square_of_outward_collar hgends hgfront hc hρ hzero htrace
  refine ⟨c, L, W, ρ, H, hD, hH, hHends, hHbottom, hHshell, ?_,
    hc, hc1, hLfin, hL, hLB, hJL, hLnhds, haxisModel,
    hW, hWP, hWSp, hρ, hzero, htrace, hpositive, hread, hfull, hlevels⟩
  rw [image_union]
  exact union_subset (hRT.trans (section34_inner_tube_subset_interior_outer hprep hpack e)) hWSp

end DifferentialGeometry.Topology.PiecewiseLinear
