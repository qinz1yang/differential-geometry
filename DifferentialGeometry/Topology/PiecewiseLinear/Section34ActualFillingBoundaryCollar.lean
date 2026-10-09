import DifferentialGeometry.Topology.PiecewiseLinear.Section34PairedCornerCollarModel
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FillingBoundaryCollarExterior

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

theorem exists_section34_actual_filling_boundary_exterior_collar
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
      C k ∩ R.space) (hdis : Disjoint (C 0) (C 1)) :
    let J := (f 0 '' section34MarkedAxis) ∪ (f 1 '' section34MarkedAxis)
    let B := fun k => f k '' (section34CornerBase (a k) (b k) ×ˢ Icc (0 : ℝ) 1)
    ∃ (c : ℝ) (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (W : Set (EuclideanSpace ℝ (Fin 3)))
      (ρ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3)),
      0 < c ∧ c ≤ 1 ∧ L.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 L ∧
      L.space ⊆ frontier R.space ∩ (B 0 ∪ B 1) ∧ J ⊆ L.space ∧
      (∀ x ∈ J, L.space ∈ 𝓝[frontier R.space] x) ∧
      J = Function.invFunOn u P '' (Pg e i ∪ Pg e j) ∧
      IsPolyhedron W ∧ W ⊆ interior P ∧ u '' W ⊆ interior (Sp e) ∧
      IsPLHomeomorphOn ρ (frontier R.space ×ˢ Icc (0 : ℝ) c) W ∧
      (∀ x ∈ frontier R.space, ρ (x, 0) = x) ∧ W ∩ R.space = frontier R.space ∧
      MapsTo ρ (frontier R.space ×ˢ Ioc (0 : ℝ) c) (interior P \ R.space) ∧
      ∀ k, ∀ p ∈ section34CornerBase (a k) (b k), ∀ s ∈ Icc (0 : ℝ) 1,
        f k (p, s) ∈ L.space → ∀ t ∈ Icc (0 : ℝ) c,
          ρ (f k (p, s), t) = f k (section34CornerExteriorPush (a k) (b k) (p, t), s) ∧
          (u (ρ (f k (p, s), t)) ∈ G (ends e).1 '' CpBd (ends e).1 ↔
            p.2 = (if b k then t / 2 else -t / 2)) ∧
          (u (ρ (f k (p, s), t)) ∈ G (ends e).2 '' CpBd (ends e).2 ↔
            p.1 = (if a k then t / 2 else -t / 2)) := by
  obtain ⟨hRint, hX, hY, -, -, hclosedR, -, -, hRX, hRY, hfrontR,
      hmodelData, -, -, haxisModel⟩ :=
    section34_paired_filling_model_regions hprep hpack e hP hu hmodel R hR hsolid hRP hRT
      hfront hcontactA hcontactB hJDF hC hCP hf haxis hfirst hsecond hpages hJC
  let O := interior P ∩ u ⁻¹' interior (Sp e)
  have hO : IsOpen O :=
    (hu.continuousOn.mono interior_subset).isOpen_inter_preimage isOpen_interior isOpen_interior
  have hRO : frontier R.space ⊆ O := by
    intro x hx
    exact ⟨hRint (hclosedR.frontier_subset hx),
      section34_inner_tube_subset_interior_outer hprep hpack e
        (hRT ⟨x, hclosedR.frontier_subset hx, rfl⟩)⟩
  have hOnhds : O ∈ 𝓝ˢ[P] (frontier R.space) :=
    mem_nhdsSetWithin.mpr ⟨O, hO, hRO, inter_subset_left⟩
  obtain ⟨c, L, W, ρ, hc, hc1, hLfin, hL, hLB, hJL, hLnhds, hW, hWO,
      hρ, hzero, htrace, hpositive, hread⟩ :=
    exists_filling_boundary_exterior_collar_preserving_corners hP R hR hRint hf hends a b
      (fun k => (hmodelData k).1) (fun k => (hmodelData k).2.1)
      (fun k => (hmodelData k).2.2.1) hX hY hquad hRX hRY hfrontR
      (fun k => (hmodelData k).2.2.2) hdis hCP hOnhds
  obtain ⟨-, -, -, -, -, hboundary, -⟩ :=
    section34_actual_filling_regions hprep hpack e hu hmodel R hR hsolid hRP hRT
      hfront hcontactA hcontactB (subset_union_left.trans hJDF)
  refine ⟨c, L, W, ρ, hc, hc1, hLfin, hL, hLB, hJL, hLnhds, haxisModel,
    hW, hWO.trans inter_subset_left, ?_, hρ, hzero, htrace, hpositive, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hWO hx).2.2
  · intro k p hp s hs hpoint t ht
    have hm := hρ.bijOn.mapsTo
      (show (f k (p, s), t) ∈ frontier R.space ×ˢ Icc (0 : ℝ) c from ⟨(hLB hpoint).1, ht⟩)
    have hlocal := hboundary _ (hWO hm).1
    have hr := hread k p hp s hs hpoint t ht
    exact ⟨hr.1, hlocal.1.symm.trans hr.2.1, hlocal.2.symm.trans hr.2.2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
