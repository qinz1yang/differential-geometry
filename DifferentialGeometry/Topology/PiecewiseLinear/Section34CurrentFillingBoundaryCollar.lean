import DifferentialGeometry.Topology.PiecewiseLinear.Section34ActualFillingBoundaryCollar
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentPairedCornerModel

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_filling_boundary_exterior_collar_of_cell_contacts
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
      C k ∩ R.space) (hdis : Disjoint (C 0) (C 1)) :
    let J := (f 0 '' section34MarkedAxis) ∪ (f 1 '' section34MarkedAxis)
    let B := fun k => f k '' (section34CornerBase (a k) (b k) ×ˢ Icc (0 : ℝ) 1)
    ∃ (c : ℝ) (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (W : Set (EuclideanSpace ℝ (Fin 3)))
      (ρ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3)),
      0 < c ∧ c ≤ 1 ∧ L.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 L ∧
      L.space ⊆ frontier R.space ∩ (B 0 ∪ B 1) ∧ J ⊆ L.space ∧
      (∀ x ∈ J, L.space ∈ 𝓝[frontier R.space] x) ∧
      J = Function.invFunOn u P '' (J₀ ∪ J₁) ∧
      IsPolyhedron W ∧ W ⊆ interior P ∧ u '' W ⊆ interior S ∧
      IsPLHomeomorphOn ρ (frontier R.space ×ˢ Icc (0 : ℝ) c) W ∧
      (∀ x ∈ frontier R.space, ρ (x, 0) = x) ∧ W ∩ R.space = frontier R.space ∧
      MapsTo ρ (frontier R.space ×ˢ Ioc (0 : ℝ) c) (interior P \ R.space) ∧
      ∀ k, ∀ p ∈ section34CornerBase (a k) (b k), ∀ s ∈ Icc (0 : ℝ) 1,
        f k (p, s) ∈ L.space → ∀ t ∈ Icc (0 : ℝ) c,
          ρ (f k (p, s), t) = f k (section34CornerExteriorPush (a k) (b k) (p, t), s) ∧
          (u (ρ (f k (p, s), t)) ∈ As ↔
            p.2 = (if b k then t / 2 else -t / 2)) ∧
          (u (ρ (f k (p, s), t)) ∈ Bs ↔
            p.1 = (if a k then t / 2 else -t / 2)) := by
  obtain ⟨hRint, hX, hY, -, -, hclosedR, hregR, hconnR, hRX, hRY, hfrontR,
      hmodelData, -, -, haxisModel⟩ :=
    paired_filling_model_regions_of_cell_contacts hcellA hcellB hP hu R hR hsolid hRint
      hfront hcontactA hcontactB hJDF hC hCP hf haxis hfirst hsecond hpages hJC
  let O := interior P ∩ u ⁻¹' interior S
  have hO : IsOpen O :=
    (hu.continuousOn.mono interior_subset).isOpen_inter_preimage isOpen_interior isOpen_interior
  have hRO : frontier R.space ⊆ O := by
    intro x hx
    exact ⟨hRint (hclosedR.frontier_subset hx),
      hRS ⟨x, hclosedR.frontier_subset hx, rfl⟩⟩
  have hOnhds : O ∈ 𝓝ˢ[P] (frontier R.space) :=
    mem_nhdsSetWithin.mpr ⟨O, hO, hRO, inter_subset_left⟩
  obtain ⟨c, L, W, ρ, hc, hc1, hLfin, hL, hLB, hJL, hLnhds, hW, hWO,
      hρ, hzero, htrace, hpositive, hread⟩ :=
    exists_filling_boundary_exterior_collar_preserving_corners hP R hR hRint hf hends a b
      (fun k => (hmodelData k).1) (fun k => (hmodelData k).2.1)
      (fun k => (hmodelData k).2.2.1) hX hY hquad hRX hRY hfrontR
      (fun k => (hmodelData k).2.2.2) hdis hCP hOnhds
  obtain ⟨-, -, -, -, -, hboundary, -⟩ :=
    hu.filling_regions_of_cell_contacts hcellA hcellB hRint hclosedR hregR hconnR
      hfront hcontactA hcontactB hJDF
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
