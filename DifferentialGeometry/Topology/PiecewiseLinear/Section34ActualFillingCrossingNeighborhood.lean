import DifferentialGeometry.Topology.PiecewiseLinear.Section34ActualCrossingNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ActualFillingRegions
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingModelRegions
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingTubeFillingRecognition

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

theorem exists_section34_filling_seam_neighborhood
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i : ℕ} (hi : i < cnt e)
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
    (hJDF : Pg e i ⊆ D ∩ F)
    {O : Set M₂} (hO : IsOpen O) (hJO : Pg e i ⊆ O) :
    ∃ (C : Set (EuclideanSpace ℝ (Fin 3)))
      (f : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)) (a b : Bool),
      IsPolyhedron C ∧ C ⊆ interior P ∧ IsCylindricalDiagram f spliceSquare C ∧
      (∀ x ∈ spliceSquare, f (x, 0) = f (x, 1)) ∧
      u '' (f '' section34MarkedAxis) = Pg e i ∧
      u '' (f '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2)) =
        u '' C ∩ G (ends e).1 '' CpBd (ends e).1 ∧
      u '' (f '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3)) =
        u '' C ∩ G (ends e).2 '' CpBd (ends e).2 ∧
      (∀ j : Fin 4, u '' (f '' section34MarkedRibbon j) = u '' C ∩
        ![G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' Cp (ends e).2,
          G (ends e).2 '' CpBd (ends e).2 ∩ G (ends e).1 '' Cp (ends e).1,
          G (ends e).1 '' CpBd (ends e).1 \ interior (G (ends e).2 '' Cp (ends e).2),
          G (ends e).2 '' CpBd (ends e).2 \ interior (G (ends e).1 '' Cp (ends e).1)] j) ∧
      u '' C ⊆ O ∧ Pg e i ⊆ interior (u '' C) ∧
      f '' (section34CrossingQuadrant a b ×ˢ Icc (0 : ℝ) 1) = C ∩ R.space := by
  obtain ⟨C, f, hC, hCP, hf, hends, haxis, hfirst, hsecond, hpages, hCO, hJC⟩ :=
    exists_section34_actual_crossing_neighborhood_in_model hprep hpack e hi hP hu hmodel hO hJO
  obtain ⟨-, hX, hY, -, -, -, hclosedR, hregR, hconnR, -, -, hRX, hRY, hfrontR, hJR⟩ :=
    section34_actual_filling_regions hprep hpack e hu hmodel R hR hsolid hRP hRT
      hfront hcontactA hcontactB hJDF
  obtain ⟨-, -, -, -, hCp, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGp, -⟩ := id hpack
  have hcellA := (hCp (ends e).1).image (hGp (ends e).1)
  have hcellB := (hCp (ends e).2).image (hGp (ends e).2)
  have hregA : closure (interior (G (ends e).1 '' Cp (ends e).1)) =
      G (ends e).1 '' Cp (ends e).1 := by
    rw [← hcellA.sdiff_boundary_eq_interior]
    exact hcellA.closure_sdiff_boundary
  have hregB : closure (interior (G (ends e).2 '' Cp (ends e).2)) =
      G (ends e).2 '' Cp (ends e).2 := by
    rw [← hcellB.sdiff_boundary_eq_interior]
    exact hcellB.closure_sdiff_boundary
  have hfirst' := hfirst
  have hsecond' := hsecond
  have hpages' := hpages
  rw [hcellA.boundary_eq_frontier] at hfirst' hpages'
  rw [hcellB.boundary_eq_frontier] at hsecond' hpages'
  obtain ⟨hmfirst, hmsecond, hmpages⟩ := hu.crossing_traces_of_image hP.isPolyhedron.isClosed
    hCP hf hcellA.isCompact.isClosed hcellB.isCompact.isClosed hregA hregB
    hfirst' hsecond' hpages'
  have haxisC : f '' section34MarkedAxis ⊆ C :=
    (image_mono ((section34_marked_axis_subset_ribbon 0).trans
      (section34_marked_ribbon_subset_cylinder 0))).trans hf.image_eq.subset
  have haxisR : f '' section34MarkedAxis ⊆ R.space := by
    intro x hx
    have hux := haxis.subset (mem_image_of_mem u hx)
    have hxR := hJR (mem_image_of_mem (Function.invFunOn u P) hux)
    rwa [hu.injOn.leftInvOn_invFunOn (interior_subset (hCP (haxisC hx)))] at hxR
  have haxisInt : f '' section34MarkedAxis ⊆ interior C := by
    intro x hx
    have hux := hJC (haxis.subset (mem_image_of_mem u hx))
    rw [← hu.image_interior_of_isCompact_subset_interior hC.isCompact hCP] at hux
    obtain ⟨y, hy, heq⟩ := hux
    have hyx := hu.injOn (interior_subset (hCP (interior_subset hy)))
      (interior_subset (hCP (haxisC hx))) heq
    exact hyx ▸ hy
  obtain ⟨a, b, -, -, hquadrant⟩ := hf.exists_filling_quadrant hends hmfirst hmsecond hmpages
    hX hY haxisInt haxisR hclosedR hregR hconnR.isPreconnected hRX hRY hfrontR
  exact ⟨C, f, a, b, hC, hCP, hf, hends, haxis, hfirst, hsecond, hpages, hCO, hJC, hquadrant⟩

end DifferentialGeometry.Topology.PiecewiseLinear
