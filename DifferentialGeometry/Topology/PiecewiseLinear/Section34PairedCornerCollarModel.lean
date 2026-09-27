import DifferentialGeometry.Topology.PiecewiseLinear.Section34ActualFillingRegions
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingModelRegions
import DifferentialGeometry.Topology.PiecewiseLinear.CellMapTriangulation

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

theorem section34_paired_filling_model_regions
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
    (hJC : ∀ k, ![Pg e i, Pg e j] k ⊆ interior (u '' C k)) :
    let X := closure (interior (P ∩ u ⁻¹' (G (ends e).1 '' Cp (ends e).1)))
    let Y := closure (interior (P ∩ u ⁻¹' (G (ends e).2 '' Cp (ends e).2)))
    let Z := (f 0 '' section34MarkedAxis) ∪ (f 1 '' section34MarkedAxis)
    R.space ⊆ interior P ∧ IsClosed X ∧ IsClosed Y ∧
      closure (interior X) = X ∧ closure (interior Y) = Y ∧
      IsClosed R.space ∧ closure (interior R.space) = R.space ∧
      IsConnected (interior R.space) ∧
      R.space ∩ frontier X ⊆ frontier R.space ∧
      R.space ∩ frontier Y ⊆ frontier R.space ∧
      frontier R.space ⊆ frontier X ∪ frontier Y ∧
      (∀ k, f k '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2) = C k ∩ frontier X ∧
        f k '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3) = C k ∩ frontier Y ∧
        (∀ l : Fin 4, f k '' section34MarkedRibbon l = C k ∩
          ![frontier X ∩ Y, frontier Y ∩ X, frontier X \ interior Y,
            frontier Y \ interior X] l) ∧ f k '' section34MarkedAxis ⊆ interior (C k)) ∧
      IsPolyhedron Z ∧ Z ⊆ frontier R.space ∧
      Z = Function.invFunOn u P '' (Pg e i ∪ Pg e j) := by
  let X := closure (interior (P ∩ u ⁻¹' (G (ends e).1 '' Cp (ends e).1)))
  let Y := closure (interior (P ∩ u ⁻¹' (G (ends e).2 '' Cp (ends e).2)))
  let τ := Function.invFunOn u P
  have hleft : LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  obtain ⟨hRint, hX, hY, hregX, hregY, -, hclosedR, hregR, hconnR, -, -, hRX, hRY, hFR, -⟩ :=
    section34_actual_filling_regions hprep hpack e hu hmodel R hR hsolid hRP hRT
      hfront hcontactA hcontactB (subset_union_left.trans hJDF)
  obtain ⟨-, -, -, -, hCp, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGp, -⟩ := hpack
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
  have hcanonical (k : Fin 2) :
      f k '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2) = C k ∩ frontier X ∧
      f k '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3) = C k ∩ frontier Y ∧
      ∀ l : Fin 4, f k '' section34MarkedRibbon l = C k ∩
        ![frontier X ∩ Y, frontier Y ∩ X, frontier X \ interior Y, frontier Y \ interior X] l := by
    have hA := hfirst k
    have hB := hsecond k
    have hpg := hpages k
    rw [hcellA.boundary_eq_frontier] at hA hpg
    rw [hcellB.boundary_eq_frontier] at hB hpg
    exact hu.crossing_traces_of_image hP.isPolyhedron.isClosed (hCP k) (hf k)
      hcellA.isCompact.isClosed hcellB.isCompact.isClosed hregA hregB hA hB hpg
  have haxisSub : section34MarkedAxis ⊆ spliceCylinder :=
    (section34_marked_axis_subset_ribbon 0).trans (section34_marked_ribbon_subset_cylinder 0)
  have haxisIn (k : Fin 2) : f k '' section34MarkedAxis ⊆ C k :=
    (image_mono haxisSub).trans (hf k).image_eq.subset
  have haxisInt (k : Fin 2) : f k '' section34MarkedAxis ⊆ interior (C k) := by
    intro x hx
    have hux := hJC k ((haxis k).subset (mem_image_of_mem u hx))
    rw [← hu.image_interior_of_isCompact_subset_interior (hC k).isCompact (hCP k)] at hux
    obtain ⟨y, hy, heq⟩ := hux
    exact hu.injOn (interior_subset (hCP k (interior_subset hy)))
      (interior_subset (hCP k (haxisIn k hx))) heq ▸ hy
  have haxisBack (k : Fin 2) : f k '' section34MarkedAxis = τ '' (![Pg e i, Pg e j] k) := by
    rw [← haxis k, image_image]
    symm
    exact (image_congr fun x hx => hleft (interior_subset (hCP k (haxisIn k hx)))).trans
      (image_id' _)
  have haxisFront (k : Fin 2) : f k '' section34MarkedAxis ⊆ frontier R.space := by
    intro x hx
    have hux := (haxis k).subset (mem_image_of_mem u hx)
    have hJ : ![Pg e i, Pg e j] k ⊆ D ∩ F := by
      fin_cases k
      · exact subset_union_left.trans hJDF
      · exact subset_union_right.trans hJDF
    obtain ⟨y, hy, hyx⟩ := (hcontactB.symm.subset (hJ hux).1).2
    have hyx' : y = x := hu.injOn (hRP hy) (interior_subset (hCP k (haxisIn k hx))) hyx
    have hxR : x ∈ R.space := hyx' ▸ hy
    have hxX : x ∈ frontier X := ((hcanonical k).1.subset
      (image_mono ((section34_marked_axis_subset_ribbon 0).trans subset_union_left) hx)).2
    exact hRX ⟨hxR, hxX⟩
  have haxisPoly (k : Fin 2) : IsPolyhedron (f k '' section34MarkedAxis) := by
    have hp : IsPolyhedron section34MarkedAxis :=
      (isHPolytope_singleton (0 : ℝ × ℝ)).isPolyhedron.prod isHPolytope_Icc.isPolyhedron
    exact ((hf k).isPiecewiseAffineOn.mono_of_isPolyhedron hp haxisSub).isPolyhedron_image hp
  refine ⟨hRint, hX, hY, hregX, hregY, hclosedR, hregR, hconnR, hRX, hRY, hFR,
    fun k => ⟨(hcanonical k).1, (hcanonical k).2.1, (hcanonical k).2.2, haxisInt k⟩,
    (haxisPoly 0).union (haxisPoly 1), union_subset (haxisFront 0) (haxisFront 1), ?_⟩
  rw [haxisBack 0, haxisBack 1, image_union]
  rfl

end DifferentialGeometry.Topology.PiecewiseLinear
