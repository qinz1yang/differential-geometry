import DifferentialGeometry.Topology.PiecewiseLinear.Section34PairedCornerCollarModel
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentFillingRegions

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem paired_filling_model_regions_of_cell_contacts
    {M : Type*} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {A As B Bs D F J₀ J₁ : Set M}
    (hcellA : IsPLCellOn 3 A As) (hcellB : IsPLCellOn 3 B Bs)
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hP : IsPLBall 3 P) (hu : IsPLHomeomorphInto 3 u P)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 3 R)
    (hsolid : IsTopologicalSolidTorus R.space) (hRint : R.space ⊆ interior P)
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
    (hJC : ∀ k, ![J₀, J₁] k ⊆ interior (u '' C k)) :
    let X := closure (interior (P ∩ u ⁻¹' (A)))
    let Y := closure (interior (P ∩ u ⁻¹' (B)))
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
      Z = Function.invFunOn u P '' (J₀ ∪ J₁) := by
  let X := closure (interior (P ∩ u ⁻¹' (A)))
  let Y := closure (interior (P ∩ u ⁻¹' (B)))
  let τ := Function.invFunOn u P
  have hleft : LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hRP : R.space ⊆ P := hRint.trans interior_subset
  have hclosed : IsClosed R.space := (isPolyhedron_space R).isClosed
  have hreg : closure (interior R.space) = R.space :=
    (closure_minimal interior_subset hclosed).antisymm
      (hR.subset_closure_interior_space (by simp))
  have hconn : IsConnected (interior R.space) :=
    (isConnected_interior_space_and_compl (Set.toFinite R.faces) hR
      (hsolid.isConnected_frontier hclosed) hsolid.interior_nonempty).1
  obtain ⟨-, hX, hY, hregX, hregY, -, hclosedR, hregR, hconnR, -, -, hRX, hRY, hFR, -⟩ :=
    hu.filling_regions_of_cell_contacts hcellA hcellB hRint hclosed hreg hconn
      hfront hcontactA hcontactB hJDF
  have hregA : closure (interior (A)) =
      A := by
    rw [← hcellA.sdiff_boundary_eq_interior]
    exact hcellA.closure_sdiff_boundary
  have hregB : closure (interior (B)) =
      B := by
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
  have haxisBack (k : Fin 2) : f k '' section34MarkedAxis = τ '' (![J₀, J₁] k) := by
    rw [← haxis k, image_image]
    symm
    exact (image_congr fun x hx => hleft (interior_subset (hCP k (haxisIn k hx)))).trans
      (image_id' _)
  have haxisFront (k : Fin 2) : f k '' section34MarkedAxis ⊆ frontier R.space := by
    intro x hx
    have hux := (haxis k).subset (mem_image_of_mem u hx)
    have hJ : ![J₀, J₁] k ⊆ D ∩ F := by
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
