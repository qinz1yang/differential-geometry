import DifferentialGeometry.Topology.PiecewiseLinear.Section34InteriorFillingQuadrantRegions
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingGenerators
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingDiskComponents
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SolidTorusFilling

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

theorem section34_actual_filling_regions
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M₂}
    (hu : IsPLHomeomorphInto 3 u P)
    (hmodel : u '' P = G (ends e).1 '' Cc (ends e).1)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 3 R)
    (hsolid : IsTopologicalSolidTorus R.space) (hRP : R.space ⊆ P)
    (hRT : u '' R.space ⊆ Tp e) {D F : Set M₂}
    (hfront : u '' frontier R.space = D ∪ F)
    (hcontactA : G (ends e).1 '' CpBd (ends e).1 ∩ u '' R.space = F)
    (hcontactB : G (ends e).2 '' CpBd (ends e).2 ∩ u '' R.space = D)
    {i : ℕ} (hJDF : Pg e i ⊆ D ∩ F) :
    let X := closure (interior (P ∩ u ⁻¹' (G (ends e).1 '' Cp (ends e).1)))
    let Y := closure (interior (P ∩ u ⁻¹' (G (ends e).2 '' Cp (ends e).2)))
    let τ := Function.invFunOn u P
    R.space ⊆ interior P ∧ IsClosed X ∧ IsClosed Y ∧
      closure (interior X) = X ∧ closure (interior Y) = Y ∧
      (∀ x ∈ interior P,
        (x ∈ frontier X ↔ u x ∈ G (ends e).1 '' CpBd (ends e).1) ∧
        (x ∈ frontier Y ↔ u x ∈ G (ends e).2 '' CpBd (ends e).2)) ∧
      IsClosed R.space ∧ closure (interior R.space) = R.space ∧
      IsConnected (interior R.space) ∧
      R.space ∩ frontier X = τ '' F ∧ R.space ∩ frontier Y = τ '' D ∧
      R.space ∩ frontier X ⊆ frontier R.space ∧
      R.space ∩ frontier Y ⊆ frontier R.space ∧
      frontier R.space ⊆ frontier X ∪ frontier Y ∧ τ '' Pg e i ⊆ R.space := by
  let X := closure (interior (P ∩ u ⁻¹' (G (ends e).1 '' Cp (ends e).1)))
  let Y := closure (interior (P ∩ u ⁻¹' (G (ends e).2 '' Cp (ends e).2)))
  let τ := Function.invFunOn u P
  have hleft : LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hTS := section34_inner_tube_subset_interior_outer hprep hpack e
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, hSnCc, -⟩ := id hprep
  obtain ⟨-, -, -, htube, -, -, -, -, -, -, hGp, -⟩ := id hpack
  have hSpP : Sp e ⊆ u '' P := by
    rw [hmodel, (htube e).1]
    exact image_mono (hSnCc e _ (Or.inl rfl))
  have hRint : R.space ⊆ interior P := by
    intro x hx
    have hux : u x ∈ interior (u '' P) :=
      interior_mono hSpP (hTS (hRT ⟨x, hx, rfl⟩))
    rw [← hu.image_interior] at hux
    obtain ⟨y, hy, hyx⟩ := hux
    exact hu.injOn (interior_subset hy) (hRP hx) hyx ▸ hy
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
  have hread (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ interior P) :
      (x ∈ frontier X ↔ u x ∈ G (ends e).1 '' CpBd (ends e).1) ∧
      (x ∈ frontier Y ↔ u x ∈ G (ends e).2 '' CpBd (ends e).2) := by
    constructor
    · rw [hu.regularized_clipped_region_frontier hregA hx |>.1,
        ← hcellA.boundary_eq_frontier]
    · rw [hu.regularized_clipped_region_frontier hregB hx |>.1,
        ← hcellB.boundary_eq_frontier]
  have hclosed : IsClosed R.space := (isPolyhedron_space R).isClosed
  have hreg : closure (interior R.space) = R.space :=
    (closure_minimal interior_subset hclosed).antisymm
      (hR.subset_closure_interior_space (by simp))
  have hconn : IsConnected (interior R.space) :=
    (isConnected_interior_space_and_compl (Set.toFinite R.faces) hR
      (hsolid.isConnected_frontier hclosed) hsolid.interior_nonempty).1
  have hfrontR : frontier R.space ⊆ R.space := hclosed.frontier_subset
  have hcontact (S : Set M₂) (Z : Set (EuclideanSpace ℝ (Fin 3))) (E : Set M₂)
      (hSZ : ∀ x ∈ R.space, x ∈ Z ↔ u x ∈ S)
      (hSE : S ∩ u '' R.space = E) : R.space ∩ Z = τ '' E := by
    apply Subset.antisymm
    · intro x hx
      exact ⟨u x, hSE.subset ⟨(hSZ x hx.1).mp hx.2, x, hx.1, rfl⟩,
        hleft (hRP hx.1)⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨hyS, x, hx, rfl⟩ := hSE.symm.subset hy
      rw [hleft (hRP hx)]
      exact ⟨hx, (hSZ x hx).mpr hyS⟩
  have hfirst : R.space ∩ frontier X = τ '' F :=
    hcontact _ _ _ (fun x hx => (hread x (hRint hx)).1) hcontactA
  have hsecond : R.space ∩ frontier Y = τ '' D :=
    hcontact _ _ _ (fun x hx => (hread x (hRint hx)).2) hcontactB
  have hbackfront : τ '' (D ∪ F) ⊆ frontier R.space := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hfront.symm.subset hy
    rw [hleft (hRP (hfrontR hx))]
    exact hx
  refine ⟨hRint, isClosed_closure, isClosed_closure, closure_interior_idem,
    closure_interior_idem, hread, hclosed, hreg, hconn, hfirst, hsecond, ?_, ?_, ?_, ?_⟩
  · rw [hfirst]
    exact (image_mono subset_union_right).trans hbackfront
  · rw [hsecond]
    exact (image_mono subset_union_left).trans hbackfront
  · intro x hx
    rcases hfront.subset ⟨x, hx, rfl⟩ with hxD | hxF
    · exact Or.inr ((hread x (hRint (hfrontR hx))).2.mpr
        (hcontactB.symm.subset hxD).1)
    · exact Or.inl ((hread x (hRint (hfrontR hx))).1.mpr
        (hcontactA.symm.subset hxF).1)
  · exact ((image_mono (hJDF.trans inter_subset_left)).trans
      (image_mono subset_union_left)).trans (hbackfront.trans hfrontR)

end DifferentialGeometry.Topology.PiecewiseLinear
