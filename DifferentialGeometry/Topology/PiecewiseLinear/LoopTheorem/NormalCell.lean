import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell
import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition
import DifferentialGeometry.Topology.SimplicialComplex.EdgeGraph
import Mathlib.Combinatorics.SimpleGraph.Matching

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem doublePointSet_eq_empty_iff_injOn {X Y : Type*} (f : X → Y) (P : Set X) :
    doublePointSet f P = ∅ ↔ InjOn f P := by
  constructor
  · intro hempty x hx z hz hfxz
    by_contra hxz
    have hmem : f x ∈ doublePointSet f P :=
      ⟨x, hx, z, hz, hxz, rfl, hfxz.symm⟩
    rw [hempty] at hmem
    exact hmem
  · intro hinj
    apply eq_empty_iff_forall_notMem.mpr
    rintro y ⟨x, hx, z, hz, hxz, hxy, hzy⟩
    exact hxz (hinj hx hz (hxy.trans hzy.symm))

open Classical in
theorem mem_boundaryComplex_vertices_iff_edgeGraph_neighborSet_ncard_eq_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (G : Geometry.SimplicialComplex ℝ E) [Finite G.faces]
    (hG : IsCombinatorialManifoldWithBoundary 1 G) (v : G.vertices) :
    (v : E) ∈ (boundaryComplex 1 G).vertices ↔
      ((SimplicialComplex.edgeGraph G).neighborSet v).ncard = 1 := by
  have hcard : ∀ s ∈ G.faces, s.card ≤ 2 := fun s hs => hG.card_le G hs
  have hlink := geometricLink_space_eq_neighbors_of_card_le G hcard (v : E)
  change ({(v : E)} : Finset E) ∈ (boundaryComplex 1 G).faces ↔
    ((SimplicialComplex.edgeGraph G).neighborSet v).ncard = 1
  constructor
  · intro hv
    have hball : IsPLBall 0 (SimplicialComplex.geometricLink G {(v : E)}).space :=
      ((hG.mem_boundaryComplex_faces_iff G).mp hv).2.2
    rw [SimplicialComplex.ncard_neighborSet_edgeGraph, ← hlink, Set.ncard_eq_one]
    exact isPLBall_zero_iff.mp hball
  · intro hdegree
    apply (hG.mem_boundaryComplex_faces_iff G).mpr
    refine ⟨v.property, by simp, ?_⟩
    rw [hlink]
    apply isPLBall_zero_iff.mpr
    rw [← Set.ncard_eq_one, ← SimplicialComplex.ncard_neighborSet_edgeGraph]
    exact hdegree

open Classical in
structure NormalSingularSetTriangulation
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (D : SingularTwoCell M) (BdM : Set M) where
  carrier : Set M
  piece : PLPiece 3 M carrier
  complex : Geometry.SimplicialComplex ℝ
    (EuclideanSpace ℝ (Fin piece.ambientDim))
  finite_faces : complex.faces.Finite
  faces_subset : complex.faces ⊆ piece.piece.complex.faces
  isManifoldWithBoundary : IsCombinatorialManifoldWithBoundary 1 complex
  map_space : piece.piece.map '' complex.space = doublePointSet D D.domain
  map_boundary : piece.piece.map '' (boundaryComplex 1 complex).space =
    doublePointSet D D.domain ∩ BdM

open Classical in
structure NormalSingularCellData
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (D : SingularTwoCell M) (BdM B : Set M) where
  locallyInjective : ∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, Set.InjOn D U
  fiber_le_two : ∀ y, (D.domain ∩ D ⁻¹' {y}).encard ≤ 2
  boundary_image_subset : Set.range D.boundary ⊆ B
  image_inter_boundary : D '' D.domain ∩ BdM = Set.range D.boundary
  singularSet : NormalSingularSetTriangulation D BdM
  crossing : ∀ y ∈ doublePointSet D D.domain,
    ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
      HasPLDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source) (e y)

namespace NormalSingularSetTriangulation

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM : Set M}

abbrev Branch (T : NormalSingularSetTriangulation D BdM) :=
  (SimplicialComplex.edgeGraph T.complex).ConnectedComponent

def IsBoundaryBranch (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) : Prop :=
  ∃ v, v ∈ c.supp ∧
    ((SimplicialComplex.edgeGraph T.complex).neighborSet v).ncard = 1

open Classical in
theorem neighborSet_ncard_eq_one_or_two
    (T : NormalSingularSetTriangulation D BdM) (v : T.complex.vertices) :
    ((SimplicialComplex.edgeGraph T.complex).neighborSet v).ncard = 1 ∨
      ((SimplicialComplex.edgeGraph T.complex).neighborSet v).ncard = 2 := by
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  obtain ⟨hcard, hneighbors⟩ :=
    (isCombinatorialManifoldWithBoundary_one_iff T.complex).mp
      T.isManifoldWithBoundary
  rw [SimplicialComplex.ncard_neighborSet_edgeGraph]
  rcases hneighbors v v.property with ⟨a, ha⟩ | ⟨a, b, hab, habset⟩
  · exact Or.inl (by rw [ha, Set.ncard_singleton])
  · exact Or.inr (by rw [habset, Set.ncard_pair hab])

open Classical in
theorem neighborSet_ncard_eq_two_of_not_isBoundaryBranch
    (T : NormalSingularSetTriangulation D BdM) {c : T.Branch}
    (hc : ¬T.IsBoundaryBranch c) {v : T.complex.vertices} (hv : v ∈ c.supp) :
    ((SimplicialComplex.edgeGraph T.complex).neighborSet v).ncard = 2 := by
  rcases T.neighborSet_ncard_eq_one_or_two v with hdegree | hdegree
  · exfalso
    apply hc
    exact ⟨v, hv, hdegree⟩
  · exact hdegree

open Classical in
theorem exists_degree_one_vertex_of_isBoundaryBranch
    (T : NormalSingularSetTriangulation D BdM) {c : T.Branch}
    (hc : T.IsBoundaryBranch c) :
    ∃ v ∈ c.supp,
      ((SimplicialComplex.edgeGraph T.complex).neighborSet v).ncard = 1 := by
  obtain ⟨v, hv, hvb⟩ := hc
  exact ⟨v, hv, hvb⟩

open Classical in
noncomputable def closedBranchCount (T : NormalSingularSetTriangulation D BdM) : ℕ :=
  Nat.card {c : T.Branch // ¬T.IsBoundaryBranch c}

open Classical in
noncomputable def boundaryBranchCount (T : NormalSingularSetTriangulation D BdM) : ℕ :=
  Nat.card {c : T.Branch // T.IsBoundaryBranch c}

open Classical in
noncomputable def complexity (T : NormalSingularSetTriangulation D BdM) : ℕ :=
  T.closedBranchCount + T.boundaryBranchCount

theorem complex_space_eq_empty_iff (T : NormalSingularSetTriangulation D BdM) :
    T.complex.space = ∅ ↔ doublePointSet D D.domain = ∅ := by
  constructor
  · intro hspace
    calc
      doublePointSet D D.domain = T.piece.piece.map '' T.complex.space := T.map_space.symm
      _ = T.piece.piece.map '' ∅ := congrArg (T.piece.piece.map '' ·) hspace
      _ = ∅ := image_empty T.piece.piece.map
  · intro hdouble
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hmem : T.piece.piece.map x ∈ doublePointSet D D.domain :=
      T.map_space ▸ ⟨x, hx, rfl⟩
    rw [hdouble] at hmem
    exact hmem

theorem complex_vertices_eq_empty_iff (T : NormalSingularSetTriangulation D BdM) :
    T.complex.vertices = ∅ ↔ T.complex.space = ∅ := by
  constructor
  · intro hvertices
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨s, hs, hxs⟩ := T.complex.mem_space_iff.mp hx
    obtain ⟨v, hv⟩ := T.complex.nonempty_of_mem_faces hs
    have hv' : v ∈ T.complex.vertices :=
      T.complex.down_closed hs (Finset.singleton_subset_iff.mpr hv)
        (Finset.singleton_nonempty v)
    rw [hvertices] at hv'
    exact hv'
  · intro hspace
    apply eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hv' := T.complex.vertices_subset_space hv
    rw [hspace] at hv'
    exact hv'

open Classical in
theorem complexity_eq_zero_iff (T : NormalSingularSetTriangulation D BdM) :
    T.complexity = 0 ↔ D.IsNonsingular := by
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  let _ : Finite T.complex.vertices :=
    (SimplicialComplex.finite_vertices T.complex).to_subtype
  constructor
  · intro hzero
    have hsum : T.closedBranchCount + T.boundaryBranchCount = 0 := by
      simpa only [complexity] using hzero
    have hclosed : T.closedBranchCount = 0 := by
      exact (Nat.add_eq_zero_iff.mp hsum).1
    have hboundary : T.boundaryBranchCount = 0 := by
      exact (Nat.add_eq_zero_iff.mp hsum).2
    have hcomponents : IsEmpty T.Branch := by
      refine ⟨fun c => ?_⟩
      by_cases hc : T.IsBoundaryBranch c
      · have hempty : IsEmpty {c : T.Branch // T.IsBoundaryBranch c} :=
          Finite.card_eq_zero_iff.mp hboundary
        exact hempty.false ⟨c, hc⟩
      · have hempty : IsEmpty {c : T.Branch // ¬T.IsBoundaryBranch c} :=
          Finite.card_eq_zero_iff.mp hclosed
        exact hempty.false ⟨c, hc⟩
    have hvertices : T.complex.vertices = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro v hv
      let c : T.Branch :=
        (SimplicialComplex.edgeGraph T.complex).connectedComponentMk ⟨v, hv⟩
      exact hcomponents.false c
    exact (doublePointSet_eq_empty_iff_injOn D D.domain).mp
      (T.complex_space_eq_empty_iff.mp (T.complex_vertices_eq_empty_iff.mp hvertices))
  · intro hinj
    have hdouble : doublePointSet D D.domain = ∅ :=
      (doublePointSet_eq_empty_iff_injOn D D.domain).mpr hinj
    have hspace : T.complex.space = ∅ := T.complex_space_eq_empty_iff.mpr hdouble
    have hvertices : T.complex.vertices = ∅ := T.complex_vertices_eq_empty_iff.mpr hspace
    have hcomponents : IsEmpty T.Branch := by
      let _ : IsEmpty T.complex.vertices := Set.isEmpty_coe_sort.mpr hvertices
      infer_instance
    have hclosed : T.closedBranchCount = 0 := by
      apply Finite.card_eq_zero_iff.mpr
      exact Subtype.isEmpty_of_false fun c _ => hcomponents.false c
    have hboundary : T.boundaryBranchCount = 0 := by
      apply Finite.card_eq_zero_iff.mpr
      exact Subtype.isEmpty_of_false fun c _ => hcomponents.false c
    exact Nat.add_eq_zero_iff.mpr ⟨hclosed, hboundary⟩

end NormalSingularSetTriangulation

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem exists_fiber_eq_pair (hD : NormalSingularCellData D BdM B)
    {y : M} (hy : y ∈ doublePointSet D D.domain) :
    ∃ a b, a ≠ b ∧ D.domain ∩ D ⁻¹' {y} = {a, b} := by
  obtain ⟨a, ha, b, hb, hab, hDa, hDb⟩ := hy
  exact ⟨a, b, hab, fiber_eq_pair_of_encard_le_two D D.domain ha hb hab hDa hDb
    (hD.fiber_le_two y)⟩

theorem fiber_encard_eq_two (hD : NormalSingularCellData D BdM B)
    {y : M} (hy : y ∈ doublePointSet D D.domain) :
    (D.domain ∩ D ⁻¹' {y}).encard = 2 := by
  obtain ⟨a, b, hab, hfiber⟩ := hD.exists_fiber_eq_pair hy
  rw [hfiber, encard_pair hab]

open Classical in
theorem complexity_eq_zero_iff (hD : NormalSingularCellData D BdM B) :
    hD.singularSet.complexity = 0 ↔ D.IsNonsingular :=
  hD.singularSet.complexity_eq_zero_iff

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
