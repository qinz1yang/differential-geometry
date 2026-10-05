import DifferentialGeometry.Topology.PiecewiseLinear.Smoothing.HandleAttachment
import DifferentialGeometry.Topology.PiecewiseLinear.Combinatorial
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodHandleFiltration
import DifferentialGeometry.Topology.PiecewiseLinear.PieceParametrization
import DifferentialGeometry.Topology.PiecewiseLinear.Exhaustion
import DifferentialGeometry.Topology.Manifold.InteriorAtlas
import DifferentialGeometry.Topology.Manifold.Homeomorph.Transport

open Set Topology Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

open DifferentialGeometry.Topology.SimplicialComplex (geometricFacePrefix)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem exists_boundarylessManifold_of_isCombinatorialManifold_three [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 3 K) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanHalfSpace 3) M),
      IsManifold (𝓡∂ 3) ∞ M ∧ BoundarylessManifold (𝓡∂ 3) M ∧ Nonempty (K.space ≃ₜ M) := by
  obtain ⟨m, e, he, k, -, -, hzero, hlast, -, hman, hstep⟩ :=
    exists_pl_three_handle_filtration K hK
  let N : ℕ → Geometry.SimplicialComplex ℝ E :=
    fun i => derivedNeighborhood K (geometricFacePrefix K e he i)
  have hzero' : (N 0).space = ∅ := hzero
  have hlast' : (N m).space = K.space := hlast
  have hman' : ∀ i, IsCombinatorialManifoldWithBoundary 3 (N i) := hman
  have hstep' : ∀ i : Fin m, IsPLThreeHandleAttachment (k i) (N i.val)
      (derivedNeighborhoodCell K (e i).val).space (N (i.val + 1)).space := hstep
  have hfin : ∀ i, Finite (N i).faces := fun i => (derivedNeighborhood_faces_finite _ _).to_subtype
  have hind : ∀ i, i ≤ m →
      IsSmoothHandleStage (N i).space (Subtype.val ⁻¹' (boundaryComplex 3 (N i)).space) := by
    intro i
    induction i with
    | zero =>
      intro _
      have : IsEmpty (N 0).space := ⟨fun x => Set.notMem_empty x.val (hzero' ▸ x.property)⟩
      exact isSmoothHandleStage_of_isEmpty _ _
    | succ i ih =>
      intro hi
      have := hfin i
      have := hfin (i + 1)
      exact isSmoothHandleStage_step (hman' i) (hman' (i + 1)) (k ⟨i, hi⟩) (hstep' ⟨i, hi⟩)
        (ih (Nat.le_of_succ_le hi))
  obtain ⟨M, iT, iC, hM, -, -, h, hbd⟩ := hind m le_rfl
  have := hfin m
  have hbdempty : (boundaryComplex 3 (N m)).space = ∅ := by
    have h1 : (boundaryComplex 3 (N m)).space = id '' (boundaryComplex 3 K).space :=
      boundaryComplex_space_of_isPLHomeomorphOn (n := 2) K (N m)
        hK.isCombinatorialManifoldWithBoundary (f := id)
        (by rw [hlast']; exact (isPolyhedron_space K).isPLHomeomorphOn_id)
    have h2 : (boundaryComplex 3 K).faces = ∅ := hK.boundaryComplex_faces_eq_empty K
    rw [h1, Set.image_id, Geometry.SimplicialComplex.space, h2]
    simp
  have hbdM : (𝓡∂ 3).boundary M = ∅ := by
    rw [← hbd, hbdempty, Set.preimage_empty, Set.image_empty]
  exact ⟨M, iT, iC, hM, ModelWithCorners.Boundaryless.of_boundary_eq_empty hbdM,
    ⟨(Homeomorph.setCongr hlast'.symm).trans h⟩⟩

theorem exists_homeomorphic_smooth_manifold_of_hasGroupoid_plGroupoid_three
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [HasGroupoid X (plGroupoid 3)] :
    ∃ (N : Type u) (_ : TopologicalSpace N) (_ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) N),
      IsManifold (𝓡 3) ∞ N ∧ Nonempty (X ≃ₜ N) := by
  by_cases hX : Nonempty X
  · obtain ⟨T, hT⟩ := exists_plTriangulation_isCombinatorialManifold (n := 3) (X := X)
    have : Finite T.complex.faces := T.finite_faces
    obtain ⟨M, iT, iC, hM, hbl, ⟨h⟩⟩ :=
      exists_boundarylessManifold_of_isCombinatorialManifold_three T.complex hT
    let iC' : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M :=
      DifferentialGeometry.Manifold.interiorChartedSpace (𝓡∂ 3) ∞ (M := M)
    have hM' : IsManifold (𝓡 3) ∞ M :=
      DifferentialGeometry.Manifold.interiorIsManifold (𝓡∂ 3) ∞ (M := M)
    refine ⟨ULift.{u} M, inferInstance,
      DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
        (Homeomorph.ulift : ULift.{u} M ≃ₜ M),
      DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback (I := 𝓡 3) (n := ∞) _,
      ⟨?_⟩⟩
    have e₀ : T.complex.space ≃ₜ X := T.toPieceIn.homeomorph.trans (Homeomorph.Set.univ X)
    exact e₀.symm.trans (h.trans Homeomorph.ulift.symm)
  · have : IsEmpty X := not_nonempty_iff.mp hX
    exact ⟨X, inferInstance, inferInstance, IsManifold.empty _, ⟨Homeomorph.refl X⟩⟩

theorem exists_isManifold_of_hasGroupoid_plGroupoid_three
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [HasGroupoid X (plGroupoid 3)] :
    ∃ C : ChartedSpace (EuclideanSpace ℝ (Fin 3)) X,
      letI := C
      IsManifold (𝓡 3) ∞ X := by
  obtain ⟨N, _, _, hN, ⟨e⟩⟩ :=
    exists_homeomorphic_smooth_manifold_of_hasGroupoid_plGroupoid_three (X := X)
  exact ⟨DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace e,
    DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback (I := 𝓡 3) (n := ∞) e⟩

end DifferentialGeometry.Topology.PiecewiseLinear
