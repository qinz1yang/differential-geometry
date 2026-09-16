import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell
import DifferentialGeometry.Topology.PiecewiseLinear.PLPiece
import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

def HasPLNormalDoubleCrossingAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (P : Set E) (B : Set F)
    (y : F) : Prop :=
  (y ∈ B ∧ ∃ M : Set F, HasPLBoundaryDoubleCrossingAt f P M y) ∨
    (y ∉ B ∧ HasPLDoubleCrossingAt f P y)

theorem HasPLNormalDoubleCrossingAt.postcomp_openPartialHomeomorph
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {f : E → F} {P : Set E} {B : Set F} {y : F}
    (h : HasPLNormalDoubleCrossingAt f P B y) (e : OpenPartialHomeomorph F F)
    (he : IsPiecewiseAffineOn e e.source) (hf : MapsTo f P e.source) (hy : y ∈ e.source) :
    HasPLNormalDoubleCrossingAt (e ∘ f) P (e '' (e.source ∩ B)) (e y) := by
  rcases h with ⟨hyB, M, hcross⟩ | ⟨hyB, hcross⟩
  · refine Or.inl ⟨⟨y, ⟨hy, hyB⟩, rfl⟩, e '' (e.source ∩ M), ?_⟩
    exact hcross.postcomp_openPartialHomeomorph e he hf
  · refine Or.inr ⟨?_, hcross.postcomp_openPartialHomeomorph e he hf⟩
    rintro ⟨z, ⟨hz, hzB⟩, hzy⟩
    exact hyB ((e.injOn hz hy hzy) ▸ hzB)

structure IsNormalSingularCell {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (D : SingularTwoCell M)
    (BdM B' : Set M) : Prop where
  locallyInjective : ∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, Set.InjOn D U
  fiber_le_two : ∀ y, (D.domain ∩ D ⁻¹' {y}).encard ≤ 2
  boundary_image_subset : Set.range D.boundary ⊆ B'
  image_inter_boundary : D '' D.domain ∩ BdM = Set.range D.boundary
  doublePointSet_triangulated :
    ∃ (P : Set M) (T : PLPiece 3 M P)
      (G : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin T.ambientDim))),
      G.faces.Finite ∧ G.faces ⊆ T.piece.complex.faces ∧
        IsCombinatorialManifoldWithBoundary 1 G ∧
          T.piece.map '' G.space = doublePointSet D D.domain ∧
            T.piece.map '' (boundaryComplex 1 G).space = doublePointSet D D.domain ∩ BdM
  crossing : ∀ y ∈ doublePointSet D D.domain,
    ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
      HasPLNormalDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source)
        (e '' (e.source ∩ BdM)) (e y)

namespace IsNormalSingularCell

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B' : Set M}

theorem locallyInjective_restrict (h : IsNormalSingularCell D BdM B')
    {Q : Set (EuclideanSpace ℝ (Fin 2))} (hQ : Q ⊆ D.domain) :
    ∀ x ∈ Q, ∃ U ∈ 𝓝[Q] x, Set.InjOn D U := by
  intro x hx
  obtain ⟨U, hU, hinj⟩ := h.locallyInjective x (hQ hx)
  exact ⟨U, nhdsWithin_mono x hQ hU, hinj⟩

theorem fiber_le_two_restrict (h : IsNormalSingularCell D BdM B')
    {Q : Set (EuclideanSpace ℝ (Fin 2))} (hQ : Q ⊆ D.domain) (y : M) :
    (Q ∩ D ⁻¹' {y}).encard ≤ 2 :=
  (encard_le_encard (inter_subset_inter hQ Subset.rfl)).trans (h.fiber_le_two y)

theorem doublePointSet_mono {Q : Set (EuclideanSpace ℝ (Fin 2))}
    (hQ : Q ⊆ D.domain) : doublePointSet D Q ⊆ doublePointSet D D.domain := by
  rintro y ⟨x, hx, z, hz, hxz, hxy, hzy⟩
  exact ⟨x, hQ hx, z, hQ hz, hxz, hxy, hzy⟩

theorem exists_crossing_chart (h : IsNormalSingularCell D BdM B')
    {y : M} (hy : y ∈ doublePointSet D D.domain) :
    ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
      HasPLNormalDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source)
        (e '' (e.source ∩ BdM)) (e y) :=
  h.crossing y hy

end IsNormalSingularCell

end DifferentialGeometry.Topology.PiecewiseLinear
