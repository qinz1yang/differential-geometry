import DifferentialGeometry.Geometry.Boundary.Manifold.CollaredQuotientInteriorAtlas
import DifferentialGeometry.Topology.Manifold.Homeomorph.Transport

open Set Function Topology
open scoped Manifold ContDiff

noncomputable section
set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

universe u v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type u} [TopologicalSpace X] [ChartedSpace H X]
variable {ι : Type v} [Finite ι]

namespace CollaredGluing

private def intrinsicInteriorOpen (I : ModelWithCorners ℝ E H) (X : Type u)
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] :
    TopologicalSpace.Opens X :=
  DifferentialGeometry.Manifold.intrinsicInterior I ∞ (by norm_num)

private noncomputable def intrinsicInteriorHomeomorph (I : ModelWithCorners ℝ E H) (X : Type u)
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] :
    ↥(I.interior X) ≃ₜ intrinsicInteriorOpen I X :=
  Homeomorph.setCongr (by rfl)

@[instance_reducible]
private noncomputable def intrinsicInteriorChartedSpace (I : ModelWithCorners ℝ E H)
    (X : Type u) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] :
    ChartedSpace E ↥(I.interior X) := by
  let _ : BoundarylessManifold I (intrinsicInteriorOpen I X) :=
    DifferentialGeometry.Manifold.boundarylessManifold_intrinsicInterior I ∞ (by norm_num)
  let _ : ChartedSpace E (intrinsicInteriorOpen I X) :=
    DifferentialGeometry.Manifold.interiorChartedSpace I ∞
  exact DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := E) (intrinsicInteriorHomeomorph I X)

private theorem intrinsicInteriorIsManifold (I : ModelWithCorners ℝ E H) (X : Type u)
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] :
    @IsManifold ℝ _ E _ _ E _ (𝓘(ℝ, E)) ∞ ↥(I.interior X) _
      (intrinsicInteriorChartedSpace I X) := by
  let U := intrinsicInteriorOpen I X
  let _ : BoundarylessManifold I U :=
    DifferentialGeometry.Manifold.boundarylessManifold_intrinsicInterior I ∞ (by norm_num)
  let _ : ChartedSpace E U :=
    DifferentialGeometry.Manifold.interiorChartedSpace I ∞
  let _ : IsManifold 𝓘(ℝ, E) ∞ U :=
    DifferentialGeometry.Manifold.interiorIsManifold I ∞
  have hchart : ChartedSpace E ↥(I.interior X) := intrinsicInteriorChartedSpace I X
  exact DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
    (H := E) (I := 𝓘(ℝ, E)) (n := ∞) (intrinsicInteriorHomeomorph I X)

private theorem intrinsicInteriorBoundaryless (I : ModelWithCorners ℝ E H)
    (X : Type u) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] :
    @BoundarylessManifold ℝ _ E _ _ E _ (𝓘(ℝ, E)) ↥(I.interior X) _
      (intrinsicInteriorChartedSpace I X) := by
  let U := intrinsicInteriorOpen I X
  let _ : BoundarylessManifold I U :=
    DifferentialGeometry.Manifold.boundarylessManifold_intrinsicInterior I ∞ (by norm_num)
  let _ : ChartedSpace E U :=
    DifferentialGeometry.Manifold.interiorChartedSpace I ∞
  let _ : IsManifold 𝓘(ℝ, E) ∞ U :=
    DifferentialGeometry.Manifold.interiorIsManifold I ∞
  have hchart : ChartedSpace E ↥(I.interior X) := intrinsicInteriorChartedSpace I X
  have hboundaryless : @BoundarylessManifold ℝ _ E _ _ E _ (𝓘(ℝ, E)) ↥(I.interior X) _
      (intrinsicInteriorChartedSpace I X) :=
    by
      simpa only using DifferentialGeometry.Manifold.Homeomorph.boundaryless_manifold_pullback
        (H := E) (I := 𝓘(ℝ, E)) (n := ∞) (intrinsicInteriorHomeomorph I X) (by norm_num)
  exact DifferentialGeometry.Manifold.Homeomorph.boundaryless_manifold_pullback
    (H := E) (I := 𝓘(ℝ, E)) (n := ∞) (intrinsicInteriorHomeomorph I X) (by norm_num)

noncomputable def interiorPieceHomeomorph (G : CollaredGluing I X ι) [IsManifold I ∞ X]
    (hne : Nonempty ↥(I.interior X)) :
    ↥(I.interior X) ≃ₜ ↥(G.interiorPiece hne).target :=
  (Homeomorph.Set.univ ↥(I.interior X)).symm.trans
    (G.interiorPiece hne).toHomeomorphSourceTarget

@[simp]
theorem interiorPieceHomeomorph_apply (G : CollaredGluing I X ι) [IsManifold I ∞ X]
    (hne : Nonempty ↥(I.interior X)) (x : ↥(I.interior X)) :
    G.interiorPieceHomeomorph hne x =
      ⟨G.interiorPiece hne x, (G.interiorPiece hne).map_source (Set.mem_univ x)⟩ := rfl

theorem isOpen_interiorPiece_target (G : CollaredGluing I X ι) [IsManifold I ∞ X]
    (hne : Nonempty ↥(I.interior X)) :
    IsOpen (G.interiorPiece hne).target := by
  rw [G.interiorPiece_target hne, ← G.range_quotientMk_subtype (U := I.interior X)]
  exact G.isOpenEmbedding_quotientMk_interior.isOpen_range

@[instance_reducible]
noncomputable def interiorPieceChartedSpace (G : CollaredGluing I X ι) [IsManifold I ∞ X]
    (hne : Nonempty ↥(I.interior X)) :
    ChartedSpace E ↥(G.interiorPiece hne).target :=
  @DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace E ↥(I.interior X)
    ↥(G.interiorPiece hne).target _ _ (intrinsicInteriorChartedSpace I X) _
    (G.interiorPieceHomeomorph hne).symm

theorem interiorPiece_isManifold (G : CollaredGluing I X ι) [IsManifold I ∞ X]
    (hne : Nonempty ↥(I.interior X)) :
    @IsManifold ℝ _ E _ _ E _ (𝓘(ℝ, E)) ∞ ↥(G.interiorPiece hne).target _
      (G.interiorPieceChartedSpace hne) := by
  have hchart : ChartedSpace E ↥(I.interior X) := intrinsicInteriorChartedSpace I X
  have hman : @IsManifold ℝ _ E _ _ E _ (𝓘(ℝ, E)) ∞ ↥(I.interior X) _
      (intrinsicInteriorChartedSpace I X) := intrinsicInteriorIsManifold I X
  exact @DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback E ↥(I.interior X)
    ↥(G.interiorPiece hne).target _ _ (intrinsicInteriorChartedSpace I X) _ ℝ E _ _ _
    (𝓘(ℝ, E)) ∞ hman (G.interiorPieceHomeomorph hne).symm

theorem interiorPiece_boundarylessManifold (G : CollaredGluing I X ι) [IsManifold I ∞ X]
    (hne : Nonempty ↥(I.interior X)) :
    @BoundarylessManifold ℝ _ E _ _ E _ (𝓘(ℝ, E)) ↥(G.interiorPiece hne).target _
      (G.interiorPieceChartedSpace hne) := by
  have hchart : ChartedSpace E ↥(I.interior X) := intrinsicInteriorChartedSpace I X
  have hman : @IsManifold ℝ _ E _ _ E _ (𝓘(ℝ, E)) ∞ ↥(I.interior X) _
      (intrinsicInteriorChartedSpace I X) := intrinsicInteriorIsManifold I X
  have hboundaryless : @BoundarylessManifold ℝ _ E _ _ E _ (𝓘(ℝ, E)) ↥(I.interior X) _
      (intrinsicInteriorChartedSpace I X) := intrinsicInteriorBoundaryless I X
  exact @DifferentialGeometry.Manifold.Homeomorph.boundaryless_manifold_pullback E
    ↥(I.interior X) ↥(G.interiorPiece hne).target _ _ (intrinsicInteriorChartedSpace I X) _
    ℝ E _ _ _ (𝓘(ℝ, E)) ∞ hman hboundaryless (G.interiorPieceHomeomorph hne).symm
    (by norm_num)

end CollaredGluing

section UnitInterval

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

theorem unitIntervalCollaredGluing_interiorPiece_target_nonempty :
    (unitIntervalCollaredGluing.interiorPiece
      unitIntervalCollaredGluing_interior_nonempty).target.Nonempty := by
  let x : ↥((𝓡∂ 1).interior (Icc (0 : ℝ) 1)) :=
    ⟨⟨(1 : ℝ) / 2, by norm_num⟩, unitIntervalCollaredGluing_mem_interior⟩
  exact ⟨unitIntervalCollaredGluing.interiorPiece
      unitIntervalCollaredGluing_interior_nonempty x,
    (unitIntervalCollaredGluing.interiorPiece
      unitIntervalCollaredGluing_interior_nonempty).map_source (Set.mem_univ x)⟩

theorem unitIntervalCollaredGluing_interiorPiece_isManifold :
    @IsManifold ℝ _ (EuclideanSpace ℝ (Fin 1)) _ _ (EuclideanSpace ℝ (Fin 1)) _
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 1))) ∞
      ↥(unitIntervalCollaredGluing.interiorPiece
        unitIntervalCollaredGluing_interior_nonempty).target _
      (unitIntervalCollaredGluing.interiorPieceChartedSpace
        unitIntervalCollaredGluing_interior_nonempty) :=
  CollaredGluing.interiorPiece_isManifold unitIntervalCollaredGluing
    unitIntervalCollaredGluing_interior_nonempty

theorem unitIntervalCollaredGluing_interiorPiece_boundarylessManifold :
    @BoundarylessManifold ℝ _ (EuclideanSpace ℝ (Fin 1)) _ _
      (EuclideanSpace ℝ (Fin 1)) _ (𝓘(ℝ, EuclideanSpace ℝ (Fin 1)))
      ↥(unitIntervalCollaredGluing.interiorPiece
        unitIntervalCollaredGluing_interior_nonempty).target _
      (unitIntervalCollaredGluing.interiorPieceChartedSpace
        unitIntervalCollaredGluing_interior_nonempty) :=
  CollaredGluing.interiorPiece_boundarylessManifold unitIntervalCollaredGluing
    unitIntervalCollaredGluing_interior_nonempty

end UnitInterval

end DifferentialGeometry.Geometry.Boundary
