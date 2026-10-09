/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLPieceWithBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.RelativePieceNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_prescribed_cutOut_piece_with_boundary_source
    {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [TopologicalSpace Y]
    (f : X → Y) {S Sbd : Set X}
    (T : PLPieceIn E 2 X S)
    (D : Geometry.SimplicialComplex ℝ E) (hD : D.faces ⊆ T.complex.faces)
    (hSbd : T.map '' D.space = Sbd)
    {W V₀ V : Set Y} (hW : closure W ⊆ V₀)
    (hsource : S ⊆ f ⁻¹' V)
    (hDQ : T.map '' (regularNeighborhoodIn T.complex D.space).space ⊆ interior S)
    (hC : IsCompact (f ⁻¹' closure V₀))
    (hCsource : f ⁻¹' closure V₀ ⊆ interior S) :
    ∃ (P : Set X) (Tbd : PLPieceWithBoundary E 2 X P Sbd)
      (L : Geometry.SimplicialComplex ℝ E),
      IsCombinatorialManifoldWithBoundary 2 Tbd.piece.complex ∧
        L.faces ⊆ Tbd.piece.complex.faces ∧ D.faces ⊆ L.faces ∧
          IsCompact P ∧ f ⁻¹' closure V₀ ⊆ interior P ∧
            P ⊆ f ⁻¹' V ∧ f ⁻¹' closure W ⊆ interior P ∧
              Tbd.piece.map = T.map := by
  obtain ⟨P, T', L, hman, hL, hD', hCimage, hCinterior, hPsub, hmap, houter⟩ :=
    T.exists_manifold_neighborhood_preserving_subcomplex D hD hDQ hC hCsource
  have hcompact : IsCompact P := T'.isCompact
  have hPsubV : P ⊆ f ⁻¹' V := by
    intro x hx
    exact hsource (interior_subset (hPsub hx))
  have hWinterior : f ⁻¹' closure W ⊆ interior P := by
    intro x hx
    apply hCinterior
    exact subset_closure (hW hx)
  let Tbd : PLPieceWithBoundary E 2 X P Sbd :=
    { piece := T',
      boundaryComplex := D,
      boundary_faces := (hD'.trans hL),
      boundary_image := by rw [hmap, hSbd],
      source_compact := hcompact,
      source_manifold := hman }
  exact ⟨P, Tbd, L, hman, hL, hD', hcompact, hCinterior, hPsubV,
    hWinterior, hmap⟩

end DifferentialGeometry.Topology.PiecewiseLinear
