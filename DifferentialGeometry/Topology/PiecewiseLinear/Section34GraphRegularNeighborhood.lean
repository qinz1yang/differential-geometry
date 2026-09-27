/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedExhaustionRegularNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ControlledVertexCells

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M}

open Classical in
theorem isLocallyFiniteRegularNeighborhoodOf_section34GraphVertexCells
    {𝒦 𝒦₀ 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
    (hU : IsOpen U) (h𝒦₀ : IsCombinatorialManifoldWithBoundary 3 𝒦₀.complex)
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hderived : 𝒦'.complex = secondDerived 𝒦₀.complex) (hmap₀ : 𝒦'.map = 𝒦₀.map) :
    IsLocallyFiniteRegularNeighborhoodOf (n := 3)
      (⋃ w : Section34VertexIndex 𝒦 𝒦', section34GraphVertexCell 𝒦 𝒦' w)
      (graphSkeletonSpace 𝒦) U := by
  let L := restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦)
  have hL : L.faces ⊆ (secondDerived 𝒦₀.complex).faces := by
    rw [← hderived]
    exact restrict_faces_subset _ _
  have hcore := isSubdivision_restrict_preimage_graphSkeletonSpace hsub hmap
  have hcard : ∀ s ∈ L.faces, s.card ≤ 2 := fun s hs => hcore.card_le
    (fun t ht => ((mem_restrict_preimage_graphSkeletonSpace_iff 𝒦).mp ht).2) hs
  have himage : 𝒦'.map '' L.space = graphSkeletonSpace 𝒦 := by
    rw [show L.space = (restrict 𝒦.complex (𝒦.map ⁻¹' graphSkeletonSpace 𝒦)).space
      from hcore.space_eq, hmap, image_restrict_preimage_graphSkeletonSpace]
  have hN := 𝒦₀.isLocallyFiniteRegularNeighborhoodOf_secondDerived hU h𝒦₀ L hL hcard
  rw [← hderived, ← hmap₀, himage] at hN
  rw [iUnion_section34GraphVertexCell]
  exact hN

end DifferentialGeometry.Topology.PiecewiseLinear
