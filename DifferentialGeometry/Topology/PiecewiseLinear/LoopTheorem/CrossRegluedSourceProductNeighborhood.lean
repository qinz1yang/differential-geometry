/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceProductBranch
import DifferentialGeometry.Topology.PiecewiseLinear.CellMapTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRetraction
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance

open Set Topology
open DifferentialGeometry.Topology.Homotopy

namespace DifferentialGeometry.Topology.PiecewiseLinear

private noncomputable local instance euclideanDecidableEq :
    DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _

theorem isPolyhedron_crossingProductCell_boundary :
    IsPolyhedron (Set.range crossingProductCell.boundary) := by
  have hP := crossingProductCell.isPLBall_domain.isPLSphere_frontier.isPolyhedron
  have hcomp := isPiecewiseAffineOn_crossingProductMap.comp
    (isPiecewiseAffineOn_seamWitnessPlaneSymm hP)
  rw [preimage_univ, inter_univ] at hcomp
  have hpa := hcomp.affine_comp spliceEmbedding.toLinearMap.toAffineMap
  have hpoly := hpa.isPolyhedron_image hP
  convert hpoly using 1
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

private theorem boundary_derivedNeighborhood_properties
    (K L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces]
    (hL : L.faces ⊆ K.faces) (hKspace : K.space = frontier crossingProductSide)
    (hLspace : L.space = Set.range crossingProductCell.boundary) :
    IsCombinatorialManifoldWithBoundary 2 (derivedNeighborhood K L) ∧
      (derivedNeighborhood K L).space ⊆ frontier crossingProductSide ∧
      Set.range crossingProductCell.boundary ⊆ (derivedNeighborhood K L).space ∧
      (∀ z ∈ Set.range crossingProductCell.boundary,
        (derivedNeighborhood K L).space ∈ 𝓝[frontier crossingProductSide] z) := by
  have hS : IsPLSphere 2 K.space := by
    rw [hKspace]
    exact isPLBall_crossingProductSide.isPLSphere_frontier
  have hman : IsCombinatorialManifold 2 K := hS.isCombinatorialManifold
  refine ⟨hman.isCombinatorialManifoldWithBoundary.derivedNeighborhood L, ?_, ?_, ?_⟩
  · rw [← hKspace]
    exact derivedNeighborhood_space_subset K L
  · rw [← hLspace]
    exact subcomplex_space_subset_derivedNeighborhood hL
  · rw [← hLspace, ← hKspace]
    exact fun _ hz => derivedNeighborhood_mem_nhdsWithin hL hz

open Classical in
theorem crossingProductCell_exists_boundary_derivedNeighborhood :
    ∃ K L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      K.faces.Finite ∧ L.faces ⊆ K.faces ∧
      K.space = frontier crossingProductSide ∧
      L.space = Set.range crossingProductCell.boundary ∧
      IsCombinatorialManifoldWithBoundary 2 (derivedNeighborhood K L) ∧
      (derivedNeighborhood K L).space ⊆ frontier crossingProductSide ∧
      Set.range crossingProductCell.boundary ⊆ (derivedNeighborhood K L).space ∧
      (∀ z ∈ Set.range crossingProductCell.boundary,
        (derivedNeighborhood K L).space ∈ 𝓝[frontier crossingProductSide] z) := by
  have hS := isPLBall_crossingProductSide.isPLSphere_frontier
  obtain ⟨K₀, hK₀fin, hK₀space⟩ := hS.isPolyhedron.exists_simplicialComplex
  let _ : Finite K₀.faces := hK₀fin.to_subtype
  have hsub : Set.range crossingProductCell.boundary ⊆ frontier crossingProductSide := by
    rw [← crossingProductCell_image_inter_frontier_side]
    exact inter_subset_right
  obtain ⟨K, hK, hKfin, hcover⟩ := exists_isSubdivision_subcomplexes K₀
    (fun _ : Unit => Set.range crossingProductCell.boundary)
    (fun _ => isPolyhedron_crossingProductCell_boundary)
    (fun _ => hsub.trans hK₀space.symm.subset)
  let _ : Finite K.faces := hKfin.to_subtype
  let L := restrict K (Set.range crossingProductCell.boundary)
  have hL : L.faces ⊆ K.faces := restrict_faces_subset _ _
  have hLspace : L.space = Set.range crossingProductCell.boundary :=
    restrict_space_of_eq_biUnion K _ (hcover ())
  have hKspace : K.space = frontier crossingProductSide := hK.space_eq.trans hK₀space
  exact ⟨K, L, hKfin, hL, hKspace, hLspace,
    boundary_derivedNeighborhood_properties K L hL hKspace hLspace⟩

theorem crossingProductCell_exists_boundary_regularNeighborhood :
    ∃ B : Set (EuclideanSpace ℝ (Fin 3)), IsPolyhedron B ∧
      B ⊆ frontier crossingProductSide ∧ Set.range crossingProductCell.boundary ⊆ B ∧
      (∀ z ∈ Set.range crossingProductCell.boundary, B ∈ 𝓝[frontier crossingProductSide] z) ∧
      Nonempty (StrongDeformationRetract {z : B | (z : EuclideanSpace ℝ (Fin 3)) ∈
        Set.range crossingProductCell.boundary}) := by
  classical
  obtain ⟨K, L, hKfin, hL, _, hLspace, _, hBside, hBcore, hBnhds⟩ :=
    crossingProductCell_exists_boundary_derivedNeighborhood
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite (derivedNeighborhood K L).faces :=
    (derivedNeighborhood_faces_finite K L).to_subtype
  refine ⟨(derivedNeighborhood K L).space, isPolyhedron_space _, hBside, hBcore, hBnhds, ?_⟩
  have heq : derivedNeighborhoodSubcomplex K L =
      {z : (derivedNeighborhood K L).space | (z : EuclideanSpace ℝ (Fin 3)) ∈
        Set.range crossingProductCell.boundary} := by
    ext z
    exact hLspace ▸ Iff.rfl
  exact ⟨(derivedNeighborhoodStrongDeformationRetract hL).congr heq⟩

end DifferentialGeometry.Topology.PiecewiseLinear
