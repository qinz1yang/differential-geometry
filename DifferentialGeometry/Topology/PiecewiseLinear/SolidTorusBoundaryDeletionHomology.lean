/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryCollarInward
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusComplementHomology

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsCombinatorialSolidTorus.bijective_integralSingularHomologyMap_of_interior_subset
    {S A : Set E3} (hS : IsCombinatorialSolidTorus S) (n : ℕ)
    (hAi : interior S ⊆ A) (hAS : A ⊆ S) :
    Function.Bijective (integralSingularHomologyMap n
      (⟨inclusion hAS, continuous_inclusion hAS⟩ : C(A, S))) := by
  let _ : CompactSpace (frontier S) := isCompact_iff_compactSpace.mp
    (hS.isPolyhedron.isCompact.of_isClosed_subset isClosed_frontier
      hS.isPolyhedron.isClosed.frontier_subset)
  obtain ⟨c, _, _, _, _, hside, _⟩ := hS.exists_collared_exterior_cover
  have hfront : frontier S ⊆ Set.range (Subtype.val : frontier S → E3) := by
    rw [Subtype.range_coe]
  exact (integralSingularHomologyHomotopyEquiv n
    (c.intermediateDomainHomotopyEquiv hfront hside hAi hAS)).bijective

theorem IsCombinatorialSolidTorus.bijective_integralSingularHomologyMap_of_exterior_subset
    {S A : Set E3} (hS : IsCombinatorialSolidTorus S) (n : ℕ)
    (hAi : Sᶜ ⊆ A) (hAS : A ⊆ (interior S)ᶜ) :
    Function.Bijective (integralSingularHomologyMap n
      (⟨inclusion hAS, continuous_inclusion hAS⟩ : C(A, ((interior S)ᶜ : Set E3)))) := by
  let _ : CompactSpace (frontier S) := isCompact_iff_compactSpace.mp
    (hS.isPolyhedron.isCompact.of_isClosed_subset isClosed_frontier
      hS.isPolyhedron.isClosed.frontier_subset)
  obtain ⟨c, hcover, hmeet, hScl, hEcl, _, hside⟩ := hS.exists_collared_exterior_cover
  have hcover' := (union_comm (interior S)ᶜ S).trans hcover
  have hfront : frontier (interior S)ᶜ ⊆ Set.range (Subtype.val : frontier S → E3) := by
    rw [Subtype.range_coe]
    exact ((frontier_eq_inter_of_closure_sdiff_eq hcover' hEcl hScl).trans
      ((inter_comm _ _).trans hmeet)).subset
  have hint : interior (interior S)ᶜ = Sᶜ :=
    interior_eq_compl_of_closure_sdiff_eq hcover' hScl
  exact (integralSingularHomologyHomotopyEquiv n
    (c.reverse.intermediateDomainHomotopyEquiv hfront hside (hint ▸ hAi) hAS)).bijective

end DifferentialGeometry.Topology.PiecewiseLinear
