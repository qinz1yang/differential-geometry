/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.CollaredCoverProduct
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative
import DifferentialGeometry.Topology.PiecewiseLinear.TorusBicollar
import Mathlib.Analysis.Normed.Module.Connected

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem closure_interior_of_combinatorial_solid_torus {S : Set E3}
    (hS : IsCombinatorialSolidTorus S) : closure (interior S) = S := by
  apply Subset.antisymm (closure_minimal interior_subset hS.isPolyhedron.isClosed)
  obtain ⟨-, n, -, C, -, hCS, hC, -⟩ := hS
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hCS.symm ▸ hx)
  have hCi : (C i).space ⊆ S := (subset_iUnion _ i).trans hCS.subset
  exact closure_mono (interior_mono hCi) ((hC i).closure_interior.symm ▸ hi)

theorem IsCombinatorialSolidTorus.exists_collared_exterior_cover
    {S : Set E3} (hS : IsCombinatorialSolidTorus S) :
    ∃ c : ThreeManifold.TwoSidedCollar (Subtype.val : frontier S → E3),
      S ∪ (interior S)ᶜ = univ ∧ S ∩ (interior S)ᶜ = frontier S ∧
      closure (S \ (interior S)ᶜ) = S ∧
      closure ((interior S)ᶜ \ S) = (interior S)ᶜ ∧
      (∀ p : frontier S × ℝ, c.toFun p ∈ S ↔ p.2 ≤ 0) ∧
      (∀ p : frontier S × ℝ, c.reverse.toFun p ∈ (interior S)ᶜ ↔ p.2 ≤ 0) := by
  have hT := hS.isPLTorus_frontier
  obtain ⟨L, -, -, hLc, hLT⟩ := hT.exists_combinatorial_triangulation
  let _ : ConnectedSpace (frontier S) :=
    isConnected_iff_connectedSpace.mp (hLT ▸ hLc)
  obtain ⟨c⟩ := hT.isBicollared
  have hcover : S ∪ (interior S)ᶜ = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ interior S
    · exact Or.inl (interior_subset hx)
    · exact Or.inr hx
  have hmeet : S ∩ (interior S)ᶜ = frontier S :=
    hS.isPolyhedron.isClosed.frontier_eq.symm
  have hScl : closure (S \ (interior S)ᶜ) = S := by
    rw [Set.sdiff_compl, inter_eq_right.mpr interior_subset]
    exact closure_interior_of_combinatorial_solid_torus hS
  have hEcl : closure ((interior S)ᶜ \ S) = (interior S)ᶜ := by
    have heq : (interior S)ᶜ \ S = Sᶜ := by
      ext x
      exact ⟨fun hx => hx.2, fun hx => ⟨fun hi => hx (interior_subset hi), hx⟩⟩
    rw [heq, closure_compl]
  have hmeet' : S ∩ (interior S)ᶜ = Set.range (Subtype.val : frontier S → E3) := by
    rw [Subtype.range_coe]
    exact hmeet
  obtain ⟨d, -, hdS, hdE, -, -⟩ :=
    c.exists_open_cover_of_closed_cover hcover hmeet' hScl hEcl
  exact ⟨d, hcover, hmeet, hScl, hEcl, hdS, hdE⟩

theorem IsCombinatorialSolidTorus.bijective_integralSingularHomologyMap_frontier_pair
    {S : Set E3} (hS : IsCombinatorialSolidTorus S) :
    Function.Bijective (fun a : integralSingularHomology 1 (frontier S) =>
      (integralSingularHomologyMap 1
        (⟨inclusion hS.isPolyhedron.isClosed.frontier_subset, continuous_inclusion _⟩ :
          C(frontier S, S)) a,
      integralSingularHomologyMap 1
        (⟨inclusion (show frontier S ⊆ (interior S)ᶜ from fun _ hx => hx.2),
          continuous_inclusion _⟩ : C(frontier S, ((interior S)ᶜ : Set E3))) a)) := by
  obtain ⟨L, -, -, hLc, hLT⟩ := hS.isPLTorus_frontier.exists_combinatorial_triangulation
  let _ : ConnectedSpace (frontier S) :=
    isConnected_iff_connectedSpace.mp (hLT ▸ hLc)
  obtain ⟨c, hcover, hmeet, hScl, hEcl, -, -⟩ := hS.exists_collared_exterior_cover
  exact bijective_integralSingularHomologyMap_pair_of_collared_closed_cover
    c hcover hmeet hScl hEcl 1
    (integralSingularHomology_subsingleton_of_contractible 1 one_ne_zero E3)
    (integralSingularHomology_subsingleton_of_contractible 2 (by omega) E3)

end DifferentialGeometry.Topology.PiecewiseLinear
