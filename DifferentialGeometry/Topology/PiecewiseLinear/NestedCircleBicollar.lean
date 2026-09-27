/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalCircleBicollar

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def IsPLBicollarNeighborhood (W J S : Set E) : Prop :=
  IsPolyhedron W ∧ W ⊆ S ∧ W ∈ nhdsSetWithin J S ∧
    ∃ ρ : E × ℝ → E, IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W ∧
      ∀ x ∈ J, ρ (x, 0) = x

def IsNestedPLBicollarNeighborhood (A B J S : Set E) : Prop :=
  IsPLBicollarNeighborhood A J S ∧ IsPLBicollarNeighborhood B J S ∧
    ∃ O : Set E, IsOpen O ∧ J ⊆ O ∧ B ⊆ O ∩ S ∧ O ∩ S ⊆ A

theorem IsPLSphere.exists_nested_bicollar_neighborhoods
    {S J U : Set E} (hS : IsPLSphere 2 S) (hJ : IsPLSphere 1 J) (hJS : J ⊆ S)
    (hU : U ∈ nhdsSetWithin J S) :
    ∃ A B : Set E, A ⊆ U ∧ IsNestedPLBicollarNeighborhood A B J S := by
  obtain ⟨A, ρ, hA, hAS, hAU, hAnhds, hρ, hρ0⟩ :=
    hS.exists_bicollar_of_isPLSphere_one hJ hJS hU
  obtain ⟨O, hO, hJO, hOSA⟩ := mem_nhdsSetWithin.mp hAnhds
  have hOnhds : O ∈ nhdsSetWithin J S := Filter.mem_inf_of_left <|
    mem_nhdsSet_iff_forall.mpr fun x hx => hO.mem_nhds (hJO hx)
  obtain ⟨B, σ, hB, hBS, hBO, hBnhds, hσ, hσ0⟩ :=
    hS.exists_bicollar_of_isPLSphere_one hJ hJS hOnhds
  exact ⟨A, B, hAU, ⟨⟨hA, hAS, hAnhds, ρ, hρ, hρ0⟩,
    ⟨hB, hBS, hBnhds, σ, hσ, hσ0⟩, O, hO, hJO,
    fun x hx => ⟨hBO hx, hBS hx⟩, hOSA⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
