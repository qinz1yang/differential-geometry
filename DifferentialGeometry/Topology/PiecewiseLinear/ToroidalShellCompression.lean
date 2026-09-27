/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ToroidalShell
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceIncompressibility
import DifferentialGeometry.Topology.PiecewiseLinear.ToroidalShellSphere

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsToroidalShell.exists_connected_separating_surface_fundamentalGroup_map_injective
    (h252 : Moise252) {Y T₀ T₁ : Set (EuclideanSpace ℝ (Fin 3))}
    (hY : IsToroidalShell Y T₀ T₁) :
    ∃ (S : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) (hSfin : S.faces.Finite),
      letI := hSfin.to_subtype
      IsCombinatorialManifold 2 S ∧ IsConnected S.space ∧ IsOrientable 2 S ∧
      IsTwoSided S.space ∧ Separates S.space T₀ T₁ ∧
      ∃ hSY : S.space ⊆ interior Y, ∀ x : S.space,
        Function.Injective (FundamentalGroup.map
          (⟨Set.inclusion hSY, continuous_inclusion hSY⟩ : C(S.space, interior Y)) x) := by
  obtain ⟨S, hSfin, hS, hSc, hSo, hSt, hSY, hsep, hmin⟩ :=
    hY.exists_connected_separating_surface_bettiOne_min
  let _ : Finite S.faces := hSfin.to_subtype
  have havoid : T₀ ∪ T₁ ⊆ (interior Y)ᶜ := fun _ hx => (hY.frontier_eq.symm.subset hx).2
  refine ⟨S, hSfin, hS, hSc, hSo, hSt, hsep, hSY, ?_⟩
  intro x
  exact hS.fundamentalGroup_map_injective_of_bettiOne_min h252 S (by simp) hSc
    isOpen_interior hSY hY.isConnected_left.isPreconnected hY.isConnected_right.isPreconnected
    (subset_union_left.trans havoid) (subset_union_right.trans havoid) hsep
    (fun P hPfin hP hPc _ hPsep => hmin P hPfin hP hPc hPsep) x

theorem
    IsToroidalShell.exists_non_simply_connected_separating_surface_fundamentalGroup_map_injective
    (h252 : Moise252) {Y T₀ T₁ : Set (EuclideanSpace ℝ (Fin 3))}
    (hY : IsToroidalShell Y T₀ T₁) :
    ∃ (S : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) (hSfin : S.faces.Finite),
      letI := hSfin.to_subtype
      IsCombinatorialManifold 2 S ∧ IsConnected S.space ∧ IsOrientable 2 S ∧
      IsTwoSided S.space ∧ Separates S.space T₀ T₁ ∧ ¬ SimplyConnectedSpace S.space ∧
      ∃ hSY : S.space ⊆ interior Y, ∀ x : S.space,
        Function.Injective (FundamentalGroup.map
          (⟨Set.inclusion hSY, continuous_inclusion hSY⟩ : C(S.space, interior Y)) x) := by
  obtain ⟨S, hSfin, hS, hSc, hSo, hSt, hsep, hSY, hi⟩ :=
    hY.exists_connected_separating_surface_fundamentalGroup_map_injective h252
  let _ : Finite S.faces := hSfin.to_subtype
  exact ⟨S, hSfin, hS, hSc, hSo, hSt, hsep,
    hY.not_simplyConnectedSpace_of_separates S hS hSY hsep, hSY, hi⟩

end DifferentialGeometry.Topology.PiecewiseLinear
