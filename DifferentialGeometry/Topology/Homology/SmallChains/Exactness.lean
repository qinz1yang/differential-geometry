/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.Algebra.PushoutHomology
import DifferentialGeometry.Topology.Homology.SmallChains.QuasiIso
import DifferentialGeometry.Topology.Homology.SmallChains.Union

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace DifferentialGeometry.Homology

universe u

variable (X : TopCat.{u}) (s t : Set X) {k : Type u} [Ring k] (R : ModuleCat.{u} k)

theorem exists_intersection_preimage_of_small_map_eq_zero (n : ℕ)
    (z : ((TopCat.toSSet.obj (TopCat.of s)).chainComplex R).homology n)
    (hz : _root_.HomologicalComplex.homologyMap
      (SSet.chainComplexMap (firstSubspaceToSmall X s t) R) n z = 0) :
    ∃ y : ((TopCat.toSSet.obj (TopCat.of (s ∩ t : Set X))).chainComplex R).homology n,
      _root_.HomologicalComplex.homologyMap (SSet.chainComplexMap
        (TopCat.toSSet.map (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left))) R) n y
            = z ∧
      _root_.HomologicalComplex.homologyMap (SSet.chainComplexMap
        (TopCat.toSSet.map (subspaceInclusion X (show s ∩ t ⊆ t from Set.inter_subset_right))) R) n
            y = 0 := by
  let _ : Mono (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left)) :=
    (TopCat.mono_iff_injective _).mpr (Set.inclusion_injective Set.inter_subset_left)
  let _ : Mono (SSet.chainComplexMap (TopCat.toSSet.map
      (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left))) R) := by
    unfold SSet.chainComplexMap
    infer_instance
  exact DifferentialGeometry.HomologicalComplex.exists_homology_preimage_of_pushout
    (subspaceSmallChainSquare X s t R) n z hz

theorem exists_intersection_preimage_of_inclusion_map_eq_zero
    (hs : IsOpen s) (ht : IsOpen t) (hcover : s ∪ t = Set.univ) (n : ℕ)
    (z : (((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).obj (TopCat.of s)))
    (hz : (((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).map
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X)))) z = 0) :
    ∃ y : (((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).obj (TopCat.of (s ∩ t : Set X))),
      (((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).map
        (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left))) y = z ∧
      (((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).map
        (subspaceInclusion X (show s ∩ t ⊆ t from Set.inter_subset_right))) y = 0 := by
  have hopen : ∀ b, IsOpen (twoSetFamily X s t b) := by
    intro b
    cases b
    · exact ht
    · exact hs
  have hcov : ∀ x : X, ∃ b, x ∈ twoSetFamily X s t b := by
    intro x
    have hx : x ∈ s ∪ t := hcover.symm ▸ Set.mem_univ x
    rcases hx with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  let e := smallChainHomologyIso X (twoSetFamily X s t) R hopen hcov n
  apply exists_intersection_preimage_of_small_map_eq_zero X s t R n z
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  rw [map_zero]
  change (_root_.HomologicalComplex.homologyMap
    (SSet.chainComplexMap (firstSubspaceToSmall X s t) R) n ≫
      _root_.HomologicalComplex.homologyMap (smallChainMap X (twoSetFamily X s t) R) n) z = 0
  rw [← _root_.HomologicalComplex.homologyMap_comp]
  have hcomp : SSet.chainComplexMap (firstSubspaceToSmall X s t) R ≫
      smallChainMap X (twoSetFamily X s t) R =
      SSet.chainComplexMap (TopCat.toSSet.map
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X)))) R := by
    exact (((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).map_comp
      (firstSubspaceToSmall X s t) (smallSingularSimplices X (twoSetFamily X s t)).ι).symm
  rw [hcomp]
  exact hz

end DifferentialGeometry.Homology
