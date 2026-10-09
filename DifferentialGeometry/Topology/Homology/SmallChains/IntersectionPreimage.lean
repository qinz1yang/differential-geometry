/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.Algebra.PushoutHomologyDifference
import DifferentialGeometry.Topology.Homology.SmallChains.Exactness

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace DifferentialGeometry.Homology

universe u

variable (X : TopCat.{u}) (s t : Set X) {k : Type u} [Ring k] (R : ModuleCat.{u} k)

theorem exists_intersection_preimage_of_small_maps_eq (n : ℕ)
    (z : ((TopCat.toSSet.obj (TopCat.of s)).chainComplex R).homology n)
    (w : ((TopCat.toSSet.obj (TopCat.of t)).chainComplex R).homology n)
    (hzw : _root_.HomologicalComplex.homologyMap
      (SSet.chainComplexMap (firstSubspaceToSmall X s t) R) n z =
        _root_.HomologicalComplex.homologyMap
          (SSet.chainComplexMap (secondSubspaceToSmall X s t) R) n w) :
    ∃ y : ((TopCat.toSSet.obj (TopCat.of (s ∩ t : Set X))).chainComplex R).homology n,
      _root_.HomologicalComplex.homologyMap (SSet.chainComplexMap
        (TopCat.toSSet.map (subspaceInclusion X
          (show s ∩ t ⊆ s from Set.inter_subset_left))) R) n y = z ∧
      _root_.HomologicalComplex.homologyMap (SSet.chainComplexMap
        (TopCat.toSSet.map (subspaceInclusion X
          (show s ∩ t ⊆ t from Set.inter_subset_right))) R) n y = w := by
  let _ : Mono (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left)) :=
    (TopCat.mono_iff_injective _).mpr (Set.inclusion_injective Set.inter_subset_left)
  let _ : Mono (SSet.chainComplexMap (TopCat.toSSet.map
      (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left))) R) := by
    unfold SSet.chainComplexMap
    infer_instance
  exact DifferentialGeometry.HomologicalComplex.exists_homology_preimage_of_pushout_eq
    (subspaceSmallChainSquare X s t R) n z w hzw

theorem exists_intersection_preimage_of_inclusion_maps_eq
    (hs : IsOpen s) (ht : IsOpen t) (hcover : s ∪ t = Set.univ) (n : ℕ)
    (z : (((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).obj (TopCat.of s)))
    (w : (((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).obj (TopCat.of t)))
    (hzw : (((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).map
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X)))) z =
      (((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).map
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(t, X)))) w) :
    ∃ y : (((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).obj
        (TopCat.of (s ∩ t : Set X))),
      (((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).map
        (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left))) y = z ∧
      (((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).map
        (subspaceInclusion X (show s ∩ t ⊆ t from Set.inter_subset_right))) y = w := by
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
  apply exists_intersection_preimage_of_small_maps_eq X s t R n z w
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  change (_root_.HomologicalComplex.homologyMap
    (SSet.chainComplexMap (firstSubspaceToSmall X s t) R) n ≫
      _root_.HomologicalComplex.homologyMap (smallChainMap X (twoSetFamily X s t) R) n) z =
    (_root_.HomologicalComplex.homologyMap
      (SSet.chainComplexMap (secondSubspaceToSmall X s t) R) n ≫
        _root_.HomologicalComplex.homologyMap (smallChainMap X (twoSetFamily X s t) R) n) w
  rw [← _root_.HomologicalComplex.homologyMap_comp,
    ← _root_.HomologicalComplex.homologyMap_comp]
  have hfirst : SSet.chainComplexMap (firstSubspaceToSmall X s t) R ≫
      smallChainMap X (twoSetFamily X s t) R =
      SSet.chainComplexMap (TopCat.toSSet.map
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X)))) R :=
    (((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).map_comp
      (firstSubspaceToSmall X s t) (smallSingularSimplices X (twoSetFamily X s t)).ι).symm
  have hsecond : SSet.chainComplexMap (secondSubspaceToSmall X s t) R ≫
      smallChainMap X (twoSetFamily X s t) R =
      SSet.chainComplexMap (TopCat.toSSet.map
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(t, X)))) R :=
    (((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).map_comp
      (secondSubspaceToSmall X s t) (smallSingularSimplices X (twoSetFamily X s t)).ι).symm
  rw [hfirst, hsecond]
  exact hzw

end DifferentialGeometry.Homology
