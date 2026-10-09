/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.Algebra.PushoutHomologyGeneration
import DifferentialGeometry.Topology.Homology.SmallChains.Exactness
import DifferentialGeometry.Topology.Homology.Reduced
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Integral

open Set CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace DifferentialGeometry.Topology

theorem exists_integralFirstHomology_sum_of_open_cover
    {X : Type} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    [PathConnectedSpace (U ∩ V : Set X)] (a : integralSingularHomology 1 X) :
    ∃ u : integralSingularHomology 1 U, ∃ v : integralSingularHomology 1 V,
      integralSingularHomologyMap 1 (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) u +
        integralSingularHomologyMap 1 (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X)) v = a := by
  let T := TopCat.of X
  let R := integralSingularCoefficients
  let F := Homology.twoSetFamily T U V
  have hopen : ∀ i, IsOpen (F i) := by
    intro i
    cases i
    · exact hV
    · exact hU
  have hcov : ∀ x : T, ∃ i, x ∈ F i := by
    intro x
    have hx : x ∈ U ∪ V := hcover.symm ▸ mem_univ x
    rcases hx with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  let f := Homology.subspaceInclusion T (show U ∩ V ⊆ U from inter_subset_left)
  let _ : Mono f := (TopCat.mono_iff_injective _).mpr (inclusion_injective inter_subset_left)
  let _ : Mono (SSet.chainComplexMap (TopCat.toSSet.map f) R) := by
    unfold SSet.chainComplexMap
    infer_instance
  have hmono : Mono (SSet.homologyMap (TopCat.toSSet.map f) R 0) :=
    mono_of_mono_fac (Homology.singularHomologyZeroAugmentation_naturality R f)
  let e := Homology.smallChainHomologyIso T F R hopen hcov 1
  obtain ⟨u, v, huv⟩ :=
    DifferentialGeometry.HomologicalComplex.exists_homology_sum_of_pushout
      (Homology.subspaceSmallChainSquare T U V R) 1 0 rfl
      ((ModuleCat.mono_iff_injective _).mp hmono) (e.inv a)
  refine ⟨u, v, ?_⟩
  have h := congrArg e.hom huv
  have hea : e.hom (e.inv a) = a := e.toLinearEquiv.apply_symm_apply a
  rw [map_add, hea] at h
  change (_root_.HomologicalComplex.homologyMap
    (SSet.chainComplexMap (Homology.firstSubspaceToSmall T U V) R) 1 ≫
      _root_.HomologicalComplex.homologyMap (Homology.smallChainMap T F R) 1) u +
    (_root_.HomologicalComplex.homologyMap
      (SSet.chainComplexMap (Homology.secondSubspaceToSmall T U V) R) 1 ≫
        _root_.HomologicalComplex.homologyMap (Homology.smallChainMap T F R) 1) v = a at h
  rw [← _root_.HomologicalComplex.homologyMap_comp,
    ← _root_.HomologicalComplex.homologyMap_comp] at h
  have hfirst : SSet.chainComplexMap (Homology.firstSubspaceToSmall T U V) R ≫
      Homology.smallChainMap T F R =
      SSet.chainComplexMap (TopCat.toSSet.map
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))) R :=
    (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj R).map_comp
      (Homology.firstSubspaceToSmall T U V) (Homology.smallSingularSimplices T F).ι).symm
  have hsecond : SSet.chainComplexMap (Homology.secondSubspaceToSmall T U V) R ≫
      Homology.smallChainMap T F R =
      SSet.chainComplexMap (TopCat.toSSet.map
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X)))) R :=
    (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj R).map_comp
      (Homology.secondSubspaceToSmall T U V) (Homology.smallSingularSimplices T F).ι).symm
  rw [hfirst, hsecond] at h
  exact h

end DifferentialGeometry.Topology
