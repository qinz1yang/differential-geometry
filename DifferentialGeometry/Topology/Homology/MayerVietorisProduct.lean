/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.Algebra.PushoutHomologyProduct
import DifferentialGeometry.Topology.Homology.SmallChains.IntersectionPreimage
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Integral

open Set CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace DifferentialGeometry.Topology

theorem bijective_integralSingularHomologyMap_intersection
    {X : Type} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ) (n : ℕ)
    (hn : Subsingleton (integralSingularHomology n X))
    (hn' : Subsingleton (integralSingularHomology (n + 1) X)) :
    Function.Bijective (fun a : integralSingularHomology n (U ∩ V : Set X) =>
      (integralSingularHomologyMap n
        (⟨inclusion inter_subset_left, continuous_inclusion inter_subset_left⟩ :
          C((U ∩ V : Set X), U)) a,
      integralSingularHomologyMap n
        (⟨inclusion inter_subset_right, continuous_inclusion inter_subset_right⟩ :
          C((U ∩ V : Set X), V)) a)) := by
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
  have hsmall (k : ℕ) (hk : Subsingleton (integralSingularHomology k X)) :
      Subsingleton (((Homology.smallSingularSimplices T F : SSet).chainComplex R).homology k) := by
    let e := Homology.smallChainHomologyIso T F R hopen hcov k
    refine ⟨fun a b => (ModuleCat.mono_iff_injective e.hom).mp inferInstance ?_⟩
    exact hk.elim _ _
  let _ : Mono (Homology.subspaceInclusion T
      (show U ∩ V ⊆ U from inter_subset_left)) :=
    (TopCat.mono_iff_injective _).mpr (inclusion_injective inter_subset_left)
  let _ : Mono (SSet.chainComplexMap (TopCat.toSSet.map
      (Homology.subspaceInclusion T (show U ∩ V ⊆ U from inter_subset_left))) R) := by
    unfold SSet.chainComplexMap
    infer_instance
  exact DifferentialGeometry.HomologicalComplex.bijective_homologyMap_pair_of_pushout
    (Homology.subspaceSmallChainSquare T U V R) (n + 1) n rfl (hsmall (n + 1) hn') (hsmall n hn)

end DifferentialGeometry.Topology
