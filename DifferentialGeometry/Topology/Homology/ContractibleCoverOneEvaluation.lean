import DifferentialGeometry.Topology.Homology.ContractibleCoverOne
import DifferentialGeometry.Topology.Homology.ContractibleCoverChainEvaluation
import DifferentialGeometry.Topology.Homology.RelativeFunctoriality
import DifferentialGeometry.Topology.Homology.TwoSetSmallChains
import DifferentialGeometry.Topology.Homology.SphereHomologyShift
import DifferentialGeometry.Topology.Homology.SphereHomologyOne

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralRelativeConnecting_zero_liftCycles_apply (A : Set X)
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X 1)
    (hz : (z ≫ (cokernel.π (integralSingularChainMap (singularSubspaceInclusion A))).f 1) ≫
        (integralRelativeChains A).d 1 0 = 0)
    (a : integralSingularCoefficients ⟶ (integralSingularChains (A : Set X)).X 0)
    (ha : a ≫ (integralSingularChainMap (singularSubspaceInclusion A)).f 0 =
      z ≫ (integralSingularChains X).d 1 0) :
    integralRelativeConnecting 0 A
      ((((integralRelativeChains A).liftCycles
          (z ≫ (cokernel.π (integralSingularChainMap (singularSubspaceInclusion A))).f 1) 0
          ((ComplexShape.down ℕ).next_eq' (by simp)) hz) ≫
        (integralRelativeChains A).homologyπ 1) (ULift.up 1)) =
      (((integralSingularChains (A : Set X)).liftCycles a 0 ChainComplex.next_nat_zero
          (by rw [(integralSingularChains (A : Set X)).shape 0 0 (by simp), comp_zero])) ≫
        (integralSingularChains (A : Set X)).homologyπ 0) (ULift.up 1) := by
  have h := (integralRelativeChainSequence_shortExact A).δ_eq 1 0 (by simp)
    (z ≫ (cokernel.π (integralSingularChainMap (singularSubspaceInclusion A))).f 1) hz
    z rfl a ha 0 ChainComplex.next_nat_zero
  exact congrArg (fun f => f (ULift.up 1)) h

private theorem integralRelativeConnectingZeroKernelEquiv_val (A : Set X) [ContractibleSpace X]
    (x : integralRelativeHomology 1 A) :
    (integralRelativeConnectingZeroKernelEquiv A x).val = integralRelativeConnecting 0 A x :=
  rfl

theorem integralHomologyOneContractibleCoverEquiv_liftCycles_apply [PathConnectedSpace X]
    (A B : Set X) [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X 1)
    (hz : z ≫ (integralSingularChains X).d 1 0 = 0)
    (zA : integralSingularCoefficients ⟶ (integralSingularChains A).X 1)
    (zB : integralSingularCoefficients ⟶ (integralSingularChains B).X 1)
    (hsplit : zA ≫ (integralSingularChainMap (singularSubspaceInclusion A)).f 1 +
      zB ≫ (integralSingularChainMap (singularSubspaceInclusion B)).f 1 = z)
    (a : integralSingularCoefficients ⟶
      (integralSingularChains (subspaceIntersection A B)).X 0)
    (ha : a ≫ (integralSingularChainMap
        (singularSubspaceInclusion (subspaceIntersection A B))).f 0 =
      zB ≫ (integralSingularChains B).d 1 0) :
    integralHomologyOneContractibleCoverEquiv A B hA hB hcover
      (((integralSingularChains X).liftCycles z 0 ((ComplexShape.down ℕ).next_eq' (by simp)) hz ≫
        (integralSingularChains X).homologyπ 1) (ULift.up 1)) =
      (((integralSingularChains (subspaceIntersection A B)).liftCycles a 0
        ChainComplex.next_nat_zero (by rw [(integralSingularChains
          (subspaceIntersection A B)).shape 0 0 (by simp), comp_zero])) ≫
        (integralSingularChains (subspaceIntersection A B)).homologyπ 0) (ULift.up 1) := by
  let πA : integralSingularChains X ⟶ integralRelativeChains A :=
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion A))
  let πI : integralSingularChains B ⟶ integralRelativeChains (subspaceIntersection A B) :=
    cokernel.π (integralSingularChainMap (singularSubspaceInclusion (subspaceIntersection A B)))
  let ι : integralRelativeChains (subspaceIntersection A B) ⟶ integralRelativeChains A :=
    integralRelativeChainMap (singularSubspaceInclusion B) (subspaceIntersection_mapsTo A B)
  have hzA : (z ≫ πA.f 1) ≫ (integralRelativeChains A).d 1 0 = 0 := by
    rw [Category.assoc, HomologicalComplex.Hom.comm, ← Category.assoc, hz, zero_comp]
  have hcondA : (integralSingularChainMap (singularSubspaceInclusion A)).f 1 ≫ πA.f 1 = 0 := by
    have h : ((integralSingularChainMap (singularSubspaceInclusion A) ≫
        cokernel.π (integralSingularChainMap (singularSubspaceInclusion A))).f 1) = 0 := by
      rw [cokernel.condition (integralSingularChainMap (singularSubspaceInclusion A)),
        HomologicalComplex.zero_f]
    rw [HomologicalComplex.comp_f] at h
    exact h
  have hzI : (zB ≫ πI.f 1) ≫
      (integralRelativeChains (subspaceIntersection A B)).d 1 0 = 0 := by
    have hcondI : (integralSingularChainMap
        (singularSubspaceInclusion (subspaceIntersection A B))).f 0 ≫ πI.f 0 = 0 := by
      have h : ((integralSingularChainMap
          (singularSubspaceInclusion (subspaceIntersection A B)) ≫
          cokernel.π (integralSingularChainMap
            (singularSubspaceInclusion (subspaceIntersection A B)))).f 0) = 0 := by
        rw [cokernel.condition (integralSingularChainMap
            (singularSubspaceInclusion (subspaceIntersection A B))), HomologicalComplex.zero_f]
      rw [HomologicalComplex.comp_f] at h
      exact h
    rw [Category.assoc, HomologicalComplex.Hom.comm, ← Category.assoc, ← ha, Category.assoc,
      hcondI, comp_zero]
  have hchain : (zB ≫ πI.f 1) ≫ ι.f 1 = z ≫ πA.f 1 := by
    have hπ : πI ≫ ι = (integralSingularChainMap (singularSubspaceInclusion B)) ≫ πA :=
      integralRelativeChainMap_π (singularSubspaceInclusion B) (subspaceIntersection_mapsTo A B)
    have hπf : πI.f 1 ≫ ι.f 1 =
        (integralSingularChainMap (singularSubspaceInclusion B)).f 1 ≫ πA.f 1 := by
      have h : (πI ≫ ι).f 1 =
          ((integralSingularChainMap (singularSubspaceInclusion B)) ≫ πA).f 1 := by
        rw [hπ]
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at h
      exact h
    have hsplit' : zB ≫ (integralSingularChainMap (singularSubspaceInclusion B)).f 1 =
        z - zA ≫ (integralSingularChainMap (singularSubspaceInclusion A)).f 1 := by
      rw [← hsplit]
      abel
    rw [Category.assoc, hπf, ← Category.assoc, hsplit', Preadditive.sub_comp, Category.assoc,
      hcondA, comp_zero, sub_zero]
  have h1 : (integralAbsoluteToRelativeOneIsoOfContractible A).toLinearEquiv
      (((integralSingularChains X).liftCycles z 0 ((ComplexShape.down ℕ).next_eq' (by simp)) hz ≫
        (integralSingularChains X).homologyπ 1) (ULift.up 1)) =
      (((integralRelativeChains A).liftCycles (z ≫ πA.f 1) 0
        ((ComplexShape.down ℕ).next_eq' (by simp)) hzA ≫
        (integralRelativeChains A).homologyπ 1) (ULift.up 1)) :=
    chainComplex_homologyMap_liftCycles_apply πA 0 z hz hzA
  have h2 : (integralRelativeOpenExcisionIso 1 A B hA hB hcover).symm.toLinearEquiv
      (((integralRelativeChains A).liftCycles (z ≫ πA.f 1) 0
        ((ComplexShape.down ℕ).next_eq' (by simp)) hzA ≫
        (integralRelativeChains A).homologyπ 1) (ULift.up 1)) =
      (((integralRelativeChains (subspaceIntersection A B)).liftCycles (zB ≫ πI.f 1) 0
        ((ComplexShape.down ℕ).next_eq' (by simp)) hzI ≫
        (integralRelativeChains (subspaceIntersection A B)).homologyπ 1) (ULift.up 1)) := by
    rw [← Iso.toLinearEquiv_symm]
    have hzι : ((zB ≫ πI.f 1) ≫ ι.f 1) ≫ (integralRelativeChains A).d 1 0 = 0 := by
      rw [hchain, Category.assoc, HomologicalComplex.Hom.comm, ← Category.assoc, hz, zero_comp]
    have hstep : (integralRelativeOpenExcisionIso 1 A B hA hB hcover).toLinearEquiv
        (((integralRelativeChains (subspaceIntersection A B)).liftCycles (zB ≫ πI.f 1) 0
          ((ComplexShape.down ℕ).next_eq' (by simp)) hzI ≫
          (integralRelativeChains (subspaceIntersection A B)).homologyπ 1) (ULift.up 1)) =
        (((integralRelativeChains A).liftCycles (z ≫ πA.f 1) 0
          ((ComplexShape.down ℕ).next_eq' (by simp)) hzA ≫
          (integralRelativeChains A).homologyπ 1) (ULift.up 1)) := by
      refine (chainComplex_homologyMap_liftCycles_apply ι 0 (zB ≫ πI.f 1) hzI hzι).trans ?_
      exact congrArg (fun k : integralSingularCoefficients ⟶ (integralRelativeChains A).homology 1 =>
        k (ULift.up 1)) (chainComplex_liftCycles_homologyπ_congr 0
          ((zB ≫ πI.f 1) ≫ ι.f 1) (z ≫ πA.f 1) hzι hzA hchain)
    rw [← hstep, LinearEquiv.symm_apply_apply]
  have h3 : integralRelativeConnecting 0 (subspaceIntersection A B)
      ((((integralRelativeChains (subspaceIntersection A B)).liftCycles (zB ≫ πI.f 1) 0
        ((ComplexShape.down ℕ).next_eq' (by simp)) hzI) ≫
        (integralRelativeChains (subspaceIntersection A B)).homologyπ 1) (ULift.up 1)) =
      (((integralSingularChains (subspaceIntersection A B)).liftCycles a 0
        ChainComplex.next_nat_zero (by rw [(integralSingularChains
          (subspaceIntersection A B)).shape 0 0 (by simp), comp_zero])) ≫
        (integralSingularChains (subspaceIntersection A B)).homologyπ 0) (ULift.up 1) :=
    integralRelativeConnecting_zero_liftCycles_apply (A := subspaceIntersection A B) zB hzI a ha
  rw [integralHomologyOneContractibleCoverEquiv]
  simp only [LinearEquiv.trans_apply]
  rw [h1, h2]
  rw [integralRelativeConnectingZeroKernelEquiv_val]
  exact h3

theorem integralHomologyOneContractibleCoverEquiv_liftCycles_apply_of_subdivision
    [PathConnectedSpace X] (k : ℕ)
    (A B : Set X) [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X 1)
    (hz : z ≫ (integralSingularChains X).d 1 0 = 0)
    (zA : integralSingularCoefficients ⟶ (integralSingularChains A).X 1)
    (zB : integralSingularCoefficients ⟶ (integralSingularChains B).X 1)
    (hsplit : zA ≫ (integralSingularChainMap (singularSubspaceInclusion A)).f 1 +
      zB ≫ (integralSingularChainMap (singularSubspaceInclusion B)).f 1 =
        integralSingularSubdivisionIterateChain 0 k z)
    (a : integralSingularCoefficients ⟶
      (integralSingularChains (subspaceIntersection A B)).X 0)
    (ha : a ≫ (integralSingularChainMap
        (singularSubspaceInclusion (subspaceIntersection A B))).f 0 =
      zB ≫ (integralSingularChains B).d 1 0) :
    integralHomologyOneContractibleCoverEquiv A B hA hB hcover
      (((integralSingularChains X).liftCycles z 0 ((ComplexShape.down ℕ).next_eq' (by simp)) hz ≫
        (integralSingularChains X).homologyπ 1) (ULift.up 1)) =
      (((integralSingularChains (subspaceIntersection A B)).liftCycles a 0
        ChainComplex.next_nat_zero (by rw [(integralSingularChains
          (subspaceIntersection A B)).shape 0 0 (by simp), comp_zero])) ≫
        (integralSingularChains (subspaceIntersection A B)).homologyπ 0) (ULift.up 1) := by
  rw [← congrArg (fun f => f (ULift.up 1))
    (integralSingularSubdivisionIterate_liftCycles_homologyπ 0 k z hz
      (integralSingularSubdivisionIterate_cycle 0 k z hz))]
  exact integralHomologyOneContractibleCoverEquiv_liftCycles_apply A B hA hB hcover
    (integralSingularSubdivisionIterateChain 0 k z)
    (integralSingularSubdivisionIterate_cycle 0 k z hz) zA zB hsplit a ha

attribute [local instance] spherePuncture_contractible

theorem integralSphereHomologyOneKernelEquiv_liftCycles_apply {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [PathConnectedSpace (Metric.sphere (0 : E) 1)]
    (v : Metric.sphere (0 : E) 1)
    (z : integralSingularCoefficients ⟶
      (integralSingularChains (Metric.sphere (0 : E) 1)).X 1)
    (hz : z ≫ (integralSingularChains (Metric.sphere (0 : E) 1)).d 1 0 = 0)
    (zA : integralSingularCoefficients ⟶
      (integralSingularChains ({v}ᶜ : Set (Metric.sphere (0 : E) 1))).X 1)
    (zB : integralSingularCoefficients ⟶
      (integralSingularChains ({-v}ᶜ : Set (Metric.sphere (0 : E) 1))).X 1)
    (hsplit : zA ≫ (integralSingularChainMap
        (singularSubspaceInclusion ({v}ᶜ : Set (Metric.sphere (0 : E) 1)))).f 1 +
      zB ≫ (integralSingularChainMap
        (singularSubspaceInclusion ({-v}ᶜ : Set (Metric.sphere (0 : E) 1)))).f 1 = z)
    (a : integralSingularCoefficients ⟶
      (integralSingularChains (subspaceIntersection
        ({v}ᶜ : Set (Metric.sphere (0 : E) 1))
        ({-v}ᶜ : Set (Metric.sphere (0 : E) 1)))).X 0)
    (ha : a ≫ (integralSingularChainMap (singularSubspaceInclusion (subspaceIntersection
        ({v}ᶜ : Set (Metric.sphere (0 : E) 1))
        ({-v}ᶜ : Set (Metric.sphere (0 : E) 1))))).f 0 =
      zB ≫ (integralSingularChains ({-v}ᶜ : Set (Metric.sphere (0 : E) 1))).d 1 0) :
    integralSphereHomologyOneKernelEquiv v
      (((integralSingularChains (Metric.sphere (0 : E) 1)).liftCycles z 0
        ((ComplexShape.down ℕ).next_eq' (by simp)) hz ≫
        (integralSingularChains (Metric.sphere (0 : E) 1)).homologyπ 1) (ULift.up 1)) =
      (((integralSingularChains (subspaceIntersection
        ({v}ᶜ : Set (Metric.sphere (0 : E) 1))
        ({-v}ᶜ : Set (Metric.sphere (0 : E) 1)))).liftCycles a 0
        ChainComplex.next_nat_zero (by rw [(integralSingularChains (subspaceIntersection
          ({v}ᶜ : Set (Metric.sphere (0 : E) 1))
          ({-v}ᶜ : Set (Metric.sphere (0 : E) 1)))).shape 0 0 (by simp), comp_zero])) ≫
        (integralSingularChains (subspaceIntersection
          ({v}ᶜ : Set (Metric.sphere (0 : E) 1))
          ({-v}ᶜ : Set (Metric.sphere (0 : E) 1)))).homologyπ 0) (ULift.up 1) := by
  exact integralHomologyOneContractibleCoverEquiv_liftCycles_apply
    ({v}ᶜ : Set (Metric.sphere (0 : E) 1)) ({-v}ᶜ : Set (Metric.sphere (0 : E) 1))
    isOpen_compl_singleton isOpen_compl_singleton (spherePunctures_cover v) z hz zA zB hsplit a ha

theorem integralSphereHomologyOneReducedEquiv_apply_val {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [PathConnectedSpace (Metric.sphere (0 : E) 1)]
    (v : Metric.sphere (0 : E) 1)
    (y : integralSingularHomology 1 (Metric.sphere (0 : E) 1)) :
    (integralSphereHomologyOneReducedEquiv v y).val =
      integralSingularHomologyMap 0 (spherePoleIntersectionHomotopyEquiv v).toFun
        (integralSphereHomologyOneKernelEquiv v y).val :=
  rfl

theorem integralSphereHomologyOneReducedEquiv_liftCycles_apply {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [PathConnectedSpace (Metric.sphere (0 : E) 1)]
    (v : Metric.sphere (0 : E) 1)
    (z : integralSingularCoefficients ⟶
      (integralSingularChains (Metric.sphere (0 : E) 1)).X 1)
    (hz : z ≫ (integralSingularChains (Metric.sphere (0 : E) 1)).d 1 0 = 0)
    (zA : integralSingularCoefficients ⟶
      (integralSingularChains ({v}ᶜ : Set (Metric.sphere (0 : E) 1))).X 1)
    (zB : integralSingularCoefficients ⟶
      (integralSingularChains ({-v}ᶜ : Set (Metric.sphere (0 : E) 1))).X 1)
    (hsplit : zA ≫ (integralSingularChainMap
        (singularSubspaceInclusion ({v}ᶜ : Set (Metric.sphere (0 : E) 1)))).f 1 +
      zB ≫ (integralSingularChainMap
        (singularSubspaceInclusion ({-v}ᶜ : Set (Metric.sphere (0 : E) 1)))).f 1 = z)
    (a : integralSingularCoefficients ⟶
      (integralSingularChains (subspaceIntersection
        ({v}ᶜ : Set (Metric.sphere (0 : E) 1))
        ({-v}ᶜ : Set (Metric.sphere (0 : E) 1)))).X 0)
    (ha : a ≫ (integralSingularChainMap (singularSubspaceInclusion (subspaceIntersection
        ({v}ᶜ : Set (Metric.sphere (0 : E) 1))
        ({-v}ᶜ : Set (Metric.sphere (0 : E) 1))))).f 0 =
      zB ≫ (integralSingularChains ({-v}ᶜ : Set (Metric.sphere (0 : E) 1))).d 1 0) :
    (integralSphereHomologyOneReducedEquiv v
      (((integralSingularChains (Metric.sphere (0 : E) 1)).liftCycles z 0
        ((ComplexShape.down ℕ).next_eq' (by simp)) hz ≫
        (integralSingularChains (Metric.sphere (0 : E) 1)).homologyπ 1) (ULift.up 1))).val =
      integralSingularHomologyMap 0 (spherePoleIntersectionHomotopyEquiv v).toFun
        ((((integralSingularChains (subspaceIntersection
          ({v}ᶜ : Set (Metric.sphere (0 : E) 1))
          ({-v}ᶜ : Set (Metric.sphere (0 : E) 1)))).liftCycles a 0
          ChainComplex.next_nat_zero (by rw [(integralSingularChains (subspaceIntersection
            ({v}ᶜ : Set (Metric.sphere (0 : E) 1))
            ({-v}ᶜ : Set (Metric.sphere (0 : E) 1)))).shape 0 0 (by simp), comp_zero])) ≫
          (integralSingularChains (subspaceIntersection
            ({v}ᶜ : Set (Metric.sphere (0 : E) 1))
            ({-v}ᶜ : Set (Metric.sphere (0 : E) 1)))).homologyπ 0) (ULift.up 1)) := by
  rw [integralSphereHomologyOneReducedEquiv_apply_val]
  rw [integralSphereHomologyOneKernelEquiv_liftCycles_apply v z hz zA zB hsplit a ha]

end DifferentialGeometry.Topology
