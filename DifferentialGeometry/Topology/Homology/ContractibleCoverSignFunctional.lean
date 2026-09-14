import DifferentialGeometry.Topology.Homology.RayComplementCoverEvaluation
import DifferentialGeometry.Topology.Homology.TwoPointReducedZero
import DifferentialGeometry.Topology.Homology.HurewiczTwoMultiplication

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace DifferentialGeometry.Topology

universe u

theorem integralZeroChainClass_eq_liftCycles {X : Type u} [TopologicalSpace X]
    (c : (integralSingularChains X).X 0) :
    integralZeroChainClass c =
      (((integralSingularChains X).liftCycles (integralChainHom 0 c) 0 ChainComplex.next_nat_zero
        (by rw [(integralSingularChains X).shape 0 0 (by simp), comp_zero])) ≫
        (integralSingularChains X).homologyπ 0) (ULift.up 1) := by
  let K := integralSingularChains X
  let z := K.liftCycles (integralChainHom 0 c) 0 ChainComplex.next_nat_zero
    (by rw [K.shape 0 0 (by simp), comp_zero])
  have hz : (K.sc 0).moduleCatCyclesIso.inv (integralZeroCycleInclusion c) = z (ULift.up 1) := by
    apply (ModuleCat.mono_iff_injective (K.iCycles 0)).mp inferInstance
    have hl := congrArg (fun f : (K.sc 0).moduleCatLeftHomologyData.K ⟶ K.X 0 =>
      f (integralZeroCycleInclusion c)) (K.sc 0).moduleCatCyclesIso_inv_iCycles
    have hr := congrArg (fun f : integralSingularCoefficients ⟶ K.X 0 => f (ULift.up 1))
      (K.liftCycles_i (integralChainHom 0 c) 0 ChainComplex.next_nat_zero
        (by rw [K.shape 0 0 (by simp), comp_zero]))
    change K.iCycles 0 ((K.sc 0).moduleCatCyclesIso.inv (integralZeroCycleInclusion c)) = c at hl
    change K.iCycles 0 (z (ULift.up 1)) = integralChainHom 0 c (ULift.up 1) at hr
    rw [hl, hr]
    change c = (integralChainHom 0 c).hom (ULift.up (1 : ℤ))
    rw [integralChainHom_hom, LinearMap.comp_apply]
    exact (LinearMap.toSpanSingleton_apply_one ℤ _ c).symm
  change (K.homologyπ 0) ((K.sc 0).moduleCatCyclesIso.inv (integralZeroCycleInclusion c)) =
    (K.homologyπ 0) (z (ULift.up 1))
  rw [hz]


def integralZeroSignFunctional {X : Type u} [TopologicalSpace X]
    (s : C(X, ULift.{u} Bool)) (b : Bool) : integralSingularHomology 0 X →ₗ[ℤ] ℤ :=
  (LinearMap.proj b : (Bool → ℤ) →ₗ[ℤ] ℤ).comp
    ((integralZeroTwoCoordinates Equiv.ulift).toLinearMap.comp
      (integralSingularHomologyMap 0 s))

theorem integralZeroSignFunctional_vertex {X : Type u} [TopologicalSpace X]
    (s : C(X, ULift.{u} Bool)) (b : Bool) (x : X) :
    integralZeroSignFunctional s b (integralZeroChainClass (integralVertexChain x)) =
      if (s x).down = b then 1 else 0 := by
  change integralZeroTwoCoordinates Equiv.ulift
    (integralSingularHomologyMap 0 s (integralZeroChainClass (integralVertexChain x))) b = _
  rw [integralZeroChainClass_map, integralVertexChain_map, integralZeroTwoCoordinates_vertex]
  rfl

variable {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
  (A B : Set X) [ContractibleSpace A] [ContractibleSpace B]
  (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
  (s : C(subspaceIntersection A B, ULift.{u} Bool)) (b : Bool)

def integralHomologyOneCoverSignFunctional : integralSingularHomology 1 X →ₗ[ℤ] ℤ :=
  (integralZeroSignFunctional s b).comp ((Submodule.subtype _).comp
    (integralHomologyOneContractibleCoverEquiv A B hA hB hcover).toLinearMap)

theorem integralHomologyOneCoverSignFunctional_apply
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X 1)
    (hz : z ≫ (integralSingularChains X).d 1 0 = 0)
    (zA : integralSingularCoefficients ⟶ (integralSingularChains A).X 1)
    (zB : integralSingularCoefficients ⟶ (integralSingularChains B).X 1)
    (hsplit : zA ≫ (integralSingularChainMap (singularSubspaceInclusion A)).f 1 +
      zB ≫ (integralSingularChainMap (singularSubspaceInclusion B)).f 1 = z)
    (x₀ x₁ : subspaceIntersection A B)
    (ha : integralChainHom 0 (integralVertexChain x₁ - integralVertexChain x₀) ≫
        (integralSingularChainMap (singularSubspaceInclusion (subspaceIntersection A B))).f 0 =
      zB ≫ (integralSingularChains B).d 1 0) :
    integralHomologyOneCoverSignFunctional A B hA hB hcover s b
      (integralHomologyClassOf 0 z hz) =
      (if (s x₁).down = b then 1 else 0) - (if (s x₀).down = b then 1 else 0) := by
  change integralZeroSignFunctional s b
    ((integralHomologyOneContractibleCoverEquiv A B hA hB hcover)
      (integralHomologyClassOf 0 z hz)).val = _
  unfold integralHomologyClassOf
  rw [integralHomologyOneContractibleCoverEquiv_liftCycles_apply A B hA hB hcover
    z hz zA zB hsplit (integralChainHom 0 (integralVertexChain x₁ - integralVertexChain x₀)) ha]
  rw [← integralZeroChainClass_eq_liftCycles, map_sub, map_sub,
    integralZeroSignFunctional_vertex, integralZeroSignFunctional_vertex]

end DifferentialGeometry.Topology
