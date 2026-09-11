import DifferentialGeometry.Topology.Homology.ReducedZero



noncomputable section

open ContinuousMap Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] [TotallyDisconnectedSpace X]


def integralZeroTwoCoordinates (e : X ≃ Bool) :
    integralSingularHomology 0 X ≃ₗ[ℤ] (Bool → ℤ) :=
  integralTotallyDisconnectedZeroEquiv.trans
    ((Finsupp.domLCongr e).trans (Finsupp.linearEquivFunOnFinite ℤ ℤ Bool))


theorem integralZeroTwoCoordinates_vertex (e : X ≃ Bool) (x : X) (b : Bool) :
    integralZeroTwoCoordinates e (integralZeroChainClass (integralVertexChain x)) b =
      if e x = b then 1 else 0 := by
  change (Finsupp.domLCongr (R := ℤ) (M := ℤ) e
    (integralTotallyDisconnectedZeroEquiv (integralZeroChainClass (integralVertexChain x)))) b = _
  rw [integralTotallyDisconnectedZeroEquiv_vertex, Finsupp.domLCongr_single]
  exact Finsupp.single_apply


theorem integralZeroAugmentation_twoCoordinates (e : X ≃ Bool)
    (a : integralSingularHomology 0 X) :
    integralZeroAugmentation a = integralZeroTwoCoordinates e a false +
      integralZeroTwoCoordinates e a true := by
  let s : (Bool → ℤ) →ₗ[ℤ] ℤ := (LinearMap.proj false : (Bool → ℤ) →ₗ[ℤ] ℤ) + (LinearMap.proj true : (Bool → ℤ) →ₗ[ℤ] ℤ)
  have h : integralZeroAugmentation.comp integralZeroChainClass =
      (s.comp (integralZeroTwoCoordinates e).toLinearMap).comp integralZeroChainClass := by
    apply (integralSingularChainBasis 0 X).ext
    intro σ
    simp only [LinearMap.comp_apply, integralSingularChainBasis_apply]
    rw [integralSimplexChain_zero_vertex, integralZeroAugmentation_vertex]
    change 1 = integralZeroTwoCoordinates e
      (integralZeroChainClass (integralVertexChain (TopCat.toSSetObj₀Equiv σ))) false +
        integralZeroTwoCoordinates e
          (integralZeroChainClass (integralVertexChain (TopCat.toSSetObj₀Equiv σ))) true
    rw [integralZeroTwoCoordinates_vertex, integralZeroTwoCoordinates_vertex]
    cases e (TopCat.toSSetObj₀Equiv σ) <;> norm_num
  obtain ⟨c, rfl⟩ := integralZeroChainClass_surjective a
  exact LinearMap.congr_fun h c


def twoCoordinateSumKernelEquiv :
    LinearMap.ker ((LinearMap.proj false : (Bool → ℤ) →ₗ[ℤ] ℤ) + (LinearMap.proj true : (Bool → ℤ) →ₗ[ℤ] ℤ) : (Bool → ℤ) →ₗ[ℤ] ℤ) ≃ₗ[ℤ] ℤ where
  toFun a := a.val true
  invFun z := ⟨fun b => if b then z else -z, by change -z + z = 0; exact neg_add_cancel z⟩
  left_inv a := by
    apply Subtype.ext
    funext b
    have h : a.val false + a.val true = 0 := a.property
    cases b
    · change -a.val true = a.val false
      omega
    · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl



def integralTwoPointReducedZeroEquiv (e : X ≃ Bool) :
    integralReducedHomologyZero X ≃ₗ[ℤ] ℤ := by
  let s : (Bool → ℤ) →ₗ[ℤ] ℤ := (LinearMap.proj false : (Bool → ℤ) →ₗ[ℤ] ℤ) + (LinearMap.proj true : (Bool → ℤ) →ₗ[ℤ] ℤ)
  have h : integralReducedHomologyZero X =
      (LinearMap.ker s).comap (integralZeroTwoCoordinates e).toLinearMap := by
    ext a
    change integralZeroAugmentation a = 0 ↔
      integralZeroTwoCoordinates e a false + integralZeroTwoCoordinates e a true = 0
    rw [integralZeroAugmentation_twoCoordinates e]
  exact ((LinearEquiv.ofEq _ _ h).trans
    ((integralZeroTwoCoordinates e).ofSubmodule' (LinearMap.ker s))).trans
      twoCoordinateSumKernelEquiv

end DifferentialGeometry.Topology
