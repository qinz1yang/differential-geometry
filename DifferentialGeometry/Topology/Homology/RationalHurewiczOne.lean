import DifferentialGeometry.Topology.Algebra.Group.FinitelyGeneratedFundamentalGroupRationalHurewicz
import DifferentialGeometry.Topology.Homology.HurewiczOneAbelianization
import DifferentialGeometry.Topology.Homology.SphereGenerator
import DifferentialGeometry.Topology.Homology.UniversalCoefficientsOneLinearEquiv
import DifferentialGeometry.Topology.VanKampen.FiniteConnectedSumFreeProduct
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Module
open scoped Topology TensorProduct

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X]

def rationalSingularHomologyOneCoefficientChange (X : TopCat.{0}) : Prop :=
  Nonempty (ℚ ⊗[ℤ] integralSingularHomology 1 X ≃ₗ[ℚ] RationalSingularHomologyOne X)

theorem subsingleton_rationalSingularHomologyOne_punit :
    Subsingleton (RationalSingularHomologyOne (TopCat.of PUnit.{1})) :=
  ModuleCat.subsingleton_of_isZero
    (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat.{0} ℚ) 1
      (ModuleCat.of ℚ ℚ) (TopCat.of PUnit.{1}) (by norm_num))

theorem subsingleton_integralSingularHomology_one_punit :
    Subsingleton (integralSingularHomology 1 (TopCat.of PUnit.{1})) :=
  ModuleCat.subsingleton_of_isZero
    (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat.{0} ℤ) 1
      integralSingularCoefficients (TopCat.of PUnit.{1}) (by norm_num))

theorem rationalSingularHomologyOneCoefficientChange_of_totallyDisconnectedSpace
    (X : TopCat.{0}) [TotallyDisconnectedSpace X] :
    rationalSingularHomologyOneCoefficientChange X := by
  refine ⟨?_⟩
  haveI : Subsingleton (integralSingularHomology 1 X) :=
    ModuleCat.subsingleton_of_isZero
      (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat.{0} ℤ) 1
        integralSingularCoefficients X (by norm_num))
  haveI : Subsingleton (RationalSingularHomologyOne X) :=
    ModuleCat.subsingleton_of_isZero
      (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat.{0} ℚ) 1
        (ModuleCat.of ℚ ℚ) X (by norm_num))
  exact LinearEquiv.ofSubsingleton _ _

theorem rationalSingularHomologyOneCoefficientChange_punit :
    rationalSingularHomologyOneCoefficientChange (TopCat.of PUnit.{1}) :=
  rationalSingularHomologyOneCoefficientChange_of_totallyDisconnectedSpace (TopCat.of PUnit.{1})

theorem integralPathLoopChainMap_boundary (x : X) [PathConnectedSpace X] :
    ((integralSingularChains X).d 1 0).hom.comp (integralPathLoopChainMap x) = 0 := by
  apply (integralSingularChainBasis 1 X).ext
  intro σ
  rw [LinearMap.comp_apply, integralSingularChainBasis_apply, integralPathLoopChainMap_simplex,
    integralPathChain_cycle, LinearMap.zero_apply]

private def integralPathLoopCycleLinearMap (x : X) [PathConnectedSpace X] :
    (integralSingularChains X).X 1 →ₗ[ℤ] integralSingularCycles 0 X :=
  (integralPathLoopChainMap x).codRestrict (integralSingularCycles 0 X) fun z => by
    have h := LinearMap.congr_fun (integralPathLoopChainMap_boundary (X := X) x) z
    rwa [LinearMap.comp_apply, LinearMap.zero_apply] at h

private def integralPathLoopCycleMap (x : X) [PathConnectedSpace X] :
    (integralSingularChains X).X 1 →ₗ[ℤ] integralSingularHomology 1 X :=
  (integralSingularCycleClassLinearMap 0 X).comp (integralPathLoopCycleLinearMap x)

private theorem integralPathLoopCycleMap_apply (x : X) [PathConnectedSpace X]
    (z : (integralSingularChains X).X 1) :
    integralPathLoopCycleMap x z =
      integralSingularCycleClass 0 X (integralPathLoopCycleLinearMap x z) :=
  rfl

private def integralPathLoopClassMap (x : X) [PathConnectedSpace X] :
    (integralSingularChains X).X 1 →ₗ[ℤ] integralSingularHomology 1 X :=
  (integralSingularChainBasis 1 X).constr (M' := integralSingularHomology 1 X) ℕ
    (fun σ => integralPathLoopClass (pathLoopOfSimplex x σ))

private theorem integralPathLoopClassMap_eq (x : X) [PathConnectedSpace X] :
    integralPathLoopClassMap x = integralPathLoopCycleMap x := by
  apply (integralSingularChainBasis 1 X).ext
  intro σ
  have hcycle : integralPathLoopCycleLinearMap x ((integralSingularChainBasis 1 X) σ) =
      ⟨integralPathChain (pathLoopOfSimplex x σ), integralPathChain_cycle _⟩ := by
    apply Subtype.ext
    change (integralPathLoopChainMap x) ((integralSingularChainBasis 1 X) σ) =
      integralPathChain (pathLoopOfSimplex x σ)
    rw [integralSingularChainBasis_apply, integralPathLoopChainMap_simplex]
  rw [integralPathLoopClassMap, Basis.constr_basis, integralPathLoopCycleMap]
  rw [LinearMap.comp_apply, hcycle]
  rw [integralSingularCycleClassLinearMap_apply]
  rfl

private theorem integralPathLoopClassMap_mem_span (x : X) [PathConnectedSpace X]
    (z : (integralSingularChains X).X 1) :
    integralPathLoopClassMap x z ∈
      Submodule.span ℤ (Set.range (fun γ : Path x x => integralPathLoopClass γ)) := by
  have hle : Submodule.span ℤ (Set.range (integralSingularChainBasis 1 X)) ≤
      Submodule.comap (integralPathLoopClassMap x)
        (Submodule.span ℤ (Set.range (fun γ : Path x x => integralPathLoopClass γ))) := by
    rw [Submodule.span_le]
    rintro y ⟨σ, rfl⟩
    exact Submodule.subset_span ⟨pathLoopOfSimplex x σ, by
      rw [integralPathLoopClassMap, Basis.constr_basis]⟩
  have hz : z ∈ Submodule.span ℤ (Set.range (integralSingularChainBasis 1 X)) := by
    rw [Basis.span_eq]
    exact Submodule.mem_top
  exact hle hz

theorem hurewiczOneLoopGeneration_of_hurewiczOneVertexPairing (x : X) [PathConnectedSpace X]
    (h : HurewiczOneVertexPairing x) : HurewiczOneLoopGeneration x := by
  intro y
  obtain ⟨z, rfl⟩ := integralSingularCycleClass_surjective 0 X y
  rw [integralSingularCycleClass_eq_of_sub_mem_range (X := X) 0 z
    (integralPathLoopCycleLinearMap x z) (h z)]
  rw [← integralPathLoopCycleMap_apply x (z : (integralSingularChains X).X 1)]
  rw [← integralPathLoopClassMap_eq x]
  exact integralPathLoopClassMap_mem_span x z

def tensorRationalAdditiveEquivOfMulEquiv {G H : Type u} [CommGroup G] [CommGroup H] (e : G ≃* H) :
    ℚ ⊗[ℤ] Additive G ≃ₗ[ℚ] ℚ ⊗[ℤ] Additive H :=
  LinearEquiv.baseChange ℤ ℚ _ _ (AddEquiv.toIntLinearEquiv (MulEquiv.toAdditive e))

theorem tensorRational_abelianizationFundamentalGroup_equiv_of_hurewiczOne (x : X)
    [PathConnectedSpace X]
    (c : integralSingularHomology (0 + 1) (liftedHomotopySphere.{u} 0))
    (hmul : ∀ a b : HomotopyGroup (Fin 1) X x,
      sphereHurewicz 0 x c (a * b) = sphereHurewicz 0 x c a + sphereHurewicz 0 x c b)
    (hsurj : Function.Surjective (sphereHurewicz 0 x c))
    (hker : ∀ a : HomotopyGroup (Fin 1) X x, sphereHurewicz 0 x c a = 0 →
      a ∈ commutator (HomotopyGroup (Fin 1) X x)) :
    Nonempty (ℚ ⊗[ℤ] Additive (Abelianization (FundamentalGroup X x)) ≃ₗ[ℚ]
      ℚ ⊗[ℤ] integralSingularHomology 1 X) := by
  obtain ⟨e⟩ := abelianizationHomotopyGroupOne_equiv_of_hurewiczOne x c hmul hsurj hker
  have e' : Abelianization (FundamentalGroup X x) ≃*
      Multiplicative (integralSingularHomology 1 X) :=
    (MulEquiv.abelianizationCongr
      (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x)).symm).trans e
  exact ⟨(tensorRationalAdditiveEquivOfMulEquiv e').trans
    (LinearEquiv.baseChange ℤ ℚ _ _ (AddEquiv.toIntLinearEquiv
      (AddEquiv.additiveMultiplicative (G := integralSingularHomology 1 X))))⟩

theorem rationalHurewiczOneClosedThreeManifold_of_hurewiczOne_of_coefficientChange
    (hH : ∀ (M : ConnectedClosedOrientedManifold.{0} 3) (p : M.Carrier),
      HurewiczOneMultiplicative M.Carrier ∧ HurewiczOneKernel M.Carrier ∧
        Function.Surjective (sphereHurewicz 0 p (integralLiftedSphereGenerator.{0} 0)))
    (hC : ∀ X : TopCat.{0}, rationalSingularHomologyOneCoefficientChange X) :
    RationalHurewiczOneClosedThreeManifold := by
  intro M p
  obtain ⟨hmul, hker, hsurj⟩ := hH M p
  have hc : IsSphereHomologyGenerator.{0} 0 (integralLiftedSphereGenerator.{0} 0) :=
    integralLiftedSphereGenerator_isGenerator 0
  obtain ⟨e⟩ := tensorRational_abelianizationFundamentalGroup_equiv_of_hurewiczOne p
    (integralLiftedSphereGenerator.{0} 0) (hmul p _ hc) hsurj (hker p _ hc)
  obtain ⟨f⟩ := hC (TopCat.of M.Carrier)
  exact ⟨e.trans f⟩

theorem moduleFinite_tensorIntegralSingularHomologyOne_of_coefficientChange
    (hC : ∀ X : TopCat.{0}, rationalSingularHomologyOneCoefficientChange X)
    (M : ClosedOrientedManifold.{0} 3) :
    Module.Finite ℚ (ℚ ⊗[ℤ] integralSingularHomology 1 M.Carrier) := by
  have hfin : Module.Finite ℚ (RationalSingularHomologyOne (TopCat.of M.Carrier)) :=
    finiteDimensional_rationalSingularHomologyOne_closedOrientedManifold M
  exact @Module.Finite.equiv ℚ _ _ _ _ _ _ _ hfin ((hC (TopCat.of M.Carrier)).some.symm)

theorem rationalFiniteAbelianizationFundamentalGroupClosedThreeManifold_of_hurewiczOne_of_coefficientChange
    (hH : ∀ (M : ConnectedClosedOrientedManifold.{0} 3) (p : M.Carrier),
      HurewiczOneMultiplicative M.Carrier ∧ HurewiczOneKernel M.Carrier ∧
        Function.Surjective (sphereHurewicz 0 p (integralLiftedSphereGenerator.{0} 0)))
    (hC : ∀ X : TopCat.{0}, rationalSingularHomologyOneCoefficientChange X) :
    RationalFiniteAbelianizationFundamentalGroupClosedThreeManifold.{0} :=
  rationalFiniteAbelianizationFundamentalGroupClosedThreeManifold_of_rationalHurewiczOne
    (rationalHurewiczOneClosedThreeManifold_of_hurewiczOne_of_coefficientChange hH hC)

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{0} 3} (E : SphericalCutCapTransition M Q)

theorem cutCapSummandCountDetermined_of_graphSumRealization_of_hurewiczOne_of_coefficientChange
    (h : E.graphSumRealization)
    (hH : ∀ (M : ConnectedClosedOrientedManifold.{0} 3) (p : M.Carrier),
      HurewiczOneMultiplicative M.Carrier ∧ HurewiczOneKernel M.Carrier ∧
        Function.Surjective (sphereHurewicz 0 p (integralLiftedSphereGenerator.{0} 0)))
    (hC : ∀ X : TopCat.{0}, rationalSingularHomologyOneCoefficientChange X) :
    E.cutCapSummandCountDetermined :=
  E.cutCapSummandCountDetermined_of_graphSumRealization_of_rationalHurewiczOne h
    (rationalHurewiczOneClosedThreeManifold_of_hurewiczOne_of_coefficientChange hH hC)

end SphericalCutCapTransition

end DifferentialGeometry.Topology
