import DifferentialGeometry.Topology.Algebra.Group.FinitelyGeneratedFundamentalGroup
import DifferentialGeometry.Topology.Homology.ClosedManifold
import DifferentialGeometry.Topology.Homology.Integral
import DifferentialGeometry.Topology.ThreeManifold.CutCapSummandCountAbelianizationRank

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Manifold ContDiff TensorProduct

namespace DifferentialGeometry.Topology

universe u

variable {n : ℕ}

abbrev RationalSingularHomologyOne (X : TopCat.{0}) : Type :=
  (((singularHomologyFunctor (ModuleCat.{0} ℚ) 1).obj (ModuleCat.of ℚ ℚ)).obj X)

theorem boundarylessManifold_closedOrientedManifold (M : ClosedOrientedManifold.{u} n) :
    BoundarylessManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) M.Carrier :=
  inferInstance

theorem finiteHomologyType_closedOrientedManifold (M : ClosedOrientedManifold.{0} n)
    (k : Type) [Field k] :
    DifferentialGeometry.Homology.finiteHomologyType k (TopCat.of M.Carrier) :=
  DifferentialGeometry.Homology.finiteHomologyType_of_compact_boundaryless_manifold
    (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) k

theorem finiteDimensional_rationalSingularHomologyOne_closedOrientedManifold
    (M : ClosedOrientedManifold.{0} n) :
    FiniteDimensional ℚ (RationalSingularHomologyOne (TopCat.of M.Carrier)) :=
  (finiteHomologyType_closedOrientedManifold M ℚ).1 1

def RationalHurewiczOneClosedThreeManifold : Prop :=
  ∀ (M : ConnectedClosedOrientedManifold.{0} 3) (p : M.Carrier),
    Nonempty (ℚ ⊗[ℤ] Additive (Abelianization (FundamentalGroup M.Carrier p)) ≃ₗ[ℚ]
      RationalSingularHomologyOne (TopCat.of M.Carrier))

theorem connectedClosedOrientedManifoldAbelianizationRationalFinite_of_rationalHurewiczOne
    (h : RationalHurewiczOneClosedThreeManifold)
    (M : ConnectedClosedOrientedManifold.{0} 3) :
    connectedClosedOrientedManifoldAbelianizationRationalFinite M := by
  have hfin : Module.Finite ℚ (RationalSingularHomologyOne (TopCat.of M.Carrier)) :=
    finiteDimensional_rationalSingularHomologyOne_closedOrientedManifold M.toClosedOrientedManifold
  exact Module.Finite.equiv (h M (chosenPoint M)).some.symm

theorem rationalFiniteAbelianizationFundamentalGroupClosedThreeManifold_of_rationalHurewiczOne
    (h : RationalHurewiczOneClosedThreeManifold) :
    RationalFiniteAbelianizationFundamentalGroupClosedThreeManifold.{0} :=
  fun M p => by
    have hfin : Module.Finite ℚ (RationalSingularHomologyOne (TopCat.of M.Carrier)) :=
      finiteDimensional_rationalSingularHomologyOne_closedOrientedManifold M.toClosedOrientedManifold
    exact Module.Finite.equiv (h M p).some.symm

theorem rationalFiniteAbelianizationFundamentalGroupClosedThreeManifold_of_rationalHurewiczOne_of_rationalHomologyFinite
    (hH : ∀ (M : ConnectedClosedOrientedManifold.{u} 3) (p : M.Carrier),
      Nonempty (ℚ ⊗[ℤ] Additive (Abelianization (FundamentalGroup M.Carrier p)) ≃ₗ[ℚ]
        ℚ ⊗[ℤ] (integralSingularHomology 1 M.Carrier)))
    (hfin : ∀ (M : ConnectedClosedOrientedManifold.{u} 3),
      Module.Finite ℚ (ℚ ⊗[ℤ] (integralSingularHomology 1 M.Carrier))) :
    RationalFiniteAbelianizationFundamentalGroupClosedThreeManifold.{u} :=
  fun M p => by
    have hM : Module.Finite ℚ (ℚ ⊗[ℤ] (integralSingularHomology 1 M.Carrier)) := hfin M
    exact Module.Finite.equiv (hH M p).some.symm

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem cutCapSummandCountDetermined_of_graphSumRealization_of_rationalHurewiczOne_of_rationalHomologyFinite
    (h : E.graphSumRealization)
    (hH : ∀ (N : ConnectedClosedOrientedManifold.{u} 3) (p : N.Carrier),
      Nonempty (ℚ ⊗[ℤ] Additive (Abelianization (FundamentalGroup N.Carrier p)) ≃ₗ[ℚ]
        ℚ ⊗[ℤ] (integralSingularHomology 1 N.Carrier)))
    (hfin : ∀ (N : ConnectedClosedOrientedManifold.{u} 3),
      Module.Finite ℚ (ℚ ⊗[ℤ] (integralSingularHomology 1 N.Carrier))) :
    E.cutCapSummandCountDetermined :=
  E.cutCapSummandCountDetermined_of_graphSumRealization_of_rationalFiniteAbelianizationFundamentalGroup
    h (rationalFiniteAbelianizationFundamentalGroupClosedThreeManifold_of_rationalHurewiczOne_of_rationalHomologyFinite
      hH hfin)

end SphericalCutCapTransition

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{0} 3} (E : SphericalCutCapTransition M Q)

theorem cutCapSummandCountDetermined_of_graphSumRealization_of_rationalHurewiczOne
    (h : E.graphSumRealization) (hH : RationalHurewiczOneClosedThreeManifold) :
    E.cutCapSummandCountDetermined :=
  E.cutCapSummandCountDetermined_of_graphSumRealization_of_rationalFiniteAbelianizationFundamentalGroup
    h (rationalFiniteAbelianizationFundamentalGroupClosedThreeManifold_of_rationalHurewiczOne hH)

end SphericalCutCapTransition

theorem finiteDimensional_rationalSingularHomologyOne_standardThreeSphereLift :
    FiniteDimensional ℚ (RationalSingularHomologyOne
      (TopCat.of standardThreeSphereLift.{0}.Carrier)) :=
  finiteDimensional_rationalSingularHomologyOne_closedOrientedManifold
    standardThreeSphereLift.toClosedOrientedManifold

theorem finiteDimensional_rationalSingularHomologyOne_sphereTwoTimesCircleLift :
    FiniteDimensional ℚ (RationalSingularHomologyOne
      (TopCat.of sphereTwoTimesCircleLift.Carrier)) :=
  finiteDimensional_rationalSingularHomologyOne_closedOrientedManifold
    sphereTwoTimesCircleLift.toClosedOrientedManifold

theorem finiteDimensional_rationalSingularHomologyOne_connectedSum_sphereTwoTimesCircleLift :
    FiniteDimensional ℚ (RationalSingularHomologyOne (TopCat.of
      (finiteConnectedSum [sphereTwoTimesCircleLift, sphereTwoTimesCircleLift]).Carrier)) :=
  finiteDimensional_rationalSingularHomologyOne_closedOrientedManifold
    (finiteConnectedSum [sphereTwoTimesCircleLift, sphereTwoTimesCircleLift]).toClosedOrientedManifold

theorem finrank_rat_tensor_additive_abelianization_sphereTwoTimesCircleLift
    (p : sphereTwoTimesCircleLift.Carrier) :
    Module.finrank ℚ (ℚ ⊗[ℤ] Additive (Abelianization
      (FundamentalGroup sphereTwoTimesCircleLift.Carrier p))) = 1 := by
  have e : Abelianization (FundamentalGroup sphereTwoTimesCircleLift.Carrier p) ≃*
      Multiplicative ℤ :=
    (MulEquiv.abelianizationCongr
      (fundamentalGroupMulEquivOfHomotopyEquiv Homeomorph.ulift.toHomotopyEquiv p p.down rfl)).trans
      ((MulEquiv.abelianizationCongr
        (exists_fundamentalGroupMulEquivInt_sphereTwoTimesCircle p.down).some).trans
        (Abelianization.equivOfComm).symm)
  have h := (LinearEquiv.baseChange ℤ ℚ _ _
    (AddEquiv.toIntLinearEquiv (MulEquiv.toAdditive e))).finrank_eq
  rw [h]
  exact DifferentialGeometry.Algebra.Module.finrank_tensorProduct_int

theorem moduleFinite_rat_tensor_additive_abelianization_standardThreeSphereLift
    (p : standardThreeSphereLift.{0}.Carrier) :
    Module.Finite ℚ (ℚ ⊗[ℤ] Additive (Abelianization
      (FundamentalGroup standardThreeSphereLift.{0}.Carrier p))) :=
  moduleFinite_rat_tensor_additive_abelianization_of_groupFG
    (groupFG_fundamentalGroup_standardThreeSphereLift p)

theorem moduleFinite_rat_tensor_additive_abelianization_sphereTwoTimesCircleLift
    (p : sphereTwoTimesCircleLift.Carrier) :
    Module.Finite ℚ (ℚ ⊗[ℤ] Additive (Abelianization
      (FundamentalGroup sphereTwoTimesCircleLift.Carrier p))) :=
  moduleFinite_rat_tensor_additive_abelianization_of_groupFG
    (groupFG_fundamentalGroup_sphereTwoTimesCircleLift p)

theorem moduleFinite_rat_tensor_additive_abelianization_connectedSum_sphereTwoTimesCircleLift
    (p : (finiteConnectedSum [sphereTwoTimesCircleLift, sphereTwoTimesCircleLift]).Carrier) :
    Module.Finite ℚ (ℚ ⊗[ℤ] Additive (Abelianization (FundamentalGroup
      (finiteConnectedSum [sphereTwoTimesCircleLift, sphereTwoTimesCircleLift]).Carrier p))) :=
  moduleFinite_rat_tensor_additive_abelianization_of_groupFG
    (finitelyGeneratedFundamentalGroup_connectedSum_sphereTwoTimesCircleLift p)

theorem not_moduleFinite_int_additive_abelianization_multiplicative_finsupp_int :
    ¬ Module.Finite ℤ (Additive (Abelianization (Multiplicative (ℕ →₀ ℤ)))) := by
  intro h
  have e : Additive (Abelianization (Multiplicative (ℕ →₀ ℤ))) ≃+ (ℕ →₀ ℤ) :=
    MulEquiv.toAdditive (Abelianization.equivOfComm
      (H := Multiplicative (ℕ →₀ ℤ))).symm
  have h' : Module.Finite ℤ (ℕ →₀ ℤ) :=
    (Module.Finite.equiv_iff (AddEquiv.toIntLinearEquiv e)).mp h
  exact (Module.not_finite_of_infinite_basis (Finsupp.basisSingleOne (R := ℤ))
    : ¬ Module.Finite ℤ (ℕ →₀ ℤ)) h'

end DifferentialGeometry.Topology
