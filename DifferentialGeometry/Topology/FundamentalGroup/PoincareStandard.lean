/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Algebra.Group.PoincareStandard
import DifferentialGeometry.Topology.FundamentalGroup.SphericalQuotient

set_option autoImplicit false

universe u v

namespace Poincare.Topology

open Poincare.Algebra.Group

abbrev poincareStandardSpaceFactor {a : ℕ} (Gamma : Fin a → Type u)
    [∀ j, Group (Gamma j)] [∀ j, MulAction (Gamma j) SphereThree]
    (b : ℕ) : Sum (Fin a) (Fin b) → Type
  | Sum.inl j => MulActionOrbitQuotient (Gamma j) SphereThree
  | Sum.inr _ => SphereTwo × Circle


noncomputable def poincareStandardSpaceFactorBasepoint
    {a : ℕ} (Gamma : Fin a → Type u)
    [∀ j, Group (Gamma j)] [∀ j, MulAction (Gamma j) SphereThree]
    (b : ℕ) : ∀ i, poincareStandardSpaceFactor Gamma b i
  | Sum.inl j => Quotient.mk (MulAction.orbitRel (Gamma j) SphereThree) sphereThreeNorth
  | Sum.inr _ => (sphereTwoNorth, 1)

noncomputable instance poincareStandardSpaceFactorTopologicalSpace
    {a : ℕ} (Gamma : Fin a → Type u)
    [∀ j, Group (Gamma j)] [∀ j, MulAction (Gamma j) SphereThree]
    (b : ℕ) (i : Sum (Fin a) (Fin b)) :
    TopologicalSpace (poincareStandardSpaceFactor Gamma b i) := by
  cases i <;> simp only [poincareStandardSpaceFactor] <;> infer_instance


abbrev poincareStandardFundamentalGroupFactors
    {a : ℕ} (Gamma : Fin a → Type u)
    [∀ j, Group (Gamma j)] [∀ j, MulAction (Gamma j) SphereThree]
    (b : ℕ) (i : Sum (Fin a) (Fin b)) :=
  FundamentalGroup (poincareStandardSpaceFactor Gamma b i)
    (poincareStandardSpaceFactorBasepoint Gamma b i)

noncomputable instance poincareStandardFundamentalGroupFactorsGroup
    {a : ℕ} (Gamma : Fin a → Type u)
    [∀ j, Group (Gamma j)] [∀ j, MulAction (Gamma j) SphereThree]
    (b : ℕ) (i : Sum (Fin a) (Fin b)) :
    Group (poincareStandardFundamentalGroupFactors Gamma b i) := by
  infer_instance


noncomputable def poincareStandardFactorEquiv
    {a : ℕ} (Gamma : Fin a → Type u)
    [∀ j, Group (Gamma j)] [∀ j, Finite (Gamma j)]
    [∀ j, MulAction (Gamma j) SphereThree]
    [∀ j, ContinuousConstSMul (Gamma j) SphereThree]
    [∀ j, IsCancelSMul (Gamma j) SphereThree]
    (b : ℕ) : ∀ i,
    poincareStandardFundamentalGroupFactors Gamma b i ≃*
      poincareStandardGroupFactors Gamma b i
  | Sum.inl _ => fundamentalGroupFiniteFreeSphereThreeQuotientEquiv
  | Sum.inr _ => by
      change FundamentalGroup (SphereTwo × Circle) (sphereTwoNorth, 1) ≃*
        ULift.{u} (Multiplicative ℤ)
      exact fundamentalGroupSphereTwoProdCircleEquivInt.trans MulEquiv.ulift.symm

noncomputable def poincareStandardFactorEquivOfIsometric
    {a : ℕ} (Gamma : Fin a → Type u)
    [∀ j, Group (Gamma j)] [∀ j, Finite (Gamma j)]
    [∀ j, MulAction (Gamma j) SphereThree]
    [∀ j, IsIsometricSMul (Gamma j) SphereThree]
    [∀ j, IsCancelSMul (Gamma j) SphereThree]
    (b : ℕ) : ∀ i,
    poincareStandardFundamentalGroupFactors Gamma b i ≃*
      poincareStandardGroupFactors Gamma b i :=
  poincareStandardFactorEquiv Gamma b


noncomputable def poincareStandardFactorFreeProductEquiv
    {a : ℕ} (Gamma : Fin a → Type u)
    [∀ j, Group (Gamma j)] [∀ j, Finite (Gamma j)]
    [∀ j, MulAction (Gamma j) SphereThree]
    [∀ j, ContinuousConstSMul (Gamma j) SphereThree]
    [∀ j, IsCancelSMul (Gamma j) SphereThree]
    (b : ℕ) :
    Monoid.CoprodI (poincareStandardFundamentalGroupFactors Gamma b) ≃*
      poincareStandardFreeProduct Gamma b :=
  Poincare.Algebra.Group.coprodIMulEquiv
    (poincareStandardFundamentalGroupFactors Gamma b)
    (poincareStandardGroupFactors Gamma b)
    (poincareStandardFactorEquiv Gamma b)


noncomputable def poincareStandardFactorFreeProductEquivOfIsometric
    {a : ℕ} (Gamma : Fin a → Type u)
    [∀ j, Group (Gamma j)] [∀ j, Finite (Gamma j)]
    [∀ j, MulAction (Gamma j) SphereThree]
    [∀ j, IsIsometricSMul (Gamma j) SphereThree]
    [∀ j, IsCancelSMul (Gamma j) SphereThree]
    (b : ℕ) :
    Monoid.CoprodI (poincareStandardFundamentalGroupFactors Gamma b) ≃*
      poincareStandardFreeProduct Gamma b :=
  poincareStandardFactorFreeProductEquiv Gamma b


@[simp]
theorem poincareStandardFactorFreeProductEquiv_comp_of
    {a : ℕ} (Gamma : Fin a → Type u)
    [∀ j, Group (Gamma j)] [∀ j, Finite (Gamma j)]
    [∀ j, MulAction (Gamma j) SphereThree]
    [∀ j, ContinuousConstSMul (Gamma j) SphereThree]
    [∀ j, IsCancelSMul (Gamma j) SphereThree]
    (b : ℕ) (i : Sum (Fin a) (Fin b)) :
    (↑(poincareStandardFactorFreeProductEquiv Gamma b) :
      Monoid.CoprodI (poincareStandardFundamentalGroupFactors Gamma b) →*
        poincareStandardFreeProduct Gamma b).comp
      (Monoid.CoprodI.of :
        poincareStandardFundamentalGroupFactors Gamma b i →*
          Monoid.CoprodI (poincareStandardFundamentalGroupFactors Gamma b)) =
      (Monoid.CoprodI.of :
        poincareStandardGroupFactors Gamma b i →* poincareStandardFreeProduct Gamma b).comp
        (poincareStandardFactorEquiv Gamma b i).toMonoidHom := by
  exact Poincare.Algebra.Group.coprodIMulEquiv_comp_of
    (poincareStandardFundamentalGroupFactors Gamma b)
    (poincareStandardGroupFactors Gamma b)
    (poincareStandardFactorEquiv Gamma b) i

@[simp]
theorem poincareStandardFactorFreeProductEquivOfIsometric_comp_of
    {a : ℕ} (Gamma : Fin a → Type u)
    [∀ j, Group (Gamma j)] [∀ j, Finite (Gamma j)]
    [∀ j, MulAction (Gamma j) SphereThree]
    [∀ j, IsIsometricSMul (Gamma j) SphereThree]
    [∀ j, IsCancelSMul (Gamma j) SphereThree]
    (b : ℕ) (i : Sum (Fin a) (Fin b)) :
    (↑(poincareStandardFactorFreeProductEquivOfIsometric Gamma b) :
      Monoid.CoprodI (poincareStandardFundamentalGroupFactors Gamma b) →*
        poincareStandardFreeProduct Gamma b).comp
      (Monoid.CoprodI.of :
        poincareStandardFundamentalGroupFactors Gamma b i →*
          Monoid.CoprodI (poincareStandardFundamentalGroupFactors Gamma b)) =
      (Monoid.CoprodI.of :
        poincareStandardGroupFactors Gamma b i →* poincareStandardFreeProduct Gamma b).comp
        (poincareStandardFactorEquivOfIsometric Gamma b i).toMonoidHom := by
  exact poincareStandardFactorFreeProductEquiv_comp_of Gamma b i

noncomputable def poincareStandardFundamentalGroupEquiv
    {a : ℕ} (Gamma : Fin a → Type u)
    [∀ j, Group (Gamma j)] [∀ j, Finite (Gamma j)]
    [∀ j, MulAction (Gamma j) SphereThree]
    [∀ j, ContinuousConstSMul (Gamma j) SphereThree]
    [∀ j, IsCancelSMul (Gamma j) SphereThree]
    (b : ℕ) {M : Type v} [TopologicalSpace M] (m : M)
    (connectedSumEquiv :
      FundamentalGroup M m ≃*
        Monoid.CoprodI (poincareStandardFundamentalGroupFactors Gamma b)) :
    FundamentalGroup M m ≃* poincareStandardFreeProduct Gamma b :=
  connectedSumEquiv.trans (poincareStandardFactorFreeProductEquiv Gamma b)

noncomputable def poincareStandardFundamentalGroupEquivOfIsometric
    {a : ℕ} (Gamma : Fin a → Type u)
    [∀ j, Group (Gamma j)] [∀ j, Finite (Gamma j)]
    [∀ j, MulAction (Gamma j) SphereThree]
    [∀ j, IsIsometricSMul (Gamma j) SphereThree]
    [∀ j, IsCancelSMul (Gamma j) SphereThree]
    (b : ℕ) {M : Type v} [TopologicalSpace M] (m : M)
    (connectedSumEquiv :
      FundamentalGroup M m ≃*
        Monoid.CoprodI (poincareStandardFundamentalGroupFactors Gamma b)) :
    FundamentalGroup M m ≃* poincareStandardFreeProduct Gamma b :=
  connectedSumEquiv.trans (poincareStandardFactorFreeProductEquivOfIsometric Gamma b)

theorem poincareStandard_factors_trivial_of_fundamentalGroupEquiv
    {a : ℕ} (Gamma : Fin a → Type u)
    [∀ j, Group (Gamma j)] [∀ j, Finite (Gamma j)]
    [∀ j, MulAction (Gamma j) SphereThree]
    [∀ j, ContinuousConstSMul (Gamma j) SphereThree]
    [∀ j, IsCancelSMul (Gamma j) SphereThree]
    (b : ℕ) {M : Type v} [TopologicalSpace M] [SimplyConnectedSpace M] (m : M)
    (connectedSumEquiv :
      FundamentalGroup M m ≃*
        Monoid.CoprodI (poincareStandardFundamentalGroupFactors Gamma b)) :
    b = 0 ∧ ∀ j, Subsingleton (Gamma j) := by
  apply (Poincare.Algebra.Group.poincareStandardFreeProduct_subsingleton_iff Gamma b).mp
  exact (poincareStandardFundamentalGroupEquiv Gamma b m connectedSumEquiv).symm.subsingleton

theorem poincareStandard_factors_trivial_of_fundamentalGroupEquivOfIsometric
    {a : ℕ} (Gamma : Fin a → Type u)
    [∀ j, Group (Gamma j)] [∀ j, Finite (Gamma j)]
    [∀ j, MulAction (Gamma j) SphereThree]
    [∀ j, IsIsometricSMul (Gamma j) SphereThree]
    [∀ j, IsCancelSMul (Gamma j) SphereThree]
    (b : ℕ) {M : Type v} [TopologicalSpace M] [SimplyConnectedSpace M] (m : M)
    (connectedSumEquiv :
      FundamentalGroup M m ≃*
        Monoid.CoprodI (poincareStandardFundamentalGroupFactors Gamma b)) :
    b = 0 ∧ ∀ j, Subsingleton (Gamma j) := by
  exact poincareStandard_factors_trivial_of_fundamentalGroupEquiv Gamma b m connectedSumEquiv

end Poincare.Topology
