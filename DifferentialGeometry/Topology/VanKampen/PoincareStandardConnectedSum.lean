/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.FundamentalGroup.PoincareStandard
import DifferentialGeometry.Topology.VanKampen.ParenthesizedFiniteConnectedSum

set_option autoImplicit false

noncomputable section

universe u

namespace Poincare.Topology.ThreeManifold

open Poincare.Algebra.Group

structure PoincareStandardConnectedSumPresentation
    {a : ℕ} (Gamma : Fin a → Type u)
    [∀ j, Group (Gamma j)] [∀ j, MulAction (Gamma j) Poincare.Topology.SphereThree]
    (b : ℕ) where

  result : BasedConnectedClosedSmoothThreeManifold

  leafIndex : Type

  construction : ParenthesizedConnectedSumConstruction (a + b) leafIndex result

  factorHomeomorph : ∀ i : Fin (a + b),
    construction.orderedFactorManifold i ≃ₜ
      Poincare.Topology.poincareStandardSpaceFactor Gamma b (finSumFinEquiv.symm i)

  factorHomeomorph_basepoint : ∀ i : Fin (a + b),
    factorHomeomorph i (construction.orderedFactorManifold i).basepoint =
      Poincare.Topology.poincareStandardSpaceFactorBasepoint Gamma b (finSumFinEquiv.symm i)

noncomputable def PoincareStandardConnectedSumPresentation.factorFundamentalGroupEquiv
    {a : ℕ} (Gamma : Fin a → Type u)
    [∀ j, Group (Gamma j)] [∀ j, MulAction (Gamma j) Poincare.Topology.SphereThree]
    (b : ℕ) (p : PoincareStandardConnectedSumPresentation Gamma b) (i : Fin (a + b)) :
    p.construction.orderedFactorFundamentalGroup i ≃*
      Poincare.Topology.poincareStandardFundamentalGroupFactors Gamma b
        (finSumFinEquiv.symm i) :=
  Poincare.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
    (p.factorHomeomorph i).toHomotopyEquiv
    (p.construction.orderedFactorManifold i).basepoint
    (Poincare.Topology.poincareStandardSpaceFactorBasepoint Gamma b
      (finSumFinEquiv.symm i))
    (p.factorHomeomorph_basepoint i)

noncomputable def PoincareStandardConnectedSumPresentation.factorFreeProductEquiv
    {a : ℕ} (Gamma : Fin a → Type u)
    [∀ j, Group (Gamma j)] [∀ j, MulAction (Gamma j) Poincare.Topology.SphereThree]
    (b : ℕ) (p : PoincareStandardConnectedSumPresentation Gamma b) :
    Monoid.CoprodI p.construction.orderedFactorFundamentalGroup ≃*
      Monoid.CoprodI
        (Poincare.Topology.poincareStandardFundamentalGroupFactors Gamma b) :=
  coprodIReindexEquiv
    p.construction.orderedFactorFundamentalGroup
    (Poincare.Topology.poincareStandardFundamentalGroupFactors Gamma b)
    finSumFinEquiv.symm
    (p.factorFundamentalGroupEquiv Gamma b)

noncomputable def PoincareStandardConnectedSumPresentation.connectedSumFundamentalGroupEquiv
    {a : ℕ} (Gamma : Fin a → Type u)
    [∀ j, Group (Gamma j)] [∀ j, MulAction (Gamma j) Poincare.Topology.SphereThree]
    (b : ℕ) (p : PoincareStandardConnectedSumPresentation Gamma b) :
    FundamentalGroup p.result p.result.basepoint ≃*
      Monoid.CoprodI
        (Poincare.Topology.poincareStandardFundamentalGroupFactors Gamma b) :=
  (fundamentalGroupEquiv_parenthesizedFiniteConnectedSum p.construction).trans
    (p.factorFreeProductEquiv Gamma b)

theorem PoincareStandardConnectedSumPresentation.connectedSumFundamentalGroupEquiv_comp_factor
    {a : ℕ} (Gamma : Fin a → Type u)
    [∀ j, Group (Gamma j)] [∀ j, MulAction (Gamma j) Poincare.Topology.SphereThree]
    (b : ℕ) (p : PoincareStandardConnectedSumPresentation Gamma b)
    (i : Fin (a + b)) :
    (p.connectedSumFundamentalGroupEquiv Gamma b).toMonoidHom.comp
        (p.construction.orderedFactorToResult i) =
      (Monoid.CoprodI.of :
        Poincare.Topology.poincareStandardFundamentalGroupFactors Gamma b
            (finSumFinEquiv.symm i) →*
          Monoid.CoprodI
            (Poincare.Topology.poincareStandardFundamentalGroupFactors Gamma b)).comp
        (p.factorFundamentalGroupEquiv Gamma b i).toMonoidHom := by
  change
    (p.factorFreeProductEquiv Gamma b).toMonoidHom.comp
        ((fundamentalGroupEquiv_parenthesizedFiniteConnectedSum
          p.construction).toMonoidHom.comp
            (p.construction.orderedFactorToResult i)) = _
  rw [fundamentalGroupEquiv_parenthesizedFiniteConnectedSum_comp_orderedFactorToResult]
  exact coprodIReindexEquiv_comp_of
    p.construction.orderedFactorFundamentalGroup
    (Poincare.Topology.poincareStandardFundamentalGroupFactors Gamma b)
    finSumFinEquiv.symm (p.factorFundamentalGroupEquiv Gamma b) i

noncomputable def PoincareStandardConnectedSumPresentation.fundamentalGroupEquivOfIsometric
    {a : ℕ} (Gamma : Fin a → Type u)
    [∀ j, Group (Gamma j)] [∀ j, Finite (Gamma j)]
    [∀ j, MulAction (Gamma j) Poincare.Topology.SphereThree]
    [∀ j, IsIsometricSMul (Gamma j) Poincare.Topology.SphereThree]
    [∀ j, IsCancelSMul (Gamma j) Poincare.Topology.SphereThree]
    (b : ℕ) (p : PoincareStandardConnectedSumPresentation Gamma b) :
    FundamentalGroup p.result p.result.basepoint ≃*
      poincareStandardFreeProduct Gamma b :=
  Poincare.Topology.poincareStandardFundamentalGroupEquivOfIsometric
    Gamma b p.result.basepoint (p.connectedSumFundamentalGroupEquiv Gamma b)

theorem PoincareStandardConnectedSumPresentation.fundamentalGroupEquivOfIsometric_comp_factor
    {a : ℕ} (Gamma : Fin a → Type u)
    [∀ j, Group (Gamma j)] [∀ j, Finite (Gamma j)]
    [∀ j, MulAction (Gamma j) Poincare.Topology.SphereThree]
    [∀ j, IsIsometricSMul (Gamma j) Poincare.Topology.SphereThree]
    [∀ j, IsCancelSMul (Gamma j) Poincare.Topology.SphereThree]
    (b : ℕ) (p : PoincareStandardConnectedSumPresentation Gamma b)
    (i : Fin (a + b)) :
    (p.fundamentalGroupEquivOfIsometric Gamma b).toMonoidHom.comp
        (p.construction.orderedFactorToResult i) =
      (Monoid.CoprodI.of :
        poincareStandardGroupFactors Gamma b (finSumFinEquiv.symm i) →*
          poincareStandardFreeProduct Gamma b).comp
        ((Poincare.Topology.poincareStandardFactorEquivOfIsometric
          Gamma b (finSumFinEquiv.symm i)).toMonoidHom.comp
            (p.factorFundamentalGroupEquiv Gamma b i).toMonoidHom) := by
  ext g
  change
    Poincare.Topology.poincareStandardFactorFreeProductEquivOfIsometric Gamma b
        (p.connectedSumFundamentalGroupEquiv Gamma b
          (p.construction.orderedFactorToResult i g)) = _
  have hsum := DFunLike.congr_fun
    (p.connectedSumFundamentalGroupEquiv_comp_factor Gamma b i) g
  change
    p.connectedSumFundamentalGroupEquiv Gamma b
        (p.construction.orderedFactorToResult i g) =
      Monoid.CoprodI.of
        (p.factorFundamentalGroupEquiv Gamma b i g) at hsum
  rw [hsum]
  have hfactor := DFunLike.congr_fun
    (Poincare.Topology.poincareStandardFactorFreeProductEquivOfIsometric_comp_of
      Gamma b (finSumFinEquiv.symm i))
    (p.factorFundamentalGroupEquiv Gamma b i g)
  exact hfactor

theorem PoincareStandardConnectedSumPresentation.factors_trivial_of_simplyConnected
    {a : ℕ} (Gamma : Fin a → Type u)
    [∀ j, Group (Gamma j)] [∀ j, Finite (Gamma j)]
    [∀ j, MulAction (Gamma j) Poincare.Topology.SphereThree]
    [∀ j, IsIsometricSMul (Gamma j) Poincare.Topology.SphereThree]
    [∀ j, IsCancelSMul (Gamma j) Poincare.Topology.SphereThree]
    (b : ℕ) (p : PoincareStandardConnectedSumPresentation Gamma b)
    [SimplyConnectedSpace p.result] :
    b = 0 ∧ ∀ j, Subsingleton (Gamma j) :=
  Poincare.Topology.poincareStandard_factors_trivial_of_fundamentalGroupEquivOfIsometric
    Gamma b p.result.basepoint (p.connectedSumFundamentalGroupEquiv Gamma b)

end Poincare.Topology.ThreeManifold
