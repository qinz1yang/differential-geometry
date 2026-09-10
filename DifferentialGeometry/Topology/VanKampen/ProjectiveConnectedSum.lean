/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Algebra.Group.TwoElementFreeProduct
import DifferentialGeometry.Topology.FundamentalGroup.RealProjective
import DifferentialGeometry.Topology.VanKampen.FiniteConnectedSum
import DifferentialGeometry.Topology.VanKampen.HomotopyEquivalentFreeProductCover

set_option autoImplicit false

namespace Poincare.Topology.VanKampen

open Poincare.Algebra.Group

noncomputable def projectiveConnectedSumFactorEquiv :
    ∀ i, fundamentalGroupSourceFactor realProjectiveThreeBasepoint
        realProjectiveThreeBasepoint i ≃* boolCoprodFamily TwoElementGroup TwoElementGroup i
  | false => fundamentalGroupRealProjectiveThreeEquivTwoElement.trans
      (MulEquiv.ulift : ULift TwoElementGroup ≃* TwoElementGroup).symm
  | true => fundamentalGroupRealProjectiveThreeEquivTwoElement.trans
      (MulEquiv.ulift : ULift TwoElementGroup ≃* TwoElementGroup).symm

noncomputable def projectiveConnectedSumSourceEquivTwoElementCoprod :
    fundamentalGroupSourceFreeProduct realProjectiveThreeBasepoint
        realProjectiveThreeBasepoint ≃*
      Monoid.Coprod TwoElementGroup TwoElementGroup :=
  (coprodIMulEquiv
    (fundamentalGroupSourceFactor realProjectiveThreeBasepoint realProjectiveThreeBasepoint)
    (boolCoprodFamily TwoElementGroup TwoElementGroup)
    projectiveConnectedSumFactorEquiv).trans
      (coprodIBoolEquivCoprod TwoElementGroup TwoElementGroup)


theorem projectiveConnectedSumSourceEquivTwoElementCoprod_of_left
    (g : FundamentalGroup RealProjectiveThree realProjectiveThreeBasepoint) :
    projectiveConnectedSumSourceEquivTwoElementCoprod
        (Monoid.CoprodI.of
          (M := fundamentalGroupSourceFactor realProjectiveThreeBasepoint
            realProjectiveThreeBasepoint) (i := false) g) =
      Monoid.Coprod.inl (fundamentalGroupRealProjectiveThreeEquivTwoElement g) := by
  change coprodIBoolEquivCoprod TwoElementGroup TwoElementGroup
      ((coprodIMulEquiv
        (fundamentalGroupSourceFactor realProjectiveThreeBasepoint
          realProjectiveThreeBasepoint)
        (boolCoprodFamily TwoElementGroup TwoElementGroup)
        projectiveConnectedSumFactorEquiv)
          (Monoid.CoprodI.of
            (M := fundamentalGroupSourceFactor realProjectiveThreeBasepoint
              realProjectiveThreeBasepoint) (i := false) g)) = _
  rw [show (coprodIMulEquiv
      (fundamentalGroupSourceFactor realProjectiveThreeBasepoint
        realProjectiveThreeBasepoint)
      (boolCoprodFamily TwoElementGroup TwoElementGroup)
      projectiveConnectedSumFactorEquiv)
        (Monoid.CoprodI.of
          (M := fundamentalGroupSourceFactor realProjectiveThreeBasepoint
            realProjectiveThreeBasepoint) (i := false) g) =
        Monoid.CoprodI.of (i := false) (projectiveConnectedSumFactorEquiv false g) by
      change (↑(coprodIMulEquiv
        (fundamentalGroupSourceFactor realProjectiveThreeBasepoint
          realProjectiveThreeBasepoint)
        (boolCoprodFamily TwoElementGroup TwoElementGroup)
        projectiveConnectedSumFactorEquiv) :
          fundamentalGroupSourceFreeProduct realProjectiveThreeBasepoint
            realProjectiveThreeBasepoint →*
          Monoid.CoprodI (boolCoprodFamily TwoElementGroup TwoElementGroup))
            (Monoid.CoprodI.of (i := false) g) = _
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using DFunLike.congr_fun
        (coprodIMulEquiv_comp_of
          (fundamentalGroupSourceFactor realProjectiveThreeBasepoint
            realProjectiveThreeBasepoint)
          (boolCoprodFamily TwoElementGroup TwoElementGroup)
          projectiveConnectedSumFactorEquiv false) g]
  rfl


theorem projectiveConnectedSumSourceEquivTwoElementCoprod_of_right
    (g : FundamentalGroup RealProjectiveThree realProjectiveThreeBasepoint) :
    projectiveConnectedSumSourceEquivTwoElementCoprod
        (Monoid.CoprodI.of
          (M := fundamentalGroupSourceFactor realProjectiveThreeBasepoint
            realProjectiveThreeBasepoint) (i := true) g) =
      Monoid.Coprod.inr (fundamentalGroupRealProjectiveThreeEquivTwoElement g) := by
  change coprodIBoolEquivCoprod TwoElementGroup TwoElementGroup
      ((coprodIMulEquiv
        (fundamentalGroupSourceFactor realProjectiveThreeBasepoint
          realProjectiveThreeBasepoint)
        (boolCoprodFamily TwoElementGroup TwoElementGroup)
        projectiveConnectedSumFactorEquiv)
          (Monoid.CoprodI.of
            (M := fundamentalGroupSourceFactor realProjectiveThreeBasepoint
              realProjectiveThreeBasepoint) (i := true) g)) = _
  rw [show (coprodIMulEquiv
      (fundamentalGroupSourceFactor realProjectiveThreeBasepoint
        realProjectiveThreeBasepoint)
      (boolCoprodFamily TwoElementGroup TwoElementGroup)
      projectiveConnectedSumFactorEquiv)
        (Monoid.CoprodI.of
          (M := fundamentalGroupSourceFactor realProjectiveThreeBasepoint
            realProjectiveThreeBasepoint) (i := true) g) =
        Monoid.CoprodI.of (i := true) (projectiveConnectedSumFactorEquiv true g) by
      change (↑(coprodIMulEquiv
        (fundamentalGroupSourceFactor realProjectiveThreeBasepoint
          realProjectiveThreeBasepoint)
        (boolCoprodFamily TwoElementGroup TwoElementGroup)
        projectiveConnectedSumFactorEquiv) :
          fundamentalGroupSourceFreeProduct realProjectiveThreeBasepoint
            realProjectiveThreeBasepoint →*
          Monoid.CoprodI (boolCoprodFamily TwoElementGroup TwoElementGroup))
            (Monoid.CoprodI.of (i := true) g) = _
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using DFunLike.congr_fun
        (coprodIMulEquiv_comp_of
          (fundamentalGroupSourceFactor realProjectiveThreeBasepoint
            realProjectiveThreeBasepoint)
          (boolCoprodFamily TwoElementGroup TwoElementGroup)
          projectiveConnectedSumFactorEquiv true) g]
  rfl

noncomputable def fundamentalGroupProjectiveConnectedSumEquiv
    {X : Type*} [TopologicalSpace X] (x₀ : X)
    (connectedSumEquiv :
      fundamentalGroupSourceFreeProduct realProjectiveThreeBasepoint
          realProjectiveThreeBasepoint ≃* FundamentalGroup X x₀) :
    FundamentalGroup X x₀ ≃* Monoid.Coprod TwoElementGroup TwoElementGroup :=
  connectedSumEquiv.symm.trans projectiveConnectedSumSourceEquivTwoElementCoprod


theorem infinite_fundamentalGroup_projectiveConnectedSum
    {X : Type*} [TopologicalSpace X] (x₀ : X)
    (connectedSumEquiv :
      fundamentalGroupSourceFreeProduct realProjectiveThreeBasepoint
          realProjectiveThreeBasepoint ≃* FundamentalGroup X x₀) :
    Infinite (FundamentalGroup X x₀) := by
  let e := fundamentalGroupProjectiveConnectedSumEquiv x₀ connectedSumEquiv
  exact Infinite.of_injective e.symm e.symm.injective

end Poincare.Topology.VanKampen

namespace Poincare.Topology.ThreeManifold

open Poincare.Algebra.Group
open Poincare.Topology.VanKampen

structure ProjectiveConnectedSumPresentation where

  left : BasedConnectedClosedSmoothThreeManifold

  right : BasedConnectedClosedSmoothThreeManifold

  result : BasedConnectedClosedSmoothThreeManifold

  leftHomeomorph : left ≃ₜ Poincare.Topology.RealProjectiveThree

  leftHomeomorph_basepoint :
    leftHomeomorph left.basepoint = Poincare.Topology.realProjectiveThreeBasepoint

  rightHomeomorph : right ≃ₜ Poincare.Topology.RealProjectiveThree

  rightHomeomorph_basepoint :
    rightHomeomorph right.basepoint = Poincare.Topology.realProjectiveThreeBasepoint

  step : ConnectedSumStep left right result


noncomputable def ProjectiveConnectedSumPresentation.leftFundamentalGroupEquiv
    (p : ProjectiveConnectedSumPresentation) :
    FundamentalGroup Poincare.Topology.RealProjectiveThree
        Poincare.Topology.realProjectiveThreeBasepoint ≃*
      FundamentalGroup p.left p.left.basepoint :=
  (Poincare.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
    p.leftHomeomorph.toHomotopyEquiv p.left.basepoint
      Poincare.Topology.realProjectiveThreeBasepoint
      p.leftHomeomorph_basepoint).symm


noncomputable def ProjectiveConnectedSumPresentation.rightFundamentalGroupEquiv
    (p : ProjectiveConnectedSumPresentation) :
    FundamentalGroup Poincare.Topology.RealProjectiveThree
        Poincare.Topology.realProjectiveThreeBasepoint ≃*
      FundamentalGroup p.right p.right.basepoint :=
  (Poincare.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
    p.rightHomeomorph.toHomotopyEquiv p.right.basepoint
      Poincare.Topology.realProjectiveThreeBasepoint
      p.rightHomeomorph_basepoint).symm

noncomputable def ProjectiveConnectedSumPresentation.sourceFactorEquiv
    (p : ProjectiveConnectedSumPresentation) : ∀ i,
    fundamentalGroupSourceFactor Poincare.Topology.realProjectiveThreeBasepoint
        Poincare.Topology.realProjectiveThreeBasepoint i ≃*
      fundamentalGroupSourceFactor p.left.basepoint p.right.basepoint i
  | false => p.leftFundamentalGroupEquiv
  | true => p.rightFundamentalGroupEquiv

noncomputable def ProjectiveConnectedSumPresentation.sourceFreeProductEquivCoprod
    (p : ProjectiveConnectedSumPresentation) :
    fundamentalGroupSourceFreeProduct Poincare.Topology.realProjectiveThreeBasepoint
        Poincare.Topology.realProjectiveThreeBasepoint ≃*
      Monoid.Coprod
        (FundamentalGroup p.left p.left.basepoint)
        (FundamentalGroup p.right p.right.basepoint) :=
  (coprodIMulEquiv
    (fundamentalGroupSourceFactor Poincare.Topology.realProjectiveThreeBasepoint
      Poincare.Topology.realProjectiveThreeBasepoint)
    (fundamentalGroupSourceFactor p.left.basepoint p.right.basepoint)
    p.sourceFactorEquiv).trans
      (fundamentalGroupSourceFreeProductEquivCoprod p.left.basepoint p.right.basepoint)

noncomputable def ProjectiveConnectedSumPresentation.connectedSumFundamentalGroupEquiv
    (p : ProjectiveConnectedSumPresentation) :
    fundamentalGroupSourceFreeProduct Poincare.Topology.realProjectiveThreeBasepoint
        Poincare.Topology.realProjectiveThreeBasepoint ≃*
      FundamentalGroup p.result p.result.basepoint :=
  p.sourceFreeProductEquivCoprod.trans p.step.forwardFundamentalGroupEquiv

theorem ProjectiveConnectedSumPresentation.connectedSumFundamentalGroupEquiv_comp_left
    (p : ProjectiveConnectedSumPresentation) :
    p.connectedSumFundamentalGroupEquiv.toMonoidHom.comp
        (Monoid.CoprodI.of
          (M := fundamentalGroupSourceFactor
            Poincare.Topology.realProjectiveThreeBasepoint
            Poincare.Topology.realProjectiveThreeBasepoint)
          (i := false)) =
      p.step.leftFactorHom.comp p.leftFundamentalGroupEquiv.toMonoidHom := by
  ext g
  change p.step.forwardFundamentalGroupEquiv
      (fundamentalGroupSourceFreeProductEquivCoprod p.left.basepoint p.right.basepoint
        ((coprodIMulEquiv
          (fundamentalGroupSourceFactor Poincare.Topology.realProjectiveThreeBasepoint
            Poincare.Topology.realProjectiveThreeBasepoint)
          (fundamentalGroupSourceFactor p.left.basepoint p.right.basepoint)
          p.sourceFactorEquiv)
            (Monoid.CoprodI.of (i := false) g))) = _
  have hsource := DFunLike.congr_fun
    (coprodIMulEquiv_comp_of
      (fundamentalGroupSourceFactor Poincare.Topology.realProjectiveThreeBasepoint
        Poincare.Topology.realProjectiveThreeBasepoint)
      (fundamentalGroupSourceFactor p.left.basepoint p.right.basepoint)
      p.sourceFactorEquiv false) g
  change
    (coprodIMulEquiv
      (fundamentalGroupSourceFactor Poincare.Topology.realProjectiveThreeBasepoint
        Poincare.Topology.realProjectiveThreeBasepoint)
      (fundamentalGroupSourceFactor p.left.basepoint p.right.basepoint)
      p.sourceFactorEquiv)
        (Monoid.CoprodI.of (i := false) g) =
      Monoid.CoprodI.of (i := false) (p.leftFundamentalGroupEquiv g) at hsource
  rw [hsource, fundamentalGroupSourceFreeProductEquivCoprod_of_false]
  exact DFunLike.congr_fun p.step.forwardFundamentalGroupEquiv_comp_inl
    (p.leftFundamentalGroupEquiv g)

theorem ProjectiveConnectedSumPresentation.connectedSumFundamentalGroupEquiv_comp_right
    (p : ProjectiveConnectedSumPresentation) :
    p.connectedSumFundamentalGroupEquiv.toMonoidHom.comp
        (Monoid.CoprodI.of
          (M := fundamentalGroupSourceFactor
            Poincare.Topology.realProjectiveThreeBasepoint
            Poincare.Topology.realProjectiveThreeBasepoint)
          (i := true)) =
      p.step.rightFactorHom.comp p.rightFundamentalGroupEquiv.toMonoidHom := by
  ext g
  change p.step.forwardFundamentalGroupEquiv
      (fundamentalGroupSourceFreeProductEquivCoprod p.left.basepoint p.right.basepoint
        ((coprodIMulEquiv
          (fundamentalGroupSourceFactor Poincare.Topology.realProjectiveThreeBasepoint
            Poincare.Topology.realProjectiveThreeBasepoint)
          (fundamentalGroupSourceFactor p.left.basepoint p.right.basepoint)
          p.sourceFactorEquiv)
            (Monoid.CoprodI.of (i := true) g))) = _
  have hsource := DFunLike.congr_fun
    (coprodIMulEquiv_comp_of
      (fundamentalGroupSourceFactor Poincare.Topology.realProjectiveThreeBasepoint
        Poincare.Topology.realProjectiveThreeBasepoint)
      (fundamentalGroupSourceFactor p.left.basepoint p.right.basepoint)
      p.sourceFactorEquiv true) g
  change
    (coprodIMulEquiv
      (fundamentalGroupSourceFactor Poincare.Topology.realProjectiveThreeBasepoint
        Poincare.Topology.realProjectiveThreeBasepoint)
      (fundamentalGroupSourceFactor p.left.basepoint p.right.basepoint)
      p.sourceFactorEquiv)
        (Monoid.CoprodI.of (i := true) g) =
      Monoid.CoprodI.of (i := true) (p.rightFundamentalGroupEquiv g) at hsource
  rw [hsource, fundamentalGroupSourceFreeProductEquivCoprod_of_true]
  exact DFunLike.congr_fun p.step.forwardFundamentalGroupEquiv_comp_inr
    (p.rightFundamentalGroupEquiv g)

noncomputable def ProjectiveConnectedSumPresentation.fundamentalGroupEquiv
    (p : ProjectiveConnectedSumPresentation) :
    FundamentalGroup p.result p.result.basepoint ≃*
      Monoid.Coprod TwoElementGroup TwoElementGroup :=
  fundamentalGroupProjectiveConnectedSumEquiv p.result.basepoint
    p.connectedSumFundamentalGroupEquiv

theorem ProjectiveConnectedSumPresentation.fundamentalGroupEquiv_comp_leftFactorHom
    (p : ProjectiveConnectedSumPresentation) :
    p.fundamentalGroupEquiv.toMonoidHom.comp p.step.leftFactorHom =
      Monoid.Coprod.inl.comp
        (Poincare.Topology.fundamentalGroupRealProjectiveThreeEquivTwoElement.toMonoidHom.comp
          p.leftFundamentalGroupEquiv.symm.toMonoidHom) := by
  ext g
  change projectiveConnectedSumSourceEquivTwoElementCoprod
      (p.connectedSumFundamentalGroupEquiv.symm (p.step.leftFactorHom g)) = _
  have hinv :
      p.connectedSumFundamentalGroupEquiv.symm (p.step.leftFactorHom g) =
        Monoid.CoprodI.of (i := false) (p.leftFundamentalGroupEquiv.symm g) := by
    apply p.connectedSumFundamentalGroupEquiv.injective
    rw [p.connectedSumFundamentalGroupEquiv.apply_symm_apply]
    have h := DFunLike.congr_fun p.connectedSumFundamentalGroupEquiv_comp_left
      (p.leftFundamentalGroupEquiv.symm g)
    change p.connectedSumFundamentalGroupEquiv
        (Monoid.CoprodI.of (i := false) (p.leftFundamentalGroupEquiv.symm g)) =
      p.step.leftFactorHom
        (p.leftFundamentalGroupEquiv (p.leftFundamentalGroupEquiv.symm g)) at h
    rw [p.leftFundamentalGroupEquiv.apply_symm_apply] at h
    exact h.symm
  rw [hinv, projectiveConnectedSumSourceEquivTwoElementCoprod_of_left]
  rfl

theorem ProjectiveConnectedSumPresentation.fundamentalGroupEquiv_comp_rightFactorHom
    (p : ProjectiveConnectedSumPresentation) :
    p.fundamentalGroupEquiv.toMonoidHom.comp p.step.rightFactorHom =
      Monoid.Coprod.inr.comp
        (Poincare.Topology.fundamentalGroupRealProjectiveThreeEquivTwoElement.toMonoidHom.comp
          p.rightFundamentalGroupEquiv.symm.toMonoidHom) := by
  ext g
  change projectiveConnectedSumSourceEquivTwoElementCoprod
      (p.connectedSumFundamentalGroupEquiv.symm (p.step.rightFactorHom g)) = _
  have hinv :
      p.connectedSumFundamentalGroupEquiv.symm (p.step.rightFactorHom g) =
        Monoid.CoprodI.of (i := true) (p.rightFundamentalGroupEquiv.symm g) := by
    apply p.connectedSumFundamentalGroupEquiv.injective
    rw [p.connectedSumFundamentalGroupEquiv.apply_symm_apply]
    have h := DFunLike.congr_fun p.connectedSumFundamentalGroupEquiv_comp_right
      (p.rightFundamentalGroupEquiv.symm g)
    change p.connectedSumFundamentalGroupEquiv
        (Monoid.CoprodI.of (i := true) (p.rightFundamentalGroupEquiv.symm g)) =
      p.step.rightFactorHom
        (p.rightFundamentalGroupEquiv (p.rightFundamentalGroupEquiv.symm g)) at h
    rw [p.rightFundamentalGroupEquiv.apply_symm_apply] at h
    exact h.symm
  rw [hinv, projectiveConnectedSumSourceEquivTwoElementCoprod_of_right]
  rfl

theorem ProjectiveConnectedSumPresentation.infinite_fundamentalGroup
    (p : ProjectiveConnectedSumPresentation) :
    Infinite (FundamentalGroup p.result p.result.basepoint) :=
  infinite_fundamentalGroup_projectiveConnectedSum p.result.basepoint
    p.connectedSumFundamentalGroupEquiv

end Poincare.Topology.ThreeManifold
