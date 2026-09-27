/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Geometry.Manifold.Instances.Sphere
import DifferentialGeometry.Topology.Algebra.Group.FreeProductAssociativity
import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import DifferentialGeometry.Topology.VanKampen.ConnectedSum

set_option autoImplicit false

open Set Topology
open scoped ContinuousMap Manifold ContDiff

noncomputable section

universe u

namespace DifferentialGeometry.Topology.ThreeManifold

open DifferentialGeometry.Topology
open DifferentialGeometry.Algebra.Group
open DifferentialGeometry.Topology.VanKampen

structure BasedConnectedClosedSmoothThreeManifold where

  Carrier : Type u

  topology : TopologicalSpace Carrier

  charted : @ChartedSpace (EuclideanSpace ℝ (Fin 3)) inferInstance Carrier topology

  t2 : @T2Space Carrier topology

  connected : @ConnectedSpace Carrier topology

  compact : @CompactSpace Carrier topology

  smooth : @IsManifold ℝ inferInstance (EuclideanSpace ℝ (Fin 3)) inferInstance inferInstance
    (EuclideanSpace ℝ (Fin 3)) inferInstance 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ Carrier
      topology charted

  basepoint : Carrier

instance : CoeSort BasedConnectedClosedSmoothThreeManifold (Type u) :=
  ⟨BasedConnectedClosedSmoothThreeManifold.Carrier⟩

instance (M : BasedConnectedClosedSmoothThreeManifold) : TopologicalSpace M := M.topology
instance (M : BasedConnectedClosedSmoothThreeManifold) :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) M := M.charted
instance (M : BasedConnectedClosedSmoothThreeManifold) : T2Space M := M.t2
instance (M : BasedConnectedClosedSmoothThreeManifold) : ConnectedSpace M := M.connected
instance (M : BasedConnectedClosedSmoothThreeManifold) : CompactSpace M := M.compact
instance (M : BasedConnectedClosedSmoothThreeManifold) :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ M := M.smooth

noncomputable def fundamentalGroupSourceFreeProductEquivCoprod
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B] (a : A) (b : B) :
    fundamentalGroupSourceFreeProduct a b ≃*
      Monoid.Coprod (FundamentalGroup A a) (FundamentalGroup B b) :=
  (coprodIMulEquiv
    (fundamentalGroupSourceFactor a b)
    (boolCoprodFamily (FundamentalGroup A a) (FundamentalGroup B b)) fun
      | false => (MulEquiv.ulift : ULift.{u} (FundamentalGroup A a) ≃*
          FundamentalGroup A a).symm
      | true => (MulEquiv.ulift : ULift.{u} (FundamentalGroup B b) ≃*
          FundamentalGroup B b).symm).trans
    (coprodIBoolEquivCoprod (FundamentalGroup A a) (FundamentalGroup B b))


theorem fundamentalGroupSourceFreeProductEquivCoprod_of_false
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B] (a : A) (b : B)
    (g : FundamentalGroup A a) :
    fundamentalGroupSourceFreeProductEquivCoprod a b
        (Monoid.CoprodI.of (M := fundamentalGroupSourceFactor a b) (i := false) g) =
      Monoid.Coprod.inl g := by
  rfl


theorem fundamentalGroupSourceFreeProductEquivCoprod_of_true
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B] (a : A) (b : B)
    (g : FundamentalGroup B b) :
    fundamentalGroupSourceFreeProductEquivCoprod a b
        (Monoid.CoprodI.of (M := fundamentalGroupSourceFactor a b) (i := true) g) =
      Monoid.Coprod.inr g := by
  rfl


structure ConnectedSumStep
    (A B C : BasedConnectedClosedSmoothThreeManifold) where

  leftCell : SmoothEmbeddedClosedThreeCellWithCollar A

  rightCell : SmoothEmbeddedClosedThreeCellWithCollar B

  glue : CellBoundary 3 ≃ₜ CellBoundary 3

  boundaryPoint : CellBoundary 3

  leftConnector : Path
    (connectedSumLeftGluingPoint leftCell boundaryPoint : A) A.basepoint

  rightConnector : Path
    (connectedSumRightGluingPoint rightCell glue boundaryPoint : B) B.basepoint

  realization : EmbeddedCellConnectedSum leftCell rightCell glue ≃ₜ C

  realization_basepoint : realization
    (connectedSumNeckMidpoint leftCell.boundaryMap rightCell.boundaryMap glue boundaryPoint) =
      C.basepoint


noncomputable def ConnectedSumStep.sourceBasepointEquiv
    {A B C : BasedConnectedClosedSmoothThreeManifold} (s : ConnectedSumStep A B C) :
    fundamentalGroupSourceFreeProduct A.basepoint B.basepoint ≃*
      fundamentalGroupSourceFreeProduct
        (connectedSumLeftGluingPoint s.leftCell s.boundaryPoint : A)
        (connectedSumRightGluingPoint s.rightCell s.glue s.boundaryPoint : B) :=
  coprodIMulEquiv
    (fundamentalGroupSourceFactor A.basepoint B.basepoint)
    (fundamentalGroupSourceFactor
      (connectedSumLeftGluingPoint s.leftCell s.boundaryPoint : A)
      (connectedSumRightGluingPoint s.rightCell s.glue s.boundaryPoint : B)) fun
    | false => DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint s.leftConnector
    | true => DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint s.rightConnector

noncomputable def ConnectedSumStep.realizationFundamentalGroupEquiv
    {A B C : BasedConnectedClosedSmoothThreeManifold} (s : ConnectedSumStep A B C) :
    FundamentalGroup (EmbeddedCellConnectedSum s.leftCell s.rightCell s.glue)
        (connectedSumNeckMidpoint s.leftCell.boundaryMap s.rightCell.boundaryMap
          s.glue s.boundaryPoint) ≃*
      FundamentalGroup C C.basepoint :=
  DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
    s.realization.toHomotopyEquiv
    (connectedSumNeckMidpoint s.leftCell.boundaryMap s.rightCell.boundaryMap
      s.glue s.boundaryPoint)
    C.basepoint s.realization_basepoint

noncomputable def ConnectedSumStep.forwardFundamentalGroupEquiv
    {A B C : BasedConnectedClosedSmoothThreeManifold} (s : ConnectedSumStep A B C) :
    Monoid.Coprod (FundamentalGroup A A.basepoint) (FundamentalGroup B B.basepoint) ≃*
      FundamentalGroup C C.basepoint :=
  (fundamentalGroupSourceFreeProductEquivCoprod A.basepoint B.basepoint).symm.trans <|
    (s.sourceBasepointEquiv.trans <|
      (fundamentalGroupEquiv_connectedSum
        s.leftCell s.rightCell s.glue s.boundaryPoint).trans <|
          s.realizationFundamentalGroupEquiv)


noncomputable def ConnectedSumStep.fundamentalGroupEquiv
    {A B C : BasedConnectedClosedSmoothThreeManifold} (s : ConnectedSumStep A B C) :
    FundamentalGroup C C.basepoint ≃*
      Monoid.Coprod (FundamentalGroup A A.basepoint) (FundamentalGroup B B.basepoint) :=
  s.forwardFundamentalGroupEquiv.symm

noncomputable def ConnectedSumStep.leftFactorHom
    {A B C : BasedConnectedClosedSmoothThreeManifold} (s : ConnectedSumStep A B C) :
    FundamentalGroup A A.basepoint →* FundamentalGroup C C.basepoint :=
  s.realizationFundamentalGroupEquiv.toMonoidHom.comp
    (connectedSumLeftTransportedFactorHom
      s.leftCell s.rightCell s.glue s.boundaryPoint s.leftConnector)

noncomputable def ConnectedSumStep.rightFactorHom
    {A B C : BasedConnectedClosedSmoothThreeManifold} (s : ConnectedSumStep A B C) :
    FundamentalGroup B B.basepoint →* FundamentalGroup C C.basepoint :=
  s.realizationFundamentalGroupEquiv.toMonoidHom.comp
    (connectedSumRightTransportedFactorHom
      s.leftCell s.rightCell s.glue s.boundaryPoint s.rightConnector)


theorem ConnectedSumStep.forwardFundamentalGroupEquiv_comp_inl
    {A B C : BasedConnectedClosedSmoothThreeManifold} (s : ConnectedSumStep A B C) :
    s.forwardFundamentalGroupEquiv.toMonoidHom.comp Monoid.Coprod.inl =
      s.leftFactorHom := by
  ext g
  change
    s.realizationFundamentalGroupEquiv
      ((fundamentalGroupEquiv_connectedSum
        s.leftCell s.rightCell s.glue s.boundaryPoint)
        (Monoid.CoprodI.of (i := false)
          (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint s.leftConnector g))) = _
  have h := DFunLike.congr_fun
    (fundamentalGroupEquiv_connectedSum_comp_left
      s.leftCell s.rightCell s.glue s.boundaryPoint)
    (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint s.leftConnector g)
  change
    (fundamentalGroupEquiv_connectedSum
      s.leftCell s.rightCell s.glue s.boundaryPoint)
        (Monoid.CoprodI.of
          (M := fundamentalGroupSourceFactor
            (connectedSumLeftGluingPoint s.leftCell s.boundaryPoint : A)
            (connectedSumRightGluingPoint s.rightCell s.glue s.boundaryPoint : B))
          (i := false)
          (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint s.leftConnector g)) =
      connectedSumLeftFactorHom s.leftCell s.rightCell s.glue s.boundaryPoint
        (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint s.leftConnector g) at h
  rw [h]
  rfl


theorem ConnectedSumStep.forwardFundamentalGroupEquiv_comp_inr
    {A B C : BasedConnectedClosedSmoothThreeManifold} (s : ConnectedSumStep A B C) :
    s.forwardFundamentalGroupEquiv.toMonoidHom.comp Monoid.Coprod.inr =
      s.rightFactorHom := by
  ext g
  change
    s.realizationFundamentalGroupEquiv
      ((fundamentalGroupEquiv_connectedSum
        s.leftCell s.rightCell s.glue s.boundaryPoint)
        (Monoid.CoprodI.of (i := true)
          (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint s.rightConnector g))) = _
  have h := DFunLike.congr_fun
    (fundamentalGroupEquiv_connectedSum_comp_right
      s.leftCell s.rightCell s.glue s.boundaryPoint)
    (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint s.rightConnector g)
  change
    (fundamentalGroupEquiv_connectedSum
      s.leftCell s.rightCell s.glue s.boundaryPoint)
        (Monoid.CoprodI.of
          (M := fundamentalGroupSourceFactor
            (connectedSumLeftGluingPoint s.leftCell s.boundaryPoint : A)
            (connectedSumRightGluingPoint s.rightCell s.glue s.boundaryPoint : B))
          (i := true)
          (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint s.rightConnector g)) =
      connectedSumRightFactorHom s.leftCell s.rightCell s.glue s.boundaryPoint
        (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint s.rightConnector g) at h
  rw [h]
  rfl

theorem ConnectedSumStep.fundamentalGroupEquiv_comp_leftFactorHom
    {A B C : BasedConnectedClosedSmoothThreeManifold} (s : ConnectedSumStep A B C) :
    s.fundamentalGroupEquiv.toMonoidHom.comp s.leftFactorHom = Monoid.Coprod.inl := by
  ext g
  apply s.forwardFundamentalGroupEquiv.injective
  change s.forwardFundamentalGroupEquiv
      (s.forwardFundamentalGroupEquiv.symm (s.leftFactorHom g)) =
    s.forwardFundamentalGroupEquiv (Monoid.Coprod.inl g)
  rw [s.forwardFundamentalGroupEquiv.apply_symm_apply]
  exact (DFunLike.congr_fun s.forwardFundamentalGroupEquiv_comp_inl g).symm

theorem ConnectedSumStep.fundamentalGroupEquiv_comp_rightFactorHom
    {A B C : BasedConnectedClosedSmoothThreeManifold} (s : ConnectedSumStep A B C) :
    s.fundamentalGroupEquiv.toMonoidHom.comp s.rightFactorHom = Monoid.Coprod.inr := by
  ext g
  apply s.forwardFundamentalGroupEquiv.injective
  change s.forwardFundamentalGroupEquiv
      (s.forwardFundamentalGroupEquiv.symm (s.rightFactorHom g)) =
    s.forwardFundamentalGroupEquiv (Monoid.Coprod.inr g)
  rw [s.forwardFundamentalGroupEquiv.apply_symm_apply]
  exact (DFunLike.congr_fun s.forwardFundamentalGroupEquiv_comp_inr g).symm

inductive LeftAssociatedConnectedSumConstruction :
    (r : ℕ) → BasedConnectedClosedSmoothThreeManifold → Type (u + 1)
  | empty (result : BasedConnectedClosedSmoothThreeManifold)
      (sphereRealization : result ≃ₜ DifferentialGeometry.Topology.SphereThree)
      (sphereRealization_basepoint :
        sphereRealization result.basepoint = DifferentialGeometry.Topology.sphereThreeNorth) :
      LeftAssociatedConnectedSumConstruction 0 result
  | singleton (factor : BasedConnectedClosedSmoothThreeManifold) :
      LeftAssociatedConnectedSumConstruction 1 factor
  | append {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
      (previous : LeftAssociatedConnectedSumConstruction r previousResult)
      (nonempty : 0 < r)
      (factor result : BasedConnectedClosedSmoothThreeManifold)
      (step : ConnectedSumStep previousResult factor result) :
      LeftAssociatedConnectedSumConstruction (r + 1) result

def LeftAssociatedConnectedSumConstruction.factorManifold
    {r : ℕ} {result : BasedConnectedClosedSmoothThreeManifold}
    (c : LeftAssociatedConnectedSumConstruction r result) :
    Fin r → BasedConnectedClosedSmoothThreeManifold :=
  match c with
  | .empty _ _ _ => fun i => Fin.elim0 i
  | .singleton factor => fun _ => factor
  | .append previous _ factor _ _ =>
      Fin.lastCases factor previous.factorManifold

@[simp]
theorem LeftAssociatedConnectedSumConstruction.factorManifold_singleton
    (factor : BasedConnectedClosedSmoothThreeManifold) (i : Fin 1) :
    (LeftAssociatedConnectedSumConstruction.singleton factor).factorManifold i = factor := by
  rfl

@[simp]
theorem LeftAssociatedConnectedSumConstruction.factorManifold_append_castSucc
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) (i : Fin r) :
    (LeftAssociatedConnectedSumConstruction.append previous nonempty factor result step).factorManifold
        (Fin.castSucc i) =
      previous.factorManifold i := by
  simp [LeftAssociatedConnectedSumConstruction.factorManifold]

@[simp]
theorem LeftAssociatedConnectedSumConstruction.factorManifold_append_last
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) :
    (LeftAssociatedConnectedSumConstruction.append previous nonempty factor result step).factorManifold
        (Fin.last r) = factor := by
  simp [LeftAssociatedConnectedSumConstruction.factorManifold]


abbrev LeftAssociatedConnectedSumConstruction.factorFundamentalGroup
    {r : ℕ} {result : BasedConnectedClosedSmoothThreeManifold}
    (c : LeftAssociatedConnectedSumConstruction r result) (i : Fin r) :=
  FundamentalGroup (c.factorManifold i) (c.factorManifold i).basepoint

noncomputable instance LeftAssociatedConnectedSumConstruction.factorFundamentalGroupGroup
    {r : ℕ} {result : BasedConnectedClosedSmoothThreeManifold}
    (c : LeftAssociatedConnectedSumConstruction r result) (i : Fin r) :
    Group (c.factorFundamentalGroup i) := by
  infer_instance


def basedFundamentalGroupEquivOfEq
    {A B : BasedConnectedClosedSmoothThreeManifold} (h : A = B) :
    FundamentalGroup A A.basepoint ≃* FundamentalGroup B B.basepoint := by
  subst B
  exact MulEquiv.refl _

noncomputable def appendCastSuccFactorEquiv
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) (i : Fin r) :
    (LeftAssociatedConnectedSumConstruction.append previous nonempty factor result step).factorFundamentalGroup
        (Fin.castSucc i) ≃*
      previous.factorFundamentalGroup i :=
  basedFundamentalGroupEquivOfEq
    (LeftAssociatedConnectedSumConstruction.factorManifold_append_castSucc
      previous nonempty factor result step i)

noncomputable def appendLastFactorEquiv
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) :
    (LeftAssociatedConnectedSumConstruction.append previous nonempty factor result step).factorFundamentalGroup
        (Fin.last r) ≃*
      FundamentalGroup factor factor.basepoint :=
  basedFundamentalGroupEquivOfEq
    (LeftAssociatedConnectedSumConstruction.factorManifold_append_last
      previous nonempty factor result step)


def factorToSingletonConnectedSumFreeProduct
    (factor : BasedConnectedClosedSmoothThreeManifold) :
    FundamentalGroup factor factor.basepoint →*
      Monoid.CoprodI
        (LeftAssociatedConnectedSumConstruction.singleton factor).factorFundamentalGroup :=
  Monoid.CoprodI.of (M :=
    (LeftAssociatedConnectedSumConstruction.singleton factor).factorFundamentalGroup) (i := 0)


def singletonConnectedSumFreeProductToFactor
    (factor : BasedConnectedClosedSmoothThreeManifold) :
    Monoid.CoprodI
        (LeftAssociatedConnectedSumConstruction.singleton factor).factorFundamentalGroup →*
      FundamentalGroup factor factor.basepoint :=
  Monoid.CoprodI.lift fun _ => MonoidHom.id _

theorem singletonConnectedSumFreeProduct_forward_inverse
    (factor : BasedConnectedClosedSmoothThreeManifold) :
    (singletonConnectedSumFreeProductToFactor factor).comp
        (factorToSingletonConnectedSumFreeProduct factor) =
      MonoidHom.id (FundamentalGroup factor factor.basepoint) := by
  ext g
  rfl

theorem singletonConnectedSumFreeProduct_inverse_forward
    (factor : BasedConnectedClosedSmoothThreeManifold) :
    (factorToSingletonConnectedSumFreeProduct factor).comp
        (singletonConnectedSumFreeProductToFactor factor) =
      MonoidHom.id
        (Monoid.CoprodI
          (LeftAssociatedConnectedSumConstruction.singleton factor).factorFundamentalGroup) := by
  apply Monoid.CoprodI.ext_hom
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  rfl

noncomputable def singletonConnectedSumFundamentalGroupEquiv
    (factor : BasedConnectedClosedSmoothThreeManifold) :
    FundamentalGroup factor factor.basepoint ≃*
      Monoid.CoprodI
        (LeftAssociatedConnectedSumConstruction.singleton factor).factorFundamentalGroup :=
  MonoidHom.toMulEquiv
    (factorToSingletonConnectedSumFreeProduct factor)
    (singletonConnectedSumFreeProductToFactor factor)
    (singletonConnectedSumFreeProduct_forward_inverse factor)
    (singletonConnectedSumFreeProduct_inverse_forward factor)


theorem singletonConnectedSumFundamentalGroupEquiv_apply
    (factor : BasedConnectedClosedSmoothThreeManifold)
    (g : FundamentalGroup factor factor.basepoint) :
    singletonConnectedSumFundamentalGroupEquiv factor g =
      Monoid.CoprodI.of
        (M := (LeftAssociatedConnectedSumConstruction.singleton factor).factorFundamentalGroup)
        (i := 0) g := by
  rfl


def appendFactorFreeProductToCoprod
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) :
    Monoid.CoprodI ((LeftAssociatedConnectedSumConstruction.append
      previous nonempty factor result step).factorFundamentalGroup) →*
      Monoid.Coprod (Monoid.CoprodI previous.factorFundamentalGroup)
        (FundamentalGroup factor factor.basepoint) :=
  Monoid.CoprodI.lift <| Fin.lastCases
    (Monoid.Coprod.inr.comp
      (appendLastFactorEquiv previous nonempty factor result step).toMonoidHom)
    (fun i => Monoid.Coprod.inl.comp <|
      (Monoid.CoprodI.of (M := previous.factorFundamentalGroup) (i := i)).comp
        (appendCastSuccFactorEquiv previous nonempty factor result step i).toMonoidHom)


def coprodToAppendFactorFreeProduct
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) :
    Monoid.Coprod (Monoid.CoprodI previous.factorFundamentalGroup)
        (FundamentalGroup factor factor.basepoint) →*
      Monoid.CoprodI ((LeftAssociatedConnectedSumConstruction.append
        previous nonempty factor result step).factorFundamentalGroup) :=
  Monoid.Coprod.lift
    (Monoid.CoprodI.lift fun i =>
      (Monoid.CoprodI.of
        (M := (LeftAssociatedConnectedSumConstruction.append
          previous nonempty factor result step).factorFundamentalGroup)
        (i := Fin.castSucc i)).comp
          (appendCastSuccFactorEquiv previous nonempty factor result step i).symm.toMonoidHom)
    ((Monoid.CoprodI.of
      (M := (LeftAssociatedConnectedSumConstruction.append
        previous nonempty factor result step).factorFundamentalGroup)
      (i := Fin.last r)).comp
        (appendLastFactorEquiv previous nonempty factor result step).symm.toMonoidHom)

theorem appendFactorFreeProduct_forward_inverse
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) :
    (appendFactorFreeProductToCoprod previous nonempty factor result step).comp
        (coprodToAppendFactorFreeProduct previous nonempty factor result step) =
      MonoidHom.id
        (Monoid.Coprod (Monoid.CoprodI previous.factorFundamentalGroup)
          (FundamentalGroup factor factor.basepoint)) := by
  apply Monoid.Coprod.hom_ext
  · apply Monoid.CoprodI.ext_hom
    intro i
    ext g
    simp [appendFactorFreeProductToCoprod, coprodToAppendFactorFreeProduct]
  · ext g
    simp [appendFactorFreeProductToCoprod, coprodToAppendFactorFreeProduct]

theorem appendFactorFreeProduct_inverse_forward
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) :
    (coprodToAppendFactorFreeProduct previous nonempty factor result step).comp
        (appendFactorFreeProductToCoprod previous nonempty factor result step) =
      MonoidHom.id
        (Monoid.CoprodI ((LeftAssociatedConnectedSumConstruction.append
          previous nonempty factor result step).factorFundamentalGroup)) := by
  apply Monoid.CoprodI.ext_hom
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · ext g
    simp [appendFactorFreeProductToCoprod, coprodToAppendFactorFreeProduct]
  · ext g
    simp [appendFactorFreeProductToCoprod, coprodToAppendFactorFreeProduct]

noncomputable def appendFactorFreeProductEquiv
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) :
    Monoid.CoprodI
        (LeftAssociatedConnectedSumConstruction.append
          previous nonempty factor result step).factorFundamentalGroup ≃*
      Monoid.Coprod (Monoid.CoprodI previous.factorFundamentalGroup)
        (FundamentalGroup factor factor.basepoint) :=
  MonoidHom.toMulEquiv
    (appendFactorFreeProductToCoprod previous nonempty factor result step)
    (coprodToAppendFactorFreeProduct previous nonempty factor result step)
    (appendFactorFreeProduct_inverse_forward previous nonempty factor result step)
    (appendFactorFreeProduct_forward_inverse previous nonempty factor result step)


theorem appendFactorFreeProductEquiv_comp_castSucc
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) (i : Fin r) :
    (appendFactorFreeProductEquiv previous nonempty factor result step).toMonoidHom.comp
        (Monoid.CoprodI.of
          (M := (LeftAssociatedConnectedSumConstruction.append
            previous nonempty factor result step).factorFundamentalGroup)
          (i := Fin.castSucc i)) =
      Monoid.Coprod.inl.comp
        ((Monoid.CoprodI.of (M := previous.factorFundamentalGroup) (i := i)).comp
          (appendCastSuccFactorEquiv
            previous nonempty factor result step i).toMonoidHom) := by
  ext g
  simp [appendFactorFreeProductEquiv, appendFactorFreeProductToCoprod]


theorem appendFactorFreeProductEquiv_comp_last
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) :
    (appendFactorFreeProductEquiv previous nonempty factor result step).toMonoidHom.comp
        (Monoid.CoprodI.of
          (M := (LeftAssociatedConnectedSumConstruction.append
            previous nonempty factor result step).factorFundamentalGroup)
          (i := Fin.last r)) =
      Monoid.Coprod.inr.comp
        (appendLastFactorEquiv previous nonempty factor result step).toMonoidHom := by
  ext g
  simp [appendFactorFreeProductEquiv, appendFactorFreeProductToCoprod]

theorem appendFactorFreeProductEquiv_symm_comp_inl_castSucc
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) (i : Fin r) :
    (appendFactorFreeProductEquiv previous nonempty factor result step).symm.toMonoidHom.comp
        (Monoid.Coprod.inl.comp
          ((Monoid.CoprodI.of (M := previous.factorFundamentalGroup) (i := i)).comp
            (appendCastSuccFactorEquiv
              previous nonempty factor result step i).toMonoidHom)) =
      (Monoid.CoprodI.of
        (M := (LeftAssociatedConnectedSumConstruction.append
          previous nonempty factor result step).factorFundamentalGroup)
        (i := Fin.castSucc i)) := by
  ext g
  apply (appendFactorFreeProductEquiv previous nonempty factor result step).injective
  change (appendFactorFreeProductEquiv previous nonempty factor result step)
      ((appendFactorFreeProductEquiv previous nonempty factor result step).symm
        (Monoid.Coprod.inl
          (Monoid.CoprodI.of
            ((appendCastSuccFactorEquiv previous nonempty factor result step i) g)))) =
    (appendFactorFreeProductEquiv previous nonempty factor result step)
      (Monoid.CoprodI.of g)
  rw [(appendFactorFreeProductEquiv previous nonempty factor result step).apply_symm_apply]
  exact (DFunLike.congr_fun
    (appendFactorFreeProductEquiv_comp_castSucc
      previous nonempty factor result step i) g).symm

theorem appendFactorFreeProductEquiv_symm_comp_inr_last
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) :
    (appendFactorFreeProductEquiv previous nonempty factor result step).symm.toMonoidHom.comp
        (Monoid.Coprod.inr.comp
          (appendLastFactorEquiv previous nonempty factor result step).toMonoidHom) =
      (Monoid.CoprodI.of
        (M := (LeftAssociatedConnectedSumConstruction.append
          previous nonempty factor result step).factorFundamentalGroup)
        (i := Fin.last r)) := by
  ext g
  apply (appendFactorFreeProductEquiv previous nonempty factor result step).injective
  change (appendFactorFreeProductEquiv previous nonempty factor result step)
      ((appendFactorFreeProductEquiv previous nonempty factor result step).symm
        (Monoid.Coprod.inr
          ((appendLastFactorEquiv previous nonempty factor result step) g))) =
    (appendFactorFreeProductEquiv previous nonempty factor result step)
      (Monoid.CoprodI.of g)
  rw [(appendFactorFreeProductEquiv previous nonempty factor result step).apply_symm_apply]
  exact (DFunLike.congr_fun
    (appendFactorFreeProductEquiv_comp_last
      previous nonempty factor result step) g).symm

noncomputable def emptyConnectedSumFundamentalGroupEquiv
    (result : BasedConnectedClosedSmoothThreeManifold)
    (sphereRealization : result ≃ₜ DifferentialGeometry.Topology.SphereThree)
    (sphereRealization_basepoint :
      sphereRealization result.basepoint = DifferentialGeometry.Topology.sphereThreeNorth) :
    FundamentalGroup result result.basepoint ≃*
      Monoid.CoprodI
        (LeftAssociatedConnectedSumConstruction.empty result sphereRealization
          sphereRealization_basepoint).factorFundamentalGroup := by
  let sphereEquiv : FundamentalGroup result result.basepoint ≃*
      FundamentalGroup DifferentialGeometry.Topology.SphereThree DifferentialGeometry.Topology.sphereThreeNorth :=
    DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
      sphereRealization.toHomotopyEquiv result.basepoint
        DifferentialGeometry.Topology.sphereThreeNorth sphereRealization_basepoint
  let target := Monoid.CoprodI
    (LeftAssociatedConnectedSumConstruction.empty result sphereRealization
      sphereRealization_basepoint).factorFundamentalGroup
  letI : Subsingleton target :=
    (coprodI_subsingleton_iff _).mpr fun i => Fin.elim0 i
  letI : Unique target :=
    { default := 1
      uniq := fun x => Subsingleton.elim x 1 }
  letI : Unique (FundamentalGroup DifferentialGeometry.Topology.SphereThree
      DifferentialGeometry.Topology.sphereThreeNorth) :=
    { default := 1
      uniq := fun x => Subsingleton.elim x 1 }
  exact sphereEquiv.trans MulEquiv.ofUnique

noncomputable def fundamentalGroupEquiv_finiteConnectedSum :
    {r : ℕ} → {result : BasedConnectedClosedSmoothThreeManifold} →
      (c : LeftAssociatedConnectedSumConstruction r result) →
      FundamentalGroup result result.basepoint ≃*
        Monoid.CoprodI c.factorFundamentalGroup
  | _, _, .empty result sphereRealization sphereRealization_basepoint =>
      emptyConnectedSumFundamentalGroupEquiv
        result sphereRealization sphereRealization_basepoint
  | _, _, .singleton factor => singletonConnectedSumFundamentalGroupEquiv factor
  | _, _, .append previous nonempty factor result step =>
      step.fundamentalGroupEquiv.trans <|
        ((fundamentalGroupEquiv_finiteConnectedSum previous).coprodCongr
          (MulEquiv.refl (FundamentalGroup factor factor.basepoint))).trans <|
            (appendFactorFreeProductEquiv previous nonempty factor result step).symm

noncomputable def LeftAssociatedConnectedSumConstruction.factorToResult :
    {r : ℕ} → {result : BasedConnectedClosedSmoothThreeManifold} →
      (c : LeftAssociatedConnectedSumConstruction r result) →
      (i : Fin r) → c.factorFundamentalGroup i →*
        FundamentalGroup result result.basepoint
  | _, _, .empty _ _ _, i => Fin.elim0 i
  | _, _, .singleton factor, i =>
      (basedFundamentalGroupEquivOfEq
        (LeftAssociatedConnectedSumConstruction.factorManifold_singleton factor i)).toMonoidHom
  | _, _, .append previous nonempty factor result step, i =>
      Fin.lastCases
        (step.rightFactorHom.comp
          (appendLastFactorEquiv previous nonempty factor result step).toMonoidHom)
        (fun j => step.leftFactorHom.comp <|
          (previous.factorToResult j).comp
            (appendCastSuccFactorEquiv
              previous nonempty factor result step j).toMonoidHom)
        i

theorem fundamentalGroupEquiv_finiteConnectedSum_comp_factorToResult :
    {r : ℕ} → {result : BasedConnectedClosedSmoothThreeManifold} →
      (c : LeftAssociatedConnectedSumConstruction r result) → (i : Fin r) →
      (fundamentalGroupEquiv_finiteConnectedSum c).toMonoidHom.comp
          (c.factorToResult i) =
        (Monoid.CoprodI.of : c.factorFundamentalGroup i →*
          Monoid.CoprodI c.factorFundamentalGroup) := by
  intro r result c
  induction c with
  | empty result sphereRealization sphereRealization_basepoint =>
      intro i
      exact Fin.elim0 i
  | singleton factor =>
      intro i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      ext g
      rfl
  | @append r previousResult previous nonempty factor result step ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · ext g
        simp only [fundamentalGroupEquiv_finiteConnectedSum,
          LeftAssociatedConnectedSumConstruction.factorToResult,
          Fin.lastCases_last, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
        change
          (appendFactorFreeProductEquiv previous nonempty factor result step).symm
            (((fundamentalGroupEquiv_finiteConnectedSum previous).coprodCongr
              (MulEquiv.refl (FundamentalGroup factor factor.basepoint)))
                (step.fundamentalGroupEquiv
                  (step.rightFactorHom
                    ((appendLastFactorEquiv
                      previous nonempty factor result step) g)))) =
            Monoid.CoprodI.of g
        have hstep := DFunLike.congr_fun step.fundamentalGroupEquiv_comp_rightFactorHom
          ((appendLastFactorEquiv previous nonempty factor result step) g)
        change step.fundamentalGroupEquiv
            (step.rightFactorHom
              ((appendLastFactorEquiv previous nonempty factor result step) g)) =
          Monoid.Coprod.inr
            ((appendLastFactorEquiv previous nonempty factor result step) g) at hstep
        rw [hstep]
        change
          (appendFactorFreeProductEquiv previous nonempty factor result step).symm
              (Monoid.Coprod.inr
                ((appendLastFactorEquiv previous nonempty factor result step) g)) =
            Monoid.CoprodI.of g
        exact DFunLike.congr_fun
          (appendFactorFreeProductEquiv_symm_comp_inr_last
            previous nonempty factor result step) g
      · ext g
        simp only [fundamentalGroupEquiv_finiteConnectedSum,
          LeftAssociatedConnectedSumConstruction.factorToResult,
          Fin.lastCases_castSucc, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
        change
          (appendFactorFreeProductEquiv previous nonempty factor result step).symm
            (((fundamentalGroupEquiv_finiteConnectedSum previous).coprodCongr
              (MulEquiv.refl (FundamentalGroup factor factor.basepoint)))
                (step.fundamentalGroupEquiv
                  (step.leftFactorHom
                    (previous.factorToResult j
                      ((appendCastSuccFactorEquiv
                        previous nonempty factor result step j) g))))) =
            Monoid.CoprodI.of g
        have hstep := DFunLike.congr_fun step.fundamentalGroupEquiv_comp_leftFactorHom
          (previous.factorToResult j
            ((appendCastSuccFactorEquiv previous nonempty factor result step j) g))
        change step.fundamentalGroupEquiv
            (step.leftFactorHom
              (previous.factorToResult j
                ((appendCastSuccFactorEquiv previous nonempty factor result step j) g))) =
          Monoid.Coprod.inl
            (previous.factorToResult j
              ((appendCastSuccFactorEquiv
                previous nonempty factor result step j) g)) at hstep
        rw [hstep]
        change
          (appendFactorFreeProductEquiv previous nonempty factor result step).symm
            (Monoid.Coprod.inl
              ((fundamentalGroupEquiv_finiteConnectedSum previous)
                (previous.factorToResult j
                  ((appendCastSuccFactorEquiv
                    previous nonempty factor result step j) g)))) =
            Monoid.CoprodI.of g
        have hih := DFunLike.congr_fun (ih j)
          ((appendCastSuccFactorEquiv previous nonempty factor result step j) g)
        change
          (fundamentalGroupEquiv_finiteConnectedSum previous)
              (previous.factorToResult j
                ((appendCastSuccFactorEquiv previous nonempty factor result step j) g)) =
            Monoid.CoprodI.of
              ((appendCastSuccFactorEquiv previous nonempty factor result step j) g) at hih
        rw [hih]
        exact DFunLike.congr_fun
          (appendFactorFreeProductEquiv_symm_comp_inl_castSucc
            previous nonempty factor result step j) g

end DifferentialGeometry.Topology.ThreeManifold
