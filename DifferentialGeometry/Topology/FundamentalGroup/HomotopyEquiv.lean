/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

set_option autoImplicit false

open CategoryTheory
open scoped ContinuousMap

universe u v

namespace Poincare.Topology

theorem fundamentalGroup_mapOfEq_bijective_of_homotopyEquiv
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) (y : Y) (h : e x = y) :
    Function.Bijective (FundamentalGroup.mapOfEq e.toFun h) := by
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e
  have hmap : Function.Bijective (FundamentalGroup.map e.toFun x) := by
    change Function.Bijective (E.functor.map :
      (FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x) →
        (E.functor.obj (FundamentalGroupoid.mk x) ⟶
          E.functor.obj (FundamentalGroupoid.mk x)))
    exact E.fullyFaithfulFunctor.map_bijective _ _
  have hconj : Function.Bijective
      (eqToIso (congrArg FundamentalGroupoid.mk h)).conj.toMonoidHom :=
    (eqToIso (congrArg FundamentalGroupoid.mk h)).conj.bijective
  exact hconj.comp hmap

noncomputable def fundamentalGroupMulEquivOfHomotopyEquiv
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) (y : Y) (h : e x = y) :
    FundamentalGroup X x ≃* FundamentalGroup Y y :=
  MulEquiv.ofBijective (FundamentalGroup.mapOfEq e.toFun h)
    (fundamentalGroup_mapOfEq_bijective_of_homotopyEquiv e x y h)

theorem fundamentalGroupMulEquivOfHomotopyEquiv_toMonoidHom
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) (y : Y) (h : e x = y) :
    (↑(fundamentalGroupMulEquivOfHomotopyEquiv e x y h) :
      FundamentalGroup X x →* FundamentalGroup Y y) =
        FundamentalGroup.mapOfEq e.toFun h := by
  rfl

end Poincare.Topology
