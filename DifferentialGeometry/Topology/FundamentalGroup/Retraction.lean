/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv

open scoped ContinuousMap

namespace DifferentialGeometry.Topology

theorem fundamentalGroup_mapOfEq_leftInverse
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (r : C(Y, X)) (hr : Function.LeftInverse r f) (x₀ : X) :
    Function.LeftInverse (FundamentalGroup.mapOfEq r (hr x₀))
      (FundamentalGroup.map f x₀) := by
  intro p
  rw [FundamentalGroup.mapOfEq_apply]
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
    change Path.Homotopic.Quotient.mk
      (((p.map f.continuous).map r.continuous).cast (hr x₀).symm (hr x₀).symm) =
        Path.Homotopic.Quotient.mk p
    congr 1
    ext t
    exact hr (p t)

theorem injective_fundamentalGroup_map_of_leftInverse
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (r : C(Y, X)) (hr : Function.LeftInverse r f) (x₀ : X) :
    Function.Injective (FundamentalGroup.map f x₀) :=
  (fundamentalGroup_mapOfEq_leftInverse f r hr x₀).injective

theorem bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : Y ≃ₕ X) (f : C(X, Y)) (hf : Function.LeftInverse e f) (x : X) :
    Function.Bijective (FundamentalGroup.map f x) := by
  have hi := fundamentalGroup_mapOfEq_leftInverse f e.toFun hf x
  have he := fundamentalGroup_mapOfEq_bijective_of_homotopyEquiv e (f x) x (hf x)
  refine ⟨hi.injective, ?_⟩
  intro a
  exact ⟨FundamentalGroup.mapOfEq e.toFun (hf x) a, he.1 (hi _)⟩

end DifferentialGeometry.Topology
