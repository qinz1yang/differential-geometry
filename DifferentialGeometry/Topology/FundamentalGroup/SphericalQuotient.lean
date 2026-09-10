/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.MetricSpace.IsometricSMul
import DifferentialGeometry.Topology.FundamentalGroup.Sphere

set_option autoImplicit false

universe u v

namespace Poincare.Topology

abbrev MulActionOrbitQuotient (G E : Type*) [Group G] [MulAction G E] :=
  Quotient (MulAction.orbitRel G E)

noncomputable def fundamentalGroupFiniteFreeQuotientEquivOpposite
    {G : Type u} {E : Type v} [Group G] [Finite G]
    [TopologicalSpace E] [T2Space E] [LocallyCompactSpace E]
    [MulAction G E] [ContinuousConstSMul G E] [IsCancelSMul G E]
    [SimplyConnectedSpace E] (e : E) :
    FundamentalGroup (MulActionOrbitQuotient G E)
        (Quotient.mk (MulAction.orbitRel G E) e) ≃* Gᵐᵒᵖ :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.fundamentalGroupEquiv
    (⟨e, rfl⟩ :
      ((Quotient.mk (MulAction.orbitRel G E)) ⁻¹'
        {Quotient.mk (MulAction.orbitRel G E) e}))

noncomputable def fundamentalGroupFiniteFreeQuotientEquiv
    {G : Type u} {E : Type v} [Group G] [Finite G]
    [TopologicalSpace E] [T2Space E] [LocallyCompactSpace E]
    [MulAction G E] [ContinuousConstSMul G E] [IsCancelSMul G E]
    [SimplyConnectedSpace E] (e : E) :
    FundamentalGroup (MulActionOrbitQuotient G E)
        (Quotient.mk (MulAction.orbitRel G E) e) ≃* G :=
  (fundamentalGroupFiniteFreeQuotientEquivOpposite e).trans (MulEquiv.inv' G).symm

noncomputable def fundamentalGroupFiniteFreeSphereThreeQuotientEquiv
    {G : Type u} [Group G] [Finite G]
    [MulAction G SphereThree] [ContinuousConstSMul G SphereThree] [IsCancelSMul G SphereThree] :
    FundamentalGroup (MulActionOrbitQuotient G SphereThree)
        (Quotient.mk (MulAction.orbitRel G SphereThree) sphereThreeNorth) ≃* G :=
  fundamentalGroupFiniteFreeQuotientEquiv sphereThreeNorth

noncomputable def fundamentalGroupFiniteFreeSphereThreeIsometricQuotientEquiv
    {G : Type u} [Group G] [Finite G]
    [MulAction G SphereThree] [IsIsometricSMul G SphereThree] [IsCancelSMul G SphereThree] :
    FundamentalGroup (MulActionOrbitQuotient G SphereThree)
        (Quotient.mk (MulAction.orbitRel G SphereThree) sphereThreeNorth) ≃* G :=
  fundamentalGroupFiniteFreeSphereThreeQuotientEquiv

end Poincare.Topology
