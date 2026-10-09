/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Covering.FundamentalGroup.CoveringSquareConsumers
import DifferentialGeometry.Geometry.Hyperbolic.Truncation
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspSliceTransport

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Hyperbolic

universe u

namespace HyperbolicTruncation

variable {H : FiniteVolumeHyperbolicModel.{u}}

def continuousCuspMap (Tr : HyperbolicTruncation H) (i : Fin Tr.count) :
    C(CuspHalfSpace, H.Carrier) :=
  ⟨Tr.cuspMap i, (Tr.cuspEmbedding i).isEmbedding.continuous⟩

theorem continuousCuspMap_comp_cuspSlice_apply (Tr : HyperbolicTruncation H)
    (i : Fin Tr.count) (r : EuclideanHalfSpace 1) (x : GC.Endpoint.Torus) :
    ((Tr.continuousCuspMap i).comp (cuspSlice r)) x = Tr.cuspMap i (x, r) :=
  rfl

theorem slice_injective_of_depth (Tr : HyperbolicTruncation H) (i : Fin Tr.count)
    (r s : EuclideanHalfSpace 1) (x : GC.Endpoint.Torus)
    (h : Function.Injective
      (FundamentalGroup.map ((Tr.continuousCuspMap i).comp (cuspSlice r)) x)) :
    Function.Injective
      (FundamentalGroup.map ((Tr.continuousCuspMap i).comp (cuspSlice s)) x) :=
  (MonoidHom.ker_eq_bot_iff _).mp
    ((GC.LongTime.cuspSlice_kernel_comp (Tr.continuousCuspMap i) r s x).symm.trans
      ((MonoidHom.ker_eq_bot_iff _).mpr h))

theorem boundaryMap_injective_of_zero_slice (Tr : HyperbolicTruncation H)
    (i : Fin Tr.count) (x : GC.Endpoint.Torus)
    (h : Function.Injective (FundamentalGroup.map
      ((Tr.continuousCuspMap i).comp (cuspSlice GC.Endpoint.halfZero)) x)) :
    Function.Injective (FundamentalGroup.map (Tr.boundary.boundaryMap i) x) :=
  DifferentialGeometry.Topology.injective_fundamentalGroup_map_of_comp_eq
    (Tr.boundary.boundaryMap i) Tr.inclusion
    ((Tr.continuousCuspMap i).comp (cuspSlice GC.Endpoint.halfZero))
    (fun y => (Tr.cusp_zero i y).symm) x h

theorem boundary_incompressible_of_slice_injective (Tr : HyperbolicTruncation H)
    (r : Fin Tr.count → EuclideanHalfSpace 1)
    (h : ∀ i x, Function.Injective
      (FundamentalGroup.map ((Tr.continuousCuspMap i).comp (cuspSlice (r i))) x)) :
    Tr.boundary.incompressible := by
  intro i x
  exact Tr.boundaryMap_injective_of_zero_slice i x
    (Tr.slice_injective_of_depth i (r i) GC.Endpoint.halfZero x (h i x))

theorem slice_injective_of_covering_square (Tr : HyperbolicTruncation H) (i : Fin Tr.count)
    (r : EuclideanHalfSpace 1) {L E : Type*} [TopologicalSpace L] [TopologicalSpace E]
    [SimplyConnectedSpace L] (q : C(L, GC.Endpoint.Torus)) (p : C(E, H.Carrier))
    (j : C(L, E)) (hq : IsCoveringMap q) (hqs : Function.Surjective q)
    (hp : IsCoveringMap p) (comm : ∀ z, p (j z) = Tr.cuspMap i (q z, r))
    (hj : Function.Injective j) (x : GC.Endpoint.Torus) :
    Function.Injective
      (FundamentalGroup.map ((Tr.continuousCuspMap i).comp (cuspSlice r)) x) :=
  DifferentialGeometry.Topology.fundamentalGroup_map_injective_of_covering_square_of_surjective
    q p ((Tr.continuousCuspMap i).comp (cuspSlice r)) j hq hp
    (fun z => (comm z).trans (Tr.continuousCuspMap_comp_cuspSlice_apply i r (q z)).symm)
    hj hqs x

theorem boundary_incompressible_of_covering_square (Tr : HyperbolicTruncation H)
    {L E : Type*} [TopologicalSpace L] [TopologicalSpace E] [SimplyConnectedSpace L]
    (r : Fin Tr.count → EuclideanHalfSpace 1) (q : Fin Tr.count → C(L, GC.Endpoint.Torus))
    (p : Fin Tr.count → C(E, H.Carrier)) (j : Fin Tr.count → C(L, E))
    (hq : ∀ i, IsCoveringMap (q i)) (hqs : ∀ i, Function.Surjective (q i))
    (hp : ∀ i, IsCoveringMap (p i))
    (comm : ∀ i z, p i (j i z) = Tr.cuspMap i (q i z, r i))
    (hj : ∀ i, Function.Injective (j i)) :
    Tr.boundary.incompressible :=
  Tr.boundary_incompressible_of_slice_injective r fun i x =>
    Tr.slice_injective_of_covering_square i (r i) (q i) (p i) (j i) (hq i) (hqs i) (hp i)
      (comm i) (hj i) x

theorem slice_injective_of_covering (Tr : HyperbolicTruncation H) (i : Fin Tr.count)
    (r : EuclideanHalfSpace 1) {E : Type*} [TopologicalSpace E] (p : C(E, H.Carrier))
    (hp : IsCoveringMap p) (S : Set E)
    (hT : p '' S = Set.range ((Tr.continuousCuspMap i).comp (cuspSlice r)))
    (hS : ∀ y : p ⁻¹' Set.range ((Tr.continuousCuspMap i).comp (cuspSlice r)),
      (y : E) ∈ S → SimplyConnectedSpace (connectedComponent y))
    (x : GC.Endpoint.Torus) :
    Function.Injective
      (FundamentalGroup.map ((Tr.continuousCuspMap i).comp (cuspSlice r)) x) :=
  DifferentialGeometry.Topology.injective_fundamentalGroup_map_of_covering_image_eq_range
    p hp S ((Tr.continuousCuspMap i).comp (cuspSlice r))
    ((Tr.cuspEmbedding i).isEmbedding.comp (cuspSlice_isEmbedding r)) hT hS x

theorem boundary_incompressible_of_covering (Tr : HyperbolicTruncation H) {E : Type*}
    [TopologicalSpace E] (p : C(E, H.Carrier)) (hp : IsCoveringMap p)
    (r : Fin Tr.count → EuclideanHalfSpace 1) (S : Fin Tr.count → Set E)
    (hT : ∀ i, p '' S i = Set.range ((Tr.continuousCuspMap i).comp (cuspSlice (r i))))
    (hS : ∀ i (y : p ⁻¹' Set.range ((Tr.continuousCuspMap i).comp (cuspSlice (r i)))),
      (y : E) ∈ S i → SimplyConnectedSpace (connectedComponent y)) :
    Tr.boundary.incompressible :=
  Tr.boundary_incompressible_of_slice_injective r fun i x =>
    Tr.slice_injective_of_covering i (r i) p hp (S i) (hT i) (hS i) x

end HyperbolicTruncation

end DifferentialGeometry.Geometry.Hyperbolic
