/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteBoundaryExhaustion
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteLocalModel

/-!
# The frame of a stage of the inward push

A stage of the inward push of a locally finite polyhedral manifold with boundary `K` moves one
compact piece `A` of the relative boundary `K \ interior K` into `interior K`, fixes a compact
piece `C` of `interior K` already moved by the earlier stages, and is the identity outside a
compact region.  It is built inside a compact local model `P`, a compact polyhedral manifold
with boundary agreeing with `K` on an open set `O`, and then extended by the identity.

This file supplies the two frame statements, both independent of the collar and of the push
formula.

## Choosing the local model

`IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isOpen_inter_eq_of_isCompact` is applied
to `A ∪ C`, not to `A`.  Taking `C` into the compact set is what makes the stage constructible:

* `A ⊆ frontier P`, so the whole of `A` lies on the boundary surface of the model and the push
  height may be made positive there;
* `frontier P ∩ O ⊆ K \ interior K`, so every frontier point of the model inside `O` is a
  genuine boundary point of `K`.  Equivalently the *artificial* frontier of `P`, the part of
  `frontier P` interior to `K`, is disjoint from `O`, hence from the compact `A`; this is the
  room the push height needs in order to vanish near the artificial frontier while staying
  positive on `A`, and it comes from `inter_interior_eq_inter_interior_of_inter_eq`;
* `C ⊆ interior P`, so the preimage of `C` in the presenting complex misses the boundary
  complex.  Without `C` in the compact set this fails: a compact subset of `interior K` may
  meet the artificial frontier of a model chosen for `A` alone, and then it cannot be routed
  through the fixed polyhedron of
  `IsPLHomeomorphOn.exists_piecewiseAffineOn_inward_leftInvOn_taper_fixing_dist_lt`, whose
  hypothesis is disjointness from the collar bottom.

## Extending by the identity

`isPLOn_of_isPLOn_local_of_eqOn_id` pastes a map which is piecewise linear on the model and the
identity off a closed subset of `O` into a map piecewise linear on all of `K`.  Both cases are
local: inside `O` the model computes `IsPLWithinAt`, by
`isPLWithinAt_congr_of_isOpen_inter_eq`; outside `O` the map agrees with the identity on a
neighbourhood, and the identity is piecewise linear on `K` by
`IsLocallyFinitePolyhedralManifoldWithBoundary.isPLOn_id`.  No agreement of the two descriptions
along a seam is needed, because the support is closed and inside `O`.

## Main results

* `IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isOpen_inter_eq_frontier_of_isCompact`:
  the local model of a stage, with its frontier clauses.
* `isPLOn_of_isPLOn_local_of_eqOn_id`: extension of a compactly supported map by the identity.
* `PLPiece.isPLOn_transport`: a piecewise affine self-map of the presenting complex is carried
  to a piecewise linear self-map of the presented set.
* `exists_isPolyhedron_nonneg_piecewiseAffineOn_pos`: the push height of a stage, positive on
  the compact set to be moved and vanishing on a polyhedral neighbourhood of the rest of the
  boundary surface.

## The push height

No new construction is needed for it.  `exists_isPolyhedron_neighborhood` fattens the compact
set `B \ U` into a polyhedron `Z` still missing `A`, and
`IsPolyhedron.exists_nonneg_piecewiseAffine_zero_set` produces a nonnegative piecewise affine
function whose zero set is exactly `Z`.  Vanishing on a *neighbourhood* of `B \ U`, and not
merely on `B \ U`, is what the extension by the identity needs, and it is the clause
`B \ U ⊆ interior Z`.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section LocalModel

variable {m : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X]

/-- **The local model of a stage of the inward push.**

The model `P` is produced for the compact set `A ∪ C`, so that both the piece of the relative
boundary to be moved and the piece of the interior to be fixed lie inside the open set `O` on
which `P` and `K` agree.

Three clauses beyond `O ∩ K = O ∩ P` are recorded.  `A ⊆ frontier P` places the set to be moved
on the boundary surface of the model.  `C ⊆ interior P` places the set to be fixed off that
surface.  `frontier P ∩ O ⊆ K \ interior K` says that the frontier of the model is genuine
throughout `O`, so the artificial frontier of `P` — which a stage push must leave fixed, since
otherwise the push cannot be extended by the identity over `K` — lies outside `O` and therefore
misses `A`.  All three come from `inter_interior_eq_inter_interior_of_inter_eq`. -/
theorem IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isOpen_inter_eq_frontier_of_isCompact
    {K : Set X} (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := m + 1) (m + 1) K)
    {A C : Set X} (hA : IsCompact A) (hC : IsCompact C) (hAK : A ⊆ K \ interior K)
    (hCK : C ⊆ interior K) :
    ∃ O : Set X, IsOpen O ∧ A ⊆ O ∧ C ⊆ O ∧ ∃ P : Set X,
      IsPolyhedralManifoldWithBoundary (n := m + 1) (m + 1) P ∧ P ⊆ K ∧ O ∩ K = O ∩ P ∧
        A ⊆ frontier P ∧ C ⊆ interior P ∧ frontier P ∩ O ⊆ K \ interior K := by
  obtain ⟨O, hO, hACO, P, hP, hPK, hOP⟩ :=
    hK.exists_isOpen_inter_eq_of_isCompact (hA.union hC)
      (union_subset (hAK.trans Set.sdiff_subset) (hCK.trans interior_subset))
  have hAO : A ⊆ O := subset_union_left.trans hACO
  have hCO : C ⊆ O := subset_union_right.trans hACO
  have hint : O ∩ interior K = O ∩ interior P :=
    inter_interior_eq_inter_interior_of_inter_eq hO hOP
  have hPcl : IsClosed P := hP.isCompact.isClosed
  refine ⟨O, hO, hAO, hCO, P, hP, hPK, hOP, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have hxP : x ∈ P := (hOP.subset ⟨hAO hx, (hAK hx).1⟩).2
    rw [hPcl.frontier_eq]
    exact ⟨hxP, fun hxi => (hAK hx).2 (hint.symm.subset ⟨hAO hx, hxi⟩).2⟩
  · exact (hint.subset ⟨hCO hx, hCK hx⟩).2
  · rw [hPcl.frontier_eq] at hx
    refine ⟨(hOP.symm.subset ⟨hx.2, hx.1.1⟩).2, fun hxi => hx.1.2 ?_⟩
    exact (hint.subset ⟨hx.2, hxi⟩).2

omit [T2Space X] in
/-- **Extension of a compactly supported map by the identity.**

The map is piecewise linear on the local model `P` and is the identity off the closed set `S`,
which lies inside the open set `O` carrying the agreement `O ∩ K = O ∩ P`.  Inside `O` the model
computes piecewise linearity at a point; outside `O` the point misses `S`, so the map agrees
with the identity on the relatively open set `K \ S` and the identity is piecewise linear on
`K`.

Neither `P ⊆ K` nor any relation between `S` and `P` is used. -/
theorem isPLOn_of_isPLOn_local_of_eqOn_id {K P O S : Set X} {f : X → X}
    (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := m + 1) (m + 1) K) (hO : IsOpen O)
    (hOP : O ∩ K = O ∩ P) (hS : IsClosed S) (hSO : S ⊆ O)
    (hf : IsPLOn (m + 1) (m + 1) f P) (hid : EqOn f id (K \ S)) :
    IsPLOn (m + 1) (m + 1) f K := by
  refine isPLOn_of_forall_exists_isOpen_inter_eq fun x hx => ?_
  by_cases hxO : x ∈ O
  · exact ⟨O, hO, hxO, P, hOP, hf x (hOP.subset ⟨hxO, hx⟩).2⟩
  · refine ⟨univ, isOpen_univ, mem_univ x, K, rfl, ?_⟩
    have hxS : x ∉ S := fun hmem => hxO (hSO hmem)
    refine piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_eventuallyEq_of_mem
      (hK.isPLOn_id x hx) ?_ hx
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hS.isOpen_compl.mem_nhds hxS)] with z hz hzS
    exact hid ⟨hz, hzS⟩

end LocalModel

section Transport

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

/-- **Transport of a piecewise affine self-map of the presenting complex.**

This is the transport step used by
`IsPolyhedralManifoldWithBoundary.exists_isPLOn_injOn_leftInvOn_dist_lt`, isolated so that a
stage push, which is built in the presenting complex of a local model, can be read as a map of
the model itself. -/
theorem PLPiece.isPLOn_transport {Y : Set X} (T : PLPiece n X Y)
    {F : EuclideanSpace ℝ (Fin T.ambientDim) → EuclideanSpace ℝ (Fin T.ambientDim)}
    (hF : IsPiecewiseAffineOn F T.piece.complex.space)
    (hFmap : MapsTo F T.piece.complex.space T.piece.complex.space) :
    IsPLOn n n
      (fun x => T.piece.map (F (Function.invFunOn T.piece.map T.piece.complex.space x))) Y := by
  refine T.piece.isPLOn_of_eqOn_comp_invFunOn (w := fun y => T.piece.map (F y)) ?_ fun _ _ => rfl
  exact T.piece.isPLOn_comp hF hFmap

end Transport

section Height

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The push height of a stage.**

On the boundary surface `B` of a local model, the height of a stage push has to be positive on
the compact set `A` that the stage moves, and has to vanish on a neighbourhood of the rest of
`B`, which contains the artificial frontier of the model and the parts of the genuine boundary
reserved for the later stages.  The open set `U` is the one carrying the agreement between the
model and the manifold, and `A ⊆ U` is what makes the two demands compatible.

The zero set `Z` is polyhedral and `B \ U` lies in its *interior*, so the push is the identity
on a neighbourhood of `B \ U` and not merely on `B \ U` itself; that is what lets the push be
extended by the identity, through `isPLOn_of_isPLOn_local_of_eqOn_id`. -/
theorem exists_isPolyhedron_nonneg_piecewiseAffineOn_pos {B A U : Set E} (hB : IsPolyhedron B)
    (hA : IsCompact A) (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ Z : Set E, IsPolyhedron Z ∧ B \ U ⊆ interior Z ∧
      ∃ g : E → ℝ, IsPiecewiseAffineOn g univ ∧ (∀ y : E, 0 ≤ g y) ∧
        (∀ y ∈ A, 0 < g y) ∧ ∀ y ∈ Z, g y = 0 := by
  obtain ⟨Z, hZ, hsub, hZA⟩ :=
    exists_isPolyhedron_neighborhood (hB.isCompact.diff hU) hA.isClosed.isOpen_compl
      fun y hy hyA => hy.2 (hAU hyA)
  obtain ⟨g, hgpl, hg0, hgzero⟩ := hZ.exists_nonneg_piecewiseAffine_zero_set
  refine ⟨Z, hZ, hsub, g, hgpl, hg0, fun y hy => ?_, fun y hy => (hgzero y).mpr hy⟩
  exact lt_of_le_of_ne (hg0 y) fun hzero => hZA ((hgzero y).mp hzero.symm) hy

end Height

end DifferentialGeometry.Topology.PiecewiseLinear
