/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteCollar

/-!
# Exhausting the relative boundary of a locally finite polyhedral manifold

`LocallyFiniteCollar.lean` replaces the ambient frontier of the auxiliary claim of
`ControlledInwardPush.lean` by the relative boundary `K \ interior K`, and proves that the
latter is a *locally* polyhedral closed manifold of one dimension less.  It records that the
triangulated global form is missing and describes it as a `LocallyFinitePieceTower` on
`K \ interior K`.

That global form needs no new definition.  `IsLocallyFinitePolyhedralManifoldWithBoundary` takes
the dimension of its pieces as a parameter independent of the dimension of the charts, so
`IsLocallyFinitePolyhedralManifoldWithBoundary (n := m + 1) m (K \ interior K)` is the tower of
compact polyhedral `m`-dimensional pieces inside the `(m + 1)`-dimensional charted space `X`.
Only pieces which are *closed* `m`-manifolds are unavailable, and they are also the wrong
demand: an exhaustion of a noncompact surface by compact pieces has pieces with boundary.

## Main results

* `isLocallyFinitePolyhedralManifoldWithBoundary_empty`: the empty set carries the structure.
  This is what makes the statement true for an open `K`, whose relative boundary is empty, and
  is recorded separately because the whole statement would be false without it.
* `isLocallyFinitePolyhedralManifoldWithBoundary_sdiff_interior_of_isOpen`: the open case.
* `IsPolyhedralManifoldWithBoundary.isLocallyFinite_sdiff_interior`: the compact case, which
  recovers `IsPolyhedralManifoldWithBoundary.isPolyhedralManifold_frontier`.
* `IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isOpen_inter_eq_of_isCompact`: the
  upgrade of `IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isOpen_inter_eq` from a
  point to a compact subset.  A single stage of the tower works for a whole compact set,
  because the stages increase.
* `IsLocallyFinitePolyhedralManifoldWithBoundary`
  `.exists_isOpen_inter_sdiff_interior_eq_of_isCompact`: the same for the relative boundary,
  with one compact polyhedral `m`-manifold.
* `IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isCompact_exhaustion_sdiff_interior`:
  the stagewise form of the global statement.  The relative boundary is the increasing union of
  compact sets `A i`, each `A (i + 1)` is a neighbourhood of `A i` relative to the relative
  boundary, and each `A i` sits inside a compact polyhedral `m`-manifold which agrees with the
  relative boundary on an open set containing `A i`.

## What remains

The full tower asks for more than `exists_isCompact_exhaustion_sdiff_interior` supplies: each
`A i` has to be enlarged to a compact polyhedral `m`-manifold *with boundary* contained in
`K \ interior K`, and consecutive enlargements have to be presented by simplicial isomorphisms
of subcomplexes (`LocallyFinitePieceTower.embed_isGlueIso` and
`LocallyFinitePieceTower.map_embed`).  The enlargement is a regular neighbourhood of `A i`
inside the stage frontier `S`, small enough to stay in `O`, for which
`exists_isSubdivision_regularNeighborhoodIn_subset_of_isOpen` and
`IsCombinatorialManifoldWithBoundary.derivedNeighborhood` are the tools; the missing step there
is the presentation of `A i` as a subcomplex of a subdivision of the boundary complex of the
stage.  The gluing data is the codimension one analogue of
`PLPiece.exists_manifold_neighborhood_with_core`, which builds only pieces of the dimension of
the ambient charts.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

/-- Two sets which agree on an open set have the same interior there.

`LocallyFiniteCollar.lean` proves this for its own use under a private name; the statement is
needed here as well, and is elementary enough that duplicating the proof is cheaper than
exposing the private one. -/
theorem inter_interior_eq_inter_interior_of_inter_eq {Y : Type*} [TopologicalSpace Y]
    {O A B : Set Y} (hO : IsOpen O) (h : O ∩ A = O ∩ B) :
    O ∩ interior A = O ∩ interior B := by
  have key : ∀ C D : Set Y, O ∩ C = O ∩ D → O ∩ interior C ⊆ O ∩ interior D := by
    intro C D hCD
    refine subset_inter inter_subset_left (interior_maximal ?_ (hO.inter isOpen_interior))
    intro y hy
    have hyC : y ∈ O ∩ C := ⟨hy.1, interior_subset hy.2⟩
    rw [hCD] at hyC
    exact hyC.2
  exact Subset.antisymm (key A B h) (key B A h.symm)

/-- The empty complex is a combinatorial manifold with boundary of every dimension.

There is no vertex, so both branches of the definition are vacuous. -/
theorem isCombinatorialManifoldWithBoundary_bot {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (m : ℕ) :
    IsCombinatorialManifoldWithBoundary m (⊥ : Geometry.SimplicialComplex ℝ E) := by
  cases m with
  | zero => exact fun _ hv => False.elim hv
  | succ k => exact fun _ hv => False.elim hv

section Empty

variable {n m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [Nonempty X]

/-- **The empty set is a locally finite polyhedral manifold with boundary of every dimension.**

The witness is the empty piece `PLPieceIn.empty`, whose complex is `⊥`.  This is the degenerate
end of the exhaustion statement for a relative boundary, and it is the reason the statement can
hold for an open set at all: the relative boundary of an open set is empty, while a tower with
no stage at all would not satisfy `LocallyFinitePieceTower.iUnion_eq`. -/
theorem isLocallyFinitePolyhedralManifoldWithBoundary_empty :
    IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) m (∅ : Set X) := by
  refine (isPolyhedralManifoldWithBoundary_of_pieceIn
    (PLPieceIn.empty (n := n) (X := X) (EuclideanSpace ℝ (Fin 0))) ?_).isLocallyFinite
  exact isCombinatorialManifoldWithBoundary_bot m

/-- **The relative boundary of an open set is a locally finite polyhedral manifold with
boundary of every dimension**, because it is empty.

`isLocallyFinitePolyhedralManifoldWithBoundary_of_isOpen` makes every open set a locally finite
polyhedral manifold with boundary, so this is the extreme case of the exhaustion statement for
a relative boundary, and the case which forces the empty set to be admissible. -/
theorem isLocallyFinitePolyhedralManifoldWithBoundary_sdiff_interior_of_isOpen {K : Set X}
    (hK : IsOpen K) :
    IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) m (K \ interior K) := by
  rw [hK.interior_eq, Set.sdiff_self]
  exact isLocallyFinitePolyhedralManifoldWithBoundary_empty

end Empty

section Tower

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {U : Set X}

/-- A stage of a locally finite piece tower lies in the interior of the next stage together
with the complement of the carrier.

This is the open set through which a stage is a relative neighbourhood of its predecessor: it
meets the carrier exactly inside the next stage.  The argument occurs inside the proof of
`LocallyFinitePieceTower.exists_core_of_isCompact`; it is isolated here because the open set
itself, and not only the resulting index, is what a compact set needs. -/
theorem LocallyFinitePieceTower.subset_interior_union_compl (T : LocallyFinitePieceTower n X U)
    (i : ℕ) : T.N i ⊆ interior (T.N (i + 1) ∪ Uᶜ) := by
  intro x hx
  obtain ⟨V, hV, hVN⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (T.subset_nhdsWithin i x hx)
  apply mem_interior_iff_mem_nhds.mpr
  refine Filter.mem_of_superset hV fun y hy => ?_
  by_cases hyU : y ∈ U
  · exact Or.inl (hVN ⟨hy, hyU⟩)
  · exact Or.inr hyU

end Tower

section Frontier

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X]

namespace IsPolyhedralManifoldWithBoundary

/-- **The relative boundary of a compact polyhedral manifold with boundary is a locally finite
polyhedral manifold with boundary of one dimension less.**

This is the compact case of the exhaustion statement for a relative boundary.  A compact set is
closed, so its relative boundary is its frontier, which is a compact polyhedral `m`-manifold by
`IsPolyhedralManifoldWithBoundary.isPolyhedralManifold_frontier`, hence a locally finite one
with the one-stage tower `LocallyFinitePieceTower.ofPiece`. -/
theorem isLocallyFinite_sdiff_interior {K : Set X}
    (hK : IsPolyhedralManifoldWithBoundary (n := m + 1) (m + 1) K) :
    IsLocallyFinitePolyhedralManifoldWithBoundary (n := m + 1) m (K \ interior K) := by
  have hcl : IsClosed K := hK.isCompact.isClosed
  rw [← hcl.frontier_eq]
  exact hK.isPolyhedralManifold_frontier.isPolyhedralManifoldWithBoundary.isLocallyFinite

end IsPolyhedralManifoldWithBoundary

namespace IsLocallyFinitePolyhedralManifoldWithBoundary

omit [T2Space X] in
/-- **A locally finite polyhedral manifold with boundary agrees, on an open set containing any
prescribed compact subset, with one compact stage of its presenting tower.**

`IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isOpen_inter_eq` is the case of a single
point.  No finite subcover is needed to pass to a compact set: the stages increase, so the
index supplied by `LocallyFinitePieceTower.exists_core_of_isCompact` already dominates the
whole compact set, and the open set is the one of
`LocallyFinitePieceTower.subset_interior_union_compl`. -/
theorem exists_isOpen_inter_eq_of_isCompact {K : Set X}
    (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := m + 1) (m + 1) K) {C : Set X}
    (hC : IsCompact C) (hCK : C ⊆ K) :
    ∃ O : Set X, IsOpen O ∧ C ⊆ O ∧ ∃ P : Set X,
      IsPolyhedralManifoldWithBoundary (n := m + 1) (m + 1) P ∧ P ⊆ K ∧ O ∩ K = O ∩ P := by
  obtain ⟨T, hT⟩ := hK
  obtain ⟨j, hj⟩ := T.exists_core_of_isCompact hC hCK
  refine ⟨interior (T.N (j + 1) ∪ Kᶜ), isOpen_interior, ?_, T.N (j + 1),
    ⟨T.piece (j + 1), hT (j + 1)⟩, T.subset (j + 1), ?_⟩
  · intro x hx
    exact T.subset_interior_union_compl j (T.core_space_subset j (hj hx))
  · refine Subset.antisymm (fun y hy => ⟨hy.1, ?_⟩) fun y hy => ⟨hy.1, T.subset (j + 1) hy.2⟩
    rcases interior_subset hy.1 with h | h
    · exact h
    · exact absurd hy.2 h

/-- **The relative boundary of a locally finite polyhedral manifold with boundary agrees, on an
open set containing any prescribed compact subset, with one compact polyhedral manifold of one
dimension less.**

This is `IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isOpen_inter_sdiff_interior_eq`
with the point replaced by a compact set, and it is what a regular neighbourhood argument inside
the relative boundary consumes: the compact polyhedral `m`-manifold is the frontier of the
stage, and it agrees with `K \ interior K` throughout `O`. -/
theorem exists_isOpen_inter_sdiff_interior_eq_of_isCompact {K : Set X}
    (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := m + 1) (m + 1) K) {C : Set X}
    (hC : IsCompact C) (hCK : C ⊆ K) :
    ∃ O : Set X, IsOpen O ∧ C ⊆ O ∧ ∃ S : Set X, IsPolyhedralManifold (n := m + 1) m S ∧
      O ∩ (K \ interior K) = O ∩ S := by
  obtain ⟨O, hO, hCO, P, hP, -, hOP⟩ := hK.exists_isOpen_inter_eq_of_isCompact hC hCK
  refine ⟨O, hO, hCO, frontier P, hP.isPolyhedralManifold_frontier, ?_⟩
  have hint := inter_interior_eq_inter_interior_of_inter_eq hO hOP
  have hKP : ∀ y ∈ O, (y ∈ K ↔ y ∈ P) := fun y hy =>
    ⟨fun hyK => (hOP.subset ⟨hy, hyK⟩).2, fun hyP => (hOP.symm.subset ⟨hy, hyP⟩).2⟩
  have hIP : ∀ y ∈ O, (y ∈ interior K ↔ y ∈ interior P) := fun y hy =>
    ⟨fun hyK => (hint.subset ⟨hy, hyK⟩).2, fun hyP => (hint.symm.subset ⟨hy, hyP⟩).2⟩
  rw [hP.isCompact.isClosed.frontier_eq]
  ext y
  simp only [mem_inter_iff, Set.mem_sdiff]
  constructor
  · rintro ⟨hyO, hyK, hyni⟩
    exact ⟨hyO, (hKP y hyO).mp hyK, fun hyi => hyni ((hIP y hyO).mpr hyi)⟩
  · rintro ⟨hyO, hyP, hyni⟩
    exact ⟨hyO, (hKP y hyO).mpr hyP, fun hyi => hyni ((hIP y hyO).mp hyi)⟩

/-- **The relative boundary of a locally finite polyhedral manifold with boundary is exhausted
by compact sets, each contained in a compact polyhedral manifold of one dimension less.**

This is the stagewise form of the tower asked for in `LocallyFiniteCollar.lean`.  The stages
are `A i = T.N i \ interior K` for a presenting tower `T`: they increase, they are compact, they
cover `K \ interior K`, and `A (i + 1)` is a neighbourhood of every point of `A i` relative to
`K \ interior K`, which is `LocallyFinitePieceTower.subset_nhdsWithin` for the carrier
`K \ interior K`.  Each `A i` lies in a compact polyhedral `m`-manifold `S` agreeing with
`K \ interior K` on an open set containing `A i`.

What a `LocallyFinitePieceTower` additionally requires is that the stages themselves be
polyhedral `m`-manifolds with boundary and that consecutive ones be glued by simplicial
isomorphisms; the sets `A i` are compact polyhedra but need not be manifolds, so they still
have to be enlarged inside `S` to regular neighbourhoods. -/
theorem exists_isCompact_exhaustion_sdiff_interior {K : Set X}
    (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := m + 1) (m + 1) K) :
    ∃ A : ℕ → Set X, Monotone A ∧ (∀ i, IsCompact (A i)) ∧ ⋃ i, A i = K \ interior K ∧
      (∀ i, ∀ x ∈ A i, A (i + 1) ∈ 𝓝[K \ interior K] x) ∧
        ∀ i, ∃ O : Set X, IsOpen O ∧ A i ⊆ O ∧ ∃ S : Set X,
          IsPolyhedralManifold (n := m + 1) m S ∧ A i ⊆ S ∧
            O ∩ (K \ interior K) = O ∩ S := by
  obtain ⟨T, -⟩ := id hK
  refine ⟨fun i => T.N i \ interior K, fun i j hij => Set.sdiff_subset_sdiff_left (T.monotone hij),
    fun i => (T.isCompact i).diff isOpen_interior, ?_, ?_, ?_⟩
  · ext y
    simp only [mem_iUnion, Set.mem_sdiff]
    constructor
    · rintro ⟨i, hy, hyi⟩
      exact ⟨T.subset i hy, hyi⟩
    · rintro ⟨hy, hyi⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp (T.iUnion_eq.symm ▸ hy)
      exact ⟨i, hi, hyi⟩
  · intro i x hx
    have h1 : T.N (i + 1) ∈ 𝓝[K \ interior K] x :=
      nhdsWithin_mono x Set.sdiff_subset (T.subset_nhdsWithin i x hx.1)
    refine Filter.mem_of_superset (Filter.inter_mem h1 self_mem_nhdsWithin) ?_
    rintro y ⟨hy, -, hyi⟩
    exact ⟨hy, hyi⟩
  · intro i
    obtain ⟨O, hO, hAO, S, hS, hOS⟩ :=
      hK.exists_isOpen_inter_sdiff_interior_eq_of_isCompact
        ((T.isCompact i).diff isOpen_interior) fun y hy => T.subset i hy.1
    exact ⟨O, hO, hAO, S, hS, fun y hy => (hOS.subset ⟨hAO hy, T.subset i hy.1, hy.2⟩).2, hOS⟩

end IsLocallyFinitePolyhedralManifoldWithBoundary

end Frontier

section Witness

/-- **The exhaustion statement at a nondegenerate instance.**

The triangulated three-simplex of `ControlledInwardPush.lean` is a compact polyhedral
three-manifold with boundary whose frontier is nonempty, so its relative boundary is nonempty
and is a locally finite polyhedral two-manifold with boundary.  The conclusion is therefore not
vacuous: it is not satisfied only by the empty relative boundary of an open set, which is what
`isLocallyFinitePolyhedralManifoldWithBoundary_sdiff_interior_of_isOpen` produces. -/
theorem exists_isLocallyFinitePolyhedralManifoldWithBoundary_boundary_nonempty :
    ∃ K : Set (EuclideanSpace ℝ (Fin 3)),
      IsLocallyFinitePolyhedralManifoldWithBoundary (n := 3) 3 K ∧
        (K \ interior K).Nonempty ∧
          IsLocallyFinitePolyhedralManifoldWithBoundary (n := 3) 2 (K \ interior K) := by
  obtain ⟨K, hK, hfr⟩ := exists_isPolyhedralManifoldWithBoundary_frontier_nonempty
  have hcl : IsClosed K := hK.isCompact.isClosed
  refine ⟨K, hK.isLocallyFinite, ?_, hK.isLocallyFinite_sdiff_interior (m := 2)⟩
  rw [← hcl.frontier_eq]
  exact hfr

end Witness

end DifferentialGeometry.Topology.PiecewiseLinear
