/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryOfBall
import DifferentialGeometry.Topology.PiecewiseLinear.ControlledInwardPush
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceTowerExistence
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralBallTopology

/-!
# The boundary of a locally finite polyhedral manifold with boundary

`ControlledInwardPush.lean` proves the inward push of Moise 35.2 for a *compact* polyhedral
three-manifold with boundary, and records that the locally finite case needs a collar of the
boundary, proposed there in the form

> for a locally finite polyhedral `n`-manifold with boundary `K` there are an open `V` with
> `frontier K ⊆ V` and a piecewise linear homeomorphism `frontier K × [0,1] ≅ V ∩ K` which is
> the identity on `frontier K × {0}`,

together with the auxiliary claim that `frontier K` is a closed polyhedral `(n-1)`-manifold.

Both are **false as stated**, and for the same reason: `frontier` is the ambient topological
frontier, while `IsLocallyFinitePolyhedralManifoldWithBoundary` is satisfied by every open set
(`isLocallyFinitePolyhedralManifoldWithBoundary_of_isOpen`), whose frontier is disjoint from it
and need not be a surface.  `exists_isLocallyFinitePolyhedralManifoldWithBoundary_frontier_point`
is the witness: `K = {0}ᶜ` in `EuclideanSpace ℝ (Fin 3)` is a locally finite polyhedral
three-manifold with boundary, `frontier K = {0}` is nonempty, disjoint from `K`, and is not a
polyhedral two-manifold.  Since a map into `V ∩ K ⊆ K` cannot be the identity on a set disjoint
from `K`, the displayed collar forces `frontier K = ∅`.

## The correction

The set the inward push has to move is `K \ interior K`, not `frontier K`; these agree exactly
when `K` is closed, and in particular for the compact case already proved.  `K` is open if and
only if `K \ interior K` is empty, so this is the honest rendering of Moise's `Int K`, and
`inter_frontier_eq_sdiff_interior` identifies it with the part of the frontier lying in `K`.

For that set the statement is true and is proved here, in the local sense of a piecewise linear
manifold.  Around each of its points `K` agrees with one compact stage of the presenting tower,
so `K \ interior K` agrees with that stage's frontier, which is a compact closed polyhedral
`(n-1)`-manifold:

* `IsPolyhedralManifoldWithBoundary.isPolyhedralManifold_frontier`: the frontier of a compact
  polyhedral `(m+1)`-manifold with boundary is a closed polyhedral `m`-manifold.
* `IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isOpen_inter_eq`: every point of `K` has
  an open neighbourhood on which `K` coincides with a compact stage.
* `IsLocallyPolyhedralManifold`, the local predicate, with
  `IsPolyhedralManifold.isLocallyPolyhedralManifold` and
  `IsLocallyPolyhedralManifold.not_isolated` showing that it is implied by the compact notion and
  still has content in positive dimension.
* `IsLocallyFinitePolyhedralManifoldWithBoundary.isLocallyPolyhedralManifold_sdiff_interior`:
  `K \ interior K` is a locally polyhedral closed `m`-manifold.  This is the corrected first
  claim, and it is exactly the statement that the frontiers of the stages glue.

## What remains

The *triangulated* global form is not proved here and cannot even be stated in the present
vocabulary: `IsPolyhedralManifold` is compact by construction, since a `PLPiece` carries a
finite complex, so the tree has no notion of a globally triangulated noncompact closed
polyhedral surface.  Supplying one means building a `LocallyFinitePieceTower` on
`K \ interior K`, that is choosing compact subsurfaces exhausting it together with the gluing
isomorphisms between consecutive triangulations; the sets `N i ∩ (K \ interior K)` are compact
polyhedra but need not be surfaces with boundary, so the exhaustion has to be built from regular
neighbourhoods inside the stage frontiers.  After that the collar itself still has to be
assembled, by iterating the collar extension of `SurfaceCollar.lean` over the stages rather than
over the dual cells of one finite surface, and the inward push of `ControlledInwardPush.lean`
then applies verbatim with the constant push height replaced by a positive piecewise affine
function on the relative boundary.

Two ingredients that were expected to help do not.  The compactness in
`IsPolyhedralManifoldWithBoundary.isTwoSided_frontier` is not a removable hypothesis but part of
the definition of its subject, and its proof uses the finiteness of the presenting complex
through a finite closed cover; and `PLPieceIn.exists_bicollar` is likewise available only for a
compact closed surface, and produces a two-sided collar with no control on which side lies
inside `K`, so intersecting it with `K` does not cut out a one-sided collar.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Link

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
/-- A combinatorial manifold of positive dimension has no isolated point: if its carrier is
nonempty then it contains two distinct points.

The link of a vertex is a piecewise linear sphere, hence nonempty, and every point of the link
of `v` lies in a face avoiding `v`. -/
theorem IsCombinatorialManifold.not_subsingleton_space {m : ℕ}
    {L : Geometry.SimplicialComplex ℝ E} (hL : IsCombinatorialManifold (m + 1) L)
    (hne : L.space.Nonempty) : ¬ L.space.Subsingleton := by
  intro hsub
  obtain ⟨q, hq⟩ := hne
  obtain ⟨s, hs, -⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hq
  obtain ⟨v, hv⟩ := L.nonempty_of_mem_faces hs
  have hvspace : v ∈ L.space :=
    L.convexHull_subset_space hs (subset_convexHull ℝ _ hv)
  have hvface : ({v} : Finset E) ∈ L.faces :=
    L.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  obtain ⟨z, hz⟩ := (hL v hvface).nonempty
  obtain ⟨t, ht, -⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hz
  obtain ⟨htne, hvt, htins⟩ := (SimplicialComplex.mem_geometricLink_singleton L v t).mp ht
  obtain ⟨w, hw⟩ := htne
  have hwspace : w ∈ L.space :=
    L.convexHull_subset_space htins (subset_convexHull ℝ _ (Finset.mem_insert_of_mem hw))
  exact hvt (by rw [hsub hvspace hwspace]; exact hw)

open Classical in
/-- A combinatorial manifold of positive dimension has no isolated point: every neighbourhood of
a point of its carrier contains another point of the carrier.

Each point of the carrier is an endpoint of a nondegenerate segment inside the carrier: a point
of a face with a vertex other than itself uses that vertex, and a vertex uses any vertex of a
face of its link, which is nonempty because the link is a piecewise linear sphere. -/
theorem IsCombinatorialManifold.exists_mem_ne_of_mem_nhds {m : ℕ}
    {L : Geometry.SimplicialComplex ℝ E} (hL : IsCombinatorialManifold (m + 1) L) {z : E}
    (hz : z ∈ L.space) {U : Set E} (hU : U ∈ 𝓝 z) : ∃ y ∈ U ∩ L.space, y ≠ z := by
  obtain ⟨u, hune, hseg⟩ : ∃ u : E, u ≠ z ∧ segment ℝ z u ⊆ L.space := by
    obtain ⟨s, hs, hzs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hz
    obtain ⟨v, hv⟩ := L.nonempty_of_mem_faces hs
    by_cases hvz : v = z
    · have hvface : ({v} : Finset E) ∈ L.faces :=
        L.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
      obtain ⟨p, hp⟩ := (hL v hvface).nonempty
      obtain ⟨t, ht, -⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hp
      obtain ⟨htne, hvt, htins⟩ := (SimplicialComplex.mem_geometricLink_singleton L v t).mp ht
      obtain ⟨w, hw⟩ := htne
      have hwv : w ≠ v := fun hwv => hvt (hwv ▸ hw)
      refine ⟨w, by rw [← hvz]; exact hwv, subset_trans ?_ (L.convexHull_subset_space htins)⟩
      refine (convex_convexHull ℝ _).segment_subset ?_ (subset_convexHull ℝ _ (by simp [hw]))
      rw [← hvz]
      exact subset_convexHull ℝ _ (by simp)
    · refine ⟨v, hvz, subset_trans ?_ (L.convexHull_subset_space hs)⟩
      exact (convex_convexHull ℝ _).segment_subset hzs (subset_convexHull ℝ _ hv)
  have hcont : Continuous fun a : ℝ => z + a • (u - z) := by
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hpre : (fun a : ℝ => z + a • (u - z)) ⁻¹' U ∈ 𝓝 (0 : ℝ) := by
    refine hcont.continuousAt.preimage_mem_nhds ?_
    simpa using hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  have hapos : 0 < min (ε / 2) 1 := lt_min (by positivity) one_pos
  have haU : z + min (ε / 2) 1 • (u - z) ∈ U := by
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hapos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨z + min (ε / 2) 1 • (u - z), ⟨haU, hseg ?_⟩, ?_⟩
  · rw [segment_eq_image']
    exact ⟨min (ε / 2) 1, ⟨hapos.le, min_le_right _ _⟩, rfl⟩
  · intro heq
    rcases smul_eq_zero.mp (add_eq_left.mp heq) with hzero | hzero
    · exact hapos.ne' hzero
    · exact hune (by rwa [sub_eq_zero] at hzero)

end Link

section LocalManifold

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

/-- A polyhedral manifold of positive dimension has no isolated point: a nonempty one is not a
subsingleton.

This is the transport of `IsCombinatorialManifold.not_subsingleton_space` along the presenting
piece, whose map is injective on the carrier of the presenting complex. -/
theorem IsPolyhedralManifold.not_subsingleton {k : ℕ} {S : Set X}
    (hS : IsPolyhedralManifold (n := n) (k + 1) S) (hne : S.Nonempty) : ¬ S.Subsingleton := by
  intro hsub
  obtain ⟨T, hT⟩ := hS
  obtain ⟨y, hy⟩ := hne
  obtain ⟨z, hz, -⟩ := T.piece.bijOn.surjOn hy
  refine hT.not_subsingleton_space ⟨z, hz⟩ ?_
  intro u hu v hv
  exact T.piece.bijOn.injOn hu hv (hsub (T.piece.bijOn.mapsTo hu) (T.piece.bijOn.mapsTo hv))

/-- A polyhedral manifold of positive dimension has no isolated point.

This is the transport of `IsCombinatorialManifold.exists_mem_ne_of_mem_nhds` along the
presenting piece; the transport is along a relative neighbourhood, because the presenting map is
continuous only on the carrier of the presenting complex. -/
theorem IsPolyhedralManifold.exists_mem_ne_of_mem_nhds {k : ℕ} {S : Set X}
    (hS : IsPolyhedralManifold (n := n) (k + 1) S) {x : X} (hx : x ∈ S) {U : Set X}
    (hU : U ∈ 𝓝 x) : ∃ y ∈ U ∩ S, y ≠ x := by
  obtain ⟨T, hT⟩ := hS
  obtain ⟨z, hz, hzx⟩ := T.piece.bijOn.surjOn hx
  have hUz : U ∈ 𝓝 (T.piece.map z) := by rw [hzx]; exact hU
  have hpre : T.piece.map ⁻¹' U ∈ 𝓝[T.piece.complex.space] z :=
    (T.piece.continuousOn.continuousWithinAt hz).preimage_mem_nhdsWithin hUz
  obtain ⟨V, hV, hzV, hVsub⟩ := mem_nhdsWithin.mp hpre
  obtain ⟨y, hy, hyz⟩ := hT.exists_mem_ne_of_mem_nhds hz (hV.mem_nhds hzV)
  refine ⟨T.piece.map y, ⟨hVsub ⟨hy.1, hy.2⟩, T.piece.bijOn.mapsTo hy.2⟩, ?_⟩
  intro heq
  exact hyz (T.piece.bijOn.injOn hy.2 hz (heq.trans hzx.symm))

/-- A set is a **locally polyhedral `m`-manifold** when every one of its points has an open
neighbourhood in the ambient space which meets it in the same set as some compact polyhedral
`m`-manifold.

This is the local rendering of a piecewise linear manifold, and it is what a collar argument
consumes.  It is not a competing global hierarchy: `IsPolyhedralManifold` is compact by
construction, since a `PLPiece` carries a finite complex, and the triangulated global notion for
a noncompact carrier would be a `LocallyFinitePieceTower` whose pieces are closed manifolds,
which is not available.  `IsLocallyPolyhedralManifold.not_isolated` records that the predicate
still has geometric content in positive dimension. -/
def IsLocallyPolyhedralManifold (m : ℕ) (S : Set X) : Prop :=
  ∀ x ∈ S, ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ ∃ P : Set X,
    IsPolyhedralManifold (n := n) m P ∧ O ∩ S = O ∩ P

/-- A compact polyhedral manifold is a locally polyhedral manifold, witnessed by the whole
ambient space. -/
theorem IsPolyhedralManifold.isLocallyPolyhedralManifold {m : ℕ} {S : Set X}
    (hS : IsPolyhedralManifold (n := n) m S) : IsLocallyPolyhedralManifold (n := n) m S :=
  fun x _ => ⟨univ, isOpen_univ, mem_univ x, S, hS, rfl⟩

/-- A locally polyhedral manifold of positive dimension has no isolated point.

In particular a nonempty one is infinite, so a single point is not a locally polyhedral manifold
of positive dimension. -/
theorem IsLocallyPolyhedralManifold.not_isolated {k : ℕ} {S : Set X}
    (hS : IsLocallyPolyhedralManifold (n := n) (k + 1) S) {x : X} (hx : x ∈ S) {U : Set X}
    (hU : U ∈ 𝓝 x) : ∃ y ∈ U ∩ S, y ≠ x := by
  obtain ⟨O, hO, hxO, P, hP, heq⟩ := hS x hx
  have hxP : x ∈ P := (heq.subset ⟨hxO, hx⟩).2
  obtain ⟨y, hy, hyx⟩ :=
    hP.exists_mem_ne_of_mem_nhds hxP (Filter.inter_mem hU (hO.mem_nhds hxO))
  exact ⟨y, ⟨hy.1.1, (heq.symm.subset ⟨hy.1.2, hy.2⟩).2⟩, hyx⟩

end LocalManifold

section RelativeBoundary

/-- The part of the frontier of a set which belongs to the set is the set minus its interior.

For a closed set the two frontiers agree; in general it is the right-hand side that measures how
far a set is from being open. -/
theorem inter_frontier_eq_sdiff_interior {Y : Type*} [TopologicalSpace Y] (K : Set Y) :
    K ∩ frontier K = K \ interior K := by
  ext y
  constructor
  · rintro ⟨hy, -, hyi⟩
    exact ⟨hy, hyi⟩
  · rintro ⟨hy, hyi⟩
    exact ⟨hy, subset_closure hy, hyi⟩

/-- Two sets which agree on an open set have the same interior there.

Interiors are local, so the equality on `O` of the sets transfers to their interiors. -/
private theorem inter_interior_eq_of_inter_eq {Y : Type*} [TopologicalSpace Y] {O A B : Set Y}
    (hO : IsOpen O) (h : O ∩ A = O ∩ B) : O ∩ interior A = O ∩ interior B := by
  have key : ∀ C D : Set Y, O ∩ C = O ∩ D → O ∩ interior C ⊆ O ∩ interior D := by
    intro C D hCD
    refine subset_inter inter_subset_left (interior_maximal ?_ (hO.inter isOpen_interior))
    intro y hy
    have hyC : y ∈ O ∩ C := ⟨hy.1, interior_subset hy.2⟩
    rw [hCD] at hyC
    exact hyC.2
  exact Subset.antisymm (key A B h) (key B A h.symm)

end RelativeBoundary

section Frontier

variable {m : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X]

open Classical in
/-- **The frontier of a compact polyhedral manifold with boundary is a closed polyhedral
manifold of one dimension less.**

The presenting piece restricted to the boundary complex presents the frontier, and the boundary
complex of a combinatorial manifold with boundary is a combinatorial manifold. -/
theorem IsPolyhedralManifoldWithBoundary.isPolyhedralManifold_frontier {P : Set X}
    (hP : IsPolyhedralManifoldWithBoundary (n := m + 1) (m + 1) P) :
    IsPolyhedralManifold (n := m + 1) m (frontier P) := by
  classical
  obtain ⟨T, hT⟩ := hP
  let _ : DecidableEq (EuclideanSpace ℝ (Fin T.ambientDim)) := Classical.decEq _
  have _ : Finite T.piece.complex.faces := T.piece.finite_faces.to_subtype
  rw [T.piece.frontier_eq_image_boundaryComplex hT]
  refine isPolyhedralManifold_of_pieceIn
    (T.piece.restrict (boundaryComplex (m + 1) T.piece.complex)
      (boundaryComplex_faces_subset (m + 1) T.piece.complex)) ?_
  simpa only [PLPieceIn.restrict_complex] using
    isCombinatorialManifold_boundaryComplex T.piece.complex hT

omit [T2Space X] in
/-- **A locally finite polyhedral manifold with boundary agrees, near each of its points, with
one compact stage of its presenting tower.**

The stage is `N (i + 1)` for any `i` with `x ∈ N i`: the tower makes `N (i + 1)` a neighbourhood
of `x` relative to `K`, and it is contained in `K`. -/
theorem IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isOpen_inter_eq {K : Set X}
    (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := m + 1) (m + 1) K) {x : X}
    (hx : x ∈ K) :
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ ∃ P : Set X,
      IsPolyhedralManifoldWithBoundary (n := m + 1) (m + 1) P ∧ P ⊆ K ∧
        O ∩ K = O ∩ P := by
  obtain ⟨T, hT⟩ := hK
  have hxU : x ∈ ⋃ i, T.N i := by rw [T.iUnion_eq]; exact hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxU
  obtain ⟨O, hO, hxO, hOsub⟩ := mem_nhdsWithin.mp (T.subset_nhdsWithin i x hi)
  refine ⟨O, hO, hxO, T.N (i + 1), ⟨T.piece (i + 1), hT (i + 1)⟩, T.subset (i + 1), ?_⟩
  exact Subset.antisymm (fun y hy => ⟨hy.1, hOsub hy⟩)
    (fun y hy => ⟨hy.1, T.subset (i + 1) hy.2⟩)

/-- **The relative boundary of a locally finite polyhedral manifold with boundary is locally a
compact closed polyhedral manifold of one dimension less.**

This is the corrected form of the auxiliary claim of `ControlledInwardPush.lean`, with the
ambient frontier replaced by `K \ interior K`.  Near a point of `K` the manifold coincides with
one compact stage, hence so do their interiors, hence so do `K \ interior K` and the frontier of
that stage. -/
theorem IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isOpen_inter_sdiff_interior_eq
    {K : Set X} (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := m + 1) (m + 1) K)
    {x : X} (hx : x ∈ K) :
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ ∃ S : Set X, IsPolyhedralManifold (n := m + 1) m S ∧
      O ∩ (K \ interior K) = O ∩ S := by
  obtain ⟨O, hO, hxO, P, hP, -, hOP⟩ := hK.exists_isOpen_inter_eq hx
  refine ⟨O, hO, hxO, frontier P, hP.isPolyhedralManifold_frontier, ?_⟩
  have hint := inter_interior_eq_of_inter_eq hO hOP
  have hKP : ∀ y ∈ O, (y ∈ K ↔ y ∈ P) := fun y hy =>
    ⟨fun hyK => (hOP.subset ⟨hy, hyK⟩).2, fun hyP => (hOP.symm.subset ⟨hy, hyP⟩).2⟩
  have hIP : ∀ y ∈ O, (y ∈ interior K ↔ y ∈ interior P) := fun y hy =>
    ⟨fun hyK => (hint.subset ⟨hy, hyK⟩).2, fun hyP => (hint.symm.subset ⟨hy, hyP⟩).2⟩
  rw [hP.isCompact.isClosed.frontier_eq]
  ext y
  simp only [mem_inter_iff, mem_sdiff]
  constructor
  · rintro ⟨hyO, hyK, hyni⟩
    exact ⟨hyO, (hKP y hyO).mp hyK, fun hyi => hyni ((hIP y hyO).mpr hyi)⟩
  · rintro ⟨hyO, hyP, hyni⟩
    exact ⟨hyO, (hKP y hyO).mpr hyP, fun hyi => hyni ((hIP y hyO).mp hyi)⟩

/-- **The relative boundary of a locally finite polyhedral manifold with boundary is a locally
polyhedral closed manifold of one dimension less.**

This is the corrected global form of the auxiliary claim of `ControlledInwardPush.lean`: the
ambient frontier is replaced by `K \ interior K`, which is Moise's `K ∖ Int K`, and the global
closed polyhedral manifold is taken in the local sense, the triangulated one not being available
for a noncompact carrier.  The content is that the frontiers of the stages glue, and they do
because near each point the manifold *is* one stage. -/
theorem IsLocallyFinitePolyhedralManifoldWithBoundary.isLocallyPolyhedralManifold_sdiff_interior
    {K : Set X} (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := m + 1) (m + 1) K) :
    IsLocallyPolyhedralManifold (n := m + 1) m (K \ interior K) :=
  fun _ hx => hK.exists_isOpen_inter_sdiff_interior_eq hx.1

end Frontier

section Witnesses

/-- **The local statement at a nondegenerate instance.**

The barycentrically subdivided three-simplex of `ControlledInwardPush.lean` is a compact
polyhedral three-manifold with boundary whose frontier is nonempty, hence a locally finite one
whose relative boundary `K \ interior K` is nonempty and equal to `frontier K`, and that
frontier is a closed polyhedral two-manifold.  So the corrected statement has content at data
which the boundaryless witnesses of `SkeletonReduction.lean` do not exercise. -/
theorem exists_isLocallyFinitePolyhedralManifoldWithBoundary_sdiff_interior_nonempty :
    ∃ K : Set (EuclideanSpace ℝ (Fin 3)),
      IsLocallyFinitePolyhedralManifoldWithBoundary (n := 3) 3 K ∧ (frontier K).Nonempty ∧
        (K \ interior K).Nonempty ∧ frontier K = K \ interior K ∧
        IsPolyhedralManifold (n := 3) 2 (frontier K) ∧
        IsLocallyPolyhedralManifold (n := 3) 2 (K \ interior K) := by
  obtain ⟨K, hK, hfr⟩ := exists_isPolyhedralManifoldWithBoundary_frontier_nonempty
  have hcl : IsClosed K := hK.isCompact.isClosed
  have hlf := hK.isLocallyFinite
  refine ⟨K, hlf, hfr, ?_, hcl.frontier_eq, hK.isPolyhedralManifold_frontier (m := 2),
    hlf.isLocallyPolyhedralManifold_sdiff_interior (m := 2)⟩
  rw [← hcl.frontier_eq]
  exact hfr

/-- **The refutation of the displayed collar and of its auxiliary claim.**

`K = {0}ᶜ` in `EuclideanSpace ℝ (Fin 3)` is open, hence a locally finite polyhedral
three-manifold with boundary, and `frontier K = {0}`.  That frontier is nonempty, so the
witness is not degenerate; it is disjoint from `K`, so no map into `V ∩ K` can restrict to the
identity on it and the proposed collar cannot exist; and it is not a polyhedral two-manifold,
which refutes the auxiliary claim.  The relative boundary `K \ interior K` is empty, which is
why the inward push itself is not refuted by this witness: on an open set the identity already
satisfies it. -/
theorem exists_isLocallyFinitePolyhedralManifoldWithBoundary_frontier_point :
    ∃ K : Set (EuclideanSpace ℝ (Fin 3)),
      IsLocallyFinitePolyhedralManifoldWithBoundary (n := 3) 3 K ∧ (frontier K).Nonempty ∧
        Disjoint (frontier K) K ∧ K \ interior K = ∅ ∧
        ¬ IsPolyhedralManifold (n := 3) 2 (frontier K) ∧
        ¬ IsLocallyPolyhedralManifold (n := 3) 2 (frontier K) := by
  have hint : interior ({0} : Set (EuclideanSpace ℝ (Fin 3))) = ∅ := interior_singleton 0
  have hfr : frontier (({0} : Set (EuclideanSpace ℝ (Fin 3)))ᶜ) = {0} := by
    rw [frontier_compl, isClosed_singleton.frontier_eq, hint, sdiff_empty]
  refine ⟨({0} : Set (EuclideanSpace ℝ (Fin 3)))ᶜ,
    isLocallyFinitePolyhedralManifoldWithBoundary_of_isOpen (m := 2) isOpen_compl_singleton,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr]
    exact singleton_nonempty 0
  · rw [hfr]
    exact disjoint_compl_right
  · rw [isOpen_compl_singleton.interior_eq, sdiff_self]
  · rw [hfr]
    intro h
    exact h.not_subsingleton (singleton_nonempty 0) subsingleton_singleton
  · rw [hfr]
    intro h
    obtain ⟨y, hy, hyne⟩ := h.not_isolated (x := 0) rfl (U := univ) Filter.univ_mem
    exact hyne hy.2

end Witnesses

end DifferentialGeometry.Topology.PiecewiseLinear
