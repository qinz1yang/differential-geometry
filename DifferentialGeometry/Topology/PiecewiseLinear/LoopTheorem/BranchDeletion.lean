/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentComplex
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCarrier
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchDescent
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchPreimage

/-!
# Deleting a branch from a normal singular set triangulation

A Lemma 2 surgery at a branch `c` of the singular set of a normal singular two cell `D`
produces a replacement cell whose double point set is
`doublePointSet D D.domain \ hD.singularSet.branchCarrier c`.  Both surgery routes then need
the *same* missing object: a `NormalSingularSetTriangulation` of that smaller set, together
with a bijection of its branches onto the branches of `D` other than `c`.  This file supplies
both, and nothing about it is geometric: it only uses the branch decomposition that
`LoopTheorem.BranchCarrier` already provides.

## The deleted triangulation

`NormalSingularSetTriangulation.deletedBranchComplex T c` is the subcomplex of `T.complex`
carried by `T.complex.space \ (T.branchComplex c).space`.  Because the branch subcomplexes are
compact and pairwise disjoint, that set is a union of connected components of `T.complex.space`,
and `deletedBranchComplex_space_eq_iUnion` identifies it with the union of the spaces of the
branch subcomplexes other than `c` — so the subcomplex really is the full subcomplex on the
vertices lying outside `c.supp`.

Restricting a complex to such a saturated set preserves every local statement: the section
`Saturated restriction` generalises the single component lemmas of
`PiecewiseLinear.ComponentComplex`
from `connectedComponentIn K.space p` to any set `C` such that every preconnected subset of
`K.space` meeting `C` lies in `C`.  The two consequences used here are
`IsCombinatorialManifoldWithBoundary.restrict_of_saturated` and
`boundaryComplex_space_restrict_of_saturated`; the latter is what makes the boundary field of
`NormalSingularSetTriangulation` transport, because the map of the piece is injective on the
space of the complex and so commutes with the intersection and the difference.

`NormalSingularSetTriangulation.deletedBranchTriangulation` assembles this into a triangulation
of `doublePointSet D' D'.domain` for *any* cell `D'` whose double point set is
`doublePointSet D D.domain \ T.branchCarrier c`, over the same boundary set.  In particular
nothing below is vacuous: `nonempty_of_doublePointSet_eq_sdiff_branchCarrier` produces one such
triangulation.

## The branch bijection

The bijection is proved once, for *every* triangulation of the smaller set, not only for the one
built here.  Under `[T2Space M]` a branch carrier is compact, hence closed, and the finitely many
branch carriers are pairwise disjoint, connected and cover the double point set; so they are its
connected components.  Two such decompositions of the same set must therefore match, which is
`exists_equiv_of_isClosed_isConnected_partition`, and
`NormalSingularSetTriangulation.exists_branchEquiv_of_doublePointSet_eq_sdiff` is the instance of
it that the surgeries need.  `NormalSingularCellData.deletedBranchEquiv` and
`NormalSingularCellData.branchCarrier_deletedBranchEquiv` are the two consumer facing terms.

Note that the *equality* of double point sets is essential and the inclusion
`doublePointSet G G.domain ⊆ doublePointSet D D.domain` together with
`Disjoint (doublePointSet G G.domain) (T.branchCarrier c)` is **not** enough: a nonsingular
subdisk of `D` satisfies both and has no branch at all.

## The direct surgery

The last section is the branch bookkeeping of the direct boundary surgery, that is, of
`NormalSingularCellData.exists_boundary_surgery_cell_of_boundaryBranch`.  Writing
`hD.branchPreimage c = A ∪ C` for the two sheets over the branch and `pullback` for the map that
reads the replacement domain inside `D.domain`, the recorded conclusions give
`MapsTo pullback G.domain D.domain`, `InjOn pullback G.domain`, `EqOn (D ∘ pullback) G G.domain`
and `Disjoint (pullback '' G.domain) C`, which bound `pullback '' G.domain ⊆ D.domain \ C`.  The
covering `D.domain \ C ⊆ pullback '' G.domain` is taken here as the explicit hypothesis `hsurj`
of `NormalSingularCellData.doublePointSet_eq_sdiff_of_boundarySurgery`; everything downstream of
it, including the branch bijection, is proved.

**That hypothesis is not satisfied by the direct surgery, and the theorems below are therefore
conditional results without a producer.**  The direct surgery glues the two *outer* cells of
`exists_three_cells_of_boundaryBranch` and discards the middle band: with its notation,
`pullback '' G.domain = D₁.domain ∪ (D₃.domain \ C) = D.domain \ (D₂.domain \ A)`.  Since
`A ⊆ frontier D₂.domain` and `C ⊆ frontier D₂.domain` (`CutAndPaste.lean:1197`), any point of
`interior D₂.domain` — nonempty, as `D₂.domain` is a two ball — lies in `D.domain \ C` and in
neither `D₁.domain` nor `D₃.domain`.  So `hsurj` fails, and with it the conclusion: the direct
surgery loses every branch with a sheet in the interior of the middle band, and admits no
bijection of branches with the complement of `c`.

The descent it does support is an *injection* of branches, which is all that
`NormalSingularSetTriangulation.complexity_lt_of_injective_origin` requires.  The statements
below are kept because they are correct and are the right tool for any surgery that really does
exhaust the complement of the deleted sheet; the cross candidate's resolved cell is one, via
`CrossSeamRegluedData.doublePointSet_cell_eq`.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

/-! ### Connected pieces of a finite closed partition -/

/-- Removing a set from another commutes with taking images along a map that is injective on a
set containing both.  This is the difference companion of `Set.InjOn.image_inter`. -/
theorem image_diff_of_injOn {X Y : Type*} {f : X → Y} {u s t : Set X} (hf : InjOn f u)
    (hs : s ⊆ u) (ht : t ⊆ u) : f '' (s \ t) = f '' s \ f '' t := by
  apply Subset.antisymm
  · rintro _ ⟨x, ⟨hxs, hxt⟩, rfl⟩
    refine ⟨⟨x, hxs, rfl⟩, ?_⟩
    rintro ⟨z, hz, hzx⟩
    exact hxt (hf (ht hz) (hs hxs) hzx ▸ hz)
  · rintro _ ⟨⟨x, hxs, rfl⟩, hx⟩
    exact ⟨x, ⟨hxs, fun hxt => hx ⟨x, hxt, rfl⟩⟩, rfl⟩

/-- A nonempty preconnected set covered by a finite family of pairwise disjoint closed sets lies
inside a single member of the family: the members are relatively clopen in their union. -/
theorem subset_of_isPreconnected_of_iUnion_isClosed {X : Type*} [TopologicalSpace X]
    {β : Type*} [Finite β] {g : β → Set X} (hclosed : ∀ b, IsClosed (g b))
    (hdisjoint : Pairwise fun b b' => Disjoint (g b) (g b')) {A : Set X}
    (hA : IsPreconnected A) (hAne : A.Nonempty) (hAU : A ⊆ ⋃ b, g b) :
    ∃ b, A ⊆ g b := by
  obtain ⟨y, hy⟩ := hAne
  obtain ⟨b, hb⟩ := mem_iUnion.mp (hAU hy)
  refine ⟨b, ?_⟩
  have hrest : IsClosed (⋃ b' ∈ {b' : β | b' ≠ b}, g b') :=
    Set.Finite.isClosed_biUnion (Set.toFinite _) fun b' _ => hclosed b'
  have hcover : A ⊆ g b ∪ ⋃ b' ∈ {b' : β | b' ≠ b}, g b' := by
    intro x hx
    obtain ⟨b', hb'⟩ := mem_iUnion.mp (hAU hx)
    by_cases hbb : b' = b
    · exact Or.inl (hbb ▸ hb')
    · exact Or.inr (mem_biUnion hbb hb')
  have hempty : ¬(A ∩ ⋃ b' ∈ {b' : β | b' ≠ b}, g b').Nonempty := by
    intro hne
    obtain ⟨z, -, hzb, hzrest⟩ :=
      isPreconnected_closed_iff.mp hA _ _ (hclosed b) hrest hcover ⟨y, hy, hb⟩ hne
    obtain ⟨b', hb'ne, hzb'⟩ := mem_iUnion₂.mp hzrest
    exact Set.disjoint_left.mp (hdisjoint hb'ne) hzb' hzb
  intro x hx
  rcases hcover hx with h | h
  · exact h
  · exact absurd ⟨x, hx, h⟩ hempty

/-- **Two closed connected partitions of the same set match.**  If two finite families of
nonempty connected closed sets are pairwise disjoint and have the same union, then their index
types are canonically in bijection, matching the members.  Both families are then the family of
connected components of the common union. -/
theorem exists_equiv_of_isClosed_isConnected_partition {X : Type*} [TopologicalSpace X]
    {α β : Type*} [Finite α] [Finite β] {f : α → Set X} {g : β → Set X}
    (hfconn : ∀ a, IsConnected (f a)) (hgconn : ∀ b, IsConnected (g b))
    (hfclosed : ∀ a, IsClosed (f a)) (hgclosed : ∀ b, IsClosed (g b))
    (hfdisjoint : Pairwise fun a a' => Disjoint (f a) (f a'))
    (hgdisjoint : Pairwise fun b b' => Disjoint (g b) (g b'))
    (hunion : ⋃ a, f a = ⋃ b, g b) :
    ∃ e : α ≃ β, ∀ a, f a = g (e a) := by
  have hfsub : ∀ a, f a ⊆ ⋃ b, g b := by
    intro a
    rw [← hunion]
    exact subset_iUnion f a
  have hgsub : ∀ b, g b ⊆ ⋃ a, f a := by
    intro b
    rw [hunion]
    exact subset_iUnion g b
  have hfg : ∀ a, ∃ b, f a ⊆ g b := fun a =>
    subset_of_isPreconnected_of_iUnion_isClosed hgclosed hgdisjoint (hfconn a).isPreconnected
      (hfconn a).nonempty (hfsub a)
  have hgf : ∀ b, ∃ a, g b ⊆ f a := fun b =>
    subset_of_isPreconnected_of_iUnion_isClosed hfclosed hfdisjoint (hgconn b).isPreconnected
      (hgconn b).nonempty (hgsub b)
  choose F hF using hfg
  choose G hG using hgf
  have hGF : ∀ a, G (F a) = a := by
    intro a
    by_contra hne
    obtain ⟨y, hy⟩ := (hfconn a).nonempty
    exact Set.disjoint_left.mp (hfdisjoint hne) (hG (F a) (hF a hy)) hy
  have hFG : ∀ b, F (G b) = b := by
    intro b
    by_contra hne
    obtain ⟨y, hy⟩ := (hgconn b).nonempty
    exact Set.disjoint_left.mp (hgdisjoint hne) (hF (G b) (hG b hy)) hy
  refine ⟨⟨F, G, hGF, hFG⟩, fun a => Subset.antisymm (hF a) ?_⟩
  have h := hG (F a)
  rw [hGF a] at h
  exact h

/-! ### Saturated restriction -/

section Saturated

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The space of a restriction to a saturated set is that set.  Saturated means that every
preconnected subset of `K.space` meeting `C` already lies in `C`, which for a union of connected
components of `K.space` holds. -/
theorem restrict_space_of_saturated (K : Geometry.SimplicialComplex ℝ E) {C : Set E}
    (hCK : C ⊆ K.space)
    (hsat : ∀ A ⊆ K.space, IsPreconnected A → (A ∩ C).Nonempty → A ⊆ C) :
    (restrict K C).space = C := by
  apply Subset.antisymm (restrict_space_subset K C)
  intro z hz
  obtain ⟨s, hs, hzs⟩ := K.mem_space_iff.mp (hCK hz)
  exact (restrict K C).convexHull_subset_space
    ⟨hs, hsat _ (K.convexHull_subset_space hs) (convex_convexHull ℝ _).isPreconnected
      ⟨z, hzs, hz⟩⟩ hzs

/-- The geometric link of a face meeting a saturated set is unchanged by the restriction. -/
theorem geometricLink_restrict_of_saturated [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) {C : Set E} {v : E} {s : Finset E} (hvs : v ∈ s)
    (hv : v ∈ C) (hsat : ∀ A ⊆ K.space, IsPreconnected A → (A ∩ C).Nonempty → A ⊆ C) :
    SimplicialComplex.geometricLink (restrict K C) s = SimplicialComplex.geometricLink K s := by
  ext t
  simp only [mem_geometricLink_faces_iff, mem_restrict_faces_iff]
  constructor
  · rintro ⟨hne, hdis, ht, -⟩
    exact ⟨hne, hdis, ht⟩
  · rintro ⟨hne, hdis, ht⟩
    exact ⟨hne, hdis, ht, hsat _ (K.convexHull_subset_space ht)
      (convex_convexHull ℝ _).isPreconnected
      ⟨v, subset_convexHull ℝ _ (Finset.mem_union_left t hvs), hv⟩⟩

open Classical in
/-- The vertex form of `geometricLink_restrict_of_saturated`. -/
theorem geometricLink_restrict_singleton_of_saturated (K : Geometry.SimplicialComplex ℝ E)
    {C : Set E} {v : E} (hv : v ∈ C)
    (hsat : ∀ A ⊆ K.space, IsPreconnected A → (A ∩ C).Nonempty → A ⊆ C) :
    SimplicialComplex.geometricLink (restrict K C) {v} =
      SimplicialComplex.geometricLink K {v} :=
  geometricLink_restrict_of_saturated K (Finset.mem_singleton_self v) hv hsat

/-- Restricting a combinatorial manifold with boundary to a saturated set gives a combinatorial
manifold with boundary of the same dimension: every vertex keeps its link. -/
theorem IsCombinatorialManifoldWithBoundary.restrict_of_saturated
    {K : Geometry.SimplicialComplex ℝ E} {n : ℕ} {C : Set E}
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (hsat : ∀ A ⊆ K.space, IsPreconnected A → (A ∩ C).Nonempty → A ⊆ C) :
    IsCombinatorialManifoldWithBoundary n (restrict K C) := by
  classical
  cases n with
  | zero =>
    intro v hv
    rw [geometricLink_restrict_singleton_of_saturated K (hv.2 (by simp)) hsat]
    exact hK v hv.1
  | succ n =>
    intro v hv
    rw [geometricLink_restrict_singleton_of_saturated K (hv.2 (by simp)) hsat]
    exact hK v hv.1

/-- The boundary complex of a restriction to a saturated set is the restriction of the boundary
complex. -/
theorem boundaryComplex_restrict_of_saturated [DecidableEq E] (n : ℕ)
    (K : Geometry.SimplicialComplex ℝ E) {C : Set E}
    (hsat : ∀ A ⊆ K.space, IsPreconnected A → (A ∩ C).Nonempty → A ⊆ C) :
    boundaryComplex n (restrict K C) = restrict (boundaryComplex n K) C := by
  ext s
  constructor
  · rintro ⟨⟨hs, hsc⟩, t, ⟨ht, htc⟩, hst, hcard, hball⟩
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces ht
    rw [geometricLink_restrict_of_saturated K hv (htc (subset_convexHull ℝ _ hv)) hsat] at hball
    exact ⟨⟨hs, t, ht, hst, hcard, hball⟩, hsc⟩
  · rintro ⟨⟨hs, t, ht, hst, hcard, hball⟩, hsc⟩
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
    have hvc := hsc (subset_convexHull ℝ _ hv)
    have htc : convexHull ℝ (t : Set E) ⊆ C :=
      hsat _ (K.convexHull_subset_space ht) (convex_convexHull ℝ _).isPreconnected
        ⟨v, subset_convexHull ℝ _ (hst hv), hvc⟩
    refine ⟨⟨hs, hsc⟩, t, ⟨ht, htc⟩, hst, hcard, ?_⟩
    rwa [geometricLink_restrict_of_saturated K (hst hv) hvc hsat]

/-- The boundary of a restriction to a saturated set is the part of the boundary lying in that
set.  This is the transport statement behind the boundary field of a deleted triangulation. -/
theorem boundaryComplex_space_restrict_of_saturated [DecidableEq E] (n : ℕ)
    (K : Geometry.SimplicialComplex ℝ E) {C : Set E}
    (hsat : ∀ A ⊆ K.space, IsPreconnected A → (A ∩ C).Nonempty → A ⊆ C) :
    (boundaryComplex n (restrict K C)).space = (boundaryComplex n K).space ∩ C := by
  rw [boundaryComplex_restrict_of_saturated n K hsat]
  apply Subset.antisymm
  · exact fun _ hx => ⟨space_mono_of_faces_subset (restrict_faces_subset _ _) hx,
      restrict_space_subset _ _ hx⟩
  · rintro x ⟨hxB, hxC⟩
    obtain ⟨s, hs, hxs⟩ := (boundaryComplex n K).mem_space_iff.mp hxB
    exact (restrict (boundaryComplex n K) C).convexHull_subset_space
      ⟨hs, hsat _ (K.convexHull_subset_space hs.1) (convex_convexHull ℝ _).isPreconnected
        ⟨x, hxs, hxC⟩⟩ hxs

/-- The boundary complex does not depend on the decidability instance used to form it.  This is
needed because a statement written at a concrete type synthesises the genuine instance while a
library statement written at a variable type carries the classical one. -/
theorem boundaryComplex_congr_decidableEq (d d' : DecidableEq E) (n : ℕ)
    (K : Geometry.SimplicialComplex ℝ E) :
    @boundaryComplex E _ _ d n K = @boundaryComplex E _ _ d' n K :=
  congrArg (fun e : DecidableEq E => @boundaryComplex E _ _ e n K) (Subsingleton.elim d d')

end Saturated

namespace NormalSingularSetTriangulation

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D D' : SingularTwoCell M} {BdM BdM' : Set M}

/-! ### The branch subcomplexes are a closed partition -/

/-- A branch subcomplex has finitely many faces, so its space is a compact polyhedron. -/
theorem isCompact_branchComplex_space (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) : IsCompact (T.branchComplex c).space :=
  (T.branchComplex_space_isPolyhedron c).isCompact

/-- A branch subcomplex has closed space. -/
theorem isClosed_branchComplex_space (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) : IsClosed (T.branchComplex c).space :=
  (T.isCompact_branchComplex_space c).isClosed

/-- A nonempty preconnected subset of the singular set lies inside a single branch: the branch
subcomplexes are finitely many, closed, pairwise disjoint and cover. -/
theorem exists_subset_branchComplex_space_of_isPreconnected
    (T : NormalSingularSetTriangulation D BdM)
    {A : Set (EuclideanSpace ℝ (Fin T.piece.ambientDim))} (hA : IsPreconnected A)
    (hAne : A.Nonempty) (hAK : A ⊆ T.complex.space) :
    ∃ b, A ⊆ (T.branchComplex b).space := by
  let _ : Finite T.Branch := T.finite_branch
  refine subset_of_isPreconnected_of_iUnion_isClosed (fun b => T.isClosed_branchComplex_space b)
    T.pairwise_disjoint_branchComplex_space hA hAne ?_
  rw [← T.space_eq_iUnion_branchComplex]
  exact hAK

/-- The complement of one branch inside the singular set is saturated: a preconnected subset of
the singular set that leaves the branch never returns to it. -/
theorem subset_diff_branchComplex_space (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) (A : Set (EuclideanSpace ℝ (Fin T.piece.ambientDim)))
    (hAK : A ⊆ T.complex.space) (hA : IsPreconnected A)
    (hne : (A ∩ (T.complex.space \ (T.branchComplex c).space)).Nonempty) :
    A ⊆ T.complex.space \ (T.branchComplex c).space := by
  obtain ⟨y, hyA, -, hyc⟩ := hne
  obtain ⟨b, hb⟩ := T.exists_subset_branchComplex_space_of_isPreconnected hA ⟨y, hyA⟩ hAK
  have hbc : b ≠ c := fun h => hyc (h ▸ hb hyA)
  exact fun x hx => ⟨hAK hx,
    Set.disjoint_left.mp (T.pairwise_disjoint_branchComplex_space hbc) (hb hx)⟩

/-! ### The deleted subcomplex -/

/-- **The singular set with the branch `c` deleted.**  The subcomplex of `T.complex` carried by
the complement of the branch subcomplex of `c`.  By `deletedBranchComplex_space_eq_iUnion` this
is the full subcomplex on the vertices outside the support of `c`. -/
noncomputable def deletedBranchComplex (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) :
    Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin T.piece.ambientDim)) :=
  restrict T.complex (T.complex.space \ (T.branchComplex c).space)

/-- The faces of the deleted subcomplex are faces of the singular set. -/
theorem deletedBranchComplex_faces_subset (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) : (T.deletedBranchComplex c).faces ⊆ T.complex.faces :=
  restrict_faces_subset T.complex _

/-- The deleted subcomplex has finitely many faces. -/
theorem deletedBranchComplex_faces_finite (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) : (T.deletedBranchComplex c).faces.Finite :=
  T.finite_faces.subset (T.deletedBranchComplex_faces_subset c)

/-- The space of the deleted subcomplex is the singular set minus the branch. -/
theorem deletedBranchComplex_space (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    (T.deletedBranchComplex c).space = T.complex.space \ (T.branchComplex c).space :=
  restrict_space_of_saturated T.complex Set.sdiff_subset (T.subset_diff_branchComplex_space c)

/-- **The space of the deleted subcomplex is the union of the other branches.**  This is the
statement that the deletion is the full subcomplex on the vertices outside the support of `c`. -/
theorem deletedBranchComplex_space_eq_iUnion (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) :
    (T.deletedBranchComplex c).space =
      ⋃ b ∈ {b : T.Branch | b ≠ c}, (T.branchComplex b).space := by
  rw [T.deletedBranchComplex_space]
  apply Subset.antisymm
  · rintro x ⟨hxK, hxc⟩
    rw [T.space_eq_iUnion_branchComplex] at hxK
    obtain ⟨b, hb⟩ := mem_iUnion.mp hxK
    exact mem_biUnion (show b ≠ c from fun h => hxc (h ▸ hb)) hb
  · intro x hx
    obtain ⟨b, hbc, hb⟩ := mem_iUnion₂.mp hx
    exact ⟨T.branchComplex_space_subset b hb,
      Set.disjoint_left.mp (T.pairwise_disjoint_branchComplex_space hbc) hb⟩

/-- The deleted subcomplex is again a combinatorial one manifold with boundary. -/
theorem deletedBranchComplex_isManifoldWithBoundary (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) : IsCombinatorialManifoldWithBoundary 1 (T.deletedBranchComplex c) :=
  T.isManifoldWithBoundary.restrict_of_saturated (T.subset_diff_branchComplex_space c)

/-- The piece of the singular set carries the complement of a branch onto the double point set
with the branch carrier removed. -/
theorem map_complex_space_diff_branchComplex_space (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) :
    T.piece.piece.map '' (T.complex.space \ (T.branchComplex c).space) =
      doublePointSet D D.domain \ T.branchCarrier c := by
  rw [image_diff_of_injOn T.piece.piece.bijOn.injOn
    (space_mono_of_faces_subset T.faces_subset) (T.branchComplex_space_subset_piece c),
    T.map_space]
  rfl

/-- The image of the deleted subcomplex is the double point set with the branch carrier
removed. -/
theorem map_deletedBranchComplex_space (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) :
    T.piece.piece.map '' (T.deletedBranchComplex c).space =
      doublePointSet D D.domain \ T.branchCarrier c := by
  rw [T.deletedBranchComplex_space]
  exact T.map_complex_space_diff_branchComplex_space c

/-- **The boundary relation survives the deletion.**  The image of the boundary of the deleted
subcomplex is the part of the smaller double point set lying on `BdM`.  The argument `d`
quantifies over the decidability instance, so that the statement applies at whichever such
instance a consumer's goal carries. -/
theorem map_boundaryComplex_deletedBranchComplex_space
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch)
    (d : DecidableEq (EuclideanSpace ℝ (Fin T.piece.ambientDim))) :
    T.piece.piece.map '' (@boundaryComplex _ _ _ d 1 (T.deletedBranchComplex c)).space =
      (doublePointSet D D.domain \ T.branchCarrier c) ∩ BdM := by
  have hpiece : T.complex.space ⊆ T.piece.piece.complex.space :=
    space_mono_of_faces_subset T.faces_subset
  have hbdry : (@boundaryComplex _ _ _ d 1 (T.deletedBranchComplex c)).space =
      (@boundaryComplex _ _ _ d 1 T.complex).space ∩
        (T.complex.space \ (T.branchComplex c).space) :=
    @boundaryComplex_space_restrict_of_saturated _ _ _ d 1 T.complex _
      (T.subset_diff_branchComplex_space c)
  have hmap : T.piece.piece.map '' (@boundaryComplex _ _ _ d 1 T.complex).space =
      doublePointSet D D.domain ∩ BdM := by
    have hb := T.map_boundary
    rwa [boundaryComplex_congr_decidableEq (E := EuclideanSpace ℝ (Fin T.piece.ambientDim))
      _ d 1 T.complex] at hb
  rw [hbdry, Set.InjOn.image_inter T.piece.piece.bijOn.injOn
    ((@boundaryComplex_space_subset _ _ _ d 1 T.complex).trans hpiece)
    (Set.sdiff_subset.trans hpiece), hmap, T.map_complex_space_diff_branchComplex_space c]
  ext y
  simp only [mem_inter_iff, mem_sdiff]
  tauto

/-! ### The deleted triangulation -/

/-- **The deleted triangulation.**  Any singular two cell whose double point set is the double
point set of `D` with the carrier of the branch `c` removed is triangulated by the deleted
subcomplex, over the same boundary set `BdM` and through the same piece.  This is the object both
Lemma 2 surgeries need in order to state their normality. -/
noncomputable def deletedBranchTriangulation (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch)
    (hD' : doublePointSet D' D'.domain = doublePointSet D D.domain \ T.branchCarrier c) :
    NormalSingularSetTriangulation D' BdM where
  carrier := T.carrier
  piece := T.piece
  complex := T.deletedBranchComplex c
  finite_faces := T.deletedBranchComplex_faces_finite c
  faces_subset := (T.deletedBranchComplex_faces_subset c).trans T.faces_subset
  isManifoldWithBoundary := T.deletedBranchComplex_isManifoldWithBoundary c
  map_space := by
    rw [hD']
    exact T.map_deletedBranchComplex_space c
  map_boundary := by
    rw [hD']
    exact T.map_boundaryComplex_deletedBranchComplex_space c _

/-- The complex of the deleted triangulation is the deleted subcomplex. -/
theorem deletedBranchTriangulation_complex (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch)
    (hD' : doublePointSet D' D'.domain = doublePointSet D D.domain \ T.branchCarrier c) :
    (T.deletedBranchTriangulation c hD').complex = T.deletedBranchComplex c :=
  rfl

/-- **Non vacuity.**  There really is a normal singular set triangulation of the smaller double
point set, so no statement below is empty. -/
theorem nonempty_of_doublePointSet_eq_sdiff_branchCarrier
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch)
    (hD' : doublePointSet D' D'.domain = doublePointSet D D.domain \ T.branchCarrier c) :
    Nonempty (NormalSingularSetTriangulation D' BdM) :=
  ⟨T.deletedBranchTriangulation c hD'⟩

/-! ### Branch carriers are the connected components of the double point set -/

/-- A branch carrier is compact: it is the continuous image of the compact space of the branch
subcomplex. -/
theorem isCompact_branchCarrier (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    IsCompact (T.branchCarrier c) :=
  (T.isCompact_branchComplex_space c).image_of_continuousOn
    (T.piece.piece.continuousOn.mono (T.branchComplex_space_subset_piece c))

/-- A branch carrier is closed in a Hausdorff manifold. -/
theorem isClosed_branchCarrier [T2Space M] (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) : IsClosed (T.branchCarrier c) :=
  (T.isCompact_branchCarrier c).isClosed

/-- The branch carriers other than `c` cover exactly the double point set with the carrier of `c`
removed. -/
theorem iUnion_branchCarrier_ne (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    ⋃ b : {b : T.Branch // b ≠ c}, T.branchCarrier b.1 =
      doublePointSet D D.domain \ T.branchCarrier c := by
  apply Subset.antisymm
  · refine iUnion_subset ?_
    rintro ⟨b, hbc⟩ y hy
    exact ⟨T.branchCarrier_subset_doublePointSet b hy,
      Set.disjoint_left.mp (T.pairwise_disjoint_branchCarrier hbc) hy⟩
  · rintro y ⟨hy, hyc⟩
    rw [← T.iUnion_branchCarrier] at hy
    obtain ⟨b, hb⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨⟨b, fun h => hyc (h ▸ hb)⟩, hb⟩

/-- **The branch bookkeeping of a branch deletion.**  Any normal singular set triangulation of
the double point set of `D` with the carrier of the branch `c` removed has its branches in
bijection with the branches of `D` other than `c`, matching the branch carriers.

The equality of double point sets is essential: the inclusion together with disjointness from the
carrier of `c` would be satisfied by a nonsingular subdisk, which has no branch at all. -/
theorem exists_branchEquiv_of_doublePointSet_eq_sdiff [T2Space M]
    (T : NormalSingularSetTriangulation D BdM) (S : NormalSingularSetTriangulation D' BdM')
    (c : T.Branch)
    (hD' : doublePointSet D' D'.domain = doublePointSet D D.domain \ T.branchCarrier c) :
    ∃ e : S.Branch ≃ {b : T.Branch // b ≠ c},
      ∀ b, S.branchCarrier b = T.branchCarrier (e b).1 := by
  let _ : Finite T.Branch := T.finite_branch
  let _ : Finite S.Branch := S.finite_branch
  refine exists_equiv_of_isClosed_isConnected_partition
    (f := S.branchCarrier) (g := fun b : {b : T.Branch // b ≠ c} => T.branchCarrier b.1)
    (fun b => S.branchCarrier_isConnected b) (fun b => T.branchCarrier_isConnected b.1)
    (fun b => S.isClosed_branchCarrier b) (fun b => T.isClosed_branchCarrier b.1)
    S.pairwise_disjoint_branchCarrier
    (fun b b' hbb => T.pairwise_disjoint_branchCarrier fun h => hbb (Subtype.ext h)) ?_
  rw [S.iUnion_branchCarrier, T.iUnion_branchCarrier_ne c]
  exact hD'

/-- The branch bijection of `exists_branchEquiv_of_doublePointSet_eq_sdiff` as a term. -/
noncomputable def branchEquivCompl [T2Space M] (T : NormalSingularSetTriangulation D BdM)
    (S : NormalSingularSetTriangulation D' BdM') (c : T.Branch)
    (hD' : doublePointSet D' D'.domain = doublePointSet D D.domain \ T.branchCarrier c) :
    S.Branch ≃ {b : T.Branch // b ≠ c} :=
  (T.exists_branchEquiv_of_doublePointSet_eq_sdiff S c hD').choose

/-- The branch bijection matches branch carriers. -/
theorem branchCarrier_branchEquivCompl [T2Space M] (T : NormalSingularSetTriangulation D BdM)
    (S : NormalSingularSetTriangulation D' BdM') (c : T.Branch)
    (hD' : doublePointSet D' D'.domain = doublePointSet D D.domain \ T.branchCarrier c)
    (b : S.Branch) :
    S.branchCarrier b = T.branchCarrier (T.branchEquivCompl S c hD' b).1 :=
  (T.exists_branchEquiv_of_doublePointSet_eq_sdiff S c hD').choose_spec b

/-- The deleted triangulation has exactly the branches of `T` other than `c`. -/
theorem exists_branchEquiv_deletedBranchTriangulation [T2Space M]
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch)
    (hD' : doublePointSet D' D'.domain = doublePointSet D D.domain \ T.branchCarrier c) :
    ∃ e : (T.deletedBranchTriangulation c hD').Branch ≃ {b : T.Branch // b ≠ c},
      ∀ b, (T.deletedBranchTriangulation c hD').branchCarrier b = T.branchCarrier (e b).1 :=
  T.exists_branchEquiv_of_doublePointSet_eq_sdiff (T.deletedBranchTriangulation c hD') c hD'

end NormalSingularSetTriangulation

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D G : SingularTwoCell M} {BdM B BdM' B' : Set M}

/-! ### The consumer facing branch bijection -/

/-- **The branch bijection for a normal singular cell.**  If the replacement cell `G` has exactly
the double point set of `D` with the carrier of the branch `c` removed, then the branches of its
singular set correspond to the branches of `D` other than `c`, matching branch carriers.  This is
the pair of data consumed by the boundary branch surgeries. -/
theorem exists_singularSet_branchEquiv_of_doublePointSet_eq [T2Space M]
    (hD : NormalSingularCellData D BdM B) (hG : NormalSingularCellData G BdM' B')
    (c : hD.singularSet.Branch)
    (hdp : doublePointSet G G.domain =
      doublePointSet D D.domain \ hD.singularSet.branchCarrier c) :
    ∃ e : hG.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c},
      ∀ b, hG.singularSet.branchCarrier b = hD.singularSet.branchCarrier (e b).1 :=
  hD.singularSet.exists_branchEquiv_of_doublePointSet_eq_sdiff hG.singularSet c hdp

/-- The branch bijection of a branch deletion as a term, in the shape the surgeries consume. -/
noncomputable def deletedBranchEquiv [T2Space M] (hD : NormalSingularCellData D BdM B)
    (hG : NormalSingularCellData G BdM' B') (c : hD.singularSet.Branch)
    (hdp : doublePointSet G G.domain =
      doublePointSet D D.domain \ hD.singularSet.branchCarrier c) :
    hG.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c} :=
  hD.singularSet.branchEquivCompl hG.singularSet c hdp

/-- The branch bijection of a branch deletion matches branch carriers. -/
theorem branchCarrier_deletedBranchEquiv [T2Space M] (hD : NormalSingularCellData D BdM B)
    (hG : NormalSingularCellData G BdM' B') (c : hD.singularSet.Branch)
    (hdp : doublePointSet G G.domain =
      doublePointSet D D.domain \ hD.singularSet.branchCarrier c)
    (b : hG.singularSet.Branch) :
    hG.singularSet.branchCarrier b =
      hD.singularSet.branchCarrier (hD.deletedBranchEquiv hG c hdp b).1 :=
  hD.singularSet.branchCarrier_branchEquivCompl hG.singularSet c hdp b

/-! ### The branch bookkeeping of the direct boundary surgery -/

/-- Both sheets of the branch preimage are carried onto the branch: the second sheet `C` of
`hD.branchPreimage c = A ∪ C` already covers the branch carrier, because the transition `g`
identifies the two sheets over the same points of the manifold. -/
theorem branchCarrier_subset_image_of_isPLHomeomorphOn (hD : NormalSingularCellData D BdM B)
    (c : hD.singularSet.Branch) {A C : Set (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)} (hg : IsPLHomeomorphOn g A C)
    (hcompat : EqOn D (D ∘ g) A) (hcover : hD.branchPreimage c = A ∪ C) :
    hD.singularSet.branchCarrier c ⊆ D '' C := by
  intro y hy
  obtain ⟨x, hx, -, -, -, hxy, -⟩ := hD.singularSet.branchCarrier_subset_doublePointSet c hy
  have hxpre : x ∈ hD.branchPreimage c := ⟨hx, by rw [mem_preimage, hxy]; exact hy⟩
  rw [hcover] at hxpre
  rcases hxpre with hxA | hxC
  · exact ⟨g x, hg.1.mapsTo hxA, ((hcompat hxA).symm.trans hxy : D (g x) = y)⟩
  · exact ⟨x, hxC, hxy⟩

/-- **Deleting one sheet of a branch deletes exactly that branch from the double point set.**
Removing from `D.domain` a set `C` inside the branch preimage which still covers the whole branch
carrier removes precisely the branch carrier from the double point set: every fibre of `D` has at
most two points, so the surviving preimage of a point of the branch is a single point, while a
double point off the branch has neither of its two preimages in `C`. -/
theorem doublePointSet_diff_eq_sdiff_branchCarrier (hD : NormalSingularCellData D BdM B)
    (c : hD.singularSet.Branch) {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hCsub : C ⊆ hD.branchPreimage c)
    (hCcover : hD.singularSet.branchCarrier c ⊆ D '' C) :
    doublePointSet D (D.domain \ C) =
      doublePointSet D D.domain \ hD.singularSet.branchCarrier c := by
  apply Subset.antisymm
  · rintro y ⟨a, ⟨haD, haC⟩, b, ⟨hbD, hbC⟩, hab, hay, hby⟩
    refine ⟨⟨a, haD, b, hbD, hab, hay, hby⟩, ?_⟩
    intro hyc
    obtain ⟨w, hwC, hwy⟩ := hCcover hyc
    have hfiber : ({a, b} : Set (EuclideanSpace ℝ (Fin 2))) = D.domain ∩ D ⁻¹' {y} := by
      refine ((Set.finite_singleton b).insert a).eq_of_subset_of_encard_le ?_ ?_
      · rintro z (rfl | rfl)
        · exact ⟨haD, hay⟩
        · exact ⟨hbD, hby⟩
      · rw [Set.encard_pair hab]
        exact hD.fiber_le_two y
    have hw : w ∈ ({a, b} : Set (EuclideanSpace ℝ (Fin 2))) := by
      rw [hfiber]
      exact ⟨(hCsub hwC).1, hwy⟩
    rcases hw with rfl | rfl
    · exact haC hwC
    · exact hbC hwC
  · rintro y ⟨⟨a, haD, b, hbD, hab, hay, hby⟩, hyc⟩
    have hnot : ∀ z ∈ D.domain, D z = y → z ∉ C := by
      intro z _ hzy hzC
      exact hyc (hzy ▸ (hCsub hzC).2)
    exact ⟨a, ⟨haD, hnot a haD hay⟩, b, ⟨hbD, hnot b hbD hby⟩, hab, hay, hby⟩

/-- Reading the replacement cell inside `D` through an injective pullback does not change the
double point set: it is the double point set of `D` on the image of the pullback. -/
theorem doublePointSet_eq_image_of_pullback {D G : SingularTwoCell M}
    {pullback : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hinj : InjOn pullback G.domain) (heq : EqOn (D ∘ pullback) G G.domain) :
    doublePointSet G G.domain = doublePointSet D (pullback '' G.domain) := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, z, hz, hxz, hGx, hGz⟩
    exact ⟨pullback x, ⟨x, hx, rfl⟩, pullback z, ⟨z, hz, rfl⟩,
      fun h => hxz (hinj hx hz h), (heq hx).trans hGx, (heq hz).trans hGz⟩
  · rintro y ⟨-, ⟨x, hx, rfl⟩, -, ⟨z, hz, rfl⟩, hxz, hDx, hDz⟩
    exact ⟨x, hx, z, hz, fun h => hxz (congrArg pullback h),
      (heq hx).symm.trans hDx, (heq hz).symm.trans hDz⟩

/-- **The double point set of the direct boundary surgery.**  With the notation of
`exists_boundary_surgery_cell_of_boundaryBranch`, where `hD.branchPreimage c = A ∪ C`, the
transition `g` identifies the two sheets over the branch and `pullback` reads the replacement
domain inside `D.domain`, the replacement cell has exactly the double point set of `D` with the
carrier of `c` removed.

The hypothesis `hsurj`, that the pullback image exhausts `D.domain` off the deleted sheet `C`, is
the surjectivity that rules out a replacement which merely has fewer double points, such as a
nonsingular subdisk.  It is **not** among the recorded conclusions of that endpoint, and it is
**false** of it: the direct surgery discards the interior of the middle cell, so its pullback
image is `D.domain \ (D₂.domain \ A)`, strictly smaller than `D.domain \ C`.  See the module
docstring.  This theorem is therefore a correct conditional statement whose producer is some
other surgery, not the direct one. -/
theorem doublePointSet_eq_sdiff_of_boundarySurgery (hD : NormalSingularCellData D BdM B)
    (c : hD.singularSet.Branch) {A C : Set (EuclideanSpace ℝ (Fin 2))}
    {g pullback : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hg : IsPLHomeomorphOn g A C) (hcompat : EqOn D (D ∘ g) A)
    (hcover : hD.branchPreimage c = A ∪ C)
    (hmaps : MapsTo pullback G.domain D.domain) (hinj : InjOn pullback G.domain)
    (heq : EqOn (D ∘ pullback) G G.domain) (hdisj : Disjoint (pullback '' G.domain) C)
    (hsurj : D.domain \ C ⊆ pullback '' G.domain) :
    doublePointSet G G.domain =
      doublePointSet D D.domain \ hD.singularSet.branchCarrier c := by
  have hpull : pullback '' G.domain = D.domain \ C := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨hmaps hx, Set.disjoint_left.mp hdisj ⟨x, hx, rfl⟩⟩
    · exact hsurj
  rw [doublePointSet_eq_image_of_pullback hinj heq, hpull]
  refine hD.doublePointSet_diff_eq_sdiff_branchCarrier c ?_
    (hD.branchCarrier_subset_image_of_isPLHomeomorphOn c hg hcompat hcover)
  rw [hcover]
  exact subset_union_right

/-- **The branch bookkeeping of the direct boundary surgery.**  Under the hypotheses of
`doublePointSet_eq_sdiff_of_boundarySurgery`, any normality data for the replacement cell has its
branches in bijection with the branches of `D` other than `c`, matching branch carriers.  This is
the pair `(e, he)` that the boundary branch descent consumes. -/
theorem exists_branchEquiv_of_boundarySurgery [T2Space M] (hD : NormalSingularCellData D BdM B)
    (hG : NormalSingularCellData G BdM' B') (c : hD.singularSet.Branch)
    {A C : Set (EuclideanSpace ℝ (Fin 2))}
    {g pullback : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hg : IsPLHomeomorphOn g A C) (hcompat : EqOn D (D ∘ g) A)
    (hcover : hD.branchPreimage c = A ∪ C)
    (hmaps : MapsTo pullback G.domain D.domain) (hinj : InjOn pullback G.domain)
    (heq : EqOn (D ∘ pullback) G G.domain) (hdisj : Disjoint (pullback '' G.domain) C)
    (hsurj : D.domain \ C ⊆ pullback '' G.domain) :
    ∃ e : hG.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c},
      ∀ b, hG.singularSet.branchCarrier b = hD.singularSet.branchCarrier (e b).1 :=
  hD.exists_singularSet_branchEquiv_of_doublePointSet_eq hG c
    (hD.doublePointSet_eq_sdiff_of_boundarySurgery c hg hcompat hcover hmaps hinj heq hdisj hsurj)

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
