/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalConfiguration
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyPolyhedral

/-!
# Pseudo-cells, tubes and handle decompositions

The definitional layer of Moise, *Geometric topology in dimensions 2 and 3*, Section 32, printed
pages 223 and 228, together with Theorems 32.1-32.4 as named propositions.

`IsPseudoCell Ec Eint Ebd P` is page 223: `Eint` is an open two-cell, `Ebd` a one-sphere,
the two are disjoint, `closure Eint = Eint ∪ Ebd`, `Ec` is their union, the centre `P` lies in
`Eint`, and `Eint \ {P}` is a polyhedron.  The book writes `Int Ec = Eint` and `Bd Ec = Ebd`,
and those are cell notions: they are carried here as named parameters and are never the ambient
`interior` or `frontier` of a planar set.  `IsPseudoCell` deviates from the printed definition
in exactly one way, forced by this tree: the book's "`Eint - P` is a polyhedron" is rendered by
`IsLocallyPolyhedral`, because `IsPolyhedron` of `Polyhedra.lean` is a finite union of
H-polytopes and hence compact, while `Eint \ {P}` is never compact, already for the tame planar
model below.  Nothing else is weakened: `Eint` and `Ebd` carry no piecewise linear structure,
`Ec` is not assumed to be a two-cell, and no local connectedness at `Ebd` is assumed.

`IsTube K N C D Dbd h N'` is the first paragraph of page 223: `K` is a finite one-dimensional
complex, so its faces have at most two vertices and at least one has two, `N` is a
neighbourhood of `|K|` cut by the splitting disks `D e`, with intrinsic
boundaries `Dbd e`, into the dual cells `C v`, one vertex each, `C u ∩ C v` being the splitting
disk of the edge `uv` and empty otherwise; `h` is a merely topological embedding of `N` and
`N' = h '' N` is the tube.  The splitting disks and dual cells of `N'` are the sets `h '' D e`
and `h '' C v` and are not carried as further parameters.  Deviations: the book's "orthogonal to
the edge at its midpoint" is dropped, since only `D e ∩ |K| = {midpoint}` is ever used, and
"regular neighbourhood" is rendered by the properties of the cut that Sections 32 and 33
consume, not by a derived neighbourhood of a named triangulation.

`IsHandleDecompositionOfTube` is the output of 32.3 read as a definition, as the section title
and the digest of Section 33 read it: pseudo-cells `Ec e` with centres the images of the edge
midpoints and boundaries the images of the `Dbd e`, meeting the image graph only in the centre,
and the handle pieces `Cpp v` with one vertex each, covering `N'`, and meeting exactly along
the `Ec e` of the edges.  Page 228 also constructs the `Cpp v` as closures of the components of
`N' - ⋃ Ec e`; that is the construction, not the notion, and it is not a field here.

The numbered propositions.  `Moise321` is Theorem 1 of page 224 with its clauses (1)-(4);
clause (3), "`Int E` separates `v'₁` from `v'₂` in `Int (C'₁ ∪ C'₂)`", is stated as `Separates`
inside the subspace `Int (C'₁ ∪ C'₂)`, never in `ℝ³`.  `Moise322` is Theorem 2 of page 227 with
clauses (5), (6) and the printed "exactly two components", rendered by two disjoint connected
sets covering the complement such that every preconnected subset of the complement lies in one
of them.  `Moise323` is Theorem 3 of page 228: its clauses (7), (9), (10) are the fields of
`IsHandleDecompositionOfTube`, and clause (8) is the extra conclusion `Cpp v ⊆ V v` for an
arbitrary prescribed neighbourhood `V v` of `h '' C v`; this is the only metric clause of the
whole chain and the one that Section 33's Lemma 1 consumes.  `Moise324` is Theorem 4 of pages
228-229 for an arbitrary pseudo-cell of `ℝ³`, which Section 33 uses in its Lemma 8 and in its
endgame; the two-cells it produces are piecewise linear and their boundaries are intrinsic,
read off a parametrisation of the standard two-simplex.

Section 32 does not use the notion the book introduces on page 232 under the reading "loop
theorem disk"; that is a Section 33 notion and is not defined here.

The inhabitant `isPseudoCell_planarSquare` is the closed unit square of the `xy`-plane of `ℝ³`
with its relative interior, its rim, and the origin as centre: a genuinely two-dimensional,
non-degenerate pseudo-cell whose regular part is not compact, so the deviation above is
exercised rather than avoided.  `IsTube` and `IsHandleDecompositionOfTube` carry no inhabitant
theorem yet.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Cells

def IsOpenTopologicalCell (n : ℕ) {X : Type*} [TopologicalSpace X] (U : Set X) : Prop :=
  Nonempty (U ≃ₜ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)

def IsTopologicalSphere (n : ℕ) {X : Type*} [TopologicalSpace X] (J : Set X) : Prop :=
  Nonempty (J ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

structure IsPseudoCell (Ec Eint Ebd : Set (EuclideanSpace ℝ (Fin 3)))
    (P : EuclideanSpace ℝ (Fin 3)) : Prop where
  carrierEq : Ec = Eint ∪ Ebd
  isOpenCell : IsOpenTopologicalCell 2 Eint
  isSphere : IsTopologicalSphere 1 Ebd
  disjointRim : Disjoint Eint Ebd
  closureEq : closure Eint = Eint ∪ Ebd
  centerMem : P ∈ Eint
  regular : IsLocallyPolyhedral (Eint \ {P})

end Cells

section PlanarPolyhedron

noncomputable def euclideanCoord {n : ℕ} (i : Fin n) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ where
  toFun x := x i
  map_add' _ _ := by simp [PiLp.add_apply]
  map_smul' _ _ := by simp [PiLp.smul_apply]

@[simp] theorem euclideanCoord_apply {n : ℕ} (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    euclideanCoord i x = x i := rfl

theorem isHPolytope_of_coordBox {C : Set (EuclideanSpace ℝ (Fin 3))} (hC : IsCompact C)
    (lower upper : Fin 3 → ℝ) (heq : C = {p | ∀ i, p i ∈ Icc (lower i) (upper i)}) :
    IsHPolytope C := by
  refine ⟨hC, Fin 3 ⊕ Fin 3, inferInstance,
    Sum.elim (fun i => euclideanCoord i) (fun i => -euclideanCoord i),
    Sum.elim upper (fun i => -lower i), ?_⟩
  rw [heq]
  ext p
  constructor
  · intro hp i
    rcases i with i | i
    · simpa using (hp i).2
    · simpa using neg_le_neg (hp i).1
  · intro hp i
    have h1 : p i ≤ upper i := by simpa using hp (Sum.inl i)
    have h2 : -p i ≤ -lower i := by simpa using hp (Sum.inr i)
    exact ⟨by linarith, h1⟩

theorem isCompact_rectTwo (a b c d : ℝ) : IsCompact (rectTwo a b c d) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_rectTwo a b c d) (isBounded_rectTwo a b c d)

theorem isPolyhedron_planarRect (a b c d : ℝ) :
    IsPolyhedron (planarPoint '' rectTwo a b c d) := by
  refine IsHPolytope.isPolyhedron (isHPolytope_of_coordBox
    ((isCompact_rectTwo a b c d).image continuous_planarPoint)
    (fun i => if i = 0 then a else if i = 1 then c else 0)
    (fun i => if i = 0 then b else if i = 1 then d else 0) ?_)
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    fin_cases i
    · simpa using hx.1
    · simpa using hx.2
    · simp
  · intro hp
    have h2 : p 2 = 0 := le_antisymm (by simpa using (hp 2).2) (by simpa using (hp 2).1)
    obtain ⟨x, rfl⟩ := (planarPoint_mem_iff p).mpr h2
    exact ⟨x, ⟨by simpa using hp 0, by simpa using hp 1⟩, rfl⟩

end PlanarPolyhedron

section PseudoCellInhabitant

noncomputable def squareTwo : Set (EuclideanSpace ℝ (Fin 2)) := rectTwo (-1) 1 (-1) 1

noncomputable def planarSquare : Set (EuclideanSpace ℝ (Fin 3)) := planarPoint '' squareTwo

noncomputable def planarSquareInterior : Set (EuclideanSpace ℝ (Fin 3)) :=
  planarPoint '' interior squareTwo

noncomputable def planarSquareRim : Set (EuclideanSpace ℝ (Fin 3)) :=
  planarPoint '' frontier squareTwo

theorem convex_squareTwo : Convex ℝ squareTwo := convex_rectTwo (-1) 1 (-1) 1

theorem isClosed_squareTwo : IsClosed squareTwo := isClosed_rectTwo (-1) 1 (-1) 1

theorem isCompact_squareTwo : IsCompact squareTwo := isCompact_rectTwo (-1) 1 (-1) 1

theorem isBounded_squareTwo : Bornology.IsBounded squareTwo := isBounded_rectTwo (-1) 1 (-1) 1

theorem isPolyhedron_planarSquare : IsPolyhedron planarSquare :=
  isPolyhedron_planarRect (-1) 1 (-1) 1

theorem zero_mem_interior_squareTwo : (0 : EuclideanSpace ℝ (Fin 2)) ∈ interior squareTwo := by
  refine openRectTwo_subset_interior_rectTwo (-1) 1 (-1) 1 ⟨?_, ?_⟩
  · change (0 : EuclideanSpace ℝ (Fin 2)) 0 ∈ Ioo (-1 : ℝ) 1
    norm_num [PiLp.zero_apply]
  · change (0 : EuclideanSpace ℝ (Fin 2)) 1 ∈ Ioo (-1 : ℝ) 1
    norm_num [PiLp.zero_apply]

theorem interior_nonempty_squareTwo : (interior squareTwo).Nonempty :=
  ⟨0, zero_mem_interior_squareTwo⟩

theorem disjoint_interior_frontier_squareTwo :
    Disjoint (interior squareTwo) (frontier squareTwo) :=
  disjoint_left.mpr fun _ hx hx' => hx'.2 hx

theorem sdiff_frontier_squareTwo : squareTwo \ frontier squareTwo = interior squareTwo := by
  ext x
  constructor
  · rintro ⟨hx, hxf⟩
    by_contra hxi
    exact hxf ⟨subset_closure hx, hxi⟩
  · intro hx
    exact ⟨interior_subset hx, fun hxf => hxf.2 hx⟩

theorem interior_union_frontier_squareTwo :
    interior squareTwo ∪ frontier squareTwo = squareTwo := by
  have h : interior squareTwo ∪ frontier squareTwo = closure squareTwo :=
    union_sdiff_cancel interior_subset_closure
  rw [h, isClosed_squareTwo.closure_eq]

theorem isClosed_planarSquareRim : IsClosed planarSquareRim :=
  ((isCompact_squareTwo.of_isClosed_subset isClosed_frontier
    isClosed_squareTwo.frontier_subset).image continuous_planarPoint).isClosed

theorem isPseudoCell_planarSquare :
    IsPseudoCell planarSquare planarSquareInterior planarSquareRim (planarPoint 0) := by
  have hne : (interior squareTwo).Nonempty := interior_nonempty_squareTwo
  have hcarrier : planarSquare = planarSquareInterior ∪ planarSquareRim := by
    rw [planarSquare, planarSquareInterior, planarSquareRim, ← image_union,
      interior_union_frontier_squareTwo]
  refine ⟨hcarrier, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact nonempty_homeomorph_planarImage_interior convex_squareTwo isBounded_squareTwo hne
  · exact nonempty_homeomorph_planarImage_frontier convex_squareTwo isBounded_squareTwo hne
  · exact Set.disjoint_image_of_injective planarPoint_injective
      disjoint_interior_frontier_squareTwo
  · have hclint : closure (interior squareTwo) = squareTwo := by
      rw [convex_squareTwo.closure_interior_eq_closure_of_nonempty_interior hne,
        isClosed_squareTwo.closure_eq]
    rw [← hcarrier, planarSquare, planarSquareInterior]
    refine Subset.antisymm (closure_minimal (image_mono interior_subset)
      ((isCompact_squareTwo.image continuous_planarPoint).isClosed)) ?_
    calc planarPoint '' squareTwo = planarPoint '' closure (interior squareTwo) := by
          rw [hclint]
      _ ⊆ closure (planarPoint '' interior squareTwo) :=
          image_closure_subset_closure_image continuous_planarPoint
  · exact ⟨0, zero_mem_interior_squareTwo, rfl⟩
  · have hdiff : planarSquareInterior = planarSquare \ planarSquareRim := by
      rw [planarSquare, planarSquareInterior, planarSquareRim,
        ← image_sdiff planarPoint_injective, sdiff_frontier_squareTwo]
    rw [hdiff]
    exact ((isPolyhedron_planarSquare.isLocallyPolyhedral.sdiff_isClosed
      isClosed_planarSquareRim).sdiff_isClosed isClosed_singleton)

theorem isOpenTopologicalCell_planarSquareInterior :
    IsOpenTopologicalCell 2 planarSquareInterior :=
  isPseudoCell_planarSquare.isOpenCell

theorem isTopologicalSphere_planarSquareRim : IsTopologicalSphere 1 planarSquareRim :=
  isPseudoCell_planarSquare.isSphere

theorem not_isClosed_planarSquareInterior : ¬ IsClosed planarSquareInterior := by
  intro hclosed
  have hcl := isPseudoCell_planarSquare.closureEq
  rw [hclosed.closure_eq] at hcl
  have hsub : planarSquareRim ⊆ planarSquareInterior := by
    conv_rhs => rw [hcl]
    exact subset_union_right
  have hempty : planarSquareRim = ∅ := by
    have hd : Disjoint planarSquareRim planarSquareRim :=
      (isPseudoCell_planarSquare.disjointRim).mono_left hsub
    simpa using disjoint_self.mp hd
  have hfr : frontier squareTwo = ∅ := by
    by_contra hfrne
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hfrne
    have hmem : planarPoint x ∈ planarSquareRim := mem_image_of_mem planarPoint hx
    rw [hempty] at hmem
    exact hmem
  have hclopen : IsClopen squareTwo := isClopen_iff_frontier_eq_empty.mpr hfr
  rcases isClopen_iff.mp hclopen with h | h
  · have hzero : (0 : EuclideanSpace ℝ (Fin 2)) ∈ interior squareTwo :=
      zero_mem_interior_squareTwo
    rw [h, interior_empty] at hzero
    exact hzero
  · have hmem : EuclideanSpace.single (0 : Fin 2) (2 : ℝ) ∈ rectTwo (-1) 1 (-1) 1 := by
      have hu : EuclideanSpace.single (0 : Fin 2) (2 : ℝ) ∈ squareTwo := by
        rw [h]; exact mem_univ _
      exact hu
    have h2 : (EuclideanSpace.single (0 : Fin 2) (2 : ℝ)) 0 ≤ 1 := (mem_rectTwo.mp hmem).1.2
    simp at h2

end PseudoCellInhabitant

section Tubes

open Classical in
structure IsTube (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (N : Set (EuclideanSpace ℝ (Fin 3)))
    (C : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)))
    (D Dbd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (N' : Set (EuclideanSpace ℝ (Fin 3))) : Prop where
  facesFinite : K.faces.Finite
  oneDimensional : ∀ s ∈ K.faces, s.card ≤ 2
  hasEdge : ∃ e ∈ K.faces, e.card = 2
  isNeighborhood : N ∈ nhdsSet K.space
  dualBall : ∀ v ∈ K.vertices, IsPLBall 3 (C v)
  dualVertex : ∀ v ∈ K.vertices, C v ∩ K.vertices = {v}
  splitCell : ∀ e ∈ K.faces, e.card = 2 →
    ∃ r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) (D e) ∧ Dbd e = r '' stdSimplexBoundary 2
  splitMidpoint : ∀ e ∈ K.faces, e.card = 2 → D e ∩ K.space = {e.centroid ℝ id}
  unionEq : N = ⋃ v ∈ K.vertices, C v
  interEdge : ∀ u ∈ K.vertices, ∀ v ∈ K.vertices, u ≠ v → ({u, v} : Finset _) ∈ K.faces →
    C u ∩ C v = D {u, v}
  interNonEdge : ∀ u ∈ K.vertices, ∀ v ∈ K.vertices, u ≠ v → ({u, v} : Finset _) ∉ K.faces →
    C u ∩ C v = ∅
  isEmbedding : Topology.IsEmbedding (N.domRestrict h)
  imageEq : N' = h '' N

open Classical in
structure IsHandleDecompositionOfTube
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (N : Set (EuclideanSpace ℝ (Fin 3)))
    (C : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)))
    (D Dbd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (N' : Set (EuclideanSpace ℝ (Fin 3)))
    (Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))) : Prop where
  tube : IsTube K N C D Dbd h N'
  pseudoCell : ∀ e ∈ K.faces, e.card = 2 →
    IsPseudoCell (Ec e) (Eint e) (Ebd e) (h (e.centroid ℝ id))
  rimEq : ∀ e ∈ K.faces, e.card = 2 → Ebd e = h '' Dbd e
  meetsGraph : ∀ e ∈ K.faces, e.card = 2 →
    Ec e ∩ h '' K.space = {h (e.centroid ℝ id)}
  oneVertex : ∀ v ∈ K.vertices, Cpp v ∩ h '' K.vertices = {h v}
  coversTube : N' = ⋃ v ∈ K.vertices, Cpp v
  handleEdge : ∀ u ∈ K.vertices, ∀ v ∈ K.vertices, u ≠ v → ({u, v} : Finset _) ∈ K.faces →
    Cpp u ∩ Cpp v = Ec {u, v}
  handleNonEdge : ∀ u ∈ K.vertices, ∀ v ∈ K.vertices, u ≠ v →
    ({u, v} : Finset _) ∉ K.faces → Cpp u ∩ Cpp v = ∅

end Tubes

section Statements

open Classical in
def Moise321 : Prop :=
  ∀ (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (N : Set (EuclideanSpace ℝ (Fin 3)))
    (C : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)))
    (D Dbd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (N' : Set (EuclideanSpace ℝ (Fin 3))),
    IsTube K N C D Dbd h N' →
    ∀ u ∈ K.vertices, ∀ v ∈ K.vertices, u ≠ v → ({u, v} : Finset _) ∈ K.faces →
    ∀ W : Set (EuclideanSpace ℝ (Fin 3)), IsClosed W →
      h '' (D {u, v} \ Dbd {u, v}) \ {h (({u, v} : Finset _).centroid ℝ id)} ⊆ interior W →
      W ⊆ h '' C u ∪ h '' C v →
      W ∩ frontier (h '' C u ∪ h '' C v) = h '' Dbd {u, v} →
      W ∩ h '' K.space = {h (({u, v} : Finset _).centroid ℝ id)} →
      ∃ Ec Eint Ebd : Set (EuclideanSpace ℝ (Fin 3)),
        IsPseudoCell Ec Eint Ebd (h (({u, v} : Finset _).centroid ℝ id)) ∧
        Ebd = h '' Dbd {u, v} ∧ Ec ⊆ W ∧
        DifferentialGeometry.Topology.Separates
          (((↑) : interior (h '' C u ∪ h '' C v) → EuclideanSpace ℝ (Fin 3)) ⁻¹' Eint)
          (((↑) : interior (h '' C u ∪ h '' C v) → EuclideanSpace ℝ (Fin 3)) ⁻¹' {h u})
          (((↑) : interior (h '' C u ∪ h '' C v) → EuclideanSpace ℝ (Fin 3)) ⁻¹' {h v}) ∧
        Ec ∩ h '' K.space = {h (({u, v} : Finset _).centroid ℝ id)}

open Classical in
def Moise322 : Prop :=
  ∀ (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (N : Set (EuclideanSpace ℝ (Fin 3)))
    (C : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)))
    (D Dbd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (N' : Set (EuclideanSpace ℝ (Fin 3))),
    IsTube K N C D Dbd h N' →
    ∀ u ∈ K.vertices, ∀ v ∈ K.vertices, u ≠ v → ({u, v} : Finset _) ∈ K.faces →
    ∀ W : Set (EuclideanSpace ℝ (Fin 3)), IsClosed W →
      h '' (D {u, v} \ Dbd {u, v}) \ {h (({u, v} : Finset _).centroid ℝ id)} ⊆ interior W →
      W ⊆ h '' C u ∪ h '' C v →
      W ∩ frontier (h '' C u ∪ h '' C v) = h '' Dbd {u, v} →
      W ∩ h '' K.space = {h (({u, v} : Finset _).centroid ℝ id)} →
      ∃ (Ec Eint Ebd U₁ U₂ : Set (EuclideanSpace ℝ (Fin 3))),
        IsPseudoCell Ec Eint Ebd (h (({u, v} : Finset _).centroid ℝ id)) ∧
        Ebd = h '' Dbd {u, v} ∧ Ec ⊆ W ∧
        IsConnected U₁ ∧ IsConnected U₂ ∧ Disjoint U₁ U₂ ∧
        U₁ ∪ U₂ = (h '' C u ∪ h '' C v) \ Ec ∧
        (∀ V : Set (EuclideanSpace ℝ (Fin 3)), IsPreconnected V →
          V ⊆ (h '' C u ∪ h '' C v) \ Ec → V ⊆ U₁ ∨ V ⊆ U₂) ∧
        Ec ⊆ frontier U₁ ∧ Ec ⊆ frontier U₂ ∧
        h '' (frontier (C u) ∩ frontier N) ⊆ frontier U₁ ∧
        h '' (frontier (C v) ∩ frontier N) ⊆ frontier U₂

def Moise323 : Prop :=
  ∀ (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (N : Set (EuclideanSpace ℝ (Fin 3)))
    (C : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)))
    (D Dbd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (N' : Set (EuclideanSpace ℝ (Fin 3))),
    IsTube K N C D Dbd h N' →
    ∀ V : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)),
      (∀ v ∈ K.vertices, V v ∈ nhdsSet (h '' C v)) →
      ∃ (Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
        (Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))),
        IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp ∧
        ∀ v ∈ K.vertices, Cpp v ⊆ V v

def Moise324 : Prop :=
  ∀ (Ec Eint Ebd : Set (EuclideanSpace ℝ (Fin 3))) (P : EuclideanSpace ℝ (Fin 3)),
    IsPseudoCell Ec Eint Ebd P →
    ∀ δ : ℝ, 0 < δ →
      ∃ (Δ Δbd : Set (EuclideanSpace ℝ (Fin 3)))
        (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
        IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ ∧
        Δbd = r '' stdSimplexBoundary 2 ∧
        Δ ⊆ Metric.ball P δ ∧
        Δbd = Δ ∩ Ec ∧
        ∃ (DJ : Set (EuclideanSpace ℝ (Fin 3))) (s : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
          IsPLHomeomorphOn s (stdSimplex ℝ (Fin 3)) DJ ∧ DJ ⊆ Ec ∧
          Δbd = s '' stdSimplexBoundary 2 ∧
          P ∈ DJ \ s '' stdSimplexBoundary 2

end Statements

end DifferentialGeometry.Topology.PiecewiseLinear
