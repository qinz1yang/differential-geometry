/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Statements

/-!
# Sorry-first skeleton of stages P2--P5 of Section 34, the normalised face balls

The assembly `section34NormalFamily` proves the endpoint `Section34NormalFamilyStatement` for
real from the seven leaves of this file; every `sorry` is a leaf and none sits inside an
assembly.  The endpoint is stated so that it matches, binder for binder, the frozen leaf
`exists_section34NormalFamily` of the terminal skeleton, whose hypotheses are
`[Nonempty M₁] [T2Space M₁] [SecondCountableTopology M₁] [SecondCountableTopology M₂]`,
`[HasGroupoid M₁ (plGroupoid 3)]`, `[HasGroupoid M₂ (plGroupoid 3)]`, `IsOpen U`,
`Topology.IsEmbedding (U.domRestrict h)`, `ContinuousOn η U` and `∀ x ∈ U, 0 < η x`.  Skeletons
cannot import each other, so the match is textual: the terminal skeleton discharges its leaf by
`intro`ducing that binder list and applying this endpoint to `h341`, to the two named
propositions of the real module `Section34Statements` and to `hU hh hηc hηpos`, the four
explicit hypotheses being in the same order in both statements.

What is taken as given and what is produced.  `Section34ControlStatement` (step P0) supplies the
realisation ambient `EuclideanSpace ℝ (Fin N)`, the triangulation `𝒦`, the combinatorial
manifold certificate and the carrier system `H`; `ControlledGraphNeighborhoodStatement` (step P1)
is applied with `W := U` and `ψ := η` and supplies the subdivision `𝒦'`, the source cut diagram
`src, srcBd`, the carrier assignment `cr` and the piecewise linear map `f₁`, that is the first
three conjuncts of `Section34NormalPlus`; P2, the generator clause of Moise's Lemma 2, is already
a field of `Section34GraphFrame`.  The target vertex balls, splitting disks and their intrinsic
boundaries are not further data: they are the four `f₁`-images
`section34VertexBallImage src f₁`, `section34VertexBallImage srcBd f₁`,
`section34SplitDiskImage src f₁` and `section34SplitDiskImage srcBd f₁`, which is what makes
conjuncts six and seven of `Section34NormalPlus` reflexivity and conjunct ten a consequence of
the boundary formula of the cut frame.  What is genuinely produced here is the family `fbl`, the
book's `C_σ` of Lemma 5 on page 241, together with its normalisation: `Section34Exterior`,
`Section34Trace`, the cell clauses and the two clauses saying that neither Operation 1 nor
Operation 2 is possible.

The measure and why a step at one label leaves the others alone.  `section34FaceBallRank` adds
the number of connected components of `fblBd s ∩ frontier (⋃ w, tgtV w)`, the book's `c_σ`, and
the number of points of `fblBd s ∩ ⋃ e, tgtEBd e`, the book's `p_σ`; both are finite by two
fields of the invariant bundle, which is the only form in which general position is recorded,
`HasPLCrossingAt` being a predicate on subsets of a normed space and not on subsets of the
manifold `M₂`.  The rank of a label reads the family only at that label, which is
`section34FaceBallRank_congr`, proved here; so a step that changes `fbl` and `fblBd` only at `s`
provably leaves every other rank fixed, and the descent is per label and needs no assumption.
Operation 1 removes one component and adds no crossing, Operation 2 removes two crossings and
adds no component, so the sum strictly decreases in both cases.

Operation 2 is **not** stated as an ambient isotopy, against the reading of `A2-answer-digest`
Q3, and the reason is a refutation and not a convenience.  `Section34NormalPlus` pins
`tgtV w = f₁ '' src (.vertexBall w)`, so the splitting circle `tgtEBd e` is fixed once `f₁` is
fixed; and if `Φ` is any homeomorphism of `M₂` with `Φ '' tgtEBd e = tgtEBd e`, then
`Φ '' X ∩ tgtEBd e = Φ '' (X ∩ tgtEBd e)` has exactly as many points as `X ∩ tgtEBd e`, so no
such `Φ` can lower `p_σ`.  An isotopy realising Operation 2 therefore has to move the splitting
circles, hence to move the individual vertex balls, hence to change `tgtV`, which the frozen
conjunct forbids.  The bigon slide is accordingly stated as a replacement of the single set
`fbl s`; its support is not an extra clause, because the first field of `Section34Exterior`,
which is a field of the invariant bundle before and after the step, already puts both the old
and the new `fbl s` inside `interior (H t.1)` for every tetrahedron `t` incident to `s`, and the
carriers `H` are locally finite in `h '' U` by `Section34CarrierControl`.

The leaves, with content and review state.  All seven are **unreviewed**.

`IsPLHomeomorphInto.mono_of_isPLCellOn` (short): a piecewise linear embedding of a set restricts
to a piecewise linear embedding of a piecewise linear cell inside it.  The tree has
`IsPLOn.mono_of_isPolyhedron` only for a map whose domain is the model space, and the controlled
graph-neighbourhood skeleton records the restriction of an `IsPLHomeomorphInto` as unavailable;
the cell hypothesis is what supplies the polyhedron to restrict to.  It is used twice, for
conjuncts eight and nine, through `IsPLCellOn.image`.

`exists_splitDisk_src_eq_inter_vertexBall` (short): two distinct dual balls of the source cut
diagram that meet, meet in a splitting disk of the diagram.  `Section34CutFrame` states the
converse, that every splitting disk is such an intersection, and never this direction; it is a
**gap in the frozen P1 interface**, and it is what conjunct eleven of `Section34NormalPlus`
needs.  It is derivable from the frame for the labels of dimension two that are face disks,
because the face-arc equation would make one set both a piecewise linear `1`-cell and a
`2`-cell, which `IsPLCellOn.dim_eq` forbids; for the patch and arc labels the frame has no such
exclusion, so the clause is owed by P1 and cannot be repaired here.

`exists_section34FaceBalls` (P3, Lemmas 3--5, deep): the initial family `C_σ`, one closed
piecewise linear `3`-ball per `2`-simplex, with Lemma 5 in manifold form as
`Section34FaceBallInvariants`.  Chart-local: `Section34CarrierControl` puts each carrier `H t`
inside one piecewise linear chart of `M₂`, and `Moise341` read in that chart supplies the
approximation and the general position, which is the only use of `h341` in this file.  It covers
the page 240 [ASSERTED] items of Lemma 3, the arbitrarily small shell-separated cell
neighbourhoods of `σ` and their transfer along `h`, the unquantified "general position in one of
its usual senses", and the page 241 [ASSERTED] sufficient condition for Lemma 5(7).

`exists_section34Compression` (P4a, Operation 1 and Lemma 6, deep) and
`exists_section34BigonSlide` (P4b, Operation 2 and Lemma 7, deep): one step at one label.  Each
takes the invariants and an available operation at `s`, in the shape `Section34Compression` and
`Section34BigonSlide` whose negations are literally conjuncts sixteen and seventeen of
`Section34NormalPlus`, and returns a family that agrees with the old one at every other label,
still satisfies the invariants and has strictly smaller rank at `s`.  They cover the page 242
[ASSERTED] items: that one of the two spheres produced by Operation 1 still bounds a `3`-cell
around `h '' Bd σ`, that Operation 2 exists at all, and the unargued clauses (1), (3), (4), (6),
(8) of Lemma 6 and the whole of Lemma 7, the preservation of 5(6) and of 5(7) under Operation 2
being the two that `A-section34-lemma-list` §5 names as the first places a formalisation stalls.
`A2-answer-digest`'s cleanliness point is honoured: Operation 1's input already carries
`Dj ∩ fblBd s = Jd`, the exact-intersection form of the clean disk.

`exists_section34TerminalFaceBalls` (P5, Lemma 8, deep): the isolated limit step.  Book Lemma 8
alternates the two operations until neither is possible and counts over a finite complex; here
the label type is infinite, so the leaf takes the two steps as hypotheses in exactly the shape
the two previous leaves produce, plus the carrier control, and returns a family satisfying the
invariants at which neither operation is available.  The descent itself is per label and finite,
`section34FaceBallRank_congr` being proved here, and the carriers are locally finite in `h '' U`;
what the leaf still owes is the passage to the pointwise limit of a locally finite sequence of
modifications, and the fairness argument that a legal move of the limit, having a compact
witness meeting finitely many carriers, would already have been performed.

`section34Trace_of_noOperation` (Lemmas 9--11, deep): from the invariants and the two
impossibility clauses, `Section34Trace`.  Lemma 9's chain argument needs the link condition of
page 239, that in the link of a vertex the interior of an edge never separates two vertices; by
`A2-answer-digest` Q4 that is (Link-E) for a triangulated `2`-sphere or `2`-disk, hence a
consequence of `IsCombinatorialManifold 3 𝒦.complex`, which is the first field of
`Section34CutFrame`, so it is **not** a further gap in P1 and is not taken as a hypothesis here.
Lemma 10 is used inside the same leaf, and Lemma 11 needs 28.8, which the tree does not state;
this leaf is where that external input enters.  It covers the page 243 [ASSERTED] termination
consequence and the page 244 [SLIP]/[AMBIG] around the 28.8 citation and "easily gives a
contradiction".

Proved here, not leaves.  `simplexBody_subset_of_mem_faces` and `graphSkeletonSpace_subset`, the
containments that let the controlled form of 35.1 be applied with `W := U`;
`nonempty_simplexRim` and `nonempty_section34FaceTorus`, the non-degeneracy of the torus that
Lemma 5(6) is stated on; `section34FaceBallRank_congr`; and the whole packaging of the seventeen
conjuncts of `Section34NormalPlus`, including the two cell conjuncts, the containment of a
splitting disk image in a vertex ball boundary image, conjunct eleven from the injectivity of
`f₁` on the cut neighbourhood, the carrier containment of a tetrahedron ball, and the two
impossibility conjuncts from the negations produced by P5.

Vacuity.  `[Nonempty M₁]` is inherited from the frozen leaf and is necessary, a
`LocallyFinitePLPieceIn` having a total realisation map.  The generator field of
`Section34FaceBallInvariants` would be vacuous on an empty face torus; it is not, because
`nonempty_section34FaceTorus`, proved here from the neighbourhood field of `Section34GraphFrame`
and from `nonempty_simplexRim`, exhibits a point in every `section34FaceTorus`, so the clause
always quantifies over a nonempty space.  The rank is a function of the current family alone and
of the label, never a free parameter: `section34FaceBallRank_congr` states exactly that, and the
two finiteness fields of the bundle stop `Set.ncard` from reading an infinite set as zero, which
is the only way a descent on `ncard` could be satisfied trivially.  The arbitrary sets `Dj`,
`Jd`, `B`, `Bb` of the two operation predicates are unpinned on purpose, because those
predicates occur negated: conjuncts sixteen and seventeen say that no such data exist, so a free
parameter there strengthens the statement instead of hollowing it.  The families `tgtV`,
`tgtVBd`, `tgtE`, `tgtEBd` are never left free in a leaf hypothesis; every leaf carries them as
the four `f₁`-images, so no leaf can be satisfied by a family unrelated to the cut diagram.  On
the shared fixture `U = M₁ = M₂ = ℝ³`, `h` a non-piecewise-linear small perturbation of the
identity, a fine tetrahedral triangulation and the standard dual cells, every field of the
bundle is satisfied by the thickened triangles `C_σ`, which are `3`-balls containing `h '' Bd σ`
in their interiors, and `IsCombinatorialManifold 3` is used only for the complex of the open set
`U`, never for a nonempty finite complex of `ℝ³`.  Two clauses of the invariant are **not**
exposed by `Section34NormalPlus` and so cannot reach step P6: Lemma 5(1), that `fbl s` is a
neighbourhood of `h '' simplexRim 𝒦 s.1`, and Lemma 5(6), the generator clause; the face disk
`Δ_σ` of P6 is chosen inside `fblBd s` and its irreducibility argument uses both.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Vocabulary

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁}

def section34VertexBallImage {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    (c : Section34CutLabelOf 𝒦 𝒦' → Set M₁) (g : M₁ → M₂)
    (w : Section34VertexIndex 𝒦 𝒦') : Set M₂ :=
  g '' c (Section34Label.vertexBall w)

def section34SplitDiskImage {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    (c : Section34CutLabelOf 𝒦 𝒦' → Set M₁) (g : M₁ → M₂)
    (e : Section34EdgeIndex 𝒦 𝒦') : Set M₂ :=
  g '' c (Section34Label.splitDisk e)

def section34TraceComponents {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    (tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (fblBd : Section34SimplexIndex 𝒦 3 → Set M₂) (s : Section34SimplexIndex 𝒦 3) :
    Set (Set M₂) :=
  (fun y => connectedComponentIn (fblBd s ∩ frontier (⋃ w, tgtV w)) y) ''
    (fblBd s ∩ frontier (⋃ w, tgtV w))

noncomputable def section34FaceBallRank {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    (tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (fblBd : Section34SimplexIndex 𝒦 3 → Set M₂) (s : Section34SimplexIndex 𝒦 3) : ℕ :=
  (section34TraceComponents tgtV fblBd s).ncard +
    (fblBd s ∩ ⋃ e : Section34EdgeIndex 𝒦 𝒦', tgtEBd e).ncard

omit [FiniteDimensional ℝ Ea] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] in
theorem section34FaceBallRank_congr {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    {tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    {tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
    {fblBd fblBd' : Section34SimplexIndex 𝒦 3 → Set M₂} {s : Section34SimplexIndex 𝒦 3}
    (hs : fblBd s = fblBd' s) :
    section34FaceBallRank tgtV tgtEBd fblBd s = section34FaceBallRank tgtV tgtEBd fblBd' s := by
  simp only [section34FaceBallRank, section34TraceComponents, hs]

def Section34FaceBallInvariants (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U) (h : M₁ → M₂)
    (H : Finset Ea → Set M₂) (tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂) : Prop :=
  (∀ s, IsPLCellOn 3 (fbl s) (fblBd s)) ∧
  (∀ s : Section34SimplexIndex 𝒦 3, h '' simplexRim 𝒦 s.1 ⊆ interior (fbl s)) ∧
  (∀ (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦'),
    ¬ Section34Incident w.1 s.1 → fbl s ∩ tgtV w = ∅) ∧
  (∀ s s', s ≠ s' → fbl s ∩ fbl s' ⊆ interior (⋃ w, tgtV w)) ∧
  (∀ s, CarriesFundamentalGroupOnto (fblBd s ∩ frontier (section34FaceTorus tgtV s))
    (section34FaceTorus tgtV s)) ∧
  (∀ s, (fblBd s ∩ ⋃ e : Section34EdgeIndex 𝒦 𝒦', tgtEBd e).Finite) ∧
  (∀ s, (section34TraceComponents tgtV fblBd s).Finite) ∧
  Section34Exterior 𝒦 𝒦' h H tgtV fbl

def Section34Compression (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
    (tgtVBd : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (tgtE : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂) (s : Section34SimplexIndex 𝒦 3) : Prop :=
  ∃ (w : Section34VertexIndex 𝒦 𝒦') (Dj Jd : Set M₂),
    IsPLCellOn 2 Dj Jd ∧ Dj ⊆ tgtVBd w ∧ Jd ⊆ fblBd s ∧ Dj ∩ fblBd s = Jd ∧
      (∀ e : Section34EdgeIndex 𝒦 𝒦', Disjoint Dj (tgtE e)) ∧
      ∀ s' : Section34SimplexIndex 𝒦 3, s' ≠ s → Disjoint (Dj \ Jd) (fbl s')

def Section34BigonSlide (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
    (tgtVBd : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (tgtE tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (fblBd : Section34SimplexIndex 𝒦 3 → Set M₂) (s : Section34SimplexIndex 𝒦 3) : Prop :=
  ∃ (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦') (B Bb Dj Jd : Set M₂),
    IsPLCellOn 1 B Bb ∧ B ⊆ fblBd s ∧ B ⊆ tgtVBd w ∧ Bb ⊆ tgtEBd e ∧
      B ∩ (⋃ e' : Section34EdgeIndex 𝒦 𝒦', tgtE e') = Bb ∧ IsPLCellOn 2 Dj Jd ∧
      Dj ⊆ tgtVBd w ∧ Jd ⊆ B ∪ tgtEBd e ∧
      ∀ s' : Section34SimplexIndex 𝒦 3, Disjoint (Dj \ Jd) (fblBd s')

end Vocabulary

section Leaves

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {H : Finset Ea → Set M₂}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

omit [FiniteDimensional ℝ Ea] in
theorem simplexBody_subset_of_mem_faces {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) :
    simplexBody 𝒦 t ⊆ U := by
  rintro _ ⟨x, hx, rfl⟩
  exact 𝒦.bijOn.mapsTo (𝒦.complex.convexHull_subset_space ht hx)

omit [FiniteDimensional ℝ Ea] in
theorem graphSkeletonSpace_subset (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U) :
    graphSkeletonSpace 𝒦 ⊆ U := by
  simp only [graphSkeletonSpace]
  exact iUnion₂_subset fun _ ht => simplexBody_subset_of_mem_faces ht.1

omit [FiniteDimensional ℝ Ea] in
theorem nonempty_simplexRim {t : Finset Ea} (ht : 2 ≤ t.card) : (simplexRim 𝒦 t).Nonempty := by
  obtain ⟨v, hv⟩ : ∃ v, v ∈ t := Finset.card_pos.mp (by omega)
  have hne : ({v} : Finset Ea) ≠ t := by
    intro hEq
    have hcard := congrArg Finset.card hEq
    simp only [Finset.card_singleton] at hcard
    omega
  refine ⟨𝒦.map v, ?_⟩
  simp only [simplexRim, mem_iUnion₂]
  exact ⟨{v}, lt_of_le_of_ne (Finset.singleton_subset_iff.mpr hv) hne,
    ⟨v, subset_convexHull ℝ _ (by simp), rfl⟩⟩

omit [FiniteDimensional ℝ Ea] in
theorem nonempty_section34FaceTorus
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁) (s : Section34SimplexIndex 𝒦 3) :
    (section34FaceTorus (section34VertexBallImage src f₁) s).Nonempty := by
  obtain ⟨-, -, -, -, -,
    -, -, -, hrim, -,
    -, -, -, -⟩ := id hgraph
  have hcard : 2 ≤ s.1.card := by
    have hc := s.2.2
    omega
  obtain ⟨x, hx⟩ := nonempty_simplexRim (𝒦 := 𝒦) hcard
  exact ⟨h x, interior_subset (hrim s ⟨x, hx, rfl⟩)⟩

theorem IsPLHomeomorphInto.mono_of_isPLCellOn {d : ℕ} {Z S B : Set M₁} {G : M₁ → M₂}
    (hG : IsPLHomeomorphInto 3 G Z) (hS : IsPLCellOn d S B) (hSZ : S ⊆ Z) :
    IsPLHomeomorphInto 3 G S := by
  sorry

theorem exists_splitDisk_src_eq_inter_vertexBall
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) {w w' : Section34VertexIndex 𝒦 𝒦'}
    (hww : w ≠ w')
    (hmeet : (src (Section34Label.vertexBall w) ∩
      src (Section34Label.vertexBall w')).Nonempty) :
    ∃ e : Section34EdgeIndex 𝒦 𝒦', src (Section34Label.splitDisk e) =
      src (Section34Label.vertexBall w) ∩ src (Section34Label.vertexBall w') := by
  sorry

theorem exists_section34FaceBalls (h341 : Moise341)
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁) :
    ∃ fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂,
      Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
        (section34SplitDiskImage srcBd f₁) fbl fblBd := by
  sorry

theorem exists_section34Compression
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁)
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (s : Section34SimplexIndex 𝒦 3)
    (hop : Section34Compression 𝒦 𝒦' (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) fbl fblBd s) :
    ∃ fbl' fblBd' : Section34SimplexIndex 𝒦 3 → Set M₂,
      Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
        (section34SplitDiskImage srcBd f₁) fbl' fblBd' ∧
      (∀ s', s' ≠ s → fbl' s' = fbl s' ∧ fblBd' s' = fblBd s') ∧
      section34FaceBallRank (section34VertexBallImage src f₁)
          (section34SplitDiskImage srcBd f₁) fblBd' s <
        section34FaceBallRank (section34VertexBallImage src f₁)
          (section34SplitDiskImage srcBd f₁) fblBd s := by
  sorry

theorem exists_section34BigonSlide
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁)
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (s : Section34SimplexIndex 𝒦 3)
    (hop : Section34BigonSlide 𝒦 𝒦' (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁) fblBd s) :
    ∃ fbl' fblBd' : Section34SimplexIndex 𝒦 3 → Set M₂,
      Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
        (section34SplitDiskImage srcBd f₁) fbl' fblBd' ∧
      (∀ s', s' ≠ s → fbl' s' = fbl s' ∧ fblBd' s' = fblBd s') ∧
      section34FaceBallRank (section34VertexBallImage src f₁)
          (section34SplitDiskImage srcBd f₁) fblBd' s <
        section34FaceBallRank (section34VertexBallImage src f₁)
          (section34SplitDiskImage srcBd f₁) fblBd s := by
  sorry

theorem exists_section34TerminalFaceBalls
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁)
    (hctrl : Section34CarrierControl U 𝒦 h η H)
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hcomp : ∀ (g gBd : Section34SimplexIndex 𝒦 3 → Set M₂) (s : Section34SimplexIndex 𝒦 3),
      Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
        (section34SplitDiskImage srcBd f₁) g gBd →
      Section34Compression 𝒦 𝒦' (section34VertexBallImage srcBd f₁)
        (section34SplitDiskImage src f₁) g gBd s →
      ∃ g' gBd' : Section34SimplexIndex 𝒦 3 → Set M₂,
        Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
          (section34SplitDiskImage srcBd f₁) g' gBd' ∧
        (∀ s', s' ≠ s → g' s' = g s' ∧ gBd' s' = gBd s') ∧
        section34FaceBallRank (section34VertexBallImage src f₁)
            (section34SplitDiskImage srcBd f₁) gBd' s <
          section34FaceBallRank (section34VertexBallImage src f₁)
            (section34SplitDiskImage srcBd f₁) gBd s)
    (hslide : ∀ (g gBd : Section34SimplexIndex 𝒦 3 → Set M₂) (s : Section34SimplexIndex 𝒦 3),
      Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
        (section34SplitDiskImage srcBd f₁) g gBd →
      Section34BigonSlide 𝒦 𝒦' (section34VertexBallImage srcBd f₁)
        (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁) gBd s →
      ∃ g' gBd' : Section34SimplexIndex 𝒦 3 → Set M₂,
        Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
          (section34SplitDiskImage srcBd f₁) g' gBd' ∧
        (∀ s', s' ≠ s → g' s' = g s' ∧ gBd' s' = gBd s') ∧
        section34FaceBallRank (section34VertexBallImage src f₁)
            (section34SplitDiskImage srcBd f₁) gBd' s <
          section34FaceBallRank (section34VertexBallImage src f₁)
            (section34SplitDiskImage srcBd f₁) gBd s) :
    ∃ fbl' fblBd' : Section34SimplexIndex 𝒦 3 → Set M₂,
      Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
        (section34SplitDiskImage srcBd f₁) fbl' fblBd' ∧
      (∀ s, ¬ Section34Compression 𝒦 𝒦' (section34VertexBallImage srcBd f₁)
        (section34SplitDiskImage src f₁) fbl' fblBd' s) ∧
      ∀ s, ¬ Section34BigonSlide 𝒦 𝒦' (section34VertexBallImage srcBd f₁)
        (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁) fblBd' s := by
  sorry

theorem section34Trace_of_noOperation
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁)
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hnc : ∀ s, ¬ Section34Compression 𝒦 𝒦' (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) fbl fblBd s)
    (hnb : ∀ s, ¬ Section34BigonSlide 𝒦 𝒦' (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁) fblBd s) :
    Section34Trace 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fblBd := by
  sorry

end Leaves

def Section34NormalFamilyStatement : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
    [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
    {η : M₁ → ℝ} [Nonempty M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)]
    [HasGroupoid M₂ (plGroupoid 3)], IsOpen U → Topology.IsEmbedding (U.domRestrict h) →
    ContinuousOn η U → (∀ x ∈ U, 0 < η x) →
    ∃ (N : ℕ) (𝒦 𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin N)) 3 M₁ U)
      (src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁)
      (H : Finset (EuclideanSpace ℝ (Fin N)) → Set M₂)
      (cr : Section34VertexIndex 𝒦 𝒦' → Finset (EuclideanSpace ℝ (Fin N))) (f₁ : M₁ → M₂)
      (tgtV tgtVBd : Section34VertexIndex 𝒦 𝒦' → Set M₂)
      (tgtE tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
      (fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂),
      Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁ tgtV tgtVBd tgtE tgtEBd fbl fblBd

theorem section34NormalFamily (h341 : Moise341) (hP0 : Section34ControlStatement.{u})
    (h351 : ControlledGraphNeighborhoodStatement.{u}) : Section34NormalFamilyStatement.{u} := by
  intro M₁ M₂ _ _ _ _ U h η _ _ _ _ _ _ hU hh hηc hηpos
  obtain ⟨N, 𝒦, H, hcm, hctrl⟩ := hP0 hU hh η hηc hηpos
  obtain ⟨𝒦', src, srcBd, cr, f₁, hcut, hgraph⟩ :=
    h351 hU hh (EuclideanSpace ℝ (Fin N)) 𝒦 hcm η H hctrl hU
      (graphSkeletonSpace_subset 𝒦) Subset.rfl η hηc hηpos
  obtain ⟨-, -, hpl, -, -,
    -, -, -, -, -,
    -, -, -, -⟩ := id hgraph
  obtain ⟨-, -, -, hcell, hbd,
    -, -, -, -, -,
    -, -, -, -, -,
    -, -, -, -, hsupT,
    -, -, hends, -, -⟩ := id hcut
  obtain ⟨hsup, -, -, -, -, -⟩ := id hctrl
  obtain ⟨fbl₀, fblBd₀, hinv₀⟩ := exists_section34FaceBalls h341 hcut hctrl hgraph
  obtain ⟨fbl, fblBd, hinv, hnc, hnb⟩ :=
    exists_section34TerminalFaceBalls hcut hgraph hctrl hinv₀
      (fun _ _ s hg hop => exists_section34Compression hcut hgraph hg s hop)
      (fun _ _ s hg hop => exists_section34BigonSlide hcut hgraph hg s hop)
  obtain ⟨hfblcell, -, hfblV, hfblfbl, -, -, -, hext⟩ := id hinv
  have htrace := section34Trace_of_noOperation hcut hgraph hinv hnc hnb
  have hsubV : ∀ w : Section34VertexIndex 𝒦 𝒦',
      src (Section34Label.vertexBall w) ⊆ section34CutNeighborhood src := by
    intro w
    simp only [section34CutNeighborhood]
    exact subset_iUnion
      (fun v : Section34VertexIndex 𝒦 𝒦' => src (Section34Label.vertexBall v)) w
  have hsubE : ∀ e : Section34EdgeIndex 𝒦 𝒦',
      src (Section34Label.splitDisk e) ⊆ section34CutNeighborhood src := by
    intro e
    obtain ⟨w, w', -, -, heq⟩ := hends e
    rw [heq]
    exact inter_subset_left.trans (hsubV w)
  have hVcell : ∀ w, IsPLCellOn 3 (section34VertexBallImage src f₁ w)
      (section34VertexBallImage srcBd f₁ w) := fun w =>
    (hcell (Section34Label.vertexBall w)).image
      (hpl.mono_of_isPLCellOn (hcell (Section34Label.vertexBall w)) (hsubV w))
  have hEcell : ∀ e, IsPLCellOn 2 (section34SplitDiskImage src f₁ e)
      (section34SplitDiskImage srcBd f₁ e) := fun e =>
    (hcell (Section34Label.splitDisk e)).image
      (hpl.mono_of_isPLCellOn (hcell (Section34Label.splitDisk e)) (hsubE e))
  have hEV : ∀ (e : Section34EdgeIndex 𝒦 𝒦') (w : Section34VertexIndex 𝒦 𝒦'),
      src (Section34Label.splitDisk e) ⊆ src (Section34Label.vertexBall w) →
        section34SplitDiskImage src f₁ e ⊆ section34VertexBallImage srcBd f₁ w := by
    intro e w hsube
    simp only [section34SplitDiskImage, section34VertexBallImage]
    refine image_mono ?_
    rw [hbd (Section34Label.vertexBall w)]
    exact subset_biUnion_of_mem (u := src)
      (show Section34Label.splitDisk e ∈
        section34Face src (Section34Label.vertexBall w) \ {Section34Label.vertexBall w} from
        ⟨hsube, by simp⟩)
  have hVV : ∀ w w' : Section34VertexIndex 𝒦 𝒦', w ≠ w' →
      section34VertexBallImage src f₁ w ∩ section34VertexBallImage src f₁ w' ⊆
        ⋃ e, section34SplitDiskImage src f₁ e := by
    intro w w' hww
    simp only [section34VertexBallImage, section34SplitDiskImage]
    rintro y ⟨⟨a, ha, rfl⟩, b, hb, hab⟩
    have hEq : b = a := hpl.injOn (hsubV w' hb) (hsubV w ha) hab
    have hb' : a ∈ src (Section34Label.vertexBall w') := hEq ▸ hb
    obtain ⟨e, he⟩ := exists_splitDisk_src_eq_inter_vertexBall hcut hww ⟨a, ha, hb'⟩
    exact mem_iUnion.mpr ⟨e, a, by rw [he]; exact ⟨ha, hb'⟩, rfl⟩
  have htetraH : ∀ t : Section34SimplexIndex 𝒦 4,
      h '' src (Section34Label.tetraBall t) ⊆ H t.1 := fun t =>
    (image_mono (hsupT t)).trans ((hsup t.1 t.2.1).trans interior_subset)
  exact ⟨N, 𝒦, 𝒦', src, srcBd, H, cr, f₁, section34VertexBallImage src f₁,
    section34VertexBallImage srcBd f₁, section34SplitDiskImage src f₁,
    section34SplitDiskImage srcBd f₁, fbl, fblBd, hcut, hctrl, hgraph, hext, htrace,
    fun _ => rfl, fun _ => rfl, hVcell, hEcell, hEV, hVV, htetraH, hfblcell, hfblV, hfblfbl,
    fun s w Dj Jd h1 h2 h3 h4 h5 h6 => hnc s ⟨w, Dj, Jd, h1, h2, h3, h4, h5, h6⟩,
    fun s w e B Bb Dj Jd h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
      hnb s ⟨w, e, B, Bb, Dj, Jd, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
