/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.Integral
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Statements

/-!
# Sorry-first skeleton of stages P2--P5 of Section 34, the normalised face balls

The assembly `section34NormalFamily` proves the endpoint `Section34NormalFamilyStatement` for
real from seven of the eight leaves of this file; every `sorry` is a leaf and none sits inside
an assembly.  The endpoint is stated so that it matches, binder for binder, the frozen leaf
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

Review state, after the first external review (digest
`AH-section34-normalization-first-review-digest`, snapshot `f15c6f34`).  Frozen with the
statement of that snapshot: `IsPLHomeomorphInto.mono_of_isPLCellOn`,
`exists_splitDisk_src_eq_inter_vertexBall` and `exists_section34TerminalFaceBalls`; the last is
OK given its two universal step hypotheses, and its text differs from the snapshot in exactly
one respect, the argument `tgtV` that the pinned bigon adds to `Section34BigonSlide`, inserted
in its two occurrences.  Repaired after the review and unreviewed since:
`exists_section34FaceBalls`, `exists_section34Compression`, `exists_section34BigonSlide` and
`section34Trace_of_noOperation`.  New and unreviewed: `section34TraceCircle_homologyMap_ne_zero`,
the bridge for step P6, not used by the assembly.

The two findings the review corrected.  (1) The dual-ball overlap clause of leaf 2 is derivable
from the cut frame: a patch, respectively a face arc, of vertex `v` inside the ball of `w ≠ v` is
the `2`-cell `Q_t ∩ C_v` inside `Q_t ∩ C_w`, respectively the `1`-cell `C_v ∩ d_σ` inside
`C_w ∩ d_σ`, so the strict dimension clause of the frame gives equality of labels and `v = w`; a
face disk inside a dual ball would be `C_w ∩ d_σ = a_{wσ}`, one set both a `1`-cell and a
`2`-cell, which `IsPLCellOn.dim_eq` forbids; every other common face lies in a splitting disk
`D_e`, whose two ends are then the two vertices by the incidence clause, so the intersection is
`D_e`.  Leaf 2 therefore stays a derived lemma and no cut-frame field is added.  (2) Operation 2
may be realised by an ambient homeomorphism `Φ` that moves only the face ball: `C_σ⁺ = Φ '' C_σ`,
no `V, E, γ` datum is updated and `Φ '' γ_e = γ_e` is not required.  The earlier claim in this
docstring that no ambient map can lower the crossing count assumed `Φ '' ∂E_e = ∂E_e` and was
wrong; what protects the generator and the exterior is that `Φ` fixes the torus `T_σ`, the
other face balls, the markers and the outer collars of the carriers.

The counterexamples of the review, each verified against the Lean text before the repair.  A
discontinuous `h` sending a small segment of a graph edge inside a vertex ball onto `int V_v`
satisfies the cut, carrier and graph frames, so the old P3, which received neither `IsOpen U` nor
the embedding `hh`, had to put `V_v` inside the compact `C_σ`, which then met a foreign vertex
ball.  The tangential branch `z = max (x, min (−|y|, 2x + 2a))`, `a > 0`, replacing `z = x` in
one clean crossing block of the normal fixture, keeps the old bundle and both impossibility
clauses and creates a trivalent trace point, so the old `section34Trace_of_noOperation` was
false: general position had been recorded only as two finiteness counts.  And `Dj = tgtE e`,
`Jd = tgtEBd e` satisfied the old bigon premise `Jd ⊆ B ∪ tgtEBd e` with no arc `B` in `Jd` at
all.  The fixture of the review: a fine grid in `ℝ³`, the standard cut with one bivalent
subdivision vertex, `h = g ∘ ψ` and `f₁ = g` with `g` a small non-zero piecewise linear
translation and `ψ` non-piecewise-linear and supported inside one residual tetrahedron; the
normal face balls satisfy the bundle, and one removable circle and one bigon test P4.

The invariant bundle `Section34FaceBallInvariants` is Lemma 5 in manifold form, ten fields: the
cells, the rim neighbourhood 5(1), the avoidance 5(2), the overlap 5(5), general position 5(3)
and 5(4), the generator 5(6), two finiteness fields, and `Section34Exterior` for 5(7).  General
position is a field and not a count.  5(3) says that at every point of the trace
`fblBd s ∩ frontier (⋃ w, tgtV w)` the sphere `fblBd s` and the surface `frontier (⋃ w, tgtV w)`
cross, `HasPLCrossingAt` read in a chart of the maximal atlas exactly as
`Section34PiercingConditions` reads it.  5(4) says that at every point of `fblBd s ∩ tgtEBd e`
the trace and the splitting circle cross *on that surface*, `HasPLCurveCrossingOnAt`, defined
here and to be hoisted next to `HasPLCrossingAt`: after a piecewise linear homeomorphism of a
neighbourhood the surface is a plane and the two curves are two distinct lines of it.  Two
straight lines alone would not do: the cone over an arc of the unit sphere through the four
points `±p, ±q` in that order is a piecewise linear disk containing two straight lines through
the origin with both rays of one on the same side of the other.  At a trace point the frontiers
of `⋃ w, tgtV w` and of `section34FaceTorus tgtV s` agree locally, by the avoidance field, so
5(4) is stated on the former, like the counts.  The two finiteness fields are consequences of
5(3), 5(4), the compactness of `fblBd s` and the finiteness of the incident edges, not
conversely; they are kept because that derivation needs the continuity of the normal form
`IsPLHomeomorphOn` and the finiteness of `{e | Section34Incident e.1 s.1}`, neither of which the
tree states.  The generator field is the book's 5(6) verbatim: the whole trace
`fblBd s ∩ frontier (section34FaceTorus tgtV s)` carries `H₁` of the torus onto,
`CarriesFirstHomologyOnto`, defined here through the tree's `integralSingularHomologyMap 1` and
to be hoisted next to `CarriesFundamentalGroupOnto`.  It is false for an empty trace, `H₁` of a
solid torus being `ℤ`, whereas the previous field `CarriesFundamentalGroupOnto`, quantified
over the basepoints of the trace, was vacuous there and, once general position is a field, made
every trace component essential, leaving nothing for Operation 1 to do and forcing P3 to do the
work of P4a.  The second review accepted that, for the pairwise disjoint simple closed curves
of a trace on the torus `∂T_σ`, the `H₁` form is equivalent to "some trace circle carries a
generator of `π₁ T_σ`", with the reason confined to the *essential* components: those are
parallel, so the subgroup they generate in `H₁ T_σ = ℤ` is `⟨p⟩` and surjectivity forces
`p = ±1`; contractible components may still be present, and it is exactly those that
Operation 1 removes.

The measure.  `section34TraceCount` is the number of connected components of the trace, the
book's `c_σ`, `section34CrossingCount` the number of points of `fblBd s ∩ ⋃ e, tgtEBd e`, the
book's `p_σ`, and `section34FaceBallRank` their sum; `section34FaceBallRank_congr` says the
counts read the family at the one label only, so a step at `s` provably leaves every other rank
fixed and the descent is per label.  P4a concludes `c⁺ + 1 ≤ c ∧ p⁺ ≤ p` and P4b concludes
`c⁺ = c ∧ p⁺ + 2 = p`, the book's two sentences after Lemma 7;
`section34FaceBallRank_lt_of_compression` and `section34FaceBallRank_lt_of_bigonSlide`, proved
here, turn them into the strict descent that the frozen P5 leaf takes as its two universal step
hypotheses.

Operation 2 is stated as the replacement of the single set `fbl s`, and the bigon is pinned to
the book's data of page 242: an arc `B ⊆ fblBd s ∩ tgtVBd w` with ends `Bb` on the splitting
circle `tgtEBd e` and no other point on a splitting disk, an arc `B' ⊆ tgtEBd e` with the same
ends, `B ∩ B' = Bb`, and a disk `Dj ⊆ tgtVBd w ∩ frontier (⋃ w, tgtV w)` with intrinsic boundary
`Jd = B ∪ B'` whose interior meets no `fblBd s'`.  The same premise, verbatim, is conjunct
seventeen of `Section34NormalPlus`, whose negation the assembly discharges term by term from P5,
so the two were changed together and the P6 leaf of the terminal skeleton now consumes the
precise clause.  Conjunct sixteen, Operation 1, was left as it was: its disk is pinned by the
clean intersection `Dj ∩ fblBd s = Jd` and by disjointness from every closed splitting disk,
which forces `Dj` onto the outer surface, so no instance of the shape `Dj = tgtE e` exists
there.  The support of a step needs no extra clause, because the first field of
`Section34Exterior`, a field of the bundle before and after the step, puts both the old and the
new `fbl s` inside `interior (H t.1)` for every tetrahedron `t` incident to `s`, and the
carriers `H` are locally finite in `h '' U` by `Section34CarrierControl`.

The leaves.

`IsPLHomeomorphInto.mono_of_isPLCellOn` (short, OK, frozen): a piecewise linear embedding of a
set restricts to a piecewise linear embedding of a piecewise linear cell inside it; a cell is a
restrictable local polyhedron in both directions.  Used twice, for conjuncts eight and nine,
through `IsPLCellOn.image`.

`exists_splitDisk_src_eq_inter_vertexBall` (short, OK, frozen): two distinct dual balls of the
source cut diagram that meet, meet in a splitting disk of the diagram.  Derivable as explained
above; it is what conjunct eleven of `Section34NormalPlus` needs.

`exists_section34FaceBalls` (P3, Lemmas 3--5, deep, repaired): the initial family `C_σ`, one
closed piecewise linear `3`-ball per `2`-simplex, with Lemma 5 in manifold form as
`Section34FaceBallInvariants`; it now receives `IsOpen U` and the embedding `hh`, without which
the compact image boundaries it needs do not exist.  Chart-local: `Section34CarrierControl`
puts each carrier `H t` inside one piecewise linear chart of `M₂`, and `Moise341` read in that
chart supplies the approximation and the general position, which is the only use of `h341` in
this file.  It covers the page 240 [ASSERTED] items of Lemma 3, the arbitrarily small
shell-separated cell neighbourhoods of `σ` and their transfer along `h`, the two general
position clauses, and the page 241 [ASSERTED] sufficient condition for Lemma 5(7).

`exists_section34Compression` (P4a, Operation 1 and Lemma 6, deep, repaired) and
`exists_section34BigonSlide` (P4b, Operation 2 and Lemma 7, deep, repaired): one step at one
label.  Each takes `hU hh`, the invariants and an available operation at `s`, in the shape
`Section34Compression` and `Section34BigonSlide` whose negations are literally conjuncts sixteen
and seventeen of `Section34NormalPlus`, and returns a family that agrees with the old one at
every other label, still satisfies the invariants and has the two counts at `s` as stated
above.  They cover the page 242 [ASSERTED] items: that one of the two spheres produced by
Operation 1 still bounds a `3`-cell around `h '' Bd σ` — this is where the compression step also
receives `hctrl`, added at the second review: outside `ℝ³` an outer compression need not leave a
sphere bounding a ball (in `S² × ℝ`, compressing `(S² ∖ Int D) × [−1,1]` along `D × {0}` gives two
spheres, each a non-zero class of `H₂`, neither bounding a ball), so the proof chooses a
tetrahedron `t ⊇ s`, places the old ball and the compression disk inside `interior (H t)`, and
uses the single-chart PL ball carrier of `Section34CarrierControl` to fill the compressed sphere
by the local Schoenflies theorem — that Operation 2 exists at all, and the
unargued clauses (1), (3), (4), (6), (8) of Lemma 6 and the whole of Lemma 7, the preservation
of 5(6) and of 5(7) under Operation 2 being the two that `A-section34-lemma-list` §5 names as
the first places a formalisation stalls.  `A2-answer-digest`'s cleanliness point is honoured:
Operation 1's input already carries `Dj ∩ fblBd s = Jd`, the exact-intersection form of the
clean disk.

`exists_section34TerminalFaceBalls` (P5, Lemma 8, deep, OK, frozen): the isolated limit step.
Book Lemma 8 alternates the two operations until neither is possible and counts over a finite
complex; here the label type is infinite, so the leaf takes the two steps as hypotheses in the
descent shape, plus the carrier control, and returns a family satisfying the invariants at
which neither operation is available.  The descent itself is per label and finite, and the
carriers are locally finite in `h '' U`; what the leaf owes is the passage to the pointwise
limit of a locally finite sequence of modifications and the fairness argument that a legal move
of the limit, having a compact witness meeting finitely many carriers, would already have been
performed: a fair enumeration of the labels, each changed finitely often, so that every compact
witness stabilises.

`section34Trace_of_noOperation` (Lemmas 9--11, deep, repaired): from `hU hh`, the invariants and
the two impossibility clauses, `Section34Trace`.  Lemma 9's chain argument needs the link
condition of page 239, that in the link of a vertex the interior of an edge never separates two
vertices; by `A2-answer-digest` Q4 that is (Link-E) for a triangulated `2`-sphere or `2`-disk,
hence a consequence of `IsCombinatorialManifold 3 𝒦.complex`, the first field of
`Section34CutFrame`, so it is **not** a further gap in P1 and is not taken as a hypothesis here.
Lemma 10 is used inside the same leaf, and Lemma 11 needs 28.8, which the tree does not state;
this leaf is where that external input enters.  It covers the page 243 [ASSERTED] termination
consequence and the page 244 [SLIP]/[AMBIG] around the 28.8 citation and "easily gives a
contradiction".

`section34TraceCircle_homologyMap_ne_zero` (bridge for P6, new): a polyhedral circle `J` on
`frontier (section34FaceTorus tgtV s)` meeting every incident splitting circle in exactly one
point is nonzero in `H₁` of the torus `T_σ`.  Its hypotheses are the cut frame, the graph frame,
the four `f₁`-images and the one-point clause of `Section34Trace`, nothing else, so P6 consumes
it by destructuring `Section34Trace` and applying it to each `J s i`, with `J s i ⊆ frontier`
read off `fblBd s ∩ frontier (section34FaceTorus tgtV s) = ⋃ i < r s, J s i`.  The argument: the
at least three splitting circles of `σ` cut the torus into annuli in the cyclic order of `∂σ`; a
circle bounding a disk of the torus meets a splitting circle `c_e` only in a point of the
disk's boundary, so the open disk lies in one annulus and cannot reach a third circle; and the
arcs of `J` between consecutive one-point meetings lie in consecutive annuli, so `J` crosses
each meridian disk `tgtE e` exactly once, which no null-homologous curve of `T_σ` does.  No
transversality is used, which is why it is derivable from `Section34NormalPlus` alone and why
5(1) and 5(6) are not added to that predicate, following ruling ③ of the review.  It stays a
leaf because the cyclic order of the annuli is combinatorics of `𝒦'` on `∂σ` that no exporter
states yet.

Proved here, not leaves.  `simplexBody_subset_of_mem_faces` and `graphSkeletonSpace_subset`, the
containments that let the controlled form of 35.1 be applied with `W := U`;
`nonempty_simplexRim` and `nonempty_section34FaceTorus`, which record that the target of the
generator field is a nonempty space; `carriesFirstHomologyOnto_self`, an inhabitant of the new
generator predicate; `section34FaceBallRank_congr` and the two descent lemmas; and the whole
packaging of the seventeen conjuncts of `Section34NormalPlus`, including the two cell conjuncts,
the containment of a splitting disk image in a vertex ball boundary image, conjunct eleven from
the injectivity of `f₁` on the cut neighbourhood, the carrier containment of a tetrahedron ball,
and the two impossibility conjuncts from the negations produced by P5.

Vacuity.  `[Nonempty M₁]` is inherited from the frozen leaf and is necessary, a
`LocallyFinitePLPieceIn` having a total realisation map.  The generator field quantifies over
`H₁` of the trace and not over its basepoints, and is false for an empty trace.  The counts are
functions of the current family and of the label alone, never free parameters,
`section34FaceBallRank_congr` stating exactly that, and the two finiteness fields stop
`Set.ncard` from reading an infinite set as zero.  The sets `Dj`, `Jd`, `B`, `B'`, `Bb` of the
two operation predicates are unpinned on purpose, because those predicates occur negated:
conjuncts sixteen and seventeen say that no such data exist, so a free parameter there
strengthens the statement instead of hollowing it, and the equations `Jd = B ∪ B'`,
`B ∩ B' = Bb`, `Dj ∩ fblBd s = Jd` are what keep the free sets an actual bigon or an actual
compression disk.  The families `tgtV`, `tgtVBd`, `tgtE`, `tgtEBd` are never left free in a
leaf hypothesis; every leaf carries them as the four `f₁`-images, so no leaf can be satisfied
by a family unrelated to the cut diagram.  On the fixture above every field of the bundle is
satisfied by the thickened triangles `C_σ`, and `IsCombinatorialManifold 3` is used only for the
complex of the open set `U`, never for a nonempty finite complex of `ℝ³`.  Two clauses of the
invariant are **not** exposed by `Section34NormalPlus`: Lemma 5(1), that `fbl s` is a
neighbourhood of `h '' simplexRim 𝒦 s.1`, and Lemma 5(6), the generator clause; what P6 needs
from them is the bridge leaf.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section CurveCrossing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def HasPLCurveCrossingOnAt (S A B : Set E) (x : E) : Prop :=
  ∃ (U V : Set E) (φ : E → E) (T P Q : Submodule ℝ E),
    IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ IsPLHomeomorphOn φ U V ∧ φ x = 0 ∧
      Module.finrank ℝ T = 2 ∧ Module.finrank ℝ P = 1 ∧ Module.finrank ℝ Q = 1 ∧
      P ≤ T ∧ Q ≤ T ∧ P ⊓ Q = ⊥ ∧ ∀ᶠ y in 𝓝 x,
        (y ∈ S ↔ φ y ∈ T) ∧ (y ∈ A ↔ φ y ∈ P) ∧ (y ∈ B ↔ φ y ∈ Q)

end CurveCrossing

section FirstHomology

variable {Y : Type u} [TopologicalSpace Y]

def CarriesFirstHomologyOnto (J T : Set Y) : Prop :=
  J ⊆ T ∧ ∀ hJT : J ⊆ T,
    Function.Surjective
      (integralSingularHomologyMap 1 (⟨inclusion hJT, continuous_inclusion hJT⟩ : C(J, T)))

theorem carriesFirstHomologyOnto_self (T : Set Y) : CarriesFirstHomologyOnto T T := by
  refine ⟨Subset.rfl, fun hJT => ?_⟩
  have hid : (⟨inclusion hJT, continuous_inclusion hJT⟩ : C(T, T)) = ContinuousMap.id T :=
    ContinuousMap.ext fun _ => rfl
  rw [hid, integralSingularHomologyMap_id]
  exact fun x => ⟨x, rfl⟩

end FirstHomology

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

noncomputable def section34TraceCount {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    (tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (fblBd : Section34SimplexIndex 𝒦 3 → Set M₂) (s : Section34SimplexIndex 𝒦 3) : ℕ :=
  (section34TraceComponents tgtV fblBd s).ncard

noncomputable def section34CrossingCount {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    (tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (fblBd : Section34SimplexIndex 𝒦 3 → Set M₂) (s : Section34SimplexIndex 𝒦 3) : ℕ :=
  (fblBd s ∩ ⋃ e : Section34EdgeIndex 𝒦 𝒦', tgtEBd e).ncard

noncomputable def section34FaceBallRank {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    (tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (fblBd : Section34SimplexIndex 𝒦 3 → Set M₂) (s : Section34SimplexIndex 𝒦 3) : ℕ :=
  section34TraceCount tgtV fblBd s + section34CrossingCount tgtEBd fblBd s

omit [FiniteDimensional ℝ Ea] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] in
theorem section34FaceBallRank_congr {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    {tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    {tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
    {fblBd fblBd' : Section34SimplexIndex 𝒦 3 → Set M₂} {s : Section34SimplexIndex 𝒦 3}
    (hs : fblBd s = fblBd' s) :
    section34FaceBallRank tgtV tgtEBd fblBd s = section34FaceBallRank tgtV tgtEBd fblBd' s := by
  simp only [section34FaceBallRank, section34TraceCount, section34CrossingCount,
    section34TraceComponents, hs]

omit [FiniteDimensional ℝ Ea] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] in
theorem section34FaceBallRank_lt_of_compression {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    {tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    {tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
    {fblBd fblBd' : Section34SimplexIndex 𝒦 3 → Set M₂} {s : Section34SimplexIndex 𝒦 3}
    (hc : section34TraceCount tgtV fblBd' s + 1 ≤ section34TraceCount tgtV fblBd s)
    (hp : section34CrossingCount tgtEBd fblBd' s ≤ section34CrossingCount tgtEBd fblBd s) :
    section34FaceBallRank tgtV tgtEBd fblBd' s < section34FaceBallRank tgtV tgtEBd fblBd s := by
  simp only [section34FaceBallRank]
  omega

omit [FiniteDimensional ℝ Ea] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] in
theorem section34FaceBallRank_lt_of_bigonSlide {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    {tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    {tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
    {fblBd fblBd' : Section34SimplexIndex 𝒦 3 → Set M₂} {s : Section34SimplexIndex 𝒦 3}
    (hc : section34TraceCount tgtV fblBd' s = section34TraceCount tgtV fblBd s)
    (hp : section34CrossingCount tgtEBd fblBd' s + 2 = section34CrossingCount tgtEBd fblBd s) :
    section34FaceBallRank tgtV tgtEBd fblBd' s < section34FaceBallRank tgtV tgtEBd fblBd s := by
  simp only [section34FaceBallRank]
  omega

def Section34FaceBallInvariants (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U) (h : M₁ → M₂)
    (H : Finset Ea → Set M₂) (tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂) : Prop :=
  (∀ s, IsPLCellOn 3 (fbl s) (fblBd s)) ∧
  (∀ s : Section34SimplexIndex 𝒦 3, h '' simplexRim 𝒦 s.1 ⊆ interior (fbl s)) ∧
  (∀ (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦'),
    ¬ Section34Incident w.1 s.1 → fbl s ∩ tgtV w = ∅) ∧
  (∀ s s', s ≠ s' → fbl s ∩ fbl s' ⊆ interior (⋃ w, tgtV w)) ∧
  (∀ s, ∀ y ∈ fblBd s ∩ frontier (⋃ w, tgtV w),
    ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, y ∈ c.source ∧
      HasPLCrossingAt (c '' (fblBd s ∩ c.source))
        (c '' (frontier (⋃ w, tgtV w) ∩ c.source)) (c y)) ∧
  (∀ (s : Section34SimplexIndex 𝒦 3) (e : Section34EdgeIndex 𝒦 𝒦'),
    ∀ y ∈ fblBd s ∩ tgtEBd e,
    ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, y ∈ c.source ∧
      HasPLCurveCrossingOnAt (c '' (frontier (⋃ w, tgtV w) ∩ c.source))
        (c '' (fblBd s ∩ frontier (⋃ w, tgtV w) ∩ c.source))
        (c '' (tgtEBd e ∩ c.source)) (c y)) ∧
  (∀ s, CarriesFirstHomologyOnto (fblBd s ∩ frontier (section34FaceTorus tgtV s))
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
    (tgtV tgtVBd : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (tgtE tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (fblBd : Section34SimplexIndex 𝒦 3 → Set M₂) (s : Section34SimplexIndex 𝒦 3) : Prop :=
  ∃ (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦') (B B' Bb Dj Jd : Set M₂),
    IsPLCellOn 1 B Bb ∧ B ⊆ fblBd s ∧ B ⊆ tgtVBd w ∧ Bb ⊆ tgtEBd e ∧
      B ∩ (⋃ e' : Section34EdgeIndex 𝒦 𝒦', tgtE e') = Bb ∧
      IsPLCellOn 1 B' Bb ∧ B' ⊆ tgtEBd e ∧ B ∩ B' = Bb ∧
      IsPLCellOn 2 Dj Jd ∧ Dj ⊆ tgtVBd w ∩ frontier (⋃ w, tgtV w) ∧ Jd = B ∪ B' ∧
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

theorem exists_section34FaceBalls (h341 : Moise341) (hU : IsOpen U)
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁) :
    ∃ fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂,
      Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
        (section34SplitDiskImage srcBd f₁) fbl fblBd := by
  sorry

theorem exists_section34Compression (hU : IsOpen U)
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hctrl : Section34CarrierControl U 𝒦 h η H)
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
      section34TraceCount (section34VertexBallImage src f₁) fblBd' s + 1 ≤
        section34TraceCount (section34VertexBallImage src f₁) fblBd s ∧
      section34CrossingCount (section34SplitDiskImage srcBd f₁) fblBd' s ≤
        section34CrossingCount (section34SplitDiskImage srcBd f₁) fblBd s := by
  sorry

theorem exists_section34BigonSlide (hU : IsOpen U)
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁)
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (s : Section34SimplexIndex 𝒦 3)
    (hop : Section34BigonSlide 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34VertexBallImage srcBd f₁) (section34SplitDiskImage src f₁)
      (section34SplitDiskImage srcBd f₁) fblBd s) :
    ∃ fbl' fblBd' : Section34SimplexIndex 𝒦 3 → Set M₂,
      Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
        (section34SplitDiskImage srcBd f₁) fbl' fblBd' ∧
      (∀ s', s' ≠ s → fbl' s' = fbl s' ∧ fblBd' s' = fblBd s') ∧
      section34TraceCount (section34VertexBallImage src f₁) fblBd' s =
        section34TraceCount (section34VertexBallImage src f₁) fblBd s ∧
      section34CrossingCount (section34SplitDiskImage srcBd f₁) fblBd' s + 2 =
        section34CrossingCount (section34SplitDiskImage srcBd f₁) fblBd s := by
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
      Section34BigonSlide 𝒦 𝒦' (section34VertexBallImage src f₁)
        (section34VertexBallImage srcBd f₁) (section34SplitDiskImage src f₁)
        (section34SplitDiskImage srcBd f₁) gBd s →
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
      ∀ s, ¬ Section34BigonSlide 𝒦 𝒦' (section34VertexBallImage src f₁)
        (section34VertexBallImage srcBd f₁) (section34SplitDiskImage src f₁)
        (section34SplitDiskImage srcBd f₁) fblBd' s := by
  sorry

theorem section34Trace_of_noOperation (hU : IsOpen U)
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁)
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hnc : ∀ s, ¬ Section34Compression 𝒦 𝒦' (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) fbl fblBd s)
    (hnb : ∀ s, ¬ Section34BigonSlide 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34VertexBallImage srcBd f₁) (section34SplitDiskImage src f₁)
      (section34SplitDiskImage srcBd f₁) fblBd s) :
    Section34Trace 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fblBd := by
  sorry

theorem section34TraceCircle_homologyMap_ne_zero
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁)
    (s : Section34SimplexIndex 𝒦 3) {J : Set M₂} (hJ : IsPolyhedralSphere (n := 3) 1 J)
    (hJT : J ⊆ frontier (section34FaceTorus (section34VertexBallImage src f₁) s))
    (hJe : ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 s.1 →
      ∃ p, J ∩ section34SplitDiskImage srcBd f₁ e = {p})
    (hsub : J ⊆ section34FaceTorus (section34VertexBallImage src f₁) s) :
    integralSingularHomologyMap 1
      (⟨inclusion hsub, continuous_inclusion hsub⟩ :
        C(J, section34FaceTorus (section34VertexBallImage src f₁) s)) ≠ 0 := by
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
  obtain ⟨fbl₀, fblBd₀, hinv₀⟩ := exists_section34FaceBalls h341 hU hh hcut hctrl hgraph
  obtain ⟨fbl, fblBd, hinv, hnc, hnb⟩ :=
    exists_section34TerminalFaceBalls hcut hgraph hctrl hinv₀
      (fun _ _ s hg hop => by
        obtain ⟨g', gBd', hinv', hoff, hc, hp⟩ :=
          exists_section34Compression hU hh hcut hctrl hgraph hg s hop
        exact ⟨g', gBd', hinv', hoff, section34FaceBallRank_lt_of_compression hc hp⟩)
      (fun _ _ s hg hop => by
        obtain ⟨g', gBd', hinv', hoff, hc, hp⟩ :=
          exists_section34BigonSlide hU hh hcut hgraph hg s hop
        exact ⟨g', gBd', hinv', hoff, section34FaceBallRank_lt_of_bigonSlide hc hp⟩)
  obtain ⟨hfblcell, -, hfblV, hfblfbl, -, -, -, -, -, hext⟩ := id hinv
  have htrace := section34Trace_of_noOperation hU hh hcut hgraph hinv hnc hnb
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
    fun s w e B B' Bb Dj Jd h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
      hnb s ⟨w, e, B, B', Bb, Dj, Jd, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
