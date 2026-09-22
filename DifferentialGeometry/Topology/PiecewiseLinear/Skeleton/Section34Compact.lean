/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.Integral
import DifferentialGeometry.Topology.PiecewiseLinear.CellMapTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.ControlledInwardPush
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import DifferentialGeometry.Topology.PiecewiseLinear.TameNestedCells

/-!
# Sorry-first skeleton of Section 34 on a compact piecewise linear ball: a producer of `Moise341`

The two assemblies `moise341OnNeighborhood` and `moise341_of_onNeighborhood` prove, for real,
the local endpoint `Moise341OnNeighborhood` and then `Moise341` (Moise 34.1, page 239) from the
twelve leaves of this file and the two named propositions `Moise331` (33.1) and `Moise305Tame`
(the tame 30.5, proved from `Moise304`); every `sorry` is a leaf and none sits inside an
assembly.  This closes the cycle found on 2026-09-21 (design consult AL, digest AO): the only
tree route to `Moise341` ran through `Moise352Open`, whose terminal skeleton depends on the
controlled 35.1, which consumes `Moise341`.  The chain is now one way,
`33.1 → 34.1 → controlled 35.1 → 35.2`.

Why the open skeletons cannot be instantiated at `U := C`.  `Section34CutFrame` asks the
boundaryless `IsCombinatorialManifold 3 𝒦.complex`, which no nonempty finite complex of `ℝ³`
satisfies, and `⋃ src = U`, whereas the cells of the compact cut cover `C ∪ N` with `N ⊄ C`;
`Section34Exterior` reads "unbounded component" as "reaches the frontier of a carrier", while
Lemma 5(7) and the `Y₀` rule of page 245 use the unbounded component of `ℝ³` literally; and the
boundaryless boundary formulas `∂C_v = ⋃ D_e ∪ ⋃ X_{tv}`, `∂D_e = ⋃ I_{te}` are false at a
boundary vertex or edge.  Three sets are kept apart: the ball `C`, the open domain `V` of the
embedding, and the assembly domain `C ∪ N`.

The entry reduction (option (c) of the design, the opening reduction of §34, page 239):
`moise341_of_onNeighborhood` pushes `C` into its interior by
`exists_isPLBall_subset_interior_dist_lt`, proved here from the tree's controlled inward push
`IsCombinatorialManifoldWithBoundary.exists_piecewiseAffineOn_inward_dist_lt` (a triangulation
of the ball from `IsPolyhedron.exists_simplicialComplex`, its manifold certificate from
`IsPLBall.isCombinatorialManifoldWithBoundary`), applies the neighbourhood statement to
`C₋ := p '' C`, `V := interior C`, tolerance `ε / 2`, and composes; the push is independent of
the approximation theorem, `h` is never extended beyond `C`, and no approximation is extended
across a collar.

The finite cut.  `Section34BoundedLabel` has the eight cell kinds of `Section34Frame` **and two
more**, the outer faces `O_v` of the boundary vertices and the outer arcs `o_e` of the boundary
edges, pinned by `O_v = closure (∂C_v \ (C ∪ ⋃ D_e))` and `o_e = closure (∂D_e \ C)`, so that the
general boundary formula of the cut frame decomposes all of `∂C_v` and `∂D_e`.  Face disks and
residual balls are pinned by the book's `d_σ = Cl(σ − N)`, `C(σ³) = Cl(σ³ − N)`.  The link
condition removes only the open edge and retains both endpoints.  In a sphere or disk link,
one can bypass it along the other two edges of an incident triangle; no extra subdivision is
needed for this condition.  It remains a frame clause until that consequence is formalised.

Local outer-cut check: `C` a tetrahedron, `K = K'` the tetrahedron itself, and `N` a regular
neighbourhood of its six edges.  All four vertices and six edges are on the boundary; `∂C_v`
is the union of three splitting disks, one patch and one outer face, `∂D_e` of one edge arc and
one outer arc, `∂O_v` of three face arcs and three outer arcs, `∂o_e` of two marked points.
Without the two outer kinds the boundaryless formulas leave `∂C_v` minus a hexagon and `∂D_e`
minus an arc undecomposed; that is the interface error of option (a).  The link of each vertex
is a triangle, which satisfies the link condition.  This checks the outer-cut combinatorics
only, not the carrier or approximation hypotheses.  A full fixture for a small tolerance
requires a sufficiently fine triangulation `K` and compatible `K'`, chosen after `h` and `ε`;
that joint fixture remains UNTESTED.

The first review is recorded in `consult/AS-section34-compact-first-review-digest.md`.
Ten leaves were accepted; the envelope and compression interfaces below add the supplied
open-domain and carrier certificates.  All twelve proof obligations remain open.

`exists_compactCutAndGraph` (Lemma 1, Lemma 2's configuration, the subdivision; deep; pages
239--240): from `h331` and the entry data, `K, K'`, the full cut, carriers, `N ⊆ V` and `f₁`.  This
joint choice is **not** a projection of `Moise331`: the finite cut and 33.1's derived
neighbourhood are linked by a compatible subdivision; the carriers and the tolerance are chosen
first, then `f₁`, then the inner torus `S₁`.  The proved exporter
`Section34CompactGraphFrame.carriesFundamentalGroupOnto` applies the tree's nested-torus
generator theorem to `(S₁, N''_σ, S₂, h '' ∂σ)`; the assembly passes this conclusion explicitly
to `compactTraceHomology`.  [ASSERTED] in the book: Lemma 1(2)--(4) "for `f₁`
sufficiently close", Lemma 2's (a)--(f) and that `∂σ` is a spine, and the sufficient condition
for 5(7) of page 241 (recorded here as the
exterior clause for the thin obstacle `⋃_{v ∈ t} V_v ∪ ⋃_{σ ⊂ t} h '' σ`).

`exists_compactFaceEnvelopes` (the smallness of Lemmas 3--5; medium): open neighbourhoods
`env σ` of `h '' σ` avoiding the non-incident vertex balls, overlapping only in `Int N''`, inside
the carriers, with the auxiliary ball `A` of Lemma 4 (a polyhedral cell around `h '' τ` for a
source disk `τ` with `τ ∩ K² = ∂σ`, by `h305`) such that `env σ ∩ A ⊆ Int N''_σ`, and 5(7) for
the thickened obstacle, derived from the thin one by choosing the envelopes after finitely many
escape paths.  The explicit `IsOpen V` input supplies room for transporting the auxiliary
ball's two collars; mere containment `C ⊆ V` does not supply that room.

`exists_compactFaceShellBalls` (Lemma 3, first half; medium; page 240): from `h305`, piecewise
linear 3-balls `C_σ ⊆ env σ` with `h '' σ ⊆ Int C_σ`; the nested cells around `σ` with a
spherical shell and a bicollared outer sphere are built in the source and transported by the
embedding.  [ASSERTED]: arbitrarily small shell-separated cell neighbourhoods of `σ` and their
transfer along `h`.

`exists_compactFaceBallsGeneralPosition` (Lemma 3, second half; medium): the two crossing normal
forms 5(3), 5(4) and the two finiteness counts by a small piecewise linear perturbation inside
the envelopes.  [AMBIG] "general position in one of its usual senses" is read as both forms.

`compactTraceHomology` (Lemma 4; deep; page 241): the whole trace `∂C_σ ∩ ∂N''_σ` of a ball in
its envelope carries `H₁(N''_σ)` onto, via the auxiliary ball `A` and the explicit, proved
fundamental-group generator clause.  The passage from that generator to trace homology is open.
[SLIP] the book cites Lemma 1(4) for what is Lemma 2.

`exists_compactCompression` (Operation 1 and Lemma 6; deep; page 242) and
`exists_compactBigonSlide` (Operation 2 and Lemma 7; deep; page 242): one step at one label,
preserving the invariants, the other labels unchanged, `c⁺ + 1 ≤ c ∧ p⁺ ≤ p` respectively
`c⁺ = c ∧ p⁺ + 2 = p`; the bigon is pinned as in clause 17 of `Section34NormalPlus`.  In `ℝ³`
the compressed sphere bounds a ball by the piecewise linear Schoenflies theorem.  The supplied
carrier certificate makes each incident carrier a PL ball, so its connected unbounded exterior
keeps that filling inside the carrier.  [ASSERTED]:
that one of the two spheres of Operation 1 still surrounds `h '' ∂σ`, the existence of the drag
of Operation 2 (Figure 34.1), clauses (1), (3), (4), (6), (8) of Lemma 6, the whole of Lemma 7.

`compactTrace_of_noOperation` (Lemmas 9--11; deep; pages 243--244): from the invariants and the
two impossibility clauses, the finite trace certificate `Section34CompactTrace`, whose last
clause is that each trace circle is nonzero in `H₁(N''_σ)`.  Uses the link condition and 28.8,
which the tree does not state.  [ASSERTED]: Case 2 of Lemma 11; [AMBIG] the 28.8 citation.

`exists_compactFaceDisks` (page 244, step P6; medium): the irreducible disks `D''_σ ⊆ ∂C_σ` with
boundary a trace circle, their face arcs and marked points.  [ASSERTED]: existence of the
irreducible disk.

`exists_compactResidualBalls` (pages 244--245, step P7; deep): the residual balls `C''(σ³)`
bounded by the four patches `X_i` and the four face disks, the patches chosen by the literal
unbounded-component rule, the edge arcs with the empty-sector certificate (no third marked point
on `D''_e ∩ ∂C''(σ³)`), **and the outer faces and outer arcs of the target**, pinned by the same
closure formulas as in the source, with the tilings `∂V_w = ⋃ E_e ∪ ⋃ X''_{tw} ∪ O''_w` and
`∂E_e = ⋃ I''_{te} ∪ o''_e`.  [ASSERTED]: that `⋃ D''_σ` does not separate `ℝ³`; the cyclic order
of the edge arcs around `∂E_e` comes from the empty-sector certificate.

`compactSourceFace_iff_cutLe` (page 244, source incidences; short): on the source cut, inclusion
of cells is the reflexive transitive closure of the codimension-one incidences, now including
the outer faces and arcs.

`compactTargetRecognition` (page 245--246, step P8; medium): the target family, all ten kinds,
has intrinsic boundary the union of its proper faces and exact pairwise meets for the face
relation read off the source.  Rests on the uniqueness of the intrinsic boundary
(`IsPLCellOn.boundary_eq`) and its agreement with the frontier in codimension zero.

Proved here, not leaves: the entry reduction and the push for a ball; the descent
`exists_compactTerminalFaceBalls` (Lemma 8, page 243), a strong induction on the finite sum
`∑_σ (c_σ + p_σ)`, with no limit leaf, the [ASSERTED] termination of alternating the two
operations being discharged by the common measure; the assembly of the initial invariant bundle
from the envelopes, the shell balls, general position and Lemma 4, including 5(7) by
monotonicity of the unbounded component; the whole extension in the order marked points,
splitting circles, face arcs, splitting disks, faces, vertex balls, face disks, residual balls,
which is the dimension induction of `exists_isPLHomeomorphInto_of_labelledCells` applied to the
labelled diagram `(src, tc)` with the face relation `section34Face src`; the `ε`-estimate from
the carriers; the restriction of the assembled embedding of `C ∪ N` to `C`; and the finiteness
of the label type.  `f|N = f₁` is not required (the Query of page 246).

Inhabitants.  `carriesIntegralFirstHomologyOnto_self` inhabits the generator predicate.
`HasPLSurfaceCurveCrossingAt`: UNTESTED, missing brick an explicit normal form at the origin
with the plane `z = 0` and the two axes (`isPLOn_id_of_isOpen` gives the chart).  The frames
`Section34CompactCutFrame`, `Section34CompactCarrierControl`, `Section34CompactGraphFrame`,
`Section34CompactFaceEnvelopes`, `Section34CompactFaceBallInvariants`, `Section34CompactTrace`,
`Section34CompactFaceDiskFamily`, `Section34CompactResidualPlus`: UNTESTED.  The local
tetrahedron check above does not supply a joint carrier-controlled fixture: this still needs a
sufficiently fine triangulation, a compatible subdivision and a regular neighbourhood with
verified dual cells.  Nondegeneracy at the intended entry starts from `IsPLBall 3 C`; no
unconditional inhabitant of these frames is claimed.  `Section34CompactExterior` on its own
holds for an empty obstacle (the component of `univ` is unbounded); it gets its content from
the cell clauses of the bundles it sits in and is never a hypothesis by itself.

Vacuity.  The generator clauses quantify over `H₁` of a nonempty torus and fail for an empty
trace; the counts read the family at one label only (`section34CompactFaceBallRank_congr`); the
operations occur negated, so their free sets strengthen the statements; every leaf carries the
four `f₁`-images and never a free target family; no injectivity hypothesis is placed on a loop;
the outer cells, the face disks and the residual balls of the source are pinned by formulas.

To be hoisted into a real module: `Section34BoundedLabel` with `section34BoundedDim`,
`section34BoundedCell`, its finiteness; the compact index types, `Section34CompactCutStep`,
`section34CompactCutNeighborhood`, `section34CompactFaceTorus`, the frames and the counts;
`HasPLSurfaceCurveCrossingAt` and `CarriesIntegralFirstHomologyOnto` (to be merged with the
same-content predicates of `Section34Normalization`); `IsPLCellOn.isPolyhedron`,
`isPLHomeomorphInto_of_isPLHomeomorphOn_of_subset`, `exists_isPLBall_subset_interior_dist_lt`,
`isEmbedding_domRestrict_interior_of_continuousOn_injOn`.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe v

section Label

inductive Section34BoundedLabel (Vx Tt Ed Fc Pa Ar Eg Mk Ov Oe : Type v) : Type v
  | vertexBall (v : Vx)
  | tetraBall (t : Tt)
  | splitDisk (e : Ed)
  | faceDisk (s : Fc)
  | patch (x : Pa)
  | faceArc (a : Ar)
  | edgeArc (i : Eg)
  | markedPoint (p : Mk)
  | outerFace (o : Ov)
  | outerArc (q : Oe)

variable {Vx Tt Ed Fc Pa Ar Eg Mk Ov Oe : Type v}

def section34BoundedDim : Section34BoundedLabel Vx Tt Ed Fc Pa Ar Eg Mk Ov Oe → ℕ
  | .vertexBall _ => 3
  | .tetraBall _ => 3
  | .splitDisk _ => 2
  | .faceDisk _ => 2
  | .patch _ => 2
  | .faceArc _ => 1
  | .edgeArc _ => 1
  | .markedPoint _ => 0
  | .outerFace _ => 2
  | .outerArc _ => 1

def section34BoundedCell {M : Type*} (cV : Vx → Set M) (cT : Tt → Set M) (cE : Ed → Set M)
    (cF : Fc → Set M) (cP : Pa → Set M) (cA : Ar → Set M) (cG : Eg → Set M) (cM : Mk → Set M)
    (cO : Ov → Set M) (cQ : Oe → Set M) :
    Section34BoundedLabel Vx Tt Ed Fc Pa Ar Eg Mk Ov Oe → Set M
  | .vertexBall v => cV v
  | .tetraBall t => cT t
  | .splitDisk e => cE e
  | .faceDisk s => cF s
  | .patch x => cP x
  | .faceArc a => cA a
  | .edgeArc i => cG i
  | .markedPoint p => cM p
  | .outerFace o => cO o
  | .outerArc q => cQ q

theorem section34BoundedDim_le_three (l : Section34BoundedLabel Vx Tt Ed Fc Pa Ar Eg Mk Ov Oe) :
    section34BoundedDim l ≤ 3 := by
  cases l <;> simp [section34BoundedDim]

theorem section34BoundedDim_eq_three {l : Section34BoundedLabel Vx Tt Ed Fc Pa Ar Eg Mk Ov Oe}
    (hl : section34BoundedDim l = 3) : (∃ v, l = .vertexBall v) ∨ ∃ t, l = .tetraBall t := by
  cases l <;> first
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr ⟨_, rfl⟩
    | simp [section34BoundedDim] at hl

def section34BoundedEncode : Section34BoundedLabel Vx Tt Ed Fc Pa Ar Eg Mk Ov Oe →
    Option Vx × Option Tt × Option Ed × Option Fc × Option Pa × Option Ar × Option Eg ×
      Option Mk × Option Ov × Option Oe
  | .vertexBall v => (some v, none, none, none, none, none, none, none, none, none)
  | .tetraBall t => (none, some t, none, none, none, none, none, none, none, none)
  | .splitDisk e => (none, none, some e, none, none, none, none, none, none, none)
  | .faceDisk s => (none, none, none, some s, none, none, none, none, none, none)
  | .patch x => (none, none, none, none, some x, none, none, none, none, none)
  | .faceArc a => (none, none, none, none, none, some a, none, none, none, none)
  | .edgeArc i => (none, none, none, none, none, none, some i, none, none, none)
  | .markedPoint p => (none, none, none, none, none, none, none, some p, none, none)
  | .outerFace o => (none, none, none, none, none, none, none, none, some o, none)
  | .outerArc q => (none, none, none, none, none, none, none, none, none, some q)

theorem section34BoundedEncode_injective :
    Function.Injective (section34BoundedEncode (Vx := Vx) (Tt := Tt) (Ed := Ed) (Fc := Fc)
      (Pa := Pa) (Ar := Ar) (Eg := Eg) (Mk := Mk) (Ov := Ov) (Oe := Oe)) := by
  intro l m hlm
  cases l <;> cases m <;>
    simp only [section34BoundedEncode, Prod.mk.injEq, Option.some.injEq, reduceCtorEq,
      and_true, true_and, and_false] at hlm <;>
    rw [hlm]

instance [Finite Vx] [Finite Tt] [Finite Ed] [Finite Fc] [Finite Pa] [Finite Ar] [Finite Eg]
    [Finite Mk] [Finite Ov] [Finite Oe] :
    Finite (Section34BoundedLabel Vx Tt Ed Fc Pa Ar Eg Mk Ov Oe) :=
  Finite.of_injective _ section34BoundedEncode_injective

end Label

section Vocabulary

variable {K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}

def section34CompactGraphSkeleton (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  ⋃ t ∈ {t : Finset (EuclideanSpace ℝ (Fin 3)) | t ∈ K.faces ∧ t.card ≤ 2},
    convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin 3)))

def section34CompactSimplexRim (t : Finset (EuclideanSpace ℝ (Fin 3))) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  ⋃ s ∈ {s : Finset (EuclideanSpace ℝ (Fin 3)) | s ⊂ t},
    convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 3)))

def section34CompactCarrierSupport (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (t : Finset (EuclideanSpace ℝ (Fin 3))) : Set (EuclideanSpace ℝ (Fin 3)) :=
  ⋃ w ∈ (t : Set (EuclideanSpace ℝ (Fin 3))),
    ⋃ s ∈ {s : Finset (EuclideanSpace ℝ (Fin 3)) | s ∈ K.faces ∧ w ∈ s},
      convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 3)))

theorem section34CompactSimplexRim_subset (t : Finset (EuclideanSpace ℝ (Fin 3))) :
    section34CompactSimplexRim t ⊆ convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin 3))) :=
  iUnion₂_subset fun _ hs => convexHull_mono (Finset.coe_subset.mpr hs.subset)

abbrev Section34CompactSimplexIndex
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) (k : ℕ) :=
  {t : Finset (EuclideanSpace ℝ (Fin 3)) // t ∈ K.faces ∧ t.card = k}

abbrev Section34CompactGraphIndex
    (K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (Γ : Set (EuclideanSpace ℝ (Fin 3))) (k : ℕ) :=
  {t : Finset (EuclideanSpace ℝ (Fin 3)) //
    t ∈ K'.faces ∧ t.card = k ∧ convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Γ}

abbrev Section34CompactVertexIndex
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) :=
  Section34CompactGraphIndex K' (section34CompactGraphSkeleton K) 1

abbrev Section34CompactEdgeIndex
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) :=
  Section34CompactGraphIndex K' (section34CompactGraphSkeleton K) 2

abbrev Section34CompactPatchIndex
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) :=
  {p : Section34CompactSimplexIndex K 4 × Section34CompactVertexIndex K K' //
    Section34Incident p.2.1 p.1.1}

abbrev Section34CompactArcIndex
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) :=
  {p : Section34CompactSimplexIndex K 3 × Section34CompactVertexIndex K K' //
    Section34Incident p.2.1 p.1.1}

abbrev Section34CompactEdgeArcIndex
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) :=
  {p : Section34CompactSimplexIndex K 4 × Section34CompactEdgeIndex K K' //
    Section34Incident p.2.1 p.1.1}

abbrev Section34CompactMarkIndex
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) :=
  {p : Section34CompactSimplexIndex K 3 × Section34CompactEdgeIndex K K' //
    Section34Incident p.2.1 p.1.1}

abbrev Section34CompactOuterVertexIndex
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) :=
  {w : Section34CompactVertexIndex K K' //
    (w.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ frontier K.space}

abbrev Section34CompactOuterEdgeIndex
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) :=
  {e : Section34CompactEdgeIndex K K' //
    convexHull ℝ (e.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ frontier K.space}

abbrev Section34CompactLabelOf
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) :=
  Section34BoundedLabel (Section34CompactVertexIndex K K') (Section34CompactSimplexIndex K 4)
    (Section34CompactEdgeIndex K K') (Section34CompactSimplexIndex K 3)
    (Section34CompactPatchIndex K K') (Section34CompactArcIndex K K')
    (Section34CompactEdgeArcIndex K K') (Section34CompactMarkIndex K K')
    (Section34CompactOuterVertexIndex K K') (Section34CompactOuterEdgeIndex K K')

theorem finite_section34CompactSimplexIndex (hK : K.faces.Finite) (k : ℕ) :
    Finite (Section34CompactSimplexIndex K k) :=
  (hK.subset fun _ ht => ht.1).to_subtype

theorem finite_section34CompactGraphIndex (hK' : K'.faces.Finite)
    (Γ : Set (EuclideanSpace ℝ (Fin 3))) (k : ℕ) :
    Finite (Section34CompactGraphIndex K' Γ k) :=
  (hK'.subset fun _ ht => ht.1).to_subtype

theorem finite_section34CompactLabelOf (hK : K.faces.Finite) (hK' : K'.faces.Finite) :
    Finite (Section34CompactLabelOf K K') := by
  have h3 := finite_section34CompactSimplexIndex hK 3
  have h4 := finite_section34CompactSimplexIndex hK 4
  have hv := finite_section34CompactGraphIndex hK' (section34CompactGraphSkeleton K) 1
  have he := finite_section34CompactGraphIndex hK' (section34CompactGraphSkeleton K) 2
  infer_instance

theorem exists_face_of_section34CompactVertexIndex (w : Section34CompactVertexIndex K K') :
    ∃ t ∈ K.faces, (w.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin 3))) := by
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp w.2.2.1
  have hvΓ : v ∈ section34CompactGraphSkeleton K :=
    w.2.2.2 (subset_convexHull ℝ _ (by rw [hv]; simp))
  simp only [section34CompactGraphSkeleton, mem_iUnion, mem_ofPred_eq, exists_prop] at hvΓ
  obtain ⟨t, ⟨ht, -⟩, hvt⟩ := hvΓ
  refine ⟨t, ht, ?_⟩
  rw [hv, Finset.coe_singleton, singleton_subset_iff]
  exact hvt

def Section34CompactCutStep :
    Section34CompactLabelOf K K' → Section34CompactLabelOf K K' → Prop
  | .splitDisk e, .vertexBall w => w.1 ⊆ e.1
  | .patch x, .vertexBall w => x.1.2 = w
  | .outerFace o, .vertexBall w => o.1 = w
  | .faceDisk s, .tetraBall t => Section34Incident s.1 t.1
  | .patch x, .tetraBall t => x.1.1 = t
  | .edgeArc i, .splitDisk e => i.1.2 = e
  | .outerArc q, .splitDisk e => q.1 = e
  | .faceArc a, .faceDisk s => a.1.1 = s
  | .faceArc a, .patch x => a.1.2 = x.1.2 ∧ Section34Incident a.1.1.1 x.1.1.1
  | .edgeArc i, .patch x => i.1.1 = x.1.1 ∧ x.1.2.1 ⊆ i.1.2.1
  | .faceArc a, .outerFace o =>
    a.1.2 = o.1 ∧ convexHull ℝ (a.1.1.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ frontier K.space
  | .outerArc q, .outerFace o => o.1.1 ⊆ q.1.1
  | .markedPoint p, .faceArc a => p.1.1 = a.1.1 ∧ a.1.2.1 ⊆ p.1.2.1
  | .markedPoint p, .edgeArc i => p.1.2 = i.1.2 ∧ Section34Incident p.1.1.1 i.1.1.1
  | .markedPoint p, .outerArc q =>
    p.1.2 = q.1 ∧ convexHull ℝ (p.1.1.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ frontier K.space
  | _, _ => False

def Section34CompactCutLe :
    Section34CompactLabelOf K K' → Section34CompactLabelOf K K' → Prop :=
  Relation.ReflTransGen Section34CompactCutStep

def section34CompactCutNeighborhood
    (src : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  ⋃ w : Section34CompactVertexIndex K K', src (.vertexBall w)

def section34CompactFaceTorus
    (V : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (s : Section34CompactSimplexIndex K 3) : Set (EuclideanSpace ℝ (Fin 3)) :=
  ⋃ (a : Section34CompactArcIndex K K') (_ : a.1.1 = s), V a.1.2

def section34CompactVertexBallImage
    (c : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (w : Section34CompactVertexIndex K K') : Set (EuclideanSpace ℝ (Fin 3)) :=
  g '' c (.vertexBall w)

def section34CompactSplitDiskImage
    (c : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (e : Section34CompactEdgeIndex K K') : Set (EuclideanSpace ℝ (Fin 3)) :=
  g '' c (.splitDisk e)

open Classical in
def Section34CompactLinkCondition
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin 3), {v} ∈ K.faces →
    ∀ e ∈ (SimplicialComplex.geometricLink K {v}).faces, e.card = 2 →
    ∀ a b : EuclideanSpace ℝ (Fin 3), {a} ∈ (SimplicialComplex.geometricLink K {v}).faces →
      {b} ∈ (SimplicialComplex.geometricLink K {v}).faces →
      b ∈ connectedComponentIn ((SimplicialComplex.geometricLink K {v}).space \
        (convexHull ℝ (e : Set (EuclideanSpace ℝ (Fin 3))) \ (e : Set (EuclideanSpace ℝ (Fin 3)))))
        a

def Section34CompactCutFrame (C : Set (EuclideanSpace ℝ (Fin 3)))
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (src srcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  K.space = C ∧
  K.faces.Finite ∧
  K'.faces.Finite ∧
  IsCombinatorialManifoldWithBoundary 3 K ∧
  IsSubdivision K' K ∧
  Section34CompactLinkCondition K ∧
  (∀ l, IsPLCellOn (section34BoundedDim l) (src l) (srcBd l)) ∧
  (∀ l, srcBd l = ⋃ m ∈ section34Face src l \ {l}, src m) ∧
  (∀ l m, src l ∩ src m = ⋃ k ∈ section34Face src l ∩ section34Face src m, src k) ∧
  (∀ l m, src m ⊆ src l → m = l ∨ section34BoundedDim m < section34BoundedDim l) ∧
  (⋃ l, src l) = C ∪ section34CompactCutNeighborhood src ∧
  (∀ a : Section34CompactArcIndex K K',
    src (.faceArc a) = src (.vertexBall a.1.2) ∩ src (.faceDisk a.1.1)) ∧
  (∀ p : Section34CompactMarkIndex K K',
    src (.markedPoint p) = src (.splitDisk p.1.2) ∩ src (.faceDisk p.1.1)) ∧
  (∀ x : Section34CompactPatchIndex K K',
    src (.patch x) = src (.tetraBall x.1.1) ∩ src (.vertexBall x.1.2)) ∧
  (∀ i : Section34CompactEdgeArcIndex K K',
    src (.edgeArc i) = src (.tetraBall i.1.1) ∩ src (.splitDisk i.1.2)) ∧
  (∀ o : Section34CompactOuterVertexIndex K K', src (.outerFace o) =
    closure (srcBd (.vertexBall o.1) \
      (C ∪ ⋃ e : Section34CompactEdgeIndex K K', src (.splitDisk e)))) ∧
  (∀ q : Section34CompactOuterEdgeIndex K K',
    src (.outerArc q) = closure (srcBd (.splitDisk q.1) \ C)) ∧
  (∀ s : Section34CompactSimplexIndex K 3, src (.faceDisk s) =
    closure (convexHull ℝ (s.1 : Set (EuclideanSpace ℝ (Fin 3))) \
      section34CompactCutNeighborhood src)) ∧
  (∀ t : Section34CompactSimplexIndex K 4, src (.tetraBall t) =
    closure (convexHull ℝ (t.1 : Set (EuclideanSpace ℝ (Fin 3))) \
      section34CompactCutNeighborhood src)) ∧
  (∀ (s : Section34CompactSimplexIndex K 3) (w : Section34CompactVertexIndex K K'),
    ¬ Section34Incident w.1 s.1 → src (.faceDisk s) ∩ src (.vertexBall w) = ∅) ∧
  (∀ (s : Section34CompactSimplexIndex K 3) (e : Section34CompactEdgeIndex K K'),
    ¬ Section34Incident e.1 s.1 → src (.faceDisk s) ∩ src (.splitDisk e) = ∅) ∧
  (∀ (t : Section34CompactSimplexIndex K 4) (w : Section34CompactVertexIndex K K'),
    ¬ Section34Incident w.1 t.1 → src (.tetraBall t) ∩ src (.vertexBall w) = ∅) ∧
  (∀ (t : Section34CompactSimplexIndex K 4) (e : Section34CompactEdgeIndex K K'),
    ¬ Section34Incident e.1 t.1 → src (.tetraBall t) ∩ src (.splitDisk e) = ∅) ∧
  (∀ l, ∃ m, section34BoundedDim m = 3 ∧ src l ⊆ src m) ∧
  (∀ w : Section34CompactVertexIndex K K',
    (w.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ src (.vertexBall w)) ∧
  (∀ (w : Section34CompactVertexIndex K K') (e : Section34CompactEdgeIndex K K'),
    (src (.vertexBall w) ∩ src (.splitDisk e)).Nonempty → w.1 ⊆ e.1) ∧
  (∀ e : Section34CompactEdgeIndex K K', ∃ w w' : Section34CompactVertexIndex K K', w ≠ w' ∧
    (e.1 : Set (EuclideanSpace ℝ (Fin 3))) =
      (w.1 : Set (EuclideanSpace ℝ (Fin 3))) ∪ (w'.1 : Set (EuclideanSpace ℝ (Fin 3))) ∧
    src (.splitDisk e) = src (.vertexBall w) ∩ src (.vertexBall w')) ∧
  (∀ (t : Section34CompactSimplexIndex K 4) (s : Section34CompactSimplexIndex K 3),
    Section34Incident s.1 t.1 → src (.faceDisk s) ⊆ src (.tetraBall t)) ∧
  ∀ s : Section34CompactSimplexIndex K 3, ∃ t : Section34CompactSimplexIndex K 4,
    Section34Incident s.1 t.1

def Section34CompactCarrierControl
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (ε : ℝ)
    (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  (∀ t ∈ K.faces, h '' section34CompactCarrierSupport K t ⊆ interior (H t)) ∧
  (∀ t ∈ K.faces, ∀ y ∈ H t, ∀ z ∈ H t, dist y z < ε) ∧
  ∀ t ∈ K.faces, IsPLCellOn 3 (H t) (frontier (H t))

def section34CompactTetraObstacle
    (tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (fbl : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (t : Section34CompactSimplexIndex K 4) : Set (EuclideanSpace ℝ (Fin 3)) :=
  (⋃ (x : Section34CompactPatchIndex K K') (_ : x.1.1 = t), tgtV x.1.2) ∪
    ⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1), fbl s

def Section34CompactExterior
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (fbl : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ (t : Section34CompactSimplexIndex K 4) (w : Section34CompactVertexIndex K K'),
    ¬ Section34Incident w.1 t.1 → ∀ y ∈ h '' (w.1 : Set (EuclideanSpace ℝ (Fin 3))),
      ¬ Bornology.IsBounded
        (connectedComponentIn (section34CompactTetraObstacle tgtV fbl t)ᶜ y)

theorem section34CompactExterior_mono
    {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {fbl fbl' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hsub : ∀ s, fbl s ⊆ fbl' s) (hext : Section34CompactExterior K K' h tgtV fbl') :
    Section34CompactExterior K K' h tgtV fbl := by
  intro t w hw y hy hb
  have hobs : section34CompactTetraObstacle tgtV fbl t ⊆
      section34CompactTetraObstacle tgtV fbl' t :=
    union_subset_union Subset.rfl (iUnion₂_mono fun s _ => hsub s)
  exact hext t w hw y hy
    (hb.subset (connectedComponentIn_mono y (compl_subset_compl.mpr hobs)))

def Section34CompactGraphFrame (V : Set (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (ε : ℝ)
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (src : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (f₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) : Prop :=
  section34CompactCutNeighborhood src ⊆ V ∧
  IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
    (f₁ '' section34CompactCutNeighborhood src) ∧
  f₁ '' section34CompactCutNeighborhood src ∈ nhdsSet (h '' section34CompactGraphSkeleton K) ∧
  (∀ x ∈ section34CompactCutNeighborhood src, dist (f₁ x) (h x) < ε / 3) ∧
  (∀ w : Section34CompactVertexIndex K K', h '' (w.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆
    interior (section34CompactVertexBallImage src f₁ w)) ∧
  (∀ (e : Section34CompactEdgeIndex K K') (s : Section34CompactSimplexIndex K 3),
    (section34CompactSplitDiskImage src f₁ e ∩
      h '' convexHull ℝ (s.1 : Set (EuclideanSpace ℝ (Fin 3)))).Nonempty →
      Section34Incident e.1 s.1) ∧
  (∀ (w : Section34CompactVertexIndex K K') (s : Section34CompactSimplexIndex K 3),
    (section34CompactVertexBallImage src f₁ w ∩
      h '' convexHull ℝ (s.1 : Set (EuclideanSpace ℝ (Fin 3)))).Nonempty →
      Section34Incident w.1 s.1) ∧
  (∀ s : Section34CompactSimplexIndex K 3, h '' section34CompactSimplexRim s.1 ⊆
    interior (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s)) ∧
  (∀ s : Section34CompactSimplexIndex K 3, ∃ S₁ S₂ : Set (EuclideanSpace ℝ (Fin 3)),
    IsTopologicalSolidTorus S₁ ∧ IsTopologicalSolidTorus S₂ ∧
    IsCombinatorialSolidTorus
      (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) ∧
    S₁ ⊆ interior (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) ∧
    section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s ⊆ interior S₂ ∧
    IsToroidalShell (closure (S₂ \ S₁)) (frontier S₁) (frontier S₂) ∧
    IsSpine S₁ (h '' section34CompactSimplexRim s.1)) ∧
  (∀ (w : Section34CompactVertexIndex K K') (t : Finset (EuclideanSpace ℝ (Fin 3))),
    t ∈ K.faces → (w.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin 3))) →
    h '' src (.vertexBall w) ∪ section34CompactVertexBallImage src f₁ w ⊆ interior (H t)) ∧
  Section34CompactExterior K K' h (section34CompactVertexBallImage src f₁)
    (fun s => h '' convexHull ℝ (s.1 : Set (EuclideanSpace ℝ (Fin 3))))

theorem Section34CompactGraphFrame.carriesFundamentalGroupOnto
    {V : Set (EuclideanSpace ℝ (Fin 3))}
    {h f₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {ε : ℝ}
    {src : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (s : Section34CompactSimplexIndex K 3) :
    CarriesFundamentalGroupOnto (h '' section34CompactSimplexRim s.1)
      (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) := by
  obtain ⟨-, -, -, -, -, -, -, hrim, hnest, -, -⟩ := hgraph
  obtain ⟨S₁, S₂, hS₁, hS₂, hT, h₁T, hT₂, hshell, hspine⟩ := hnest s
  have hsub := (hrim s).trans interior_subset
  exact carriesFundamentalGroupOnto_of_nestedSolidTorus hsub (Homeomorph.refl _)
    (fun _ => Iff.rfl) hS₁ hS₂ hT h₁T hT₂ hshell hspine hsub

end Vocabulary

section CurveCrossing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def HasPLSurfaceCurveCrossingAt (S A B : Set E) (x : E) : Prop :=
  ∃ (U V : Set E) (φ : E → E) (T P Q : Submodule ℝ E),
    IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ IsPLHomeomorphOn φ U V ∧ φ x = 0 ∧
      Module.finrank ℝ T = 2 ∧ Module.finrank ℝ P = 1 ∧ Module.finrank ℝ Q = 1 ∧
      P ≤ T ∧ Q ≤ T ∧ P ⊓ Q = ⊥ ∧ ∀ᶠ y in 𝓝 x,
        (y ∈ S ↔ φ y ∈ T) ∧ (y ∈ A ↔ φ y ∈ P) ∧ (y ∈ B ↔ φ y ∈ Q)

end CurveCrossing

section FirstHomology

variable {Y : Type} [TopologicalSpace Y]

def CarriesIntegralFirstHomologyOnto (J T : Set Y) : Prop :=
  J ⊆ T ∧ ∀ hJT : J ⊆ T,
    Function.Surjective
      (integralSingularHomologyMap 1 (⟨inclusion hJT, continuous_inclusion hJT⟩ : C(J, T)))

theorem carriesIntegralFirstHomologyOnto_self (T : Set Y) :
    CarriesIntegralFirstHomologyOnto T T := by
  refine ⟨Subset.rfl, fun hJT => ?_⟩
  have hid : (⟨inclusion hJT, continuous_inclusion hJT⟩ : C(T, T)) = ContinuousMap.id T :=
    ContinuousMap.ext fun _ => rfl
  rw [hid, integralSingularHomologyMap_id]
  exact fun x => ⟨x, rfl⟩

end FirstHomology

section Invariants

variable {K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}

def section34CompactTraceComponents
    (tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (s : Section34CompactSimplexIndex K 3) : Set (Set (EuclideanSpace ℝ (Fin 3))) :=
  (fun y => connectedComponentIn (fblBd s ∩ frontier (⋃ w, tgtV w)) y) ''
    (fblBd s ∩ frontier (⋃ w, tgtV w))

noncomputable def section34CompactTraceCount
    (tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (s : Section34CompactSimplexIndex K 3) : ℕ :=
  (section34CompactTraceComponents tgtV fblBd s).ncard

noncomputable def section34CompactCrossingCount
    (tgtEBd : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (s : Section34CompactSimplexIndex K 3) : ℕ :=
  (fblBd s ∩ ⋃ e : Section34CompactEdgeIndex K K', tgtEBd e).ncard

noncomputable def section34CompactFaceBallRank
    (tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtEBd : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (s : Section34CompactSimplexIndex K 3) : ℕ :=
  section34CompactTraceCount tgtV fblBd s + section34CompactCrossingCount tgtEBd fblBd s

theorem section34CompactFaceBallRank_congr
    {tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {tgtEBd : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {fblBd fblBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    {s : Section34CompactSimplexIndex K 3} (hs : fblBd s = fblBd' s) :
    section34CompactFaceBallRank tgtV tgtEBd fblBd s =
      section34CompactFaceBallRank tgtV tgtEBd fblBd' s := by
  simp only [section34CompactFaceBallRank, section34CompactTraceCount,
    section34CompactCrossingCount, section34CompactTraceComponents, hs]

theorem section34CompactFaceBallRank_lt_of_compression
    {tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {tgtEBd : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {fblBd fblBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    {s : Section34CompactSimplexIndex K 3}
    (hc : section34CompactTraceCount tgtV fblBd' s + 1 ≤ section34CompactTraceCount tgtV fblBd s)
    (hp : section34CompactCrossingCount tgtEBd fblBd' s ≤
      section34CompactCrossingCount tgtEBd fblBd s) :
    section34CompactFaceBallRank tgtV tgtEBd fblBd' s <
      section34CompactFaceBallRank tgtV tgtEBd fblBd s := by
  simp only [section34CompactFaceBallRank]
  omega

theorem section34CompactFaceBallRank_lt_of_bigonSlide
    {tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {tgtEBd : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {fblBd fblBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    {s : Section34CompactSimplexIndex K 3}
    (hc : section34CompactTraceCount tgtV fblBd' s = section34CompactTraceCount tgtV fblBd s)
    (hp : section34CompactCrossingCount tgtEBd fblBd' s + 2 =
      section34CompactCrossingCount tgtEBd fblBd s) :
    section34CompactFaceBallRank tgtV tgtEBd fblBd' s <
      section34CompactFaceBallRank tgtV tgtEBd fblBd s := by
  simp only [section34CompactFaceBallRank]
  omega

def Section34CompactFaceBallInvariants
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtEBd : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (fbl fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  (∀ s, IsPLCellOn 3 (fbl s) (fblBd s)) ∧
  (∀ s : Section34CompactSimplexIndex K 3,
    h '' section34CompactSimplexRim s.1 ⊆ interior (fbl s)) ∧
  (∀ (s : Section34CompactSimplexIndex K 3) (w : Section34CompactVertexIndex K K'),
    ¬ Section34Incident w.1 s.1 → fbl s ∩ tgtV w = ∅) ∧
  (∀ s s', s ≠ s' → fbl s ∩ fbl s' ⊆ interior (⋃ w, tgtV w)) ∧
  (∀ s, ∀ y ∈ fblBd s ∩ frontier (⋃ w, tgtV w),
    HasPLCrossingAt (fblBd s) (frontier (⋃ w, tgtV w)) y) ∧
  (∀ (s : Section34CompactSimplexIndex K 3) (e : Section34CompactEdgeIndex K K'),
    ∀ y ∈ fblBd s ∩ tgtEBd e,
      HasPLSurfaceCurveCrossingAt (frontier (⋃ w, tgtV w))
        (fblBd s ∩ frontier (⋃ w, tgtV w)) (tgtEBd e) y) ∧
  (∀ s, CarriesIntegralFirstHomologyOnto
    (fblBd s ∩ frontier (section34CompactFaceTorus tgtV s)) (section34CompactFaceTorus tgtV s)) ∧
  (∀ s, (fblBd s ∩ ⋃ e : Section34CompactEdgeIndex K K', tgtEBd e).Finite) ∧
  (∀ s, (section34CompactTraceComponents tgtV fblBd s).Finite) ∧
  (∀ (s : Section34CompactSimplexIndex K 3) (t : Section34CompactSimplexIndex K 4),
    Section34Incident s.1 t.1 → fbl s ⊆ interior (H t.1)) ∧
  Section34CompactExterior K K' h tgtV fbl

def Section34CompactFaceEnvelopes
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (env : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  (∀ s, IsOpen (env s)) ∧
  (∀ s : Section34CompactSimplexIndex K 3,
    h '' convexHull ℝ (s.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ env s) ∧
  (∀ (s : Section34CompactSimplexIndex K 3) (w : Section34CompactVertexIndex K K'),
    ¬ Section34Incident w.1 s.1 → env s ∩ tgtV w = ∅) ∧
  (∀ s s', s ≠ s' → env s ∩ env s' ⊆ interior (⋃ w, tgtV w)) ∧
  (∀ (s : Section34CompactSimplexIndex K 3) (t : Section34CompactSimplexIndex K 4),
    Section34Incident s.1 t.1 → env s ⊆ interior (H t.1)) ∧
  (∀ s : Section34CompactSimplexIndex K 3, ∃ A : Set (EuclideanSpace ℝ (Fin 3)),
    IsPLBall 3 A ∧ h '' section34CompactSimplexRim s.1 ⊆ interior A ∧
      env s ∩ A ⊆ interior (section34CompactFaceTorus tgtV s)) ∧
  Section34CompactExterior K K' h tgtV (fun s => closure (env s))

def Section34CompactCompression
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (tgtVBd : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtE : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (fbl fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (s : Section34CompactSimplexIndex K 3) : Prop :=
  ∃ (w : Section34CompactVertexIndex K K') (Dj Jd : Set (EuclideanSpace ℝ (Fin 3))),
    IsPLCellOn 2 Dj Jd ∧ Dj ⊆ tgtVBd w ∧ Jd ⊆ fblBd s ∧ Dj ∩ fblBd s = Jd ∧
      (∀ e : Section34CompactEdgeIndex K K', Disjoint Dj (tgtE e)) ∧
      ∀ s' : Section34CompactSimplexIndex K 3, s' ≠ s → Disjoint (Dj \ Jd) (fbl s')

def Section34CompactBigonSlide
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (tgtV tgtVBd : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtE tgtEBd : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (s : Section34CompactSimplexIndex K 3) : Prop :=
  ∃ (w : Section34CompactVertexIndex K K') (e : Section34CompactEdgeIndex K K')
    (B B' Bb Dj Jd : Set (EuclideanSpace ℝ (Fin 3))),
    IsPLCellOn 1 B Bb ∧ B ⊆ fblBd s ∧ B ⊆ tgtVBd w ∧ Bb ⊆ tgtEBd e ∧
      B ∩ (⋃ e' : Section34CompactEdgeIndex K K', tgtE e') = Bb ∧
      IsPLCellOn 1 B' Bb ∧ B' ⊆ tgtEBd e ∧ B ∩ B' = Bb ∧
      IsPLCellOn 2 Dj Jd ∧ Dj ⊆ tgtVBd w ∩ frontier (⋃ w, tgtV w) ∧ Jd = B ∪ B' ∧
      ∀ s' : Section34CompactSimplexIndex K 3, Disjoint (Dj \ Jd) (fblBd s')

def Section34CompactTrace
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtEBd : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∃ (r : Section34CompactSimplexIndex K 3 → ℕ)
    (J : Section34CompactSimplexIndex K 3 → ℕ → Set (EuclideanSpace ℝ (Fin 3))),
    (∀ s, 0 < r s) ∧
    (∀ s, ∀ i < r s, IsPLSphere 1 (J s i)) ∧
    (∀ s, ∀ i < r s, ∀ j < r s, i ≠ j → Disjoint (J s i) (J s j)) ∧
    (∀ s, fblBd s ∩ frontier (⋃ w : Section34CompactVertexIndex K K', tgtV w) =
      ⋃ i < r s, J s i) ∧
    (∀ s, fblBd s ∩ frontier (section34CompactFaceTorus tgtV s) = ⋃ i < r s, J s i) ∧
    (∀ s, ∀ i < r s, ∀ e : Section34CompactEdgeIndex K K', Section34Incident e.1 s.1 →
      ∃ p, J s i ∩ tgtEBd e = {p}) ∧
    ∀ s, ∀ i < r s, ∀ hsub : J s i ⊆ section34CompactFaceTorus tgtV s,
      integralSingularHomologyMap 1
        (⟨inclusion hsub, continuous_inclusion hsub⟩ :
          C(J s i, section34CompactFaceTorus tgtV s)) ≠ 0

def Section34CompactFaceDiskFamily
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtE tgtEBd : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtD tgtDBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtA tgtABd : Section34CompactArcIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtP : Section34CompactMarkIndex K K' → Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  (∀ s, IsPLCellOn 2 (tgtD s) (tgtDBd s)) ∧
  (∀ s, tgtD s ⊆ fblBd s) ∧
  (∀ s, tgtD s ∩ (⋃ w : Section34CompactVertexIndex K K', tgtV w) = tgtDBd s) ∧
  (∀ s, tgtDBd s ⊆ frontier (⋃ w : Section34CompactVertexIndex K K', tgtV w)) ∧
  (∀ s s', s ≠ s' → Disjoint (tgtD s) (tgtD s')) ∧
  (∀ a, IsPLCellOn 1 (tgtA a) (tgtABd a)) ∧
  (∀ a : Section34CompactArcIndex K K', tgtDBd a.1.1 ∩ tgtV a.1.2 = tgtA a) ∧
  (∀ (s : Section34CompactSimplexIndex K 3) (w : Section34CompactVertexIndex K K'),
    ¬ Section34Incident w.1 s.1 → tgtD s ∩ tgtV w = ∅) ∧
  (∀ p, IsPLCellOn 0 (tgtP p) ∅) ∧
  (∀ p : Section34CompactMarkIndex K K', tgtDBd p.1.1 ∩ tgtEBd p.1.2 = tgtP p) ∧
  (∀ (s : Section34CompactSimplexIndex K 3) (e : Section34CompactEdgeIndex K K'),
    ¬ Section34Incident e.1 s.1 → tgtDBd s ∩ tgtEBd e = ∅) ∧
  ∀ a : Section34CompactArcIndex K K',
    tgtABd a = tgtA a ∩ ⋃ e : Section34CompactEdgeIndex K K', tgtE e

def Section34CompactResidualPlus
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtV tgtVBd : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtE tgtEBd : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtD : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtA : Section34CompactArcIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtP : Section34CompactMarkIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtR tgtRBd : Section34CompactSimplexIndex K 4 → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtX tgtXBd : Section34CompactPatchIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtI tgtIBd : Section34CompactEdgeArcIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtO tgtOBd : Section34CompactOuterVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtQ tgtQBd : Section34CompactOuterEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3))) :
    Prop :=
  (∀ t, IsPLCellOn 3 (tgtR t) (tgtRBd t)) ∧
  (∀ x, IsPLCellOn 2 (tgtX x) (tgtXBd x)) ∧
  (∀ i, IsPLCellOn 1 (tgtI i) (tgtIBd i)) ∧
  (∀ o, IsPLCellOn 2 (tgtO o) (tgtOBd o)) ∧
  (∀ q, IsPLCellOn 1 (tgtQ q) (tgtQBd q)) ∧
  (∀ x : Section34CompactPatchIndex K K', tgtR x.1.1 ∩ tgtV x.1.2 = tgtX x) ∧
  (∀ (t : Section34CompactSimplexIndex K 4) (w : Section34CompactVertexIndex K K'),
    ¬ Section34Incident w.1 t.1 → tgtR t ∩ tgtV w = ∅) ∧
  (∀ (t : Section34CompactSimplexIndex K 4) (s : Section34CompactSimplexIndex K 3),
    Section34Incident s.1 t.1 → tgtR t ∩ tgtD s = tgtD s) ∧
  (∀ (t : Section34CompactSimplexIndex K 4) (s : Section34CompactSimplexIndex K 3),
    ¬ Section34Incident s.1 t.1 → tgtR t ∩ tgtD s = ∅) ∧
  (∀ t t', t ≠ t' → tgtR t ∩ tgtR t' ⊆ ⋃ s, tgtD s) ∧
  (∀ i : Section34CompactEdgeArcIndex K K', tgtR i.1.1 ∩ tgtE i.1.2 = tgtI i) ∧
  (∀ (t : Section34CompactSimplexIndex K 4) (e : Section34CompactEdgeIndex K K'),
    ¬ Section34Incident e.1 t.1 → tgtR t ∩ tgtE e = ∅) ∧
  (∀ i : Section34CompactEdgeArcIndex K K', tgtI i ⊆ tgtEBd i.1.2) ∧
  (∀ t : Section34CompactSimplexIndex K 4, tgtRBd t =
    (⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1), tgtD s) ∪
      ⋃ (x : Section34CompactPatchIndex K K') (_ : x.1.1 = t), tgtX x) ∧
  (∀ i : Section34CompactEdgeArcIndex K K', tgtIBd i =
    ⋃ (p : Section34CompactMarkIndex K K')
      (_ : p.1.2 = i.1.2 ∧ Section34Incident p.1.1.1 i.1.1.1), tgtP p) ∧
  (∀ x : Section34CompactPatchIndex K K', tgtXBd x =
    (⋃ (a : Section34CompactArcIndex K K')
      (_ : a.1.2 = x.1.2 ∧ Section34Incident a.1.1.1 x.1.1.1), tgtA a) ∪
    ⋃ (i : Section34CompactEdgeArcIndex K K')
      (_ : i.1.1 = x.1.1 ∧ x.1.2.1 ⊆ i.1.2.1), tgtI i) ∧
  (∀ (i : Section34CompactEdgeArcIndex K K') (p : Section34CompactMarkIndex K K'),
    p.1.2 = i.1.2 → tgtP p ⊆ tgtI i → tgtP p ⊆ tgtIBd i) ∧
  (∀ t : Section34CompactSimplexIndex K 4, tgtR t ⊆ H t.1) ∧
  (∀ o : Section34CompactOuterVertexIndex K K', tgtO o =
    closure (tgtVBd o.1 \ ((⋃ e, tgtE e) ∪ ⋃ x, tgtX x))) ∧
  (∀ q : Section34CompactOuterEdgeIndex K K', tgtQ q = closure (tgtEBd q.1 \ ⋃ i, tgtI i)) ∧
  (∀ w : Section34CompactVertexIndex K K', tgtVBd w =
    (⋃ (e : Section34CompactEdgeIndex K K') (_ : w.1 ⊆ e.1), tgtE e) ∪
    (⋃ (x : Section34CompactPatchIndex K K') (_ : x.1.2 = w), tgtX x) ∪
    ⋃ (o : Section34CompactOuterVertexIndex K K') (_ : o.1 = w), tgtO o) ∧
  (∀ e : Section34CompactEdgeIndex K K', tgtEBd e =
    (⋃ (i : Section34CompactEdgeArcIndex K K') (_ : i.1.2 = e), tgtI i) ∪
    ⋃ (q : Section34CompactOuterEdgeIndex K K') (_ : q.1 = e), tgtQ q) ∧
  (∀ o : Section34CompactOuterVertexIndex K K', tgtOBd o =
    (⋃ (a : Section34CompactArcIndex K K')
      (_ : a.1.2 = o.1 ∧
        convexHull ℝ (a.1.1.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ frontier K.space), tgtA a) ∪
    ⋃ (q : Section34CompactOuterEdgeIndex K K') (_ : o.1.1 ⊆ q.1.1), tgtQ q) ∧
  ∀ q : Section34CompactOuterEdgeIndex K K', tgtQBd q =
    ⋃ (p : Section34CompactMarkIndex K K')
      (_ : p.1.2 = q.1 ∧
        convexHull ℝ (p.1.1.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ frontier K.space), tgtP p

end Invariants

section Model

theorem IsPLCellOn.isPolyhedron {d : ℕ} {S B : Set (EuclideanSpace ℝ (Fin 3))}
    (hS : IsPLCellOn d S B) : IsPolyhedron S := by
  obtain ⟨P, r, u, hr, hu, rfl, -⟩ := hS
  exact (isPLOn_iff_isPiecewiseAffineOn.mp hu.isPLOn).isPolyhedron_image
    (IsPLBall.isPolyhedron ⟨r, hr⟩)

theorem isPLHomeomorphInto_of_isPLHomeomorphOn_of_subset
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {N P : Set (EuclideanSpace ℝ (Fin 3))} (hf : IsPLHomeomorphOn f N (f '' N))
    (hP : IsPolyhedron P) (hPN : P ⊆ N) : IsPLHomeomorphInto 3 f P := by
  have hpl : IsPiecewiseAffineOn f P := hf.isPiecewiseAffineOn.mono_of_isPolyhedron hP hPN
  have hinj : InjOn f P := hf.bijOn.injOn.mono hPN
  have hfP : IsPLHomeomorphOn f P (f '' P) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP hpl hinj.bijOn_image
  have hinv : IsPLOn 3 3 (Function.invFunOn f P) (f '' P) :=
    isPLOn_iff_isPiecewiseAffineOn.mpr hfP.isPiecewiseAffineOn_invFunOn
  exact ⟨isPLOn_iff_isPiecewiseAffineOn.mpr hpl, hinj,
    fun y hy => ⟨Function.invFunOn f P, hinv y hy, hinj.leftInvOn_invFunOn⟩⟩

theorem exists_isPLBall_subset_interior_dist_lt {C : Set (EuclideanSpace ℝ (Fin 3))}
    (hC : IsPLBall 3 C) {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hh : ContinuousOn h C) {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn p C (p '' C) ∧ p '' C ⊆ interior C ∧
        ∀ x ∈ C, dist (h (p x)) (h x) < δ := by
  classical
  obtain ⟨K, hKfin, hKC⟩ := hC.isPolyhedron.exists_simplicialComplex
  subst hKC
  have _ : Finite K.faces := hKfin.to_subtype
  have hKman : IsCombinatorialManifoldWithBoundary 3 K :=
    IsPLBall.isCombinatorialManifoldWithBoundary (n := 2) hC
  obtain ⟨f, -, hfpl, hfinj, hfmap, hfB, -, -, -, hdist⟩ :=
    IsCombinatorialManifoldWithBoundary.exists_piecewiseAffineOn_inward_dist_lt K hKman hh
      (continuousOn_const (c := δ)) (fun _ _ => hδ)
  have hfr := frontier_space_eq_boundaryComplex_space (n := 2) hKman
  refine ⟨f, isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hC.isPolyhedron hfpl
    hfinj.bijOn_image, ?_, hdist⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [← self_sdiff_frontier, hfr]
  exact ⟨hfmap hx, hfB x hx⟩

theorem isEmbedding_domRestrict_interior_of_continuousOn_injOn
    {C : Set (EuclideanSpace ℝ (Fin 3))} (hC : IsCompact C)
    {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} (hcont : ContinuousOn h C)
    (hinj : InjOn h C) : Topology.IsEmbedding ((interior C).domRestrict h) := by
  have hCemb : Topology.IsEmbedding (C.domRestrict h) := by
    let _ : CompactSpace C := isCompact_iff_compactSpace.mp hC
    exact (hcont.domRestrict.isClosedEmbedding (Set.injOn_iff_injective.mp hinj)).isEmbedding
  simpa only [Set.domRestrict_eq, Function.comp_def] using
    hCemb.comp (Topology.IsEmbedding.inclusion (interior_subset : interior C ⊆ C))

end Model

section Leaves

variable {C V : Set (EuclideanSpace ℝ (Fin 3))}
  {h f₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {ε : ℝ}
  {K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {src srcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))}
  {H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {env : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}

theorem exists_compactCutAndGraph (h331 : Moise331) (hC : IsPLBall 3 C) (hV : IsOpen V)
    (hCV : C ⊆ V) (hh : Topology.IsEmbedding (V.domRestrict h)) (hε : 0 < ε) :
    ∃ (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (src srcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3)))
      (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
      (f₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
      Section34CompactCutFrame C K K' src srcBd ∧ Section34CompactCarrierControl K h ε H ∧
        Section34CompactGraphFrame V h ε K K' src H f₁ := by
  sorry

theorem exists_compactFaceEnvelopes (h305 : Moise305Tame) (hV : IsOpen V) (hCV : C ⊆ V)
    (hh : Topology.IsEmbedding (V.domRestrict h))
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hcar : Section34CompactCarrierControl K h ε H)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁) :
    ∃ env : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
      Section34CompactFaceEnvelopes K K' h H (section34CompactVertexBallImage src f₁) env := by
  sorry

theorem exists_compactFaceShellBalls (h305 : Moise305Tame) (hV : IsOpen V) (hCV : C ⊆ V)
    (hh : Topology.IsEmbedding (V.domRestrict h))
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (henv : Section34CompactFaceEnvelopes K K' h H (section34CompactVertexBallImage src f₁)
      env) :
    ∃ fbl fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
      ∀ s : Section34CompactSimplexIndex K 3, IsPLCellOn 3 (fbl s) (fblBd s) ∧
        h '' convexHull ℝ (s.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ interior (fbl s) ∧
        fbl s ⊆ env s := by
  sorry

theorem exists_compactFaceBallsGeneralPosition
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (henv : Section34CompactFaceEnvelopes K K' h H (section34CompactVertexBallImage src f₁)
      env)
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hfam : ∀ s : Section34CompactSimplexIndex K 3, IsPLCellOn 3 (fbl s) (fblBd s) ∧
      h '' convexHull ℝ (s.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ interior (fbl s) ∧
      fbl s ⊆ env s) :
    ∃ fbl' fblBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
      (∀ s : Section34CompactSimplexIndex K 3, IsPLCellOn 3 (fbl' s) (fblBd' s) ∧
        h '' convexHull ℝ (s.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ interior (fbl' s) ∧
        fbl' s ⊆ env s) ∧
      (∀ s, ∀ y ∈ fblBd' s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w),
        HasPLCrossingAt (fblBd' s)
          (frontier (⋃ w, section34CompactVertexBallImage src f₁ w)) y) ∧
      (∀ (s : Section34CompactSimplexIndex K 3) (e : Section34CompactEdgeIndex K K'),
        ∀ y ∈ fblBd' s ∩ section34CompactSplitDiskImage srcBd f₁ e,
          HasPLSurfaceCurveCrossingAt
            (frontier (⋃ w, section34CompactVertexBallImage src f₁ w))
            (fblBd' s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w))
            (section34CompactSplitDiskImage srcBd f₁ e) y) ∧
      (∀ s, (fblBd' s ∩ ⋃ e : Section34CompactEdgeIndex K K',
        section34CompactSplitDiskImage srcBd f₁ e).Finite) ∧
      ∀ s, (section34CompactTraceComponents (section34CompactVertexBallImage src f₁)
        fblBd' s).Finite := by
  sorry

theorem compactTraceHomology (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (henv : Section34CompactFaceEnvelopes K K' h H (section34CompactVertexBallImage src f₁)
      env)
    (s : Section34CompactSimplexIndex K 3)
    (hgen : CarriesFundamentalGroupOnto (h '' section34CompactSimplexRim s.1)
      (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s))
    {B BBd : Set (EuclideanSpace ℝ (Fin 3))}
    (hB : IsPLCellOn 3 B BBd) (hrim : h '' section34CompactSimplexRim s.1 ⊆ interior B)
    (hBenv : B ⊆ env s)
    (hgp : ∀ y ∈ BBd ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w),
      HasPLCrossingAt BBd (frontier (⋃ w, section34CompactVertexBallImage src f₁ w)) y) :
    CarriesIntegralFirstHomologyOnto
      (BBd ∩ frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s))
      (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) := by
  sorry

theorem exists_compactCompression (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hcar : Section34CompactCarrierControl K h ε H)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (s : Section34CompactSimplexIndex K 3)
    (hop : Section34CompactCompression K K' (section34CompactVertexBallImage srcBd f₁)
      (section34CompactSplitDiskImage src f₁) fbl fblBd s) :
    ∃ fbl' fblBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
      Section34CompactFaceBallInvariants K K' h H (section34CompactVertexBallImage src f₁)
        (section34CompactSplitDiskImage srcBd f₁) fbl' fblBd' ∧
      (∀ s', s' ≠ s → fbl' s' = fbl s' ∧ fblBd' s' = fblBd s') ∧
      section34CompactTraceCount (section34CompactVertexBallImage src f₁) fblBd' s + 1 ≤
        section34CompactTraceCount (section34CompactVertexBallImage src f₁) fblBd s ∧
      section34CompactCrossingCount (section34CompactSplitDiskImage srcBd f₁) fblBd' s ≤
        section34CompactCrossingCount (section34CompactSplitDiskImage srcBd f₁) fblBd s := by
  sorry

theorem exists_compactBigonSlide (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (s : Section34CompactSimplexIndex K 3)
    (hop : Section34CompactBigonSlide K K' (section34CompactVertexBallImage src f₁)
      (section34CompactVertexBallImage srcBd f₁) (section34CompactSplitDiskImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) fblBd s) :
    ∃ fbl' fblBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
      Section34CompactFaceBallInvariants K K' h H (section34CompactVertexBallImage src f₁)
        (section34CompactSplitDiskImage srcBd f₁) fbl' fblBd' ∧
      (∀ s', s' ≠ s → fbl' s' = fbl s' ∧ fblBd' s' = fblBd s') ∧
      section34CompactTraceCount (section34CompactVertexBallImage src f₁) fblBd' s =
        section34CompactTraceCount (section34CompactVertexBallImage src f₁) fblBd s ∧
      section34CompactCrossingCount (section34CompactSplitDiskImage srcBd f₁) fblBd' s + 2 =
        section34CompactCrossingCount (section34CompactSplitDiskImage srcBd f₁) fblBd s := by
  sorry

theorem compactTrace_of_noOperation (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hnc : ∀ s, ¬ Section34CompactCompression K K' (section34CompactVertexBallImage srcBd f₁)
      (section34CompactSplitDiskImage src f₁) fbl fblBd s)
    (hnb : ∀ s, ¬ Section34CompactBigonSlide K K' (section34CompactVertexBallImage src f₁)
      (section34CompactVertexBallImage srcBd f₁) (section34CompactSplitDiskImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) fblBd s) :
    Section34CompactTrace K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) fblBd := by
  sorry

theorem exists_compactFaceDisks (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (htrace : Section34CompactTrace K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) fblBd)
    (hnc : ∀ s, ¬ Section34CompactCompression K K' (section34CompactVertexBallImage srcBd f₁)
      (section34CompactSplitDiskImage src f₁) fbl fblBd s)
    (hnb : ∀ s, ¬ Section34CompactBigonSlide K K' (section34CompactVertexBallImage src f₁)
      (section34CompactVertexBallImage srcBd f₁) (section34CompactSplitDiskImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) fblBd s) :
    ∃ (tgtD tgtDBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
      (tgtA tgtABd : Section34CompactArcIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
      (tgtP : Section34CompactMarkIndex K K' → Set (EuclideanSpace ℝ (Fin 3))),
      Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
        (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
        fblBd tgtD tgtDBd tgtA tgtABd tgtP := by
  sorry

theorem exists_compactResidualBalls (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hcar : Section34CompactCarrierControl K h ε H)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (htrace : Section34CompactTrace K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) fblBd)
    {tgtD tgtDBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    {tgtA tgtABd : Section34CompactArcIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {tgtP : Section34CompactMarkIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP) :
    ∃ (tgtR tgtRBd : Section34CompactSimplexIndex K 4 → Set (EuclideanSpace ℝ (Fin 3)))
      (tgtX tgtXBd : Section34CompactPatchIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
      (tgtI tgtIBd : Section34CompactEdgeArcIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
      (tgtO tgtOBd : Section34CompactOuterVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
      (tgtQ tgtQBd : Section34CompactOuterEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3))),
      Section34CompactResidualPlus K K' H (section34CompactVertexBallImage src f₁)
        (section34CompactVertexBallImage srcBd f₁) (section34CompactSplitDiskImage src f₁)
        (section34CompactSplitDiskImage srcBd f₁) tgtD tgtA tgtP tgtR tgtRBd tgtX tgtXBd
        tgtI tgtIBd tgtO tgtOBd tgtQ tgtQBd := by
  sorry

theorem compactSourceFace_iff_cutLe (hcut : Section34CompactCutFrame C K K' src srcBd) :
    ∀ l m : Section34CompactLabelOf K K', src m ⊆ src l ↔ Section34CompactCutLe m l := by
  sorry

theorem compactTargetRecognition (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    {tgtD tgtDBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    {tgtA tgtABd : Section34CompactArcIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {tgtP : Section34CompactMarkIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {tgtR tgtRBd : Section34CompactSimplexIndex K 4 → Set (EuclideanSpace ℝ (Fin 3))}
    {tgtX tgtXBd : Section34CompactPatchIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {tgtI tgtIBd : Section34CompactEdgeArcIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {tgtO tgtOBd : Section34CompactOuterVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {tgtQ tgtQBd : Section34CompactOuterEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    (hres : Section34CompactResidualPlus K K' H (section34CompactVertexBallImage src f₁)
      (section34CompactVertexBallImage srcBd f₁) (section34CompactSplitDiskImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) tgtD tgtA tgtP tgtR tgtRBd tgtX tgtXBd
      tgtI tgtIBd tgtO tgtOBd tgtQ tgtQBd)
    (hface : ∀ l m : Section34CompactLabelOf K K', src m ⊆ src l ↔ Section34CompactCutLe m l)
    (tc tcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (htc : tc = section34BoundedCell (section34CompactVertexBallImage src f₁) tgtR
      (section34CompactSplitDiskImage src f₁) tgtD tgtX tgtA tgtI tgtP tgtO tgtQ)
    (htcBd : tcBd = section34BoundedCell (section34CompactVertexBallImage srcBd f₁) tgtRBd
      (section34CompactSplitDiskImage srcBd f₁) tgtDBd tgtXBd tgtABd tgtIBd (fun _ => ∅)
      tgtOBd tgtQBd) :
    (∀ l, tcBd l = ⋃ m ∈ section34Face src l \ {l}, tc m) ∧
      ∀ l m, tc l ∩ tc m = ⋃ k ∈ section34Face src l ∩ section34Face src m, tc k := by
  sorry

end Leaves

section Descent

variable {K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
  {H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {tgtV tgtVBd : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
  {tgtE tgtEBd : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}

theorem exists_compactTerminalFaceBalls (hK : K.faces.Finite)
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hinv : Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd fbl fblBd)
    (hcomp : ∀ (g gBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
      (s : Section34CompactSimplexIndex K 3),
      Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd g gBd →
      Section34CompactCompression K K' tgtVBd tgtE g gBd s →
      ∃ g' gBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
        Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd g' gBd' ∧
        (∀ s', s' ≠ s → g' s' = g s' ∧ gBd' s' = gBd s') ∧
        section34CompactFaceBallRank tgtV tgtEBd gBd' s <
          section34CompactFaceBallRank tgtV tgtEBd gBd s)
    (hslide : ∀ (g gBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
      (s : Section34CompactSimplexIndex K 3),
      Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd g gBd →
      Section34CompactBigonSlide K K' tgtV tgtVBd tgtE tgtEBd gBd s →
      ∃ g' gBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
        Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd g' gBd' ∧
        (∀ s', s' ≠ s → g' s' = g s' ∧ gBd' s' = gBd s') ∧
        section34CompactFaceBallRank tgtV tgtEBd gBd' s <
          section34CompactFaceBallRank tgtV tgtEBd gBd s) :
    ∃ fbl' fblBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
      Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd fbl' fblBd' ∧
      (∀ s, ¬ Section34CompactCompression K K' tgtVBd tgtE fbl' fblBd' s) ∧
      ∀ s, ¬ Section34CompactBigonSlide K K' tgtV tgtVBd tgtE tgtEBd fblBd' s := by
  classical
  have hfin := finite_section34CompactSimplexIndex hK 3
  let _ : Fintype (Section34CompactSimplexIndex K 3) := Fintype.ofFinite _
  have hdrop : ∀ (gBd gBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
      (s : Section34CompactSimplexIndex K 3), (∀ s', s' ≠ s → gBd' s' = gBd s') →
      section34CompactFaceBallRank tgtV tgtEBd gBd' s <
        section34CompactFaceBallRank tgtV tgtEBd gBd s →
      ∑ s', section34CompactFaceBallRank tgtV tgtEBd gBd' s' <
        ∑ s', section34CompactFaceBallRank tgtV tgtEBd gBd s' := by
    intro gBd gBd' s hoff hlt
    refine Finset.sum_lt_sum (fun s' _ => ?_) ⟨s, Finset.mem_univ s, hlt⟩
    by_cases hs : s' = s
    · subst hs
      exact hlt.le
    · exact (section34CompactFaceBallRank_congr (hoff s' hs)).le
  suffices key : ∀ n : ℕ,
      ∀ g gBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
        ∑ s', section34CompactFaceBallRank tgtV tgtEBd gBd s' = n →
        Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd g gBd →
        ∃ fbl' fblBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
          Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd fbl' fblBd' ∧
          (∀ s, ¬ Section34CompactCompression K K' tgtVBd tgtE fbl' fblBd' s) ∧
          ∀ s, ¬ Section34CompactBigonSlide K K' tgtV tgtVBd tgtE tgtEBd fblBd' s from
    key _ fbl fblBd rfl hinv
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g gBd hn hg
    by_cases hc : ∃ s, Section34CompactCompression K K' tgtVBd tgtE g gBd s
    · obtain ⟨s, hs⟩ := hc
      obtain ⟨g', gBd', hinv', hoff, hlt⟩ := hcomp g gBd s hg hs
      exact ih _ (hn ▸ hdrop gBd gBd' s (fun s' hs' => (hoff s' hs').2) hlt) g' gBd' rfl hinv'
    · by_cases hb : ∃ s, Section34CompactBigonSlide K K' tgtV tgtVBd tgtE tgtEBd gBd s
      · obtain ⟨s, hs⟩ := hb
        obtain ⟨g', gBd', hinv', hoff, hlt⟩ := hslide g gBd s hg hs
        exact ih _ (hn ▸ hdrop gBd gBd' s (fun s' hs' => (hoff s' hs').2) hlt) g' gBd' rfl
          hinv'
      · exact ⟨g, gBd, hg, not_exists.mp hc, not_exists.mp hb⟩

end Descent

section Extension

variable {K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {src srcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))}

theorem exists_compactApproximation_of_cellDiagram (hK : K.faces.Finite)
    (hK' : K'.faces.Finite)
    (hsc : ∀ l, IsPLCellOn (section34BoundedDim l) (src l) (srcBd l))
    (hsbd : ∀ l, srcBd l = ⋃ m ∈ section34Face src l \ {l}, src m)
    (hsinter : ∀ l m, src l ∩ src m = ⋃ k ∈ section34Face src l ∩ section34Face src m, src k)
    (hsdim : ∀ l m, src m ⊆ src l → m = l ∨ section34BoundedDim m < section34BoundedDim l)
    {tc tcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))}
    (htcell : ∀ l, IsPLCellOn (section34BoundedDim l) (tc l) (tcBd l))
    (htbd : ∀ l, tcBd l = ⋃ m ∈ section34Face src l \ {l}, tc m)
    (htinter : ∀ l m, tc l ∩ tc m = ⋃ k ∈ section34Face src l ∩ section34Face src m, tc k) :
    ∃ F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphInto 3 F (⋃ l, src l) ∧ ∀ l, F '' src l = tc l := by
  have hfin := finite_section34CompactLabelOf hK hK'
  choose Pp rr uu hrr huu hsceq hsbdeq using hsc
  choose Qq ss vv hss hvv htceq htbdeq using htcell
  refine exists_isPLHomeomorphInto_of_labelledCells section34BoundedDim (section34Face src) Pp Qq
    rr ss uu vv src tc section34BoundedDim_le_three hrr hss huu hvv hsceq htceq
    (fun l m hm => hsdim l m hm) ?_ ?_ hsinter htinter ?_ ?_
  · intro l
    rw [← hsbdeq l]
    exact hsbd l
  · intro l
    rw [← htbdeq l]
    exact htbd l
  · intro x _
    exact ⟨univ, Filter.univ_mem, Set.toFinite _⟩
  · intro y _
    exact ⟨univ, Filter.univ_mem, Set.toFinite _⟩

end Extension

def Moise341OnNeighborhood : Prop :=
  ∀ (C V : Set (EuclideanSpace ℝ (Fin 3))), IsPLBall 3 C → IsOpen V → C ⊆ V →
    ∀ h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      Topology.IsEmbedding (V.domRestrict h) →
    ∀ ε : ℝ, 0 < ε →
      ∃ f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
        IsPLHomeomorphOn f C (f '' C) ∧ ∀ x ∈ C, dist (f x) (h x) < ε

theorem moise341OnNeighborhood (h331 : Moise331) (h305 : Moise305Tame) :
    Moise341OnNeighborhood := by
  classical
  intro C V hC hV hCV h hh ε hε
  obtain ⟨K, K', src, srcBd, H, f₁, hcut, hcar, hgraph⟩ :=
    exists_compactCutAndGraph h331 hC hV hCV hh hε
  have hgen := hgraph.carriesFundamentalGroupOnto
  obtain ⟨env, henv⟩ := exists_compactFaceEnvelopes h305 hV hCV hh hcut hcar hgraph
  obtain ⟨fbl₀, fblBd₀, hfam₀⟩ := exists_compactFaceShellBalls h305 hV hCV hh hcut hgraph henv
  obtain ⟨fbl₁, fblBd₁, hfam₁, hgp₁, hgp₂, hfin₁, hfin₂⟩ :=
    exists_compactFaceBallsGeneralPosition hcut hgraph henv hfam₀
  obtain ⟨-, hKfin, hK'fin, -, -, -, hscell, hsbd, hsinter, hsdim, hscover, -, -, -, -, -, -,
    -, htetra, -, -, -, -, hparent, -, -, hends, -, -⟩ := id hcut
  obtain ⟨hcarS, hcarDiam, -⟩ := id hcar
  obtain ⟨-, hf₁, -, -, -, -, -, -, -, hcarV, -⟩ := id hgraph
  obtain ⟨-, -, henvAvoid, henvOverlap, henvCar, -, henvExt⟩ := id henv
  have hrim : ∀ s : Section34CompactSimplexIndex K 3,
      h '' section34CompactSimplexRim s.1 ⊆ interior (fbl₁ s) := fun s =>
    (image_mono (section34CompactSimplexRim_subset s.1)).trans (hfam₁ s).2.1
  have hinv₁ : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl₁ fblBd₁ := by
    refine ⟨fun s => (hfam₁ s).1, hrim, fun s w hw => ?_, fun s s' hss => ?_, hgp₁, hgp₂,
      fun s => ?_, hfin₁, hfin₂, fun s t hst => ?_, ?_⟩
    · exact eq_empty_of_subset_empty
        ((inter_subset_inter_left _ (hfam₁ s).2.2).trans (henvAvoid s w hw).subset)
    · exact (inter_subset_inter (hfam₁ s).2.2 (hfam₁ s').2.2).trans (henvOverlap s s' hss)
    · exact compactTraceHomology hcut hgraph henv s (hgen s) (hfam₁ s).1 (hrim s)
        (hfam₁ s).2.2 (hgp₁ s)
    · exact (hfam₁ s).2.2.trans (henvCar s t hst)
    · exact section34CompactExterior_mono (fun s => (hfam₁ s).2.2.trans subset_closure) henvExt
  obtain ⟨fbl, fblBd, hinv, hnc, hnb⟩ :=
    exists_compactTerminalFaceBalls (tgtVBd := section34CompactVertexBallImage srcBd f₁)
      (tgtE := section34CompactSplitDiskImage src f₁) hKfin hinv₁
      (fun _ _ s hg hop => by
        obtain ⟨g', gBd', hinv', hoff, hc, hp⟩ :=
          exists_compactCompression hcut hcar hgraph hg s hop
        exact ⟨g', gBd', hinv', hoff, section34CompactFaceBallRank_lt_of_compression hc hp⟩)
      (fun _ _ s hg hop => by
        obtain ⟨g', gBd', hinv', hoff, hc, hp⟩ :=
          exists_compactBigonSlide hcut hgraph hg s hop
        exact ⟨g', gBd', hinv', hoff, section34CompactFaceBallRank_lt_of_bigonSlide hc hp⟩)
  have htrace := compactTrace_of_noOperation hcut hgraph hinv hnc hnb
  obtain ⟨tgtD, tgtDBd, tgtA, tgtABd, tgtP, hdisk⟩ :=
    exists_compactFaceDisks hcut hgraph hinv htrace hnc hnb
  obtain ⟨tgtR, tgtRBd, tgtX, tgtXBd, tgtI, tgtIBd, tgtO, tgtOBd, tgtQ, tgtQBd, hres⟩ :=
    exists_compactResidualBalls hcut hcar hgraph hinv htrace hdisk
  have hface := compactSourceFace_iff_cutLe hcut
  set tc : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3)) :=
    section34BoundedCell (section34CompactVertexBallImage src f₁) tgtR
      (section34CompactSplitDiskImage src f₁) tgtD tgtX tgtA tgtI tgtP tgtO tgtQ with htcdef
  set tcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3)) :=
    section34BoundedCell (section34CompactVertexBallImage srcBd f₁) tgtRBd
      (section34CompactSplitDiskImage srcBd f₁) tgtDBd tgtXBd tgtABd tgtIBd (fun _ => ∅)
      tgtOBd tgtQBd with htcbddef
  obtain ⟨htbd, htinter⟩ :=
    compactTargetRecognition hcut hgraph hinv hdisk hres hface tc tcBd htcdef htcbddef
  obtain ⟨hDcell, -, -, -, -, hAcell, -, -, hPcell, -, -, -⟩ := id hdisk
  obtain ⟨hRcell, hXcell, hIcell, hOcell, hQcell, -, -, -, -, -, -, -, -, -, -, -, -, hresCar,
    -, -, -, -, -, -⟩ := id hres
  have hsubV : ∀ w : Section34CompactVertexIndex K K',
      src (.vertexBall w) ⊆ section34CompactCutNeighborhood src := fun w =>
    subset_iUnion (fun v : Section34CompactVertexIndex K K' => src (.vertexBall v)) w
  have hsubE : ∀ e : Section34CompactEdgeIndex K K',
      src (.splitDisk e) ⊆ section34CompactCutNeighborhood src := by
    intro e
    obtain ⟨w, w', -, -, heq⟩ := hends e
    rw [heq]
    exact inter_subset_left.trans (hsubV w)
  have hVcell : ∀ w, IsPLCellOn 3 (section34CompactVertexBallImage src f₁ w)
      (section34CompactVertexBallImage srcBd f₁ w) := fun w =>
    (hscell (.vertexBall w)).image (isPLHomeomorphInto_of_isPLHomeomorphOn_of_subset hf₁
      (hscell (.vertexBall w)).isPolyhedron (hsubV w))
  have hEcell : ∀ e, IsPLCellOn 2 (section34CompactSplitDiskImage src f₁ e)
      (section34CompactSplitDiskImage srcBd f₁ e) := fun e =>
    (hscell (.splitDisk e)).image (isPLHomeomorphInto_of_isPLHomeomorphOn_of_subset hf₁
      (hscell (.splitDisk e)).isPolyhedron (hsubE e))
  have htcell : ∀ l, IsPLCellOn (section34BoundedDim l) (tc l) (tcBd l) := by
    intro l
    cases l with
    | vertexBall w => exact hVcell w
    | tetraBall t => exact hRcell t
    | splitDisk e => exact hEcell e
    | faceDisk s => exact hDcell s
    | patch x => exact hXcell x
    | faceArc a => exact hAcell a
    | edgeArc i => exact hIcell i
    | markedPoint p => exact hPcell p
    | outerFace o => exact hOcell o
    | outerArc q => exact hQcell q
  obtain ⟨F, hF, hFim⟩ := exists_compactApproximation_of_cellDiagram hKfin hK'fin hscell hsbd
    hsinter hsdim htcell htbd htinter
  have hCsub : C ⊆ ⋃ l, src l := by
    rw [hscover]
    exact subset_union_left
  have hdist : ∀ x ∈ C, dist (F x) (h x) < ε := by
    intro x hx
    obtain ⟨l, hl⟩ := mem_iUnion.mp (hCsub hx)
    obtain ⟨m, hm3, hlm⟩ := hparent l
    have hFx : F x ∈ tc m := by
      have h1 : F x ∈ tc l := hFim l ▸ mem_image_of_mem F hl
      have h2 : tc l ⊆ tc m := by
        intro y hy
        have hmem : y ∈ ⋃ k ∈ section34Face src l ∩ section34Face src m, tc k :=
          mem_iUnion₂.mpr ⟨l, ⟨Subset.rfl, hlm⟩, hy⟩
        rw [← htinter l m] at hmem
        exact hmem.2
      exact h2 h1
    have hhx : h x ∈ h '' src m := ⟨x, hlm hl, rfl⟩
    rcases section34BoundedDim_eq_three hm3 with ⟨w, rfl⟩ | ⟨t, rfl⟩
    · obtain ⟨t₀, ht₀, hwt₀⟩ := exists_face_of_section34CompactVertexIndex w
      have hcarw := hcarV w t₀ ht₀ hwt₀
      exact hcarDiam t₀ ht₀ (F x) (interior_subset (hcarw (Or.inr hFx))) (h x)
        (interior_subset (hcarw (Or.inl hhx)))
    · have hQt : src (.tetraBall t) ⊆ convexHull ℝ (t.1 : Set (EuclideanSpace ℝ (Fin 3))) := by
        rw [htetra t]
        exact closure_minimal sdiff_subset (t.1.finite_toSet.isClosed_convexHull ℝ)
      have hstar : convexHull ℝ (t.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆
          section34CompactCarrierSupport K t.1 := by
        obtain ⟨w, hw⟩ : ∃ w, w ∈ t.1 := Finset.card_pos.mp (by rw [t.2.2]; norm_num)
        intro y hy
        exact mem_iUnion₂.mpr ⟨w, Finset.mem_coe.mpr hw, mem_iUnion₂.mpr ⟨t.1, ⟨t.2.1, hw⟩, hy⟩⟩
      exact hcarDiam t.1 t.2.1 (F x) (hresCar t hFx) (h x)
        (interior_subset (hcarS t.1 t.2.1 ⟨x, hstar (hQt (hlm hl)), rfl⟩))
  have hpl : IsPiecewiseAffineOn F C :=
    (isPLOn_iff_isPiecewiseAffineOn.mp hF.isPLOn).mono_of_isPolyhedron hC.isPolyhedron hCsub
  exact ⟨F, isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hC.isPolyhedron hpl
    (hF.injOn.mono hCsub).bijOn_image, hdist⟩

theorem moise341_of_onNeighborhood (h331 : Moise331) (h305 : Moise305Tame) : Moise341 := by
  intro C hC h hcont hinj ε hε
  obtain ⟨p, hp, hpC, hpdist⟩ := exists_isPLBall_subset_interior_dist_lt hC hcont (half_pos hε)
  have hpball : IsPLBall 3 (p '' C) := hC.of_isPLHomeomorphOn hp
  have hemb := isEmbedding_domRestrict_interior_of_continuousOn_injOn
    hC.isPolyhedron.isCompact hcont hinj
  obtain ⟨g, hg, hgdist⟩ := moise341OnNeighborhood h331 h305 (p '' C) (interior C) hpball
    isOpen_interior hpC h hemb (ε / 2) (half_pos hε)
  refine ⟨g ∘ p, ?_, fun x hx => ?_⟩
  · rw [image_comp]
    exact hp.trans hg
  · calc dist ((g ∘ p) x) (h x)
        ≤ dist (g (p x)) (h (p x)) + dist (h (p x)) (h x) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hgdist _ ⟨x, hx, rfl⟩) (hpdist x hx)
      _ = ε := add_halves ε

end DifferentialGeometry.Topology.PiecewiseLinear
