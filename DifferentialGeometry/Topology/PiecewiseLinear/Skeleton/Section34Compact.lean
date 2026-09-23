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
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVocabulary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceEnvelopes
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTraceHomology
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactSplitDiskIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceDisks
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTargetRecognition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactSourceFaceOrder
import DifferentialGeometry.Topology.PiecewiseLinear.Section33TubeApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactBigonSlide
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCompressionLeaf
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualBalls

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
open-domain and carrier certificates.  The second review (2026-09-22, digest
`consult/BG-section34-compact-second-review-digest.md`) accepted both interfaces and the
generator export, so all twelve leaf statements are FROZEN; all twelve proof obligations
remain open, and the integral `H₁` surjection onto the whole trace (image `kℤ` with
`|k| > 1` is the warned-against gap) is internal to `compactTraceHomology`.

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

Proved and imported (Opus 5.5 fill worker, lead-accepted on 2026-09-23 with zero-diagnostic checks
and an axiom audit): `exists_compactFaceEnvelopes` (byte-identical; the auxiliary ball of Lemma 4
from `Moise305Tame.exists_isPLBall_capping`), `exists_compactFaceShellBalls` (the unused `hgraph`
dropped, strictly stronger), `exists_compactFaceBallsGeneralPosition` (byte-identical; the face
torus frontier is a PL torus carrying the incident splitting circles) and `compactTraceHomology`
(the unused `hcut` and `hgp` dropped: integral `H₁` surjectivity onto the whole trace without
transversality, as the second review demanded); the assembly calls pass the reduced arguments.
The sections `Label` through `Model` were hoisted verbatim into `Section34CompactVocabulary`; the
brick `Section34CompactSplitDiskIntersection` (two meeting vertex balls meet exactly in a splitting
disk) serves the residual-ball and face-disk leaves.  Worker analysis of the six open leaves:
`compactSourceFace_iff_cutLe` needs `N` to cross `∂C` at boundary faces, which no frame clause
states (a missing derivation, not a counterexample); the others need 28.8, Schoenflies on a PL
2-sphere, the cyclic order of incident edges and the ten-by-ten description of the cut order.

Interface repair 2026-09-23 (owner decision, the compact twin of the P4b repair):
`exists_compactBigonSlide` now receives `hcar : Section34CompactCarrierControl K h ε H`, as
`exists_compactCompression` already does; the assembly passes it.  No conclusion changed.

Proved and imported (Opus 5.5 fill worker, lead-accepted on 2026-09-23 with zero-diagnostic checks
and an axiom audit): `exists_compactFaceDisks` (step P6, module `Section34CompactFaceDisks` over
`SphereInnermostDisk`, `CircleClosedCover`, `BallUnionMeetingDisk`, `Section34CompactIncidentEdges`,
`Section34CompactTargetCells`, `Section34CompactTraceArcs`).  The unused `hnc` and `hnb` were
dropped (strictly stronger; the assembly passes four arguments): an innermost trace circle on the
PL sphere `∂C_σ` bounds a disk missing the vertex balls because a circle inside one ball would
be null in `H₁`, the cyclic incidence of the edges at a vertex of `σ` makes each `D''_σ ∩ V''_w`
one arc between consecutive marked points, and the sub-arc of a PL circle is a 1-cell.
`Section34CompactTargetCells` also gives that the open splitting-disk image lies in the interior
of the union of its two vertex balls, the position fact the target-recognition note asked for.

Proved and imported (Opus 5.5 fill worker, lead-accepted on 2026-09-23 with zero-diagnostic checks
and an axiom audit): `compactTargetRecognition` (step P8, module `Section34CompactTargetRecognition`
over `CellFaceRecognition` and `SphereCellComplement`); the unused `hinv` and `fbl` were dropped
(strictly stronger; the assembly passes nine arguments): the residual bundle's tilings and the
face-disk family give, with the uniqueness of intrinsic boundaries and position facts on `∂V_w`
and `∂E_e`, that the target family has intrinsic boundary the union of its proper faces and
exact pairwise meets read off the source order `hface`; no ten-by-ten table of the cut order was
needed.  The non-compact twin is proved conditionally (`section34TargetRecognition_of_tiling` in
`Section34TargetRecognitionOfTiling`) on two tiling clauses that `Section34ResidualPlus` lacks
while this file's bundle has them as clauses 21 and 22; that interface decision is the owner's.

Proved and imported (external collaborator, PR #9, lead-accepted on 2026-09-23 with zero-diagnostic
checks and an axiom audit; statement byte-identical): `compactSourceFace_iff_cutLe` (module
`Section34CompactSourceFaceOrder` over the facets, boundary thinness, arc end points, tetra, outer
and boundary incidence modules and the generic `PLCellBoundaryThinness`, `PLCellSphereCover`,
`PLCellOnEndpoints`, `PLCellOnIntrinsicInterior`, `GraphSimplexCofaces`): the route of digest BM,
the four frontiers of the reconnaissance probe proved under their names and the probe's two
assemblies; no frame clause was added.  The probe `Skeleton/CompactSourceFaceOrderReduction.lean`
is deleted as superseded.

Interface change 2026-09-23 (owner decision after the lease-b worker's finding, log B Batch 8):
`exists_compactCutAndGraph`, `moise341OnNeighborhood` and `moise341_of_onNeighborhood` now take
`h331 : Moise331OnTube` (module `Section33TubeApproximation`) instead of `Moise331`: 33.1 as
stated gives `f` only on its own derived neighbourhood with one global `ε`, which cannot place the
images of the vertex cells inside the neighbourhoods the graph frame prescribes, while the book
(p. 239) chooses the cut's `N` first and applies 33.1 to it.  `Moise331OnTube` is proved from the
same three named inputs (`moise331OnTube h323 h324 h264`) and implies `Moise331`
(`Moise331OnTube.moise331`), so the endpoint's dependency set is unchanged; a consumer holding
`Moise323`, `Moise324` and `Moise264` calls
`moise341_of_onNeighborhood (moise331OnTube h323 h324 h264) h305`.

Proved and imported (external collaborator, PR #11, lead-accepted on 2026-09-23 with zero-diagnostic
checks and an axiom/linter audit; statement byte-identical): `exists_compactBigonSlide` (module
`Section34CompactBigonSlide` over the `Section34CompactBigon*` modules, the compact twin of the
normalisation bigon slide with the carrier clause `hcar`).  The four leaves left in this file are
the cut-and-graph frame, the compression, the trace and the residual balls.

Proved and imported (Codex lane on lease a, item 16 of `Skeleton/FILL_QUEUE.md`, lead-accepted on
2026-09-24 with zero-diagnostic checks and an axiom/linter audit; statement byte-identical):
`exists_compactCompression` (module `Section34CompactCompressionLeaf` over the
`Section34CompactCompression*` modules: the compact twin of the compression, reusing the
through-tube and pocket bricks of the manifold case in the Euclidean ambient).  The three leaves
left in this file are the cut-and-graph frame, the trace and the residual balls.

Proved and imported (Opus 5.5 worker on lease e, Batch 9 of `Skeleton/OPUS_FILL_LOG_E.md`,
lead-accepted on 2026-09-24 with zero-diagnostic checks and an axiom/linter audit; statement
byte-identical; the hypothesis `htrace` is unused by the proof): `exists_compactResidualBalls`
(module `Section34CompactResidualBalls` over twenty-seven bricks: the two claw balls of a
tetrahedron meeting in the four hole splitting disks, the face-disk runs and the cap split of the
claw sphere, the two-ball pocket giving the residual ball, the patches and edge arcs by cap splits
on the vertex spheres, the tilings for interior vertices and edges, and the outer cells from the
cyclic order of boundary triangles).  The two leaves left in this file are the cut-and-graph
frame and the trace.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe v

section Leaves

variable {C V : Set (EuclideanSpace ℝ (Fin 3))}
  {h f₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {ε : ℝ}
  {K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {src srcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))}
  {H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {env : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}

theorem exists_compactCutAndGraph (h331 : Moise331OnTube) (hC : IsPLBall 3 C) (hV : IsOpen V)
    (hCV : C ⊆ V) (hh : Topology.IsEmbedding (V.domRestrict h)) (hε : 0 < ε) :
    ∃ (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (src srcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3)))
      (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
      (f₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
      Section34CompactCutFrame C K K' src srcBd ∧ Section34CompactCarrierControl K h ε H ∧
        Section34CompactGraphFrame V h ε K K' src H f₁ := by
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

theorem moise341OnNeighborhood (h331 : Moise331OnTube) (h305 : Moise305Tame) :
    Moise341OnNeighborhood := by
  classical
  intro C V hC hV hCV h hh ε hε
  obtain ⟨K, K', src, srcBd, H, f₁, hcut, hcar, hgraph⟩ :=
    exists_compactCutAndGraph h331 hC hV hCV hh hε
  have hgen := hgraph.carriesFundamentalGroupOnto
  obtain ⟨env, henv⟩ := exists_compactFaceEnvelopes h305 hV hCV hh hcut hcar hgraph
  obtain ⟨fbl₀, fblBd₀, hfam₀⟩ := exists_compactFaceShellBalls h305 hV hCV hh hcut henv
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
    · exact compactTraceHomology hgraph henv s (hgen s) (hfam₁ s).1 (hrim s)
        (hfam₁ s).2.2
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
          exists_compactBigonSlide hcut hcar hgraph hg s hop
        exact ⟨g', gBd', hinv', hoff, section34CompactFaceBallRank_lt_of_bigonSlide hc hp⟩)
  have htrace := compactTrace_of_noOperation hcut hgraph hinv hnc hnb
  obtain ⟨tgtD, tgtDBd, tgtA, tgtABd, tgtP, hdisk⟩ :=
    exists_compactFaceDisks hcut hgraph hinv htrace
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
    compactTargetRecognition hcut hgraph hdisk hres hface tc tcBd htcdef htcbddef
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

theorem moise341_of_onNeighborhood (h331 : Moise331OnTube) (h305 : Moise305Tame) : Moise341 := by
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
