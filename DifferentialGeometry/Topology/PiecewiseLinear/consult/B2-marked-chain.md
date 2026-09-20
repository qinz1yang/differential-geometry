# B2. Follow-up to B: how to build the marked chain along the branch

*Consultation prompt, self-contained given `B-touching-seam.md` and its answer. Answer in
English or Chinese.*

**Where to look.** Repository (private; reachable through the owner's GitHub account)
**https://github.com/liao9yuan/differential-geometry-dev**, branch **`moise-integration`**
(https://github.com/liao9yuan/differential-geometry-dev/tree/moise-integration). Read the head
of that branch only. Lean paths are relative to `DifferentialGeometry/Topology/PiecewiseLinear/`.
Your previous answer is digested in `consult/B-answer-digest.md`; we verified its checkable
claims and adopted route (a). We then tested Lemma A and Lemma B against the tree. Four things
came out; the fourth is the question.

### 1. Lemma A needs no link argument — it is two existing chart theorems

* End-point: `HasPLBoundaryCrossingAt.exists_openPartialHomeomorph_halfSpace`
  (`BoundaryCrossingChart.lean:27`) gives a PL chart whose `IsImage` clauses are already
  `M ↔ {0 ≤ z.1}`, `frontier M ↔ {z.1 = 0}`, `A ↔ {z.2.2 = 0 ∧ 0 ≤ z.1}`,
  `B ↔ {z.2.1 = 0 ∧ 0 ≤ z.1}`, `A ∩ B ↔ {z.2 = 0 ∧ 0 ≤ z.1}`. A small box in that chart *is* the
  marked end block.
* Interior: `HasPLTwoSidedCrossingAt.exists_openPartialHomeomorph_slab_interior_isImage`
  (`BoundaryCrossingChart.lean:303`), with two-sidedness already produced from normality
  (`LoopTheorem/InteriorTwoSided.lean:232`). (`HasPLCrossingAt` alone is insufficient: it
  permits a half-plane sheet, a "T".)

So both versions are ~150 lines each, no Schoenflies, no cone.

### 2. "Respects the cyclic order of the four pages" is a vacuous hypothesis

Any homeomorphism of the pair `(Q, X)` restricts to a homeomorphism of `∂Q ≅ S¹` permuting the
four points `X ∩ ∂Q`, hence induces a dihedral ray permutation automatically, and every element
of `D₄` is realised linearly. What must be carried instead is the **sheet label** — which of
the two axes is which source sheet — i.e. the `Bool` of our tagged model (your own point 7).
We will state the page clauses separately per sheet and carry a `Bool` along the chain. Do you
agree that nothing else has to be carried?

### 3. A gap in the tree that your end-point lemma exposes

At a boundary double point, `NormalSingularCellData.crossing` yields
`∃ M, HasPLBoundaryDoubleCrossingAt f P M y` — the half-space `M` is **existentially
quantified and tied neither to `BdM` nor to the chosen half `W`** (`LoopTheorem/NormalCell.lean`,
`SingularNormalForm.lean:242`, `SingularGeneralPosition.lean:2477`); the tree only ever uses it
for "the fibre lies on the frontier of the source". So "the end block lies in `W` and its
bottom face is `block ∩ H`" is not derivable today. Transversality itself is fine:
`∃ u ∈ P ⊓ Q, ℓ u = 1` forces `ℓ ≠ 0` on the double line and on both sheets.
**Q-a.** Is the following derivable, and by what argument: near `e y`, the chart image of `W`
equals the model half-space `{ℓ ≥ 0}` and the chart image of `H` equals `{ℓ = 0}`? We know the
two sheet edges lie in `H` (`image_inter_boundary`) and the cell lies in `W`
(`preimage_boundary_eq_frontier`, now proved). Two transverse arcs of a PL surface `H` through
`y` lying in the plane `{ℓ = 0}` do not force `H = {ℓ = 0}` near `y`. Is the honest fix (i) a
new field in the normal form tying `M` to `W` (then general position must produce it), or
(ii) a further PL re-charting that flattens `H` while keeping the two sheets planar — and is
(ii) always possible (a PL surface through two transverse lines, transverse to both planes)?

### 4. The real difficulty is the chain, not the blocks — which route?

Chart boxes around points of the branch come from *independent* charts, so consecutive boxes
overlap in a region that is a product sub-box of neither (shear `Q` by a `t`-dependent PL map
that is the identity near the core). Hence Lemma A (chart form) does **not** give Lemma B's
hypothesis "consecutive blocks meet exactly in the designated cross-disk". The re-parametrisation
on an interface (`Prod.map h id` for a PL automorphism `h` of `(Q, X, 0)`) is trivial; producing
blocks that *meet in a common cross-disk* is not. We see two routes.

**Route I — chart boxes + a splitting theorem.** New statement: *a marked cross-disk, properly
PL-embedded in a marked model box, meeting the core once and the figure in a cross, splits the
box into two marked boxes.* Then cut each chart box at a disk shared with its neighbour.
This looks like a 3-dimensional Schoenflies/Alexander statement for a disk in a ball **plus** a
marked straightening on the boundary sphere of each half.

**Route II — the marked version of the existing dual-cell induction.** The tree has, for an
arc interior to a combinatorial 3-manifold `K`: trimmed arc cells
`coneSet (arcCellApex v j) (arcCellBase K v j).space` (dual blocks of the arc's faces in the
barycentric subdivision), with `cell j ∩ cell (j+1)` **exactly** the cone interface disk
(`ArcCellGluing.lean:48`), non-adjacent cells disjoint (`ArcChainCells.lean:53`), and the
induction `ArcCellNormalizationInduction.lean:19` which carries one `Φ` and at each step
extends it over the next cone by
`exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked` (`ConeDiskPairExtension.lean:20`) — a
marked extension for the pair (cone, core arc) prescribed on the interface disk.
The hypothesis `hinterior` is used in exactly two places, only to get sphere links instead of
disk links (`ArcCellGluing.lean:97,146`); the end vertex cells are currently dropped.
Adapted triangulations exist: `exists_isSubdivision_subcomplexes` (`Triangulation.lean:84`),
mesh control (`Subcomplex.lean:114`), PL maps made simplicial
(`CellMapTriangulation.lean:355`), the double (`Orientation.lean:3300`). So after subdivision
`D(Δ)`, the branch and `H` are subcomplexes and each dual block meets `D(Δ)` in the cone over
`base ∩ D(Δ)`. What Route II then needs is 2-dimensional only:
*(T₄) a PL homeomorphism of the boundary circle of a PL disk `D'` matching four marked points
in order extends to a PL homeomorphism of pairs `(D', T) → (D'_model, T_model)`, where `T` is a
four-spoke tree (centre in the interior, leaves the four marked points)* — by cutting along the
spokes (the tree has crosscut and three-cell theorems, `DiskCrosscut.lean`,
`LoopTheorem/CutAndPaste.lean:1177`) and coning over each sector; plus the fact that
`base ∩ D(Δ)` *is* such a graph (two circles meeting in the two piercing points, from the two
local sheets) once stars are inside crossing charts; plus the end cells with disk links.

**Q-b.** Which route is cheaper and why? We lean to Route II (interfaces are canonical, only
2-dimensional new geometry, the induction skeleton exists). Is there a hidden cost — e.g. does
"`base ∩ D(Δ)` is the suspension of four points" need more than mesh smallness plus the two
chart theorems of §1, and does the cone structure of a dual block restrict correctly to `D(Δ)`
(is `D(Δ) ∩ coneSet apex base = coneSet apex (base ∩ D(Δ))` automatic for a subcomplex, or does
it need `D(Δ)` to be a *full* subcomplex of the subdivision)?
**Q-c.** Give the exact statement of (T₄) and of its marked cone extension (the four-page
analogue of `exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked`), including how the sheet
label `Bool` is transported, and the exact form at an end vertex on `H` (link a disk, the block
a half-ball, the bottom face the cone over the link's boundary circle) — in particular which
face of the model box corresponds to the link disk and which to `block ∩ H`.
**Q-d.** The reading of the cross reglue (your Lemma D) needs the source-side decomposition
`P = P₊ ⊔ P₋` to be polyhedral and `coord` PL on each. In Route II, is that automatic from
"`D` is simplicial for the adapted triangulations", and what exactly must be checked about the
cut-and-paste maps `f₁, f₂, f₃, h` of the reglue (they are PL homeomorphisms of 2-balls, not
simplicial for the same subdivision)?

### Constraints on the answer

Exact statements (Lean-ish welcome); say what you could not verify; do not weaken existing
statements. A considered "this is false, here is the counterexample" remains the most valuable
answer.
