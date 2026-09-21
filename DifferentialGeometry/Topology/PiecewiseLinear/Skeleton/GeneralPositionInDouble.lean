/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DoublePointFibreAgreement
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.GeneralPositionInDoubleAssembly
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaTwoBuffered

/-!
# Sorry-first skeleton of general position in the double

The assembly `generalPositionInDoubleBuffered` below is proved for real from the twelve leaves
of this file, from the proved cover theorem `exists_finiteAdaptedCover_of_compactSpace`, from the
proved bridge `eq_regionGluedMap_of_eqOn`, from
`SingularTwoCell.nonempty_normalSingularCellData_of_fields`, from
`doublePointSet_subset_of_preimage_singleton_eq_off` and from
`exists_boundary_loop_of_buffered_homotopy`; every `sorry` is a leaf, none is inside the
assembly.  The chain is: adapted half-space charts at every point of the double, a finite cover
of the whole double by regions `closure (W j) ⊆ V j` with `closure (V j)` inside one adapted
chart, a transition subdivision on every closed overlap, then a chart-by-chart induction.

The induction invariant has two halves.  After the step for the cell `D k`, with
`Z k = ⋃ j < k, closure (W j)`, (a) the crossings are PL normal double crossings over an open
set containing `Z k`, and (b) for every later index `m`, over the compact transition zone
`Z k ∩ closure (V m \ closure (W m))` the crossings are *margin stable in the chart* `ec m`:
`HasStableCrossingBlocks`.  Half (b) is what consult L §2 shows a seed needs, and what consult O
§2 localises: on the final subdivision a simplex with a frozen vertex misses `closure (W k)` by
`hsep`, so the old crossings it can disturb lie over `Z k ∩ closure (V k \ closure (W k))`, and
there the two complete local source sheets are buffered graphs `u = a (v, t)`, `v = b (u, t)`
with `Lip a · Lip b ≤ 1 - η`; the unperturbed map is then the centre of the ball of admissible
vertex maps, so no seed `φ₀`, no radius `ρ` and no pairing certificate `χ, ψ` are needed, and
`VertexParameterSpace`, `IsVertexSupOpen` and `VertexSupBall` are gone with them.  Consult O §3
shows (b) is *not* an open condition in the current chart's vertex parameters, which is why the
generic choice leaf now carries wall conditions for the later charts.

The counterexample of consult O §3.  In the later chart `H (x, y, t) = (h (x, y), t)` with `h`
the sector map that is `(y / 3, -2 x + 5 y / 3)` on `3 x ≤ y ≤ 4 x`, `(4 x / 3, y + 2 x / 3)` on
`y ≥ 4 x` and the identity elsewhere, the two flat sheets `y = 0` and `y = x` have a strict graph
margin in both charts, yet translating both by `(a, 3 a, 0)` puts their crossing line on the wall
`y = 3 x`, where the four rays become `A : (1, 0), (0, 1)` and `B : (1, 1), (-1, 1)` — the bent
model without margin, and one further small move of `B` makes it a tangency.  So an old margin in
a later chart gives no safe ball in the current chart's parameters, and the double curve must be
kept transverse to the walls: that translate is excluded by the transversality clause
`hwalltrans` of `exists_genericVertexMap_in_adaptedChart`, because the translated double line
`x = a, y = 3 a` lies *inside* the wall `y = 3 x`, so its direction lies in the wall's direction
and no transverse `w` exists.  After review R that clause, and the skeleton clause `hwallskel`,
fire only at a *free interior germ*: a double point off `BdM` whose whole fibre lies in the
interior of triangles of `R` with no frozen vertex.  The translate above is such a germ, so the
counterexample of consult O §3 is still excluded.

Free means free *in the source*, and that is a neighbourhood condition.  Review V refuted the
predicate used until the seventh iteration with `ec = ecw = id`, `ℓ = t`, `Ac = Lc = ∅`, `Rc = R`
an interior source triangle with an edge whose image runs from `(-1, 0, 2)` to `(1, 0, 2)`, an
unmoved rectangle `{x = 0, |y| ≤ 1, 1 ≤ t ≤ 3}` outside `R` and a wall triangle `F ⊆ {x = 0}` of
`Qw` with `(0, 0, 2) ∈ relint F`: for every `τ < 1 / 10` the edge still crosses the rectangle, so
some `y ∈ F` is a double point whose second preimage is *outside* `R`, the universal quantifier
over the simplices of `R` containing it is empty, and the old predicate called that germ free —
making `hwallfold` unsatisfiable.  `FreeSourceGerm R Ac g S y` now asks, of every fibre point,
both `R.space ∈ 𝓝[S] x` and that no simplex of `R` containing `x` has a frozen vertex;
`mem_space_of_freeSourceGerm` records that a free source germ has its whole fibre in `R.space`,
which is exactly what the counterexample violates.  `IsFreeDoubleGerm` is that together with
`y ∉ BdM`, `IsFreeBoundaryDoubleGerm` together with `y ∈ BdM`, and `IsFreeInteriorDoubleGerm`
adds that every fibre point is interior to a triangle.

Four strata, not two.  The claim that the degeneracies exempted from the wall conditions are
handled by equality retention is **withdrawn**: `isStableCrossingBlock_of_eqOn_compl` covers only
blocks whose whole preimage is untouched, and mixed germs do not satisfy whole-block fibre
equality.  A double point `y` of the glued map that has to be checked now falls in exactly one of
four strata, each with its own argument.

* Off the compact `Kp`.  `Kt` is the compact set of the seed leaf with `⇑D '' Rc.space ⊆
  interior Kt` and both images of `Rc.space` inside `Kt`; the assembly chooses a compact `Kp`
  with `Kt ⊆ interior Kp ⊆ Kp ⊆ V` by `exists_compact_between`.  Over `Ktᶜ` the two maps have the
  same fibres, and `hWK` proves there is no double point of the new map in `closure (W k) \ Kt`
  at all, so the part of (b) outside `Kp` is carried over the *compact* set
  `Q_out = Z ∩ P m \ interior Kp ⊆ Ktᶜ` by the proved chain
  `hasStableCrossingBlocksIn_of_isCompact_subset`, then
  `hasStableCrossingBlocksIn_of_preimage_singleton_eq`, then
  `HasStableCrossingBlocks.union` and `HasStableCrossingBlocks.mono_doublePointSet`.  This is the
  compact localisation of review V §4; a finite block cover of the possibly non-compact
  `Z ∩ P m \ Kt` is never asked for.
* Free interior germs over `Kp`: the wall clauses `hwallskel`, `hwalltrans`, `hwallfold` of the
  generic leaf, consumed by the crossing leaf.
* Free boundary germs over `Kp`: the new clause `hboundaryAffine` of the generic leaf.
* Non-free (mixed and frozen) germs over `Kp`: the new leaf
  `exists_laterMarginBlocks_of_mixedGerms`, which is *not* equality retention.

`hasStableCrossingBlocksIn_of_isCompact_subset` is a leaf, not a theorem.  Its proof needs, for
each double point `y` of the compact `Q'` inside an inner block of the given family, a block
recentred at `y`: the affine equivalence `A` composed with the translation by `-A (ec y)`, a
radius `r' ≤ r / 2` small enough that the recentred box lies inside the old block and inside `N`
(continuity of `ec` and of `A`), the sheets cut down to `SA ∩ f ⁻¹' B'`, `SB ∩ f ⁻¹' B'`, and the
boundary branch kept when `ℓ (ec y) = 0` but replaced by the interior branch when `ℓ (ec y) > 0`
(whence `hBdchart`).  The finite subfamily comes from compactness of `doublePointSet f S`, which
is why the statement carries `IsCompact S`, `ContinuousOn f S` and the injectivity scale: with
`UniformInjectivityScale S f κ` the set `{(x, z) ∈ S × S | κ ≤ dist x z, f x = f z}` is compact
and its image is the double point set.  The relative neighbourhood clauses need `MapsTo f S C`
and `hCchart` on the physical side.  Missing local API: `IsPiecewiseAffineOn` and
`IsPLHomeomorphOn` under restriction to a subset and under postcomposition with a translation.

`IsStableCrossingBlock` is not satisfiable by degenerate data over a set carrying double points.
Over a double point of the block the two graph projections force two *different* sheets:
`sheets_nonempty_of_isStableCrossingBlock` proves that both `SA` and `SB` meet the fibre, so a
one-sheet or sheet-free block is impossible, and `HasStableCrossingBlocks` demands that the
inner blocks cover `doublePointSet ∩ Q`; combining the two,
`exists_sheets_of_hasStableCrossingBlocks` proves that over *every* double point of `Q` the
family produces two disjoint sheets through that point, so a block-free family is impossible as
soon as `doublePointSet ∩ Q ≠ ∅`; `0 < η` is a field, so an `η`-free reading is impossible too.
`hasStableCrossingBlocks_of_doublePointSet_inter_eq_empty` gives the base case `Z 0 = ∅` and
nothing more; `isStableCrossingBlock_of_flatSheets` and
`isStableCrossingBlock_of_flatSheets_boundary` inhabit the block predicate with `η = 1` by two
transverse coordinate planes, `a = b = 0`, `La = Lb = 0`, in the interior and in the half space,
and `hasStableCrossingBlocksIn_of_isStableCrossingBlock` turns one such block into a one-block
family, so neither predicate is inhabited only by an empty family.  The uniform separation of
the remaining source from the block is not a separate field: the full-preimage equality
`S ∩ f ⁻¹' chartBlock = SA ∪ SB` already places every other source point outside the block, and
a uniform distance from the inner block follows from compactness of the source; a separate
uniform field would not survive `isStableCrossingBlock_of_eqOn_compl`.

Two graphs with a margin are not two source sheets.  Review R refuted the claim that the
recognition of the complete source sheets at a margin-stable block was done.  Take
`γ : [0, 6] → ℝ²` linear through `(2, 0), (0, 0), (0, 2), (-2, 2), (-2, 0), (0, 0), (0, -2)`,
`S = [0, 6] × [-2, 2]`, `D (s, t) = (γ s, 4 + t)`, `ec = id`, `ℓ = z₃`,
`A (x, y, z) = (x, y, z - 4)`, `r = 1`, `tlo = -1`: collecting the two vertical half-sheets in
`SA` and the two horizontal ones in `SB` satisfies the full preimage equation, both graph
equations with `a = b = 0` and makes both graph projections bijective, yet the two genuine
sheets are two bent `L`s whose four rays occur in the cyclic order `AABB`, a touching and not a
normal crossing, and the inverse of each projection jumps from one genuine sheet to the other
across the axis.  `IsStableCrossingBlock` therefore now carries, for each sheet, that its graph
projection is a PL homeomorphism onto its image and that at every sheet point over the *inner*
block the sheet is a neighbourhood of that point in `S` and its projection a neighbourhood of
the projected point in `blockHalfPlane tlo`; the outer block carries a compact buffer inside
`ec.source`.  The re-paired sheets of that model fail the source clause at the two parameters
over the axis, since every neighbourhood in `S` of either of them meets the other genuine sheet.
`isStableCrossingBlock_of_eqOn_sheets` transports a block along any map agreeing with the old
one on `SA ∪ SB` with the same full preimage, and is the common core of the two retention
lemmas: `isStableCrossingBlock_of_eqOn_compl` and, for the locality route of review R,
`isStableCrossingBlock_of_preimage_singleton_eq` with its cover-level companion
`hasStableCrossingBlocksIn_of_preimage_singleton_eq`, which needs every *outer* block inside the
open set `N` over which the fibres agree — that is what `HasStableCrossingBlocksIn` records.

The folded counterexample of the fourth external review violates (b).  Its two complete local
sheets are the bent `L = {y = 0, x ≥ 0} ∪ {x = 0, y ≥ 0}` and the bent `V = {y = |x|}`, both
times the crossing line.  In any affine coordinates the two ray directions of `L` must have
`|U| ≤ La |V|` and those of `V` must have `|V| ≤ Lb |U|`; since the two `V`-values of the `L`
rays have opposite signs, adding gives `|p| + |q| ≤ La (|r| + |s|) = La |V (e₂ - e₁)| ≤ La Lb
(|p| + |q|)`, hence `1 ≤ La Lb`, contradicting `La Lb ≤ 1 - η`.  So that configuration is not a
hypothesis of the seed leaf, and the seed leaf is not refuted by it; the flat fixture (two flat
sheets crossing transversally inside the chart, frozen outer ring, `Z ∩ W ≠ ∅`) does satisfy
(b) with `η = 1`, so the seed leaf is not vacuous either.

Two scales, not one.  The third external review refuted the claim that a single `ε` can both
keep the perturbed chart image inside `⇑ec '' V` and measure the ambient error: on the flat torus
`(ℝ/20ℤ)³` with `D = (s, t, 0)`, `ec q = q / 2` and `V = B (0, 1)` the chart buffer forces
`ε ≤ 1 / 2` at the origin while the inverse chart doubles the error.  Preparation returns an
ambient `δ` and a chart `ε` with the conversion
`dist z (ec (D x)) < ε → z ∈ ⇑ec '' V ∧ dist (ec.symm z) (D x) < δ`; `hcert` and `hclose` measure
in `M` with `δ`, while `hsmall`, the chart buffer, the active buffer and the boundary track
buffer measure in the chart with `ε`.

Admissibility is the `Prop`-valued `AdmissibleVertexMap`: vertex error `< τ`, equality with
`ec ∘ ⇑D` at vertices of the frozen collar, height zero exactly at the physical boundary vertices
`Bv`, positive height at all other vertices.  It is inhabited for every `τ > 0` by the
unperturbed vertex map (`exists_admissibleVertexMap_of_adaptedChart`), so the seed leaf cannot be
made vacuous by a tiny `τ`, and `Bv` is determined by `R` and `Lc`, so the seed leaf quantifies
over `Bv` and `φ` together and the generic leaf returns both.

The pairing is gone; localisation stays.  `Kt` is compact, contained in `V`, and chosen in the
seed leaf before `φ`, with `⇑D '' Rc.space ⊆ interior Kt`.  Over `Z ∩ Kt` the old crossings that
a frozen or mixed simplex can meet are protected by the seed leaf's `hprot`; off `Kt` half (a) is
transported by the identity, because
`preimage_singleton_eq_of_eqOn_compl_of_image_subset` turns `EqOn ⇑D' ⇑D Rc.spaceᶜ` together with
the two image bounds into `⇑D' ⁻¹' {y} = ⇑D ⁻¹' {y}` for every `y ∉ Kt`, and half (b) off `Kp` is
the proved first stratum above; on the free part the crossings are recognised afresh from the
guard.  Every double point over `closure (W k)` is free in the source, which the proved theorem
`freeSourceGerm_of_mem_closure` gets from `hactive`, `hsep`, `hΩcover`, `hΩR`, `hNbfr` and
`hNbA`; so the mixed layer meets the *old* region only, and its leaf is stated over the set
`Z ∩ P i ∩ Kp` alone.  Review R ruled that on entirely free simplices
the four-point guard together with the source manifold condition, local injectivity and `hpzero`
already gives interior transversality and transversality of the boundary traces, so no further
general-position clause is added for them.  In particular **no** wall condition forbids boundary
edge–edge crossings: two meeting boundary edges cross because no three of four relevant free
boundary vertices are collinear, and that is exactly the boundary model, not a degeneracy.  The
earlier claim that the complete source-sheet recognition at edge–triangle points follows from
the guard is withdrawn; it is an open obligation of `exists_normalCrossings_of_gluedCell`.

The leaves, with owner and review state.  The eight leaves marked frozen are byte-identical with
the reviewed snapshot; every other leaf changed after review V or is new.

`exists_adaptedHalfSpaceChart_in_double` (lane H, reviewed 2026-09-21, frozen): every point of
the double of a combinatorial three manifold with boundary has arbitrarily small charts of the
maximal `plGroupoid 3` atlas adapted to the actual pair.

`SingularTwoCell.exists_cutOutPiece_of_closure_subset` (lane H, reviewed 2026-09-21, frozen): the
cut-out source piece with boundary, its frozen collar `Ac` and the seam data `Ω`, `Nb`.

`exists_gluedCell_of_vertexMap_in_adaptedChart` (lane H, reviewed 2026-09-21, frozen): the
literal gluing, with equality on the whole complement.

`exists_globalInvariants_of_gluedCell` (lane H, reviewed 2026-09-21, frozen): the invariants of
the glued cell on the whole disk, with the buffered boundary homotopy.

`exists_normalizationPreparation_on_prescribedRegion` (lane H, reviewed 2026-09-21, frozen):
the control complex `T`, the scales `κ`, `δ`, `ε` and the three buffers, all before the
perturbation.

`exists_transitionSubdivisionOnOverlap` (lane H, reviewed 2026-09-21, frozen): on a compact
overlap of two adapted charts, a finite complex in the first chart's target covering a whole
*neighbourhood* of the overlap, `⇑ec '' N ⊆ interior Q.space`, on whose faces the transition is
affine.  Review R refuted the covered-set version: `N = {y}` and a one-vertex complex satisfy it
while covering no neighbourhood.  Consult O §4 forbids assuming the transitions affine.

`hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock` (lane H, reviewed 2026-09-21, frozen): a
margin-stable block is a PL normal double crossing at each double point of its *inner* block.
Under the old predicate this was FALSE by the re-pairing model above; the genuine-sheet clauses
are exactly what a proof consumes.  Its consumer is not the assembly but the proof of
`exists_protectedSubdivision_in_adaptedChart`, whose `hprot` has to produce normality of the
glued map on the frozen and mixed part from the blocks that survive the perturbation.

`hasStableCrossingBlocksIn_of_isCompact_subset` (new after review V, unreviewed): the compact
localisation lemma of review V §4, with the hypotheses and the missing API listed above.  It is
the only input of the first stratum, and the assembly uses it on `Q_out = Z ∩ P m \ interior Kp`
with `N = Ktᶜ`.

`exists_protectedSubdivision_in_adaptedChart` (lane H, reviewed 2026-09-21, frozen): the seed,
consuming (b) at `m = k` in its strengthened form, so the two genuine local source sheets are
given and no recovery of sheets from normality is needed.  It fixes `R`, `τ` and `K` before any
vertex map and asserts, for every admissible `φ`, the control clauses, the protection of the old
crossings over `Z ∩ K` that a simplex with a frozen vertex takes part in, and the survival of the
stable blocks with margin `η / 2`.  The limit argument of consult O §2 needs the *predetermined*
injectivity scale, so the leaf also receives `κ`, `hcert` and the conversion `hconv` of the
preparation certificate; `Z ∩ closure (V \ closure W)` is compact because `Z` is closed and `M`
is a compact space, and its closed buffer lies in `ec.source` because the cover theorem returns
`closure (V j) ⊆ ec.source`.

`exists_genericVertexMap_in_adaptedChart` (changed after review V, unreviewed): relative
multi-chart generic production, with the wall conditions stratified.  Beside admissibility and
the relative guard it produces, for every later chart of the fixed finite family and every free
interior germ of the new double point set inside the fixed compact overlap, that the germ misses
the one-skeleton of the transition complex and that near it the double point set is exactly a
two-sided straight segment, of unit direction transverse to every two-face carrying the point;
and, for every free germ, that a double point on the image of a source edge misses the
two-skeleton; and, new after review V, the clause `hboundaryAffine`: at every *free boundary*
germ `y` and in every later chart `i` there are an open `O₁ ∋ ec y` and an affine `A` with
`ecw i ∘ ec.symm = A` on `O₁ ∩ {ℓ ≥ 0}`.  The tree has no cross-section of a complex by a
hyperplane — `restrict` selects a subcomplex — so the clause is stated directly and not as
"`ec y` misses the one-skeleton of the complex induced by `Qw i` on `{ℓ = 0}`"; the two are
equivalent, and the second is what a density proof produces.  The bad set of the boundary plane
is `{ℓ = 0} ∩ conv F` over the two-faces `F` of `Qw i` with `aff F ⊄ {ℓ = 0}`, a finite union of
lines in that plane; a boundary double point is a crossing of two boundary traces and moves with
two free parameters inside `ker ℓ`, since admissibility keeps boundary vertices at height zero,
so it avoids that bad set generically.  Off the bad set the physical half-neighbourhood of `ec y`
meets exactly one three-face of `Qw i` (plus a two-face inside `{ℓ = 0}`, whose two cofaces lie
on opposite sides), and the transition is affine there.  Review V's counterexample —
`H (x, y, t) = (x, y, t)` for `y ≤ 3 x` and `(y / 3, -2 x + 5 y / 3, t)` for `y ≥ 3 x`, with
`A : y = t` and `B : y = x + t` crossing at the origin of `{t ≥ 0}` — is a free boundary germ
sitting on the wall `y = 3 x`, which is transverse to the boundary plane; the two determinants
are `1` and `2 / 3`, so no affine map agrees with `H` on a half-neighbourhood of the origin, and
`hboundaryAffine` fails there.  That configuration is excluded, not repaired.
Review R refuted the unstratified clauses.  Freezing a
neighbourhood of both sheets of an old double curve that lies on an edge of `Qw i` leaves every
admissible `φ` with that curve, contradicting the old `hwallskel`; and the cone over the
quadrilateral with boundary vertices `(-1,-1,0), (1,1,0), (-1,1,0), (1,-1,0)` and apex
`(0,0,1)`, with `Ac` empty and a wall two-face inside `{ℓ = 0}` around the origin, keeps two
crossing boundary edges inside that wall for every admissible `φ`, because all four corners are
`Bv` vertices and stay in `{ℓ = 0}`, contradicting the old `hwallfold`.  Both are now exempt: the
first has no free germ at all, the second is a germ on `BdM`.  Degeneracies forced by frozen data
carry no wall condition; they belong to the fourth stratum and are the content of the mixed-layer
leaf, not of equality retention.

`exists_laterMarginBlocks_of_mixedGerms` (new after review V, **NEEDS_PROOF — mathematically
unverified; an external consult is open (`consult/U-mixed-later-margin.md`)**): for one later
chart `i`, the glued map of an admissible controlled vertex map has margin-stable blocks with
some `η' > 0` over the set of its double points in `Z ∩ Pw i ∩ Kp` that are *not* free source
germs.  Its inputs are the old invariant (b) in the chart `i` over `Z ∩ Pw i`, the conclusions of
the seed leaf — `hprot`, and `hpersist`, the current-chart blocks with margin `η / 2` — and the
control certificate `hinj`, `hinj'`, `hfiber`.  Do not read it as equality retention: `hprot`
gives normality only, `hpersist` the current chart only, and the old invariant concerns the old
map, so none of the three gives the later-chart margin of the *new* map.  It is not vacuous: on
the fixture the double curve leaves `W` through the frozen ring, and the germs there have a
preimage on a simplex with a frozen vertex, so they are not free.  It is not trivially true
either.  A *new* mixed double point over `Z` — one with a moved preimage and a preimage on a
frozen or mixed simplex — is exactly the hard case, and consult O §3 shows that an old margin in
a later chart gives no safe ball in the current chart's parameters; the wall clauses do not fire
there, because they fire only at free germs.  What *is* proved is that this cannot happen over
the new region: `freeSourceGerm_of_mem_closure` shows every double point over `closure (W k)` is
a free source germ, which is why the leaf is stated over `Z ∩ Pw i ∩ Kp` and not over
`(Z ∪ closure W) ∩ Pw i ∩ Kp`.  This is the leaf most likely still wrong.

`exists_normalCrossings_of_gluedCell` (changed after review V, unreviewed): recognition on
the free part, protection on the frozen and mixed part, identity transport of (a) off `Kt`, and
the production of (b) for every later chart over `(Z ∪ closure W) ∩ closure (V m \ closure (W m))
∩ Kp` — the part of (b) outside `Kp` was removed from the leaf and is now proved in the assembly.
The leaf no longer receives the old invariant `hlater`, which went to the mixed-layer leaf; it
receives instead `hmixed`, `hboundaryAffine`, the compact `Kp` with `Kt ⊆ interior Kp ⊆ V`, and
the seam data `Nb` needed to apply `freeSourceGerm_of_mem_closure`.  So its four inputs are one
per stratum: `hwallskel`/`hwalltrans`/`hwallfold` for free interior germs, `hboundaryAffine` for
free boundary germs, `hmixed` for the non-free germs, and, off `Kp`, nothing — the assembly does
that part.  Review R refuted the previous hypothesis list with `Z = Nw = ∅`, `ℓw = 0` and
`Pw = {y}` for a new boundary double point `y`: everything held vacuously, yet no output block
can contain `y`, since an interior block must miss `BdM` while a boundary block needs
`(A z).2.2 = ℓw i z` for an affine equivalence `A`, which `ℓw i = 0` forbids.  The leaf therefore
also receives that the later charts lie in the maximal atlas, that `ℓw i ≠ 0`, the two
adaptedness equivalences of `ecw i`, `ℓw i` for `C` and for `BdM`,
`Kp ∩ (Z ∪ closure W) ∩ Pw i ⊆ Nw i`, `⇑ec '' Nw i ⊆ interior (Qw i).space`, `IsClosed Z` and
`IsClosed (Pw i)`.  Each is supplied at the single call site by the proved cover theorem, by
`exists_transitionSubdivisionOnOverlap` or by `exists_protectedSubdivision_in_adaptedChart`; the
degenerate input above violates both `ℓw i ≠ 0` and, since `y` lies in
`Kp ∩ closure W ∩ Pw i`, the covering hypothesis.

Fixture.  In the double-ball model, two transverse planar disks joined by a PL band avoiding
their intersection line into one proper immersed disk, a frozen outer ring, a later chart that is
a non-trivial affine shear and a non-zero small perturbation in the free region satisfy every
hypothesis of every changed leaf, with a non-empty double point set, a non-empty block family,
free interior germs along the interior of the intersection arc, free boundary germs where that
arc meets `BdM`, and non-free germs where it leaves `W` through the frozen ring; so no changed
leaf is trivially true on it, no changed leaf is satisfied by a degenerate witness, and none of
the four strata is empty on it.  The unmoved rectangle of review V §2 is *not* a free germ on
that fixture, since its outside preimage fails `R.space ∈ 𝓝[S] x`, while the interior double
points of the fixture are free germs, so the wall clauses are not vacuous.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

open Classical in
theorem exists_adaptedHalfSpaceChart_in_double {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (hK : IsCombinatorialManifoldWithBoundary 3 K) :
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K hK)
    let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
    let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
    let Bd := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (ι '' (PiecewiseLinear.boundaryComplex 3 K).space)
    ∀ (y : (double 3 K).space) (U : Set (double 3 K).space), U ∈ 𝓝 y →
      ∃ (ec : OpenPartialHomeomorph (double 3 K).space (EuclideanSpace ℝ (Fin 3)))
        (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
        ec ∈ (plGroupoid 3).maximalAtlas (double 3 K).space ∧ ℓ ≠ 0 ∧
          y ∈ ec.source ∧ ec.source ⊆ U ∧
          (∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x)) ∧
          (∀ x ∈ ec.source, x ∈ Bd ↔ ℓ (ec x) = 0) := by
  sorry

def UniformInjectivityScale {α : Type*} [PseudoMetricSpace α] {β : Type*} (S : Set α)
    (f : α → β) (η : ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, dist x y < η → f x = f y → x = y

theorem uniformInjectivityScale_of_injOn {α : Type*} [PseudoMetricSpace α] {β : Type*}
    {S : Set α} {f : α → β} (h : InjOn f S) (η : ℝ) : UniformInjectivityScale S f η :=
  fun _ hx _ hy _ hxy => h hx hy hxy

open Classical in
def StarInj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {β : Type*}
    (T : Geometry.SimplicialComplex ℝ E) (g : E → β) : Prop :=
  ∀ v ∈ T.vertices, InjOn g (starComplex T v).space

open Classical in
theorem starInj_of_injOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {β : Type*}
    {T : Geometry.SimplicialComplex ℝ E} {g : E → β} (h : InjOn g T.space) : StarInj T g := by
  intro v _
  exact Set.InjOn.mono (space_mono_of_faces_subset (starComplex_faces_subset T v)) h

theorem preimage_singleton_eq_of_eqOn_compl_of_image_subset {α β : Type*} {f f' : α → β}
    {R : Set α} {P : Set β} (hoff : EqOn f' f Rᶜ) (hf : f '' R ⊆ P) (hf' : f' '' R ⊆ P)
    {y : β} (hy : y ∉ P) : f' ⁻¹' {y} = f ⁻¹' {y} := by
  ext x
  by_cases hx : x ∈ R
  · simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      exact absurd (h ▸ hf' (mem_image_of_mem f' hx)) hy
    · intro h
      exact absurd (h ▸ hf (mem_image_of_mem f hx)) hy
  · simp only [mem_preimage, mem_singleton_iff, hoff hx]

def blockBox (r tlo : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | |p.1| ≤ r ∧ |p.2.1| ≤ r ∧ p.2.2 ∈ Icc tlo r}

def blockHalfPlane (tlo : ℝ) : Set (ℝ × ℝ) :=
  {p | tlo = 0 → 0 ≤ p.2}

def complexSkeleton {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)
    (K : Geometry.SimplicialComplex ℝ E) : Set E :=
  ⋃ (s : Finset E) (_ : s ∈ K.faces) (_ : s.card ≤ n + 1), convexHull ℝ (s : Set E)

section Ambient

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem exists_finiteAdaptedCover_of_compactSpace [T2Space M] [CompactSpace M] (BdM C : Set M)
    (hchart : ∀ (y : M) (U : Set M), U ∈ 𝓝 y →
      ∃ (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
        (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
        ec ∈ (plGroupoid 3).maximalAtlas M ∧ ℓ ≠ 0 ∧ y ∈ ec.source ∧ ec.source ⊆ U ∧
          (∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x)) ∧
          (∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)) :
    ∃ (n : ℕ) (W V : ℕ → Set M),
      (∀ j, IsOpen (W j)) ∧ (∀ j, IsOpen (V j)) ∧ (∀ j, closure (W j) ⊆ V j) ∧
        (∀ j, n ≤ j → W j = ∅) ∧ (⋃ j, W j) = univ ∧
        ∀ j < n, ∃ (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
          (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
          ec ∈ (plGroupoid 3).maximalAtlas M ∧ ℓ ≠ 0 ∧ closure (V j) ⊆ ec.source ∧
            (∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x)) ∧
            (∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0) := by
  have : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (H := EuclideanSpace ℝ (Fin 3)) M
  have key : ∀ y : M, ∃ (Wy Vy : Set M)
      (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
      (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
      IsOpen Wy ∧ y ∈ Wy ∧ IsOpen Vy ∧ closure Wy ⊆ Vy ∧ closure Vy ⊆ ec.source ∧
        ec ∈ (plGroupoid 3).maximalAtlas M ∧ ℓ ≠ 0 ∧
        (∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x)) ∧
        (∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0) := by
    intro y
    obtain ⟨ec, ℓ, hec, hℓ, hy, -, hC, hBd⟩ := hchart y univ Filter.univ_mem
    obtain ⟨s, hs, hsub, hcomp⟩ := local_compact_nhds (ec.open_source.mem_nhds hy)
    have hVopen : IsOpen (interior s) := isOpen_interior
    have hyV : y ∈ interior s := mem_interior_iff_mem_nhds.2 hs
    have hclV : closure (interior s) ⊆ ec.source :=
      (closure_mono interior_subset).trans (hcomp.isClosed.closure_eq.subset.trans hsub)
    obtain ⟨s', hs', hsub', hcomp'⟩ := local_compact_nhds (hVopen.mem_nhds hyV)
    exact ⟨interior s', interior s, ec, ℓ, isOpen_interior,
      mem_interior_iff_mem_nhds.2 hs', hVopen,
      (closure_mono interior_subset).trans (hcomp'.isClosed.closure_eq.subset.trans hsub'),
      hclV, hec, hℓ, hC, hBd⟩
  choose Wy Vy ecy ℓy hWopen hymem hVyopen hWVy hVycl hecm hℓne hCm hBdm using key
  obtain ⟨t, -, hcover⟩ :=
    isCompact_univ.elim_nhds_subcover Wy fun y _ => (hWopen y).mem_nhds (hymem y)
  let p : ∀ j : ℕ, j < t.card → M := fun j h => ((t.equivFin.symm ⟨j, h⟩ : {x // x ∈ t}) : M)
  refine ⟨t.card, fun j => if h : j < t.card then Wy (p j h) else ∅,
    fun j => if h : j < t.card then Vy (p j h) else ∅, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases h : j < t.card
    · simp only [dif_pos h]
      exact hWopen _
    · simp only [dif_neg h]
      exact isOpen_empty
  · intro j
    by_cases h : j < t.card
    · simp only [dif_pos h]
      exact hVyopen _
    · simp only [dif_neg h]
      exact isOpen_empty
  · intro j
    by_cases h : j < t.card
    · simp only [dif_pos h]
      exact hWVy _
    · simp only [dif_neg h, closure_empty]
      exact Subset.rfl
  · intro j hj
    exact dif_neg (not_lt.2 hj)
  · refine eq_univ_of_forall fun x => ?_
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
    refine mem_iUnion.2 ⟨((t.equivFin ⟨y, hy⟩ : Fin t.card) : ℕ), ?_⟩
    rw [dif_pos (t.equivFin ⟨y, hy⟩).isLt]
    have hval : p ((t.equivFin ⟨y, hy⟩ : Fin t.card) : ℕ) (t.equivFin ⟨y, hy⟩).isLt = y :=
      congrArg Subtype.val (t.equivFin.symm_apply_apply ⟨y, hy⟩)
    rw [hval]
    exact hxy
  · intro j hj
    refine ⟨ecy (p j hj), ℓy (p j hj), hecm _, hℓne _, ?_, hCm _, hBdm _⟩
    simp only [dif_pos hj]
    exact hVycl _

theorem SingularTwoCell.exists_cutOutPiece_of_closure_subset [T2Space M] (D : SingularTwoCell M)
    {V₀ V : Set M} (hV : IsOpen V) (hV₀ : closure V₀ ⊆ V) :
    ∃ (Rc Lc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
      (Ω Nb : Set (EuclideanSpace ℝ (Fin 2))),
      Rc.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 Rc ∧
        Lc.faces ⊆ Rc.faces ∧ Ac.faces ⊆ Rc.faces ∧
        Rc.space ⊆ D.domain ∧ Rc.space ⊆ ⇑D ⁻¹' V ∧
        Lc.space = Rc.space ∩ frontier D.domain ∧
        IsOpen Ω ∧ D.domain ∩ ⇑D ⁻¹' closure V₀ ⊆ Ω ∧ D.domain ∩ Ω ⊆ Rc.space ∧
        IsOpen Nb ∧ Rc.space \ Ω ⊆ Nb ∧ Rc.space ∩ Nb ⊆ Ac.space ∧
        Disjoint Ac.space (⇑D ⁻¹' closure V₀) := by
  sorry

theorem exists_gluedCell_of_vertexMap_in_adaptedChart [T2Space M] (D : SingularTwoCell M)
    {V : Set M} (hVopen : IsOpen V)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hec : ec ∈ (plGroupoid 3).maximalAtlas M) (hVec : V ⊆ ec.source)
    (Rc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {Ω Nb : Set (EuclideanSpace ℝ (Fin 2))}
    (hRfin : Rc.faces.Finite) (hRman : IsCombinatorialManifoldWithBoundary 2 Rc)
    (hAR : Ac.faces ⊆ Rc.faces) (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hΩ : IsOpen Ω) (hΩR : D.domain ∩ Ω ⊆ Rc.space) (hNb : IsOpen Nb)
    (hNbfr : Rc.space \ Ω ⊆ Nb) (hNbA : Rc.space ∩ Nb ⊆ Ac.space)
    (Rs : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hsub : IsSubdivision Rs Rc) (hRsfin : Rs.faces.Finite)
    (hfrozen : EqOn (simplicialMap Rs φ) (fun x => ec (D x)) Ac.space)
    (hpl : IsPiecewiseAffineOn (simplicialMap Rs φ) Rc.space)
    (hmaps : MapsTo (simplicialMap Rs φ) Rc.space (⇑ec '' V)) :
    ∃ D' : SingularTwoCell M, D'.domain = D.domain ∧
      EqOn (⇑D') (fun x => ec.symm (simplicialMap Rs φ x)) Rc.space ∧
      EqOn (⇑D') (⇑D) Rc.spaceᶜ := by
  sorry

def chartBlock (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ) : Set M :=
  ec.source ∩ ⇑ec ⁻¹' (⇑A ⁻¹' blockBox r tlo)

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem chartBlock_mono_of_half (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) {r tlo : ℝ} (hr : 0 ≤ r) (ht : tlo ≤ 0) :
    chartBlock ec A (r / 2) (tlo / 2) ⊆ chartBlock ec A r tlo := by
  intro x hx
  obtain ⟨hxs, hxb⟩ := hx
  refine ⟨hxs, ?_⟩
  simp only [mem_preimage, blockBox, mem_ofPred_eq, mem_Icc] at hxb ⊢
  exact ⟨hxb.1.trans (by linarith), hxb.2.1.trans (by linarith),
    by linarith [hxb.2.2.1], by linarith [hxb.2.2.2]⟩

def innerChartBlock (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ) : Set M :=
  chartBlock ec A (r / 2) (tlo / 2)

noncomputable def blockSheetProjA (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (f : EuclideanSpace ℝ (Fin 2) → M) :
    EuclideanSpace ℝ (Fin 2) → ℝ × ℝ :=
  fun x => ((A (ec (f x))).2.1, (A (ec (f x))).2.2)

noncomputable def blockSheetProjB (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (f : EuclideanSpace ℝ (Fin 2) → M) :
    EuclideanSpace ℝ (Fin 2) → ℝ × ℝ :=
  fun x => ((A (ec (f x))).1, (A (ec (f x))).2.2)

def FreeSourceGerm (R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → M) (S : Set (EuclideanSpace ℝ (Fin 2))) (y : M) : Prop :=
  ∀ x ∈ S ∩ g ⁻¹' {y}, R.space ∈ 𝓝[S] x ∧ ∀ σ ∈ R.faces,
    x ∈ convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))) → ∀ v ∈ σ, v ∉ Ac.space

def IsFreeDoubleGerm (R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → M) (S : Set (EuclideanSpace ℝ (Fin 2))) (BdM : Set M)
    (y : M) : Prop :=
  y ∉ BdM ∧ FreeSourceGerm R Ac g S y

def IsFreeBoundaryDoubleGerm (R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → M) (S : Set (EuclideanSpace ℝ (Fin 2))) (BdM : Set M)
    (y : M) : Prop :=
  y ∈ BdM ∧ FreeSourceGerm R Ac g S y

def IsFreeInteriorDoubleGerm (R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → M) (S : Set (EuclideanSpace ℝ (Fin 2))) (BdM : Set M)
    (y : M) : Prop :=
  IsFreeDoubleGerm R Ac g S BdM y ∧
    ∀ x ∈ S ∩ g ⁻¹' {y}, ∃ σ ∈ R.faces, σ.card = 3 ∧
      x ∈ interior (convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))))

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem mem_space_of_freeSourceGerm
    {R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))} {y : M}
    (h : FreeSourceGerm R Ac g S y) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ S ∩ g ⁻¹' {y}) : x ∈ R.space :=
  mem_of_mem_nhdsWithin hx.1 (h x hx).1

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem freeSourceGerm_of_frozenSpace_eq_empty
    {R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))} {y : M}
    (hAc : Ac.space = ∅) (hnhds : ∀ x ∈ S ∩ g ⁻¹' {y}, R.space ∈ 𝓝[S] x) :
    FreeSourceGerm R Ac g S y := by
  refine fun x hx => ⟨hnhds x hx, fun _ _ _ v _ => ?_⟩
  rw [hAc]
  exact notMem_empty v

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isFreeDoubleGerm_of_frozenSpace_eq_empty
    {R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))} {BdM : Set M}
    {y : M} (hAc : Ac.space = ∅) (hy : y ∉ BdM)
    (hnhds : ∀ x ∈ S ∩ g ⁻¹' {y}, R.space ∈ 𝓝[S] x) :
    IsFreeDoubleGerm R Ac g S BdM y :=
  ⟨hy, freeSourceGerm_of_frozenSpace_eq_empty hAc hnhds⟩

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isFreeBoundaryDoubleGerm_of_frozenSpace_eq_empty
    {R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))} {BdM : Set M}
    {y : M} (hAc : Ac.space = ∅) (hy : y ∈ BdM)
    (hnhds : ∀ x ∈ S ∩ g ⁻¹' {y}, R.space ∈ 𝓝[S] x) :
    IsFreeBoundaryDoubleGerm R Ac g S BdM y :=
  ⟨hy, freeSourceGerm_of_frozenSpace_eq_empty hAc hnhds⟩

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isFreeInteriorDoubleGerm_of_frozenSpace_eq_empty
    {R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))} {BdM : Set M}
    {y : M} (hAc : Ac.space = ∅) (hy : y ∉ BdM)
    (hnhds : ∀ x ∈ S ∩ g ⁻¹' {y}, R.space ∈ 𝓝[S] x)
    (hint : ∀ x ∈ S ∩ g ⁻¹' {y}, ∃ σ ∈ R.faces, σ.card = 3 ∧
      x ∈ interior (convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))))) :
    IsFreeInteriorDoubleGerm R Ac g S BdM y :=
  ⟨isFreeDoubleGerm_of_frozenSpace_eq_empty hAc hy hnhds, hint⟩

def IsStableCrossingBlock (f : EuclideanSpace ℝ (Fin 2) → M)
    (S : Set (EuclideanSpace ℝ (Fin 2)))
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (BdM : Set M)
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ)
    (SA SB : Set (EuclideanSpace ℝ (Fin 2))) (a b : ℝ × ℝ → ℝ) (La Lb η : ℝ) : Prop :=
  0 < r ∧ 0 < η ∧ 0 ≤ La ∧ 0 ≤ Lb ∧ La * Lb ≤ 1 - η ∧
    IsCompact (closure (chartBlock ec A r tlo)) ∧
    closure (chartBlock ec A r tlo) ⊆ ec.source ∧
    ((tlo = -r ∧ Disjoint (chartBlock ec A r tlo) BdM) ∨
        (tlo = 0 ∧ (∀ z, (A z).2.2 = ℓ z) ∧
          ∀ x ∈ SA ∪ SB, (x ∈ frontier S ↔ (A (ec (f x))).2.2 = 0))) ∧
    S ∩ f ⁻¹' chartBlock ec A r tlo = SA ∪ SB ∧ Disjoint SA SB ∧
    (∀ x ∈ SA, (A (ec (f x))).1 = a ((A (ec (f x))).2.1, (A (ec (f x))).2.2)) ∧
    (∀ x ∈ SB, (A (ec (f x))).2.1 = b ((A (ec (f x))).1, (A (ec (f x))).2.2)) ∧
    IsPLHomeomorphOn (blockSheetProjA ec A f) SA (blockSheetProjA ec A f '' SA) ∧
    IsPLHomeomorphOn (blockSheetProjB ec A f) SB (blockSheetProjB ec A f '' SB) ∧
    (∀ x ∈ SA, f x ∈ innerChartBlock ec A r tlo → SA ∈ 𝓝[S] x ∧
      blockSheetProjA ec A f '' SA ∈ 𝓝[blockHalfPlane tlo] (blockSheetProjA ec A f x)) ∧
    (∀ x ∈ SB, f x ∈ innerChartBlock ec A r tlo → SB ∈ 𝓝[S] x ∧
      blockSheetProjB ec A f '' SB ∈ 𝓝[blockHalfPlane tlo] (blockSheetProjB ec A f x)) ∧
    (∀ v v' t : ℝ, |a (v, t) - a (v', t)| ≤ La * |v - v'|) ∧
    (∀ u u' t : ℝ, |b (u, t) - b (u', t)| ≤ Lb * |u - u'|) ∧
    IsPiecewiseAffineOn a univ ∧ IsPiecewiseAffineOn b univ

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem IsStableCrossingBlock.margin_pos {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η) : 0 < η :=
  h.2.1

def HasStableCrossingBlocks (f : EuclideanSpace ℝ (Fin 2) → M)
    (S : Set (EuclideanSpace ℝ (Fin 2)))
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (BdM Q : Set M) (η : ℝ) : Prop :=
  0 < η ∧ ∃ (m : ℕ) (A : Fin m → (EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ))
      (r tlo : Fin m → ℝ) (SA SB : Fin m → Set (EuclideanSpace ℝ (Fin 2)))
      (a b : Fin m → ℝ × ℝ → ℝ) (La Lb : Fin m → ℝ),
      doublePointSet f S ∩ Q ⊆ ⋃ i, innerChartBlock ec (A i) (r i) (tlo i) ∧
        ∀ i, IsStableCrossingBlock f S ec ℓ BdM (A i) (r i) (tlo i) (SA i) (SB i) (a i) (b i)
          (La i) (Lb i) η

def HasStableCrossingBlocksIn (f : EuclideanSpace ℝ (Fin 2) → M)
    (S : Set (EuclideanSpace ℝ (Fin 2)))
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (BdM Q N : Set M) (η : ℝ) : Prop :=
  0 < η ∧ ∃ (m : ℕ) (A : Fin m → (EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ))
      (r tlo : Fin m → ℝ) (SA SB : Fin m → Set (EuclideanSpace ℝ (Fin 2)))
      (a b : Fin m → ℝ × ℝ → ℝ) (La Lb : Fin m → ℝ),
      doublePointSet f S ∩ Q ⊆ ⋃ i, innerChartBlock ec (A i) (r i) (tlo i) ∧
        (∀ i, chartBlock ec (A i) (r i) (tlo i) ⊆ N) ∧
        ∀ i, IsStableCrossingBlock f S ec ℓ BdM (A i) (r i) (tlo i) (SA i) (SB i) (a i) (b i)
          (La i) (Lb i) η

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem HasStableCrossingBlocksIn.toHasStableCrossingBlocks
    {f : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM Q N : Set M} {η : ℝ}
    (h : HasStableCrossingBlocksIn f S ec ℓ BdM Q N η) :
    HasStableCrossingBlocks f S ec ℓ BdM Q η := by
  obtain ⟨hη, m, A, r, tlo, SA, SB, a, b, La, Lb, hcov, -, hblk⟩ := h
  exact ⟨hη, m, A, r, tlo, SA, SB, a, b, La, Lb, hcov, hblk⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem hasStableCrossingBlocksIn_of_isStableCrossingBlock
    {f : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM Q N : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hcov : doublePointSet f S ∩ Q ⊆ innerChartBlock ec A r tlo)
    (hN : chartBlock ec A r tlo ⊆ N) :
    HasStableCrossingBlocksIn f S ec ℓ BdM Q N η := by
  refine ⟨h.margin_pos, 1, fun _ => A, fun _ => r, fun _ => tlo, fun _ => SA, fun _ => SB,
    fun _ => a, fun _ => b, fun _ => La, fun _ => Lb, ?_, fun _ => hN, fun _ => h⟩
  exact hcov.trans (subset_iUnion (fun _ : Fin 1 => innerChartBlock ec A r tlo) 0)

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem HasStableCrossingBlocks.mono {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM Q Q' : Set M} {η : ℝ}
    (h : HasStableCrossingBlocks f S ec ℓ BdM Q η) (hQ : Q' ⊆ Q) :
    HasStableCrossingBlocks f S ec ℓ BdM Q' η := by
  obtain ⟨hη, m, A, r, tlo, SA, SB, a, b, La, Lb, hcov, hblk⟩ := h
  exact ⟨hη, m, A, r, tlo, SA, SB, a, b, La, Lb,
    (inter_subset_inter Subset.rfl hQ).trans hcov, hblk⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem IsStableCrossingBlock.mono_margin {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η η' : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hη' : 0 < η') (hle : η' ≤ η) :
    IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η' :=
  ⟨h.1, hη', h.2.2.1, h.2.2.2.1, h.2.2.2.2.1.trans (by linarith), h.2.2.2.2.2⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem HasStableCrossingBlocks.mono_doublePointSet {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM Q Q' : Set M} {η : ℝ}
    (h : HasStableCrossingBlocks f S ec ℓ BdM Q η)
    (hQ : doublePointSet f S ∩ Q' ⊆ doublePointSet f S ∩ Q) :
    HasStableCrossingBlocks f S ec ℓ BdM Q' η := by
  obtain ⟨hη, m, A, r, tlo, SA, SB, a, b, La, Lb, hcov, hblk⟩ := h
  exact ⟨hη, m, A, r, tlo, SA, SB, a, b, La, Lb, hQ.trans hcov, hblk⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem HasStableCrossingBlocks.union {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM Q₁ Q₂ : Set M} {η₁ η₂ : ℝ}
    (h₁ : HasStableCrossingBlocks f S ec ℓ BdM Q₁ η₁)
    (h₂ : HasStableCrossingBlocks f S ec ℓ BdM Q₂ η₂) :
    HasStableCrossingBlocks f S ec ℓ BdM (Q₁ ∪ Q₂) (min η₁ η₂) := by
  obtain ⟨hη₁, m₁, A₁, r₁, t₁, SA₁, SB₁, a₁, b₁, La₁, Lb₁, hcov₁, hblk₁⟩ := h₁
  obtain ⟨hη₂, m₂, A₂, r₂, t₂, SA₂, SB₂, a₂, b₂, La₂, Lb₂, hcov₂, hblk₂⟩ := h₂
  refine ⟨lt_min hη₁ hη₂, m₁ + m₂, Fin.addCases A₁ A₂, Fin.addCases r₁ r₂,
    Fin.addCases t₁ t₂, Fin.addCases SA₁ SA₂, Fin.addCases SB₁ SB₂, Fin.addCases a₁ a₂,
    Fin.addCases b₁ b₂, Fin.addCases La₁ La₂, Fin.addCases Lb₁ Lb₂, ?_, ?_⟩
  · rintro y ⟨hy, hQ | hQ⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov₁ ⟨hy, hQ⟩)
      refine mem_iUnion.2 ⟨Fin.castAdd m₂ i, ?_⟩
      simpa only [Fin.addCases_left] using hi
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov₂ ⟨hy, hQ⟩)
      refine mem_iUnion.2 ⟨Fin.natAdd m₁ i, ?_⟩
      simpa only [Fin.addCases_right] using hi
  · refine Fin.addCases (fun i => ?_) fun i => ?_
    · simpa only [Fin.addCases_left] using
        (hblk₁ i).mono_margin (lt_min hη₁ hη₂) (min_le_left _ _)
    · simpa only [Fin.addCases_right] using
        (hblk₂ i).mono_margin (lt_min hη₁ hη₂) (min_le_right _ _)

theorem hasStableCrossingBlocksIn_of_isCompact_subset [T2Space M]
    {f : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM C Q Q' N : Set M} {η κ : ℝ}
    (h : HasStableCrossingBlocks f S ec ℓ BdM Q η)
    (hScpt : IsCompact S) (hcont : ContinuousOn f S) (hmapC : MapsTo f S C)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    (hκ : 0 < κ) (hinj : UniformInjectivityScale S f κ)
    (hQ' : IsCompact Q') (hsub : Q' ⊆ Q) (hN : IsOpen N) (hQN : Q' ⊆ N) :
    HasStableCrossingBlocksIn f S ec ℓ BdM Q' N η := by
  sorry

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem hasStableCrossingBlocks_of_doublePointSet_inter_eq_empty
    {f : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM Q : Set M} {η : ℝ}
    (hQ : doublePointSet f S ∩ Q = ∅) (hη : 0 < η) :
    HasStableCrossingBlocks f S ec ℓ BdM Q η := by
  refine ⟨hη, 0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0,
    Fin.elim0, Fin.elim0, ?_, fun i => i.elim0⟩
  rw [hQ]
  exact empty_subset _

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem sheets_nonempty_of_isStableCrossingBlock {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η) {y : M}
    (hy : y ∈ doublePointSet f S) (hyB : y ∈ chartBlock ec A r tlo) :
    (SA ∩ f ⁻¹' {y}).Nonempty ∧ (SB ∩ f ⁻¹' {y}).Nonempty := by
  obtain ⟨-, -, -, -, -, -, -, -, hpre, -, -, -, hplA, hplB, -, -, -, -, -, -⟩ := h
  obtain ⟨x, hxS, z, hzS, hxz, hxy, hzy⟩ := hy
  have hfeq : f x = f z := by rw [hxy, hzy]
  have hxmem : x ∈ SA ∪ SB := by
    rw [← hpre]
    exact ⟨hxS, by simp only [mem_preimage, hxy]; exact hyB⟩
  have hzmem : z ∈ SA ∪ SB := by
    rw [← hpre]
    exact ⟨hzS, by simp only [mem_preimage, hzy]; exact hyB⟩
  have hnotA : ¬(x ∈ SA ∧ z ∈ SA) := by
    rintro ⟨hxA, hzA⟩
    exact hxz (hplA.bijOn.injOn hxA hzA (by simp only [blockSheetProjA, hfeq]))
  have hnotB : ¬(x ∈ SB ∧ z ∈ SB) := by
    rintro ⟨hxB, hzB⟩
    exact hxz (hplB.bijOn.injOn hxB hzB (by simp only [blockSheetProjB, hfeq]))
  rcases hxmem with hxA | hxB
  · rcases hzmem with hzA | hzB
    · exact absurd ⟨hxA, hzA⟩ hnotA
    · exact ⟨⟨x, hxA, hxy⟩, ⟨z, hzB, hzy⟩⟩
  · rcases hzmem with hzA | hzB
    · exact ⟨⟨z, hzA, hzy⟩, ⟨x, hxB, hxy⟩⟩
    · exact absurd ⟨hxB, hzB⟩ hnotB

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem exists_sheets_of_hasStableCrossingBlocks {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM Q : Set M} {η : ℝ}
    (h : HasStableCrossingBlocks f S ec ℓ BdM Q η) {y : M}
    (hy : y ∈ doublePointSet f S ∩ Q) :
    ∃ SA' SB' : Set (EuclideanSpace ℝ (Fin 2)),
      Disjoint SA' SB' ∧ (SA' ∩ f ⁻¹' {y}).Nonempty ∧ (SB' ∩ f ⁻¹' {y}).Nonempty := by
  obtain ⟨-, m, A, r, tlo, SA, SB, a, b, La, Lb, hcov, hblk⟩ := h
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hy)
  obtain ⟨hr0, -, -, -, -, -, -, hside, -, hdisj, -, -, -, -, -, -, -, -, -, -⟩ := hblk i
  have ht : tlo i ≤ 0 := by
    rcases hside with ⟨h1, -⟩ | ⟨h1, -, -⟩
    · rw [h1]; linarith
    · exact le_of_eq h1
  obtain ⟨hA, hB⟩ := sheets_nonempty_of_isStableCrossingBlock (hblk i) hy.1
    (chartBlock_mono_of_half ec (A i) (le_of_lt hr0) ht hi)
  exact ⟨SA i, SB i, hdisj, hA, hB⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isStableCrossingBlock_of_flatSheets {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} (hr : 0 < r)
    (hcpt : IsCompact (closure (chartBlock ec A r (-r))))
    (hsrc : closure (chartBlock ec A r (-r)) ⊆ ec.source)
    (hBd : Disjoint (chartBlock ec A r (-r)) BdM)
    (hpre : S ∩ f ⁻¹' chartBlock ec A r (-r) = SA ∪ SB) (hdisj : Disjoint SA SB)
    (hA : ∀ x ∈ SA, (A (ec (f x))).1 = 0) (hB : ∀ x ∈ SB, (A (ec (f x))).2.1 = 0)
    (hplA : IsPLHomeomorphOn (blockSheetProjA ec A f) SA (blockSheetProjA ec A f '' SA))
    (hplB : IsPLHomeomorphOn (blockSheetProjB ec A f) SB (blockSheetProjB ec A f '' SB))
    (hnA : ∀ x ∈ SA, f x ∈ innerChartBlock ec A r (-r) → SA ∈ 𝓝[S] x ∧
      blockSheetProjA ec A f '' SA ∈ 𝓝[blockHalfPlane (-r)] (blockSheetProjA ec A f x))
    (hnB : ∀ x ∈ SB, f x ∈ innerChartBlock ec A r (-r) → SB ∈ 𝓝[S] x ∧
      blockSheetProjB ec A f '' SB ∈ 𝓝[blockHalfPlane (-r)] (blockSheetProjB ec A f x)) :
    IsStableCrossingBlock f S ec ℓ BdM A r (-r) SA SB (fun _ => 0) (fun _ => 0) 0 0 1 := by
  have hpa : IsPiecewiseAffineOn (fun _ : ℝ × ℝ => (0 : ℝ)) univ :=
    (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (ℝ × ℝ) (0 : ℝ)) isOpen_univ).congr
      fun _ _ => rfl
  refine ⟨hr, one_pos, le_rfl, le_rfl, by norm_num, hcpt, hsrc, Or.inl ⟨rfl, hBd⟩, hpre, hdisj,
    hA, hB, hplA, hplB, hnA, hnB, ?_, ?_, hpa, hpa⟩
  · intro v v' t
    simp
  · intro u u' t
    simp

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isStableCrossingBlock_of_flatSheets_boundary {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} (hr : 0 < r)
    (hcpt : IsCompact (closure (chartBlock ec A r 0)))
    (hsrc : closure (chartBlock ec A r 0) ⊆ ec.source)
    (hheight : ∀ z, (A z).2.2 = ℓ z)
    (hfront : ∀ x ∈ SA ∪ SB, (x ∈ frontier S ↔ (A (ec (f x))).2.2 = 0))
    (hpre : S ∩ f ⁻¹' chartBlock ec A r 0 = SA ∪ SB) (hdisj : Disjoint SA SB)
    (hA : ∀ x ∈ SA, (A (ec (f x))).1 = 0) (hB : ∀ x ∈ SB, (A (ec (f x))).2.1 = 0)
    (hplA : IsPLHomeomorphOn (blockSheetProjA ec A f) SA (blockSheetProjA ec A f '' SA))
    (hplB : IsPLHomeomorphOn (blockSheetProjB ec A f) SB (blockSheetProjB ec A f '' SB))
    (hnA : ∀ x ∈ SA, f x ∈ innerChartBlock ec A r 0 → SA ∈ 𝓝[S] x ∧
      blockSheetProjA ec A f '' SA ∈ 𝓝[blockHalfPlane 0] (blockSheetProjA ec A f x))
    (hnB : ∀ x ∈ SB, f x ∈ innerChartBlock ec A r 0 → SB ∈ 𝓝[S] x ∧
      blockSheetProjB ec A f '' SB ∈ 𝓝[blockHalfPlane 0] (blockSheetProjB ec A f x)) :
    IsStableCrossingBlock f S ec ℓ BdM A r 0 SA SB (fun _ => 0) (fun _ => 0) 0 0 1 := by
  have hpa : IsPiecewiseAffineOn (fun _ : ℝ × ℝ => (0 : ℝ)) univ :=
    (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (ℝ × ℝ) (0 : ℝ)) isOpen_univ).congr
      fun _ _ => rfl
  refine ⟨hr, one_pos, le_rfl, le_rfl, by norm_num, hcpt, hsrc,
    Or.inr ⟨rfl, hheight, hfront⟩, hpre, hdisj, hA, hB, hplA, hplB, hnA, hnB, ?_, ?_, hpa, hpa⟩
  · intro v v' t
    simp
  · intro u u' t
    simp

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isStableCrossingBlock_of_eqOn_sheets {f g : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hgeq : EqOn g f (SA ∪ SB))
    (hpre' : S ∩ g ⁻¹' chartBlock ec A r tlo = SA ∪ SB) :
    IsStableCrossingBlock g S ec ℓ BdM A r tlo SA SB a b La Lb η := by
  obtain ⟨hr, hη, hLa, hLb, hmar, hcpt, hsrc, hside, -, hdisj, hgA, hgB, hplA, hplB,
    hnA, hnB, hLipa, hLipb, hpa, hpb⟩ := h
  have hprojA : EqOn (blockSheetProjA ec A g) (blockSheetProjA ec A f) SA := by
    intro x hx
    simp only [blockSheetProjA, hgeq (Or.inl hx)]
  have hprojB : EqOn (blockSheetProjB ec A g) (blockSheetProjB ec A f) SB := by
    intro x hx
    simp only [blockSheetProjB, hgeq (Or.inr hx)]
  have himA : blockSheetProjA ec A g '' SA = blockSheetProjA ec A f '' SA := image_congr hprojA
  have himB : blockSheetProjB ec A g '' SB = blockSheetProjB ec A f '' SB := image_congr hprojB
  refine ⟨hr, hη, hLa, hLb, hmar, hcpt, hsrc, ?_, hpre', hdisj, ?_, ?_, ?_, ?_, ?_, ?_,
    hLipa, hLipb, hpa, hpb⟩
  · rcases hside with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, h2⟩
    · refine Or.inr ⟨h1, h2, fun x hx => ?_⟩
      rw [hgeq hx]
      exact h3 x hx
  · intro x hx
    rw [hgeq (Or.inl hx)]
    exact hgA x hx
  · intro x hx
    rw [hgeq (Or.inr hx)]
    exact hgB x hx
  · rw [himA]
    exact hplA.congr hprojA
  · rw [himB]
    exact hplB.congr hprojB
  · intro x hx hxb
    rw [hgeq (Or.inl hx)] at hxb
    rw [himA, hprojA hx]
    exact hnA x hx hxb
  · intro x hx hxb
    rw [hgeq (Or.inr hx)] at hxb
    rw [himB, hprojB hx]
    exact hnB x hx hxb

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem preimage_chartBlock_eq_of_isStableCrossingBlock {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η) :
    S ∩ f ⁻¹' chartBlock ec A r tlo = SA ∪ SB := by
  obtain ⟨-, -, -, -, -, -, -, -, hpre, -, -, -, -, -, -, -, -, -, -, -⟩ := h
  exact hpre

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isStableCrossingBlock_of_preimage_singleton_eq {f g : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM N : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hN : chartBlock ec A r tlo ⊆ N)
    (hfib : ∀ z ∈ N, S ∩ g ⁻¹' {z} = S ∩ f ⁻¹' {z}) :
    IsStableCrossingBlock g S ec ℓ BdM A r tlo SA SB a b La Lb η := by
  have hpre := preimage_chartBlock_eq_of_isStableCrossingBlock h
  have hgeq : EqOn g f (SA ∪ SB) := by
    intro x hx
    have hxpre : x ∈ S ∩ f ⁻¹' chartBlock ec A r tlo := by rw [hpre]; exact hx
    have hmem : x ∈ S ∩ g ⁻¹' {f x} := by
      rw [hfib (f x) (hN hxpre.2)]
      exact ⟨hxpre.1, rfl⟩
    exact hmem.2
  have hpre' : S ∩ g ⁻¹' chartBlock ec A r tlo = SA ∪ SB := by
    refine Subset.antisymm (fun x hx => ?_) fun x hx => ?_
    · have hmem : x ∈ S ∩ f ⁻¹' {g x} := by
        rw [← hfib (g x) (hN hx.2)]
        exact ⟨hx.1, rfl⟩
      have hfx : f x = g x := hmem.2
      rw [← hpre]
      exact ⟨hx.1, by simp only [mem_preimage, hfx]; exact hx.2⟩
    · have hxpre : x ∈ S ∩ f ⁻¹' chartBlock ec A r tlo := by rw [hpre]; exact hx
      exact ⟨hxpre.1, by simp only [mem_preimage, hgeq hx]; exact hxpre.2⟩
  exact isStableCrossingBlock_of_eqOn_sheets h hgeq hpre'

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem hasStableCrossingBlocksIn_of_preimage_singleton_eq
    {f g : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM Q N : Set M} {η : ℝ}
    (h : HasStableCrossingBlocksIn f S ec ℓ BdM Q N η) (hQN : Q ⊆ N)
    (hfib : ∀ z ∈ N, S ∩ g ⁻¹' {z} = S ∩ f ⁻¹' {z}) :
    HasStableCrossingBlocksIn g S ec ℓ BdM Q N η := by
  obtain ⟨hη, m, A, r, tlo, SA, SB, a, b, La, Lb, hcov, hin, hblk⟩ := h
  refine ⟨hη, m, A, r, tlo, SA, SB, a, b, La, Lb, ?_, hin,
    fun i => isStableCrossingBlock_of_preimage_singleton_eq (hblk i) (hin i) hfib⟩
  rintro y ⟨⟨x, hxS, z, hzS, hxz, hxy, hzy⟩, hyQ⟩
  have hfibQ : S ∩ g ⁻¹' {y} = S ∩ f ⁻¹' {y} := hfib y (hQN hyQ)
  have hx : x ∈ S ∩ f ⁻¹' {y} := by rw [← hfibQ]; exact ⟨hxS, hxy⟩
  have hz : z ∈ S ∩ f ⁻¹' {y} := by rw [← hfibQ]; exact ⟨hzS, hzy⟩
  exact hcov ⟨⟨x, hx.1, z, hz.1, hxz, hx.2, hz.2⟩, hyQ⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isStableCrossingBlock_of_eqOn_compl {f g : EuclideanSpace ℝ (Fin 2) → M}
    {S Rgn : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hoff : EqOn g f Rgnᶜ) (hfree : Disjoint Rgn (S ∩ f ⁻¹' chartBlock ec A r tlo))
    (hfree' : Disjoint Rgn (S ∩ g ⁻¹' chartBlock ec A r tlo)) :
    IsStableCrossingBlock g S ec ℓ BdM A r tlo SA SB a b La Lb η := by
  have hpre := preimage_chartBlock_eq_of_isStableCrossingBlock h
  have hgeq : EqOn g f (SA ∪ SB) := by
    intro x hx
    have hxpre : x ∈ S ∩ f ⁻¹' chartBlock ec A r tlo := by rw [hpre]; exact hx
    exact hoff fun hxR => (disjoint_left.mp hfree hxR) hxpre
  have hpre' : S ∩ g ⁻¹' chartBlock ec A r tlo = SA ∪ SB := by
    refine Subset.antisymm (fun x hx => ?_) fun x hx => ?_
    · have hxR : x ∉ Rgn := fun hxR => (disjoint_left.mp hfree' hxR) hx
      rw [← hpre]
      exact ⟨hx.1, by simp only [mem_preimage, ← hoff hxR]; exact hx.2⟩
    · have hxpre : x ∈ S ∩ f ⁻¹' chartBlock ec A r tlo := by rw [hpre]; exact hx
      exact ⟨hxpre.1, by simp only [mem_preimage, hgeq hx]; exact hxpre.2⟩
  exact isStableCrossingBlock_of_eqOn_sheets h hgeq hpre'

theorem exists_transitionSubdivisionOnOverlap
    (ec ec' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hec : ec ∈ (plGroupoid 3).maximalAtlas M) (hec' : ec' ∈ (plGroupoid 3).maximalAtlas M)
    (N : Set M) (hN : IsCompact N) (hNec : N ⊆ ec.source) (hNec' : N ⊆ ec'.source) :
    ∃ Q : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      Q.faces.Finite ∧ ⇑ec '' N ⊆ interior Q.space ∧
        Q.space ⊆ ⇑ec '' (ec.source ∩ ec'.source) ∧
        ∀ s ∈ Q.faces, ∃ A : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
          EqOn (fun z => ec' (ec.symm z)) A
            (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 3)))) := by
  sorry

theorem hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock (D : SingularTwoCell M)
    {BdM : Set M} (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hec : ec ∈ (plGroupoid 3).maximalAtlas M)
    (hℓ : ℓ ≠ 0) (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock (⇑D) D.domain ec ℓ BdM A r tlo SA SB a b La Lb η) {y : M}
    (hy : y ∈ doublePointSet (⇑D) D.domain)
    (hyB : y ∈ innerChartBlock ec A r tlo) :
    ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
      HasPLNormalDoubleCrossingAt (⇑e ∘ ⇑D) (D.domain ∩ ⇑D ⁻¹' e.source)
        (⇑e '' (e.source ∩ BdM)) (e y) := by
  sorry

def AdmissibleVertexMap (D : SingularTwoCell M)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)
    (Lc Ac R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (τ : ℝ) : Prop :=
  (Bv : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices ∧
    (∀ v ∈ R.vertices, v ∈ Bv ↔ v ∈ Lc.space) ∧
    (∀ v ∈ R.vertices, dist (φ v) (ec (D v)) < τ) ∧
    (∀ v ∈ R.vertices, v ∈ Ac.space → φ v = ec (D v)) ∧
    (∀ v ∈ R.vertices, v ∈ Bv → ℓ (φ v) = 0) ∧
    ∀ v ∈ R.vertices, v ∉ Bv → 0 < ℓ (φ v)

open Classical in
theorem exists_admissibleVertexMap_of_adaptedChart (D : SingularTwoCell M) {BdM C V : Set M}
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hVec : V ⊆ ec.source)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    (Rc Lc Ac R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (hRsfin : R.faces.Finite) (hsub : IsSubdivision R Rc)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain) {τ : ℝ} (hτ : 0 < τ) :
    ∃ Bv : Finset (EuclideanSpace ℝ (Fin 2)),
      AdmissibleVertexMap D ec ℓ Lc Ac R Bv (fun v => ec (D v)) τ := by
  classical
  have hvfin : R.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn hRsfin
  have hvR : ∀ v ∈ R.vertices, v ∈ Rc.space := by
    intro v hv
    rw [← hsub.space_eq]
    exact Geometry.SimplicialComplex.vertices_subset_space hv
  have hsrc : ∀ v ∈ R.vertices, D v ∈ ec.source := fun v hv => hVec (hRV (hvR v hv))
  have hmemBv : ∀ v, v ∈ hvfin.toFinset.filter (fun w => w ∈ Lc.space) ↔
      v ∈ R.vertices ∧ v ∈ Lc.space := by
    intro v
    simp [Finset.mem_filter, hvfin.mem_toFinset]
  refine ⟨hvfin.toFinset.filter fun w => w ∈ Lc.space, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact ((hmemBv v).1 (Finset.mem_coe.mp hv)).1
  · exact fun v hv => ⟨fun h => ((hmemBv v).1 h).2, fun h => (hmemBv v).2 ⟨hv, h⟩⟩
  · intro v _
    simpa using hτ
  · exact fun _ _ _ => rfl
  · intro v hv hvB
    have hvL : v ∈ Lc.space := ((hmemBv v).1 hvB).2
    rw [hLspace] at hvL
    have hmem : v ∈ D.domain ∩ ⇑D ⁻¹' BdM := by
      rw [hproper]
      exact hvL.2
    exact (hBdchart (D v) (hsrc v hv)).1 hmem.2
  · intro v hv hvB
    have hvRc : v ∈ Rc.space := hvR v hv
    have hvL : v ∉ Lc.space := fun h => hvB ((hmemBv v).2 ⟨hv, h⟩)
    have hne : ℓ (ec (D v)) ≠ 0 := by
      intro h
      have hBd : D v ∈ BdM := (hBdchart (D v) (hsrc v hv)).2 h
      have hfr : v ∈ frontier D.domain := by
        rw [← hproper]
        exact ⟨hRdom hvRc, hBd⟩
      exact hvL (by rw [hLspace]; exact ⟨hvRc, hfr⟩)
    exact lt_of_le_of_ne ((hCchart (D v) (hsrc v hv)).1 (hmapC (hRdom hvRc))) (Ne.symm hne)

end Ambient

section MetricAmbient

variable {M : Type u} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

open Classical in
noncomputable def regionGluedMap (D : SingularTwoCell M)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (Rs : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (Rc : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) :
    EuclideanSpace ℝ (Fin 2) → M :=
  fun x => if x ∈ Rc.space then ec.symm (simplicialMap Rs φ x) else D x

theorem eq_regionGluedMap_of_eqOn {D D' : SingularTwoCell M}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {Rs Rc : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    (hglue : EqOn (⇑D') (fun x => ec.symm (simplicialMap Rs φ x)) Rc.space)
    (hglueoff : EqOn (⇑D') (⇑D) Rc.spaceᶜ) :
    ⇑D' = regionGluedMap D ec Rs φ Rc := by
  classical
  funext x
  by_cases hx : x ∈ Rc.space
  · simp only [regionGluedMap, if_pos hx]
    exact hglue hx
  · simp only [regionGluedMap, if_neg hx]
    exact hglueoff hx

theorem exists_normalizationPreparation_on_prescribedRegion [CompactSpace M]
    (D : SingularTwoCell M) {BdM B W V : Set M}
    (hloc : ∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, InjOn (⇑D) U)
    (hfiber : ∀ y, (D.domain ∩ ⇑D ⁻¹' {y}).encard ≤ 2)
    (hbuffer : ∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z)
    (hVopen : IsOpen V) (hWV : closure W ⊆ V)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))) (hVec : V ⊆ ec.source)
    (Rc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (hRfin : Rc.faces.Finite) (hAR : Ac.faces ⊆ Rc.faces)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hAfree : Disjoint Ac.space (⇑D ⁻¹' closure W)) :
    ∃ (T : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) (κ δ ε : ℝ),
      0 < κ ∧ 0 < δ ∧ 0 < ε ∧ T.faces.Finite ∧ T.space = D.domain ∧ StarInj T (⇑D) ∧
        (∀ g : EuclideanSpace ℝ (Fin 2) → M, (∀ x ∈ D.domain, dist (g x) (D x) < δ) →
          StarInj T g → UniformInjectivityScale D.domain g κ ∧
            ∀ y, (D.domain ∩ g ⁻¹' {y}).encard ≤ 2) ∧
        (∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
          dist z (ec (D x)) < ε → z ∈ ⇑ec '' V ∧ dist (ec.symm z) (D x) < δ) ∧
        (∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
          dist z (ec (D x)) < ε → ec.symm z ∈ closure W → x ∈ Rc.space \ Ac.space) ∧
        ∀ x ∈ Rc.space ∩ frontier D.domain, ∀ z : EuclideanSpace ℝ (Fin 3),
          dist z (ec (D x)) < ε → ec.symm z ∈ BdM → B ∈ 𝓝[BdM] (ec.symm z) := by
  sorry

open Classical in
theorem exists_protectedSubdivision_in_adaptedChart [CompactSpace M]
    (D : SingularTwoCell M) {BdM C Z O W V : Set M} {η κ δ ε : ℝ}
    (hloc : ∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, InjOn (⇑D) U)
    (hfiber : ∀ y, (D.domain ∩ ⇑D ⁻¹' {y}).encard ≤ 2)
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C)
    (hnormal : ∀ y ∈ doublePointSet (⇑D) D.domain ∩ O,
      ∃ e₀ ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e₀.source ∧
        HasPLNormalDoubleCrossingAt (e₀ ∘ ⇑D) (D.domain ∩ ⇑D ⁻¹' e₀.source)
          (e₀ '' (e₀.source ∩ BdM)) (e₀ y))
    (hZclosed : IsClosed Z) (hOopen : IsOpen O) (hZO : Z ⊆ O)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hec : ec ∈ (plGroupoid 3).maximalAtlas M)
    (hℓ : ℓ ≠ 0) (hVopen : IsOpen V) (hVec : closure V ⊆ ec.source)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    (Rc Lc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {Ω Nb : Set (EuclideanSpace ℝ (Fin 2))}
    (hRfin : Rc.faces.Finite) (hRman : IsCombinatorialManifoldWithBoundary 2 Rc)
    (hLR : Lc.faces ⊆ Rc.faces) (hAR : Ac.faces ⊆ Rc.faces)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    (hΩ : IsOpen Ω) (hΩR : D.domain ∩ Ω ⊆ Rc.space) (hNb : IsOpen Nb)
    (hNbfr : Rc.space \ Ω ⊆ Nb) (hNbA : Rc.space ∩ Nb ⊆ Ac.space)
    (hWV : closure W ⊆ V) (hAfree : Disjoint Ac.space (⇑D ⁻¹' closure W))
    (hstable : HasStableCrossingBlocks (⇑D) D.domain ec ℓ BdM
      (Z ∩ closure (V \ closure W)) η)
    (T : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) (hTfin : T.faces.Finite)
    (hTspace : T.space = D.domain) (hTstar : StarInj T (⇑D))
    (hκ : 0 < κ) (hδ : 0 < δ) (hε : 0 < ε)
    (hcert : ∀ g : EuclideanSpace ℝ (Fin 2) → M, (∀ x ∈ D.domain, dist (g x) (D x) < δ) →
      StarInj T g → UniformInjectivityScale D.domain g κ ∧
        ∀ y, (D.domain ∩ g ⁻¹' {y}).encard ≤ 2)
    (hconv : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ec (D x)) < ε → z ∈ ⇑ec '' V ∧ dist (ec.symm z) (D x) < δ) :
    ∃ (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) (τ : ℝ) (K : Set M),
      0 < τ ∧ IsSubdivision R Rc ∧ R.faces.Finite ∧
        (∀ s ∈ R.faces, ∃ A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
          EqOn (fun x => ec (D x)) A
            (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2))))) ∧
        IsCompact K ∧ K ⊆ V ∧ ⇑D '' Rc.space ⊆ interior K ∧
        ∀ (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
          (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)),
          AdmissibleVertexMap D ec ℓ Lc Ac R Bv φ τ →
          IsPiecewiseAffineOn (simplicialMap R φ) Rc.space ∧
            (∀ x ∈ Rc.space, dist (simplicialMap R φ x) (ec (D x)) < ε) ∧
            EqOn (simplicialMap R φ) (fun x => ec (D x)) Ac.space ∧
            (∀ x ∈ Rc.space, 0 ≤ ℓ (simplicialMap R φ x)) ∧
            (∀ x ∈ Rc.space, ℓ (simplicialMap R φ x) = 0 ↔ x ∈ Lc.space) ∧
            (∀ σ ∈ R.faces, (∃ v ∈ σ, v ∈ Ac.space) →
              Disjoint
                (simplicialMap R φ '' convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))))
                (⇑ec '' closure W)) ∧
            MapsTo (simplicialMap R φ) Rc.space (⇑ec '' V) ∧
            regionGluedMap D ec R φ Rc '' Rc.space ⊆ K ∧
            StarInj T (regionGluedMap D ec R φ Rc) ∧
            (∀ y ∈ doublePointSet (regionGluedMap D ec R φ Rc) D.domain ∩ Z ∩ K,
              (∃ σ ∈ R.faces, (∃ v ∈ σ, v ∈ Ac.space) ∧
                  (D.domain ∩ regionGluedMap D ec R φ Rc ⁻¹' {y} ∩
                    convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))).Nonempty) →
                ∃ e₁ ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e₁.source ∧
                  HasPLNormalDoubleCrossingAt (⇑e₁ ∘ regionGluedMap D ec R φ Rc)
                    (D.domain ∩ regionGluedMap D ec R φ Rc ⁻¹' e₁.source)
                    (⇑e₁ '' (e₁.source ∩ BdM)) (e₁ y)) ∧
            HasStableCrossingBlocks (regionGluedMap D ec R φ Rc) D.domain ec ℓ BdM
              (Z ∩ closure (V \ closure W)) (η / 2) := by
  sorry

open Classical in
theorem exists_genericVertexMap_in_adaptedChart (D : SingularTwoCell M) {BdM C V : Set M}
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hVec : V ⊆ ec.source)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    (Rc Lc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (hLR : Lc.faces ⊆ Rc.faces) (hAR : Ac.faces ⊆ Rc.faces)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (hsub : IsSubdivision R Rc) (hRsfin : R.faces.Finite)
    (ι : Type) [Finite ι] (ecw : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (Qw : ι → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) (Nw : ι → Set M)
    (hNcpt : ∀ i, IsCompact (Nw i)) (hNec : ∀ i, Nw i ⊆ ec.source)
    (hNecw : ∀ i, Nw i ⊆ (ecw i).source) (hQfin : ∀ i, (Qw i).faces.Finite)
    (hQcover : ∀ i, ⇑ec '' Nw i ⊆ interior (Qw i).space)
    (hQsrc : ∀ i, (Qw i).space ⊆ ⇑ec '' (ec.source ∩ (ecw i).source))
    (hQaff : ∀ i, ∀ s ∈ (Qw i).faces,
      ∃ A : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
        EqOn (fun z => ecw i (ec.symm z)) A
          (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 3)))))
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
      (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)),
      AdmissibleVertexMap D ec ℓ Lc Ac R Bv φ τ ∧
        (∀ s : Finset (EuclideanSpace ℝ (Fin 2)),
          (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices → s.card ≤ 4 →
            (s ∩ Bv).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 →
            AffineIndependent ℝ
              (fun v : (s.filter fun x => x ∈ Ac.space) => φ (v : EuclideanSpace ℝ (Fin 2))) →
            AffineIndependent ℝ (fun v : s => φ (v : EuclideanSpace ℝ (Fin 2)))) ∧
        (∀ i : ι, ∀ y ∈ doublePointSet (regionGluedMap D ec R φ Rc) D.domain ∩ Nw i,
          IsFreeBoundaryDoubleGerm R Ac (regionGluedMap D ec R φ Rc) D.domain BdM y →
            ∃ (O : Set (EuclideanSpace ℝ (Fin 3)))
              (A : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)),
              IsOpen O ∧ ec y ∈ O ∧
                EqOn (fun z => ecw i (ec.symm z)) A (O ∩ {z | 0 ≤ ℓ z})) ∧
        (∀ i : ι, ∀ y ∈ doublePointSet (regionGluedMap D ec R φ Rc) D.domain ∩ Nw i,
          IsFreeInteriorDoubleGerm R Ac (regionGluedMap D ec R φ Rc) D.domain BdM y →
            ec y ∉ complexSkeleton 1 (Qw i)) ∧
        (∀ i : ι, ∀ y ∈ doublePointSet (regionGluedMap D ec R φ Rc) D.domain ∩ Nw i,
          IsFreeInteriorDoubleGerm R Ac (regionGluedMap D ec R φ Rc) D.domain BdM y →
            ∀ F ∈ (Qw i).faces, F.card = 3 →
              ec y ∈ convexHull ℝ (F : Set (EuclideanSpace ℝ (Fin 3))) →
                ∃ w : EuclideanSpace ℝ (Fin 3), ‖w‖ = 1 ∧
                  w ∉ vectorSpan ℝ (F : Set (EuclideanSpace ℝ (Fin 3))) ∧ ∃ ρ > 0,
                    (⇑ec '' (doublePointSet (regionGluedMap D ec R φ Rc) D.domain ∩ ec.source) ∩
                      Metric.ball (ec y) ρ ⊆ {z | ∃ c : ℝ, z = ec y + c • w}) ∧
                      ∀ c : ℝ, |c| < ρ → ec y + c • w ∈
                        ⇑ec '' (doublePointSet (regionGluedMap D ec R φ Rc) D.domain ∩
                          ec.source)) ∧
        ∀ i : ι, ∀ y ∈ doublePointSet (regionGluedMap D ec R φ Rc) D.domain ∩ Nw i,
          IsFreeDoubleGerm R Ac (regionGluedMap D ec R φ Rc) D.domain BdM y →
            ∀ σ ∈ R.faces, σ.card ≤ 2 →
              ec y ∈ simplicialMap R φ '' convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))) →
                ec y ∉ complexSkeleton 2 (Qw i) := by
  sorry

theorem exists_globalInvariants_of_gluedCell (D D' : SingularTwoCell M)
    {BdM B C V : Set M} {ε δ κ : ℝ}
    {T : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C)
    (hbuffer : ∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z) (hκ : 0 < κ)
    (hcert : ∀ g : EuclideanSpace ℝ (Fin 2) → M, (∀ x ∈ D.domain, dist (g x) (D x) < δ) →
      StarInj T g → UniformInjectivityScale D.domain g κ ∧
        ∀ y, (D.domain ∩ g ⁻¹' {y}).encard ≤ 2)
    (hclose : ∀ x ∈ D.domain, dist (D' x) (D x) < δ) (hstar : StarInj T (⇑D'))
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hVopen : IsOpen V) (hVec : V ⊆ ec.source)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    (Rc Lc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {Ω Nb : Set (EuclideanSpace ℝ (Fin 2))}
    (hRfin : Rc.faces.Finite) (hRman : IsCombinatorialManifoldWithBoundary 2 Rc)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    (hΩ : IsOpen Ω) (hΩR : D.domain ∩ Ω ⊆ Rc.space) (hNb : IsOpen Nb)
    (hNbfr : Rc.space \ Ω ⊆ Nb) (hNbA : Rc.space ∩ Nb ⊆ Ac.space)
    (Rs : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hsub : IsSubdivision Rs Rc)
    (hsmall : ∀ x ∈ Rc.space, dist (simplicialMap Rs φ x) (ec (D x)) < ε)
    (hfrozen : EqOn (simplicialMap Rs φ) (fun x => ec (D x)) Ac.space)
    (hpnonneg : ∀ x ∈ Rc.space, 0 ≤ ℓ (simplicialMap Rs φ x))
    (hpzero : ∀ x ∈ Rc.space, ℓ (simplicialMap Rs φ x) = 0 ↔ x ∈ Lc.space)
    (hchartbuf : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ec (D x)) < ε → z ∈ ⇑ec '' V)
    (hbdbuf : ∀ x ∈ Rc.space ∩ frontier D.domain, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ec (D x)) < ε → ec.symm z ∈ BdM → B ∈ 𝓝[BdM] (ec.symm z))
    (hdom' : D'.domain = D.domain)
    (hglue : EqOn (⇑D') (fun x => ec.symm (simplicialMap Rs φ x)) Rc.space)
    (hglueoff : EqOn (⇑D') (⇑D) Rc.spaceᶜ) :
    MapsTo (⇑D') D'.domain C ∧ (∀ z ∉ V, (⇑D') ⁻¹' {z} = (⇑D) ⁻¹' {z}) ∧
      (∀ x ∈ D'.domain, ∃ U ∈ 𝓝[D'.domain] x, InjOn (⇑D') U) ∧
      (∀ y, (D'.domain ∩ ⇑D' ⁻¹' {y}).encard ≤ 2) ∧
      D'.domain ∩ ⇑D' ⁻¹' BdM = frontier D'.domain ∧
      ∃ H : ContinuousMap (unitInterval × frontier D.domain) M,
        (∀ x : frontier D.domain, H (0, x) = D x) ∧
        (∀ x : frontier D.domain, H (1, x) = D' x) ∧
        ∀ (t : unitInterval) (x : frontier D.domain),
          H (t, x) ∈ BdM ∧ B ∈ 𝓝[BdM] (H (t, x)) := by
  sorry

open Classical in
theorem freeSourceGerm_of_mem_closure (D : SingularTwoCell M) {W V : Set M} {ε : ℝ}
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (Rc Ac Rs : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {Ω Nb : Set (EuclideanSpace ℝ (Fin 2))}
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    (hsub : IsSubdivision Rs Rc) (hVec : V ⊆ ec.source) (hΩ : IsOpen Ω)
    (hΩcover : D.domain ∩ ⇑D ⁻¹' closure W ⊆ Ω) (hΩR : D.domain ∩ Ω ⊆ Rc.space)
    (hNbfr : Rc.space \ Ω ⊆ Nb) (hNbA : Rc.space ∩ Nb ⊆ Ac.space)
    (hsmall : ∀ x ∈ Rc.space, dist (simplicialMap Rs φ x) (ec (D x)) < ε)
    (hactive : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ec (D x)) < ε → ec.symm z ∈ closure W → x ∈ Rc.space \ Ac.space)
    (hsep : ∀ σ ∈ Rs.faces, (∃ v ∈ σ, v ∈ Ac.space) →
      Disjoint (simplicialMap Rs φ '' convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))))
        (⇑ec '' closure W))
    (hmaps : MapsTo (simplicialMap Rs φ) Rc.space (⇑ec '' V))
    {y : M} (hy : y ∈ closure W) :
    FreeSourceGerm Rs Ac (regionGluedMap D ec Rs φ Rc) D.domain y := by
  classical
  intro x hx
  have hxdom : x ∈ D.domain := hx.1
  have hxy : regionGluedMap D ec Rs φ Rc x = y := hx.2
  have hxR : x ∈ Rc.space := by
    by_contra hxR
    have hDx : D x = y := by
      rw [← hxy]
      simp only [regionGluedMap, if_neg hxR]
    exact hxR (hΩR ⟨hxdom, hΩcover ⟨hxdom, by simp only [mem_preimage, hDx]; exact hy⟩⟩)
  have hgx : ec.symm (simplicialMap Rs φ x) = y := by
    rw [← hxy]
    simp only [regionGluedMap, if_pos hxR]
  have hxA : x ∈ Rc.space \ Ac.space :=
    hactive x hxR _ (hsmall x hxR) (by rw [hgx]; exact hy)
  have hxΩ : x ∈ Ω := by
    by_contra hxo
    exact hxA.2 (hNbA ⟨hxR, hNbfr ⟨hxR, hxo⟩⟩)
  refine ⟨?_, ?_⟩
  · rw [hsub.space_eq]
    exact mem_nhdsWithin.2 ⟨Ω, hΩ, hxΩ, fun z hz => hΩR ⟨hz.2, hz.1⟩⟩
  · intro σ hσ hxσ v hv hvA
    obtain ⟨w, hwV, hw⟩ := hmaps hxR
    have hecy : ec y = simplicialMap Rs φ x := by
      rw [← hgx, ← hw, ec.left_inv (hVec hwV)]
    exact Set.disjoint_left.mp (hsep σ hσ ⟨v, hv, hvA⟩) ⟨x, hxσ, rfl⟩ ⟨y, hy, hecy⟩

open Classical in
theorem exists_laterMarginBlocks_of_mixedGerms (D : SingularTwoCell M)
    {BdM C Z W V K Kp : Set M} {ε η κ ηl : ℝ}
    (hfiber : ∀ y, (D.domain ∩ ⇑D ⁻¹' {y}).encard ≤ 2)
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C) (hκ : 0 < κ)
    (hinj : UniformInjectivityScale D.domain (⇑D) κ)
    (hZclosed : IsClosed Z) (hWV : closure W ⊆ V) (hVopen : IsOpen V)
    (hKcpt : IsCompact K) (hKpcpt : IsCompact Kp) (hKKp : K ⊆ interior Kp) (hKpV : Kp ⊆ V)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hec : ec ∈ (plGroupoid 3).maximalAtlas M)
    (hℓ : ℓ ≠ 0) (hVec : closure V ⊆ ec.source)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    (Rc Lc Ac Rs : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hRfin : Rc.faces.Finite) (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    (hsub : IsSubdivision Rs Rc) (hRsfin : Rs.faces.Finite) (hε : 0 < ε)
    (hsmall : ∀ x ∈ Rc.space, dist (simplicialMap Rs φ x) (ec (D x)) < ε)
    (hpzero : ∀ x ∈ Rc.space, ℓ (simplicialMap Rs φ x) = 0 ↔ x ∈ Lc.space)
    (hfrozen : EqOn (simplicialMap Rs φ) (fun x => ec (D x)) Ac.space)
    (hactive : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ec (D x)) < ε → ec.symm z ∈ closure W → x ∈ Rc.space \ Ac.space)
    (hsep : ∀ σ ∈ Rs.faces, (∃ v ∈ σ, v ∈ Ac.space) →
      Disjoint (simplicialMap Rs φ '' convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))))
        (⇑ec '' closure W))
    (hmaps : MapsTo (simplicialMap Rs φ) Rc.space (⇑ec '' V))
    (hDK : ⇑D '' Rc.space ⊆ K)
    (hD'K : regionGluedMap D ec Rs φ Rc '' Rc.space ⊆ K)
    (hinj' : UniformInjectivityScale D.domain (regionGluedMap D ec Rs φ Rc) κ)
    (hpersist : HasStableCrossingBlocks (regionGluedMap D ec Rs φ Rc) D.domain ec ℓ BdM
      (Z ∩ closure (V \ closure W)) η)
    (hprot : ∀ y ∈ doublePointSet (regionGluedMap D ec Rs φ Rc) D.domain ∩ Z ∩ K,
      (∃ σ ∈ Rs.faces, (∃ v ∈ σ, v ∈ Ac.space) ∧
          (D.domain ∩ regionGluedMap D ec Rs φ Rc ⁻¹' {y} ∩
            convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))).Nonempty) →
        ∃ e₁ ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e₁.source ∧
          HasPLNormalDoubleCrossingAt (⇑e₁ ∘ regionGluedMap D ec Rs φ Rc)
            (D.domain ∩ regionGluedMap D ec Rs φ Rc ⁻¹' e₁.source)
            (⇑e₁ '' (e₁.source ∩ BdM)) (e₁ y))
    (ecw : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓw : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)
    (Qw : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) (Nw Pw : Set M)
    (hNcpt : IsCompact Nw) (hNec : Nw ⊆ ec.source) (hNecw : Nw ⊆ ecw.source)
    (hPw : Pw ⊆ ecw.source) (hQfin : Qw.faces.Finite)
    (hQcover : ⇑ec '' Nw ⊆ interior Qw.space)
    (hQaff : ∀ s ∈ Qw.faces, ∃ A : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
      EqOn (fun z => ecw (ec.symm z)) A (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 3)))))
    (hecw : ecw ∈ (plGroupoid 3).maximalAtlas M) (hℓw : ℓw ≠ 0)
    (hCw : ∀ x ∈ ecw.source, x ∈ C ↔ 0 ≤ ℓw (ecw x))
    (hBdw : ∀ x ∈ ecw.source, x ∈ BdM ↔ ℓw (ecw x) = 0)
    (hPclosed : IsClosed Pw) (hPcover : Kp ∩ (Z ∪ closure W) ∩ Pw ⊆ Nw)
    (hlater : HasStableCrossingBlocks (⇑D) D.domain ecw ℓw BdM (Z ∩ Pw) ηl) :
    ∃ η' : ℝ, 0 < η' ∧
      HasStableCrossingBlocks (regionGluedMap D ec Rs φ Rc) D.domain ecw ℓw BdM
        ((Z ∩ Pw ∩ Kp) \
          {y | FreeSourceGerm Rs Ac (regionGluedMap D ec Rs φ Rc) D.domain y}) η' := by
  sorry

open Classical in
theorem exists_normalCrossings_of_gluedCell (D D' : SingularTwoCell M)
    {BdM C Z O W V K Kp : Set M} {ε η κ : ℝ}
    (hfiber : ∀ y, (D.domain ∩ ⇑D ⁻¹' {y}).encard ≤ 2)
    (hfiber' : ∀ y, (D'.domain ∩ ⇑D' ⁻¹' {y}).encard ≤ 2)
    (hloc' : ∀ x ∈ D'.domain, ∃ U ∈ 𝓝[D'.domain] x, InjOn (⇑D') U)
    (hκ : 0 < κ) (hinj : UniformInjectivityScale D.domain (⇑D) κ)
    (hinj' : UniformInjectivityScale D.domain (⇑D') κ)
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hnormal : ∀ y ∈ doublePointSet (⇑D) D.domain ∩ O,
      ∃ e₀ ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e₀.source ∧
        HasPLNormalDoubleCrossingAt (e₀ ∘ ⇑D) (D.domain ∩ ⇑D ⁻¹' e₀.source)
          (e₀ '' (e₀.source ∩ BdM)) (e₀ y))
    (hOopen : IsOpen O) (hZO : Z ⊆ O) (hZclosed : IsClosed Z)
    (hWopen : IsOpen W) (hWV : closure W ⊆ V) (hVopen : IsOpen V) (hKclosed : IsClosed K)
    (hKpcpt : IsCompact Kp) (hKKp : K ⊆ interior Kp) (hKpV : Kp ⊆ V)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hec : ec ∈ (plGroupoid 3).maximalAtlas M)
    (hℓ : ℓ ≠ 0) (hVec : closure V ⊆ ec.source)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    (Rc Lc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {Ω Nb : Set (EuclideanSpace ℝ (Fin 2))}
    (hRfin : Rc.faces.Finite) (hRman : IsCombinatorialManifoldWithBoundary 2 Rc)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    (hDK : ⇑D '' Rc.space ⊆ K) (hD'K : ⇑D' '' Rc.space ⊆ K)
    (hΩ : IsOpen Ω) (hΩcover : D.domain ∩ ⇑D ⁻¹' closure W ⊆ Ω)
    (hΩR : D.domain ∩ Ω ⊆ Rc.space) (hNb : IsOpen Nb) (hNbfr : Rc.space \ Ω ⊆ Nb)
    (hNbA : Rc.space ∩ Nb ⊆ Ac.space)
    (Rs : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hε : 0 < ε) (hsub : IsSubdivision Rs Rc) (hRsfin : Rs.faces.Finite)
    (hBvL : ∀ v ∈ Rs.vertices, v ∈ Bv ↔ v ∈ Lc.space)
    (hsmall : ∀ x ∈ Rc.space, dist (simplicialMap Rs φ x) (ec (D x)) < ε)
    (hpnonneg : ∀ x ∈ Rc.space, 0 ≤ ℓ (simplicialMap Rs φ x))
    (hpzero : ∀ x ∈ Rc.space, ℓ (simplicialMap Rs φ x) = 0 ↔ x ∈ Lc.space)
    (hfrozen : EqOn (simplicialMap Rs φ) (fun x => ec (D x)) Ac.space)
    (hactive : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ec (D x)) < ε → ec.symm z ∈ closure W → x ∈ Rc.space \ Ac.space)
    (hsep : ∀ σ ∈ Rs.faces, (∃ v ∈ σ, v ∈ Ac.space) →
      Disjoint (simplicialMap Rs φ '' convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))))
        (⇑ec '' closure W))
    (hmaps : MapsTo (simplicialMap Rs φ) Rc.space (⇑ec '' V))
    (hguard : ∀ s : Finset (EuclideanSpace ℝ (Fin 2)),
      (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Rs.vertices → s.card ≤ 4 →
        (s ∩ Bv).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 →
        AffineIndependent ℝ
          (fun v : (s.filter fun x => x ∈ Ac.space) => φ (v : EuclideanSpace ℝ (Fin 2))) →
        AffineIndependent ℝ (fun v : s => φ (v : EuclideanSpace ℝ (Fin 2))))
    (hprot : ∀ y ∈ doublePointSet (regionGluedMap D ec Rs φ Rc) D.domain ∩ Z ∩ K,
      (∃ σ ∈ Rs.faces, (∃ v ∈ σ, v ∈ Ac.space) ∧
          (D.domain ∩ regionGluedMap D ec Rs φ Rc ⁻¹' {y} ∩
            convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))).Nonempty) →
        ∃ e₁ ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e₁.source ∧
          HasPLNormalDoubleCrossingAt (⇑e₁ ∘ regionGluedMap D ec Rs φ Rc)
            (D.domain ∩ regionGluedMap D ec Rs φ Rc ⁻¹' e₁.source)
            (⇑e₁ '' (e₁.source ∩ BdM)) (e₁ y))
    (hpersist : HasStableCrossingBlocks (regionGluedMap D ec Rs φ Rc) D.domain ec ℓ BdM
      (Z ∩ closure (V \ closure W)) η)
    (ι : Type) [Finite ι] (ecw : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓw : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ))
    (Qw : ι → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (Nw Pw : ι → Set M)
    (hNcpt : ∀ i, IsCompact (Nw i)) (hNec : ∀ i, Nw i ⊆ ec.source)
    (hNecw : ∀ i, Nw i ⊆ (ecw i).source) (hPw : ∀ i, Pw i ⊆ (ecw i).source)
    (hQfin : ∀ i, (Qw i).faces.Finite)
    (hQcover : ∀ i, ⇑ec '' Nw i ⊆ interior (Qw i).space)
    (hQaff : ∀ i, ∀ s ∈ (Qw i).faces,
      ∃ A : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
        EqOn (fun z => ecw i (ec.symm z)) A
          (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 3)))))
    (hecw : ∀ i, ecw i ∈ (plGroupoid 3).maximalAtlas M) (hℓw : ∀ i, ℓw i ≠ 0)
    (hCw : ∀ i, ∀ x ∈ (ecw i).source, x ∈ C ↔ 0 ≤ ℓw i (ecw i x))
    (hBdw : ∀ i, ∀ x ∈ (ecw i).source, x ∈ BdM ↔ ℓw i (ecw i x) = 0)
    (hPclosed : ∀ i, IsClosed (Pw i))
    (hPcover : ∀ i, Kp ∩ (Z ∪ closure W) ∩ Pw i ⊆ Nw i)
    (hmixed : ∀ i : ι, ∃ η' : ℝ, 0 < η' ∧
      HasStableCrossingBlocks (regionGluedMap D ec Rs φ Rc) D.domain (ecw i) (ℓw i) BdM
        ((Z ∩ Pw i ∩ Kp) \
          {y | FreeSourceGerm Rs Ac (regionGluedMap D ec Rs φ Rc) D.domain y}) η')
    (hboundaryAffine : ∀ i : ι,
      ∀ y ∈ doublePointSet (regionGluedMap D ec Rs φ Rc) D.domain ∩ Nw i,
      IsFreeBoundaryDoubleGerm Rs Ac (regionGluedMap D ec Rs φ Rc) D.domain BdM y →
        ∃ (O₁ : Set (EuclideanSpace ℝ (Fin 3)))
          (A : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)),
          IsOpen O₁ ∧ ec y ∈ O₁ ∧
            EqOn (fun z => ecw i (ec.symm z)) A (O₁ ∩ {z | 0 ≤ ℓ z}))
    (hwallskel : ∀ i : ι, ∀ y ∈ doublePointSet (regionGluedMap D ec Rs φ Rc) D.domain ∩ Nw i,
      IsFreeInteriorDoubleGerm Rs Ac (regionGluedMap D ec Rs φ Rc) D.domain BdM y →
        ec y ∉ complexSkeleton 1 (Qw i))
    (hwalltrans : ∀ i : ι, ∀ y ∈ doublePointSet (regionGluedMap D ec Rs φ Rc) D.domain ∩ Nw i,
      IsFreeInteriorDoubleGerm Rs Ac (regionGluedMap D ec Rs φ Rc) D.domain BdM y →
        ∀ F ∈ (Qw i).faces, F.card = 3 →
          ec y ∈ convexHull ℝ (F : Set (EuclideanSpace ℝ (Fin 3))) →
            ∃ w : EuclideanSpace ℝ (Fin 3), ‖w‖ = 1 ∧
              w ∉ vectorSpan ℝ (F : Set (EuclideanSpace ℝ (Fin 3))) ∧ ∃ ρ > 0,
                (⇑ec '' (doublePointSet (regionGluedMap D ec Rs φ Rc) D.domain ∩ ec.source) ∩
                  Metric.ball (ec y) ρ ⊆ {z | ∃ c : ℝ, z = ec y + c • w}) ∧
                  ∀ c : ℝ, |c| < ρ → ec y + c • w ∈
                    ⇑ec '' (doublePointSet (regionGluedMap D ec Rs φ Rc) D.domain ∩ ec.source))
    (hwallfold : ∀ i : ι, ∀ y ∈ doublePointSet (regionGluedMap D ec Rs φ Rc) D.domain ∩ Nw i,
      IsFreeDoubleGerm Rs Ac (regionGluedMap D ec Rs φ Rc) D.domain BdM y →
        ∀ σ ∈ Rs.faces, σ.card ≤ 2 →
          ec y ∈ simplicialMap Rs φ '' convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))) →
            ec y ∉ complexSkeleton 2 (Qw i))
    (hdom' : D'.domain = D.domain)
    (hglue : EqOn (⇑D') (fun x => ec.symm (simplicialMap Rs φ x)) Rc.space)
    (hglueoff : EqOn (⇑D') (⇑D) Rc.spaceᶜ) :
    (∃ O' : Set M, IsOpen O' ∧ Z ∪ closure W ⊆ O' ∧
        ∀ y ∈ doublePointSet (⇑D') D'.domain ∩ O',
          ∃ e₁ ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e₁.source ∧
            HasPLNormalDoubleCrossingAt (e₁ ∘ ⇑D') (D'.domain ∩ ⇑D' ⁻¹' e₁.source)
              (e₁ '' (e₁.source ∩ BdM)) (e₁ y)) ∧
      ∀ i : ι, ∃ η' : ℝ, 0 < η' ∧
        HasStableCrossingBlocks (⇑D') D'.domain (ecw i) (ℓw i) BdM
          ((Z ∪ closure W) ∩ Pw i ∩ Kp) η' := by
  sorry

end MetricAmbient

open Classical in
theorem generalPositionInDoubleBuffered : GeneralPositionInDoubleBufferedStatement := by
  classical
  intro E _ _ _ S K
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ := combinatorialChartedSpace (double 3 K)
    (isCombinatorialManifold_double_succ_succ K S.isManifold)
  let _ : CompactSpace (double 3 K).space :=
    isCompact_iff_compactSpace.mp (isPolyhedron_space (double 3 K)).isCompact
  let _ : PathConnectedSpace S.boundaryNeighborhoodSpace :=
    S.boundaryNeighborhoodPathConnectedSpace
  intro ι C Bd B G β γ hloc hfiber _ hbuffer _ hmapC hproper hsurj hparam havoid
  have hBspace : S.boundaryNeighborhood.space ⊆ K.space := fun x hx =>
    PiecewiseLinear.boundaryComplex_space_subset 3 K
      (derivedNeighborhood_space_subset S.boundaryComplex S.loopComplex hx)
  obtain ⟨n, W, V, hWopen, hVopen, hWV, hWn, huniv, hcharts⟩ :=
    exists_finiteAdaptedCover_of_compactSpace Bd C
      fun y U hU => exists_adaptedHalfSpaceChart_in_double K S.isManifold y U hU
  choose ecf ℓf hecf hℓf hVclf hCf hBdf using hcharts
  have hoverlap : ∀ (j : ℕ) (hj : j < n) (m : ℕ) (hm : m < n),
      ∃ Q : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
        Q.faces.Finite ∧
          ⇑(ecf j hj) '' (closure (V j) ∩ closure (V m)) ⊆ interior Q.space ∧
          Q.space ⊆ ⇑(ecf j hj) '' ((ecf j hj).source ∩ (ecf m hm).source) ∧
          ∀ s ∈ Q.faces, ∃ A : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
            EqOn (fun z => ecf m hm ((ecf j hj).symm z)) A
              (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 3)))) :=
    fun j hj m hm =>
      exists_transitionSubdivisionOnOverlap (ecf j hj) (ecf m hm) (hecf j hj) (hecf m hm)
        (closure (V j) ∩ closure (V m))
        ((isClosed_closure.inter isClosed_closure).isCompact)
        (inter_subset_left.trans (hVclf j hj)) (inter_subset_right.trans (hVclf m hm))
  choose Qf hQfin hQcover hQsrc hQaff using hoverlap
  have hVW : ∀ j, V j ⊆ ⋃ i, W i := by
    intro j
    rw [huniv]
    exact subset_univ _
  have hdpG : doublePointSet (⇑G) G.domain ⊆ ⋃ j, W j := by
    rw [huniv]
    exact subset_univ _
  have hUW : ⋃ j, W j ⊆ ⋃ j, ⋃ (_ : j < n), closure (W j) := by
    refine iUnion_subset fun j => ?_
    by_cases hj : j < n
    · exact fun x hx => mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hj, subset_closure hx⟩⟩
    · rw [hWn j (not_lt.mp hj)]
      exact empty_subset _
  have key : ∀ k : ℕ, ∃ (cell : SingularTwoCell (double 3 K).space)
      (Ok : Set (double 3 K).space) (b : ContinuousMap loopCircle (frontier cell.domain))
      (g : freeLoop S.boundaryNeighborhoodSpace),
      cell.domain = G.domain ∧ MapsTo (⇑cell) cell.domain C ∧
        (∀ x ∈ cell.domain, ∃ U ∈ 𝓝[cell.domain] x, InjOn (⇑cell) U) ∧
        (∀ y, (cell.domain ∩ ⇑cell ⁻¹' {y}).encard ≤ 2) ∧
        cell.domain ∩ ⇑cell ⁻¹' Bd = frontier cell.domain ∧
        (∀ z ∈ Set.range cell.boundary, B ∈ 𝓝[Bd] z) ∧
        doublePointSet (⇑cell) cell.domain ⊆ ⋃ j, W j ∧
        IsOpen Ok ∧ (⋃ j, ⋃ (_ : j < k), closure (W j)) ⊆ Ok ∧
        (∀ y ∈ doublePointSet (⇑cell) cell.domain ∩ Ok,
          ∃ e₂ ∈ atlas (EuclideanSpace ℝ (Fin 3)) (double 3 K).space, y ∈ e₂.source ∧
            HasPLNormalDoubleCrossingAt (e₂ ∘ ⇑cell) (cell.domain ∩ ⇑cell ⁻¹' e₂.source)
              (e₂ '' (e₂.source ∩ Bd)) (e₂ y)) ∧
        (∀ (m : ℕ) (hm : m < n), k ≤ m → ∃ ηm : ℝ, 0 < ηm ∧
          HasStableCrossingBlocks (⇑cell) cell.domain (ecf m hm) (ℓf m hm) Bd
            ((⋃ j, ⋃ (_ : j < k), closure (W j)) ∩ closure (V m \ closure (W m))) ηm) ∧
        Function.Surjective b ∧
        (∀ θ, ((cell (b θ) : (double 3 K).space) : E × E × ℝ) = ι (g θ)) ∧
        ¬loopClassMeets g S.basepoint S.normalSubgroup := by
    intro k
    induction k with
    | zero =>
        refine ⟨G, ∅, β, γ, rfl, hmapC, hloc, hfiber, hproper, hbuffer, hdpG, isOpen_empty,
          ?_, ?_, ?_, hsurj, hparam, havoid⟩
        · exact iUnion_subset fun j => iUnion_subset fun hj => absurd hj (Nat.not_lt_zero j)
        · exact fun y hy => absurd hy.2 (notMem_empty y)
        · intro m hm _
          have hz : (⋃ j, ⋃ (_ : j < 0), closure (W j)) = (∅ : Set (double 3 K).space) :=
            eq_empty_of_subset_empty (iUnion_subset fun j => iUnion_subset fun hj =>
              absurd hj (Nat.not_lt_zero j))
          refine ⟨1, one_pos,
            hasStableCrossingBlocks_of_doublePointSet_inter_eq_empty ?_ one_pos⟩
          rw [hz, empty_inter, inter_empty]
    | succ k ih =>
        obtain ⟨cell, Ok, b, g, hdom, hcellC, hcellloc, hcellfib, hcellpr, hcellbuf,
          hcelldp, hOkopen, hOkZ, hOkcross, hcellstb, hbsurj, hbparam, hbavoid⟩ := ih
        have hZsucc : (⋃ j, ⋃ (_ : j < k + 1), closure (W j)) ⊆
            (⋃ j, ⋃ (_ : j < k), closure (W j)) ∪ closure (W k) := by
          refine iUnion_subset fun j => iUnion_subset fun hj => ?_
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with h | h
          · exact fun x hx => mem_union_left _ (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨h, hx⟩⟩)
          · subst h
            exact fun x hx => mem_union_right _ hx
        by_cases hk : k < n
        · set ec := ecf k hk with hecdef
          set ℓ := ℓf k hk with hℓdef
          have hec : ec ∈ (plGroupoid 3).maximalAtlas (double 3 K).space := hecf k hk
          have hℓ : ℓ ≠ 0 := hℓf k hk
          have hVcl : closure (V k) ⊆ ec.source := hVclf k hk
          have hVec : V k ⊆ ec.source := subset_closure.trans hVcl
          have hCchart := hCf k hk
          have hBdchart := hBdf k hk
          obtain ⟨Rc, Lc, Ac, Ω, Nb, hRfin, hRman, hLR, hAR, hRdom, hRV, hLspace, hΩ,
            hΩcover, hΩR, hNb, hNbfr, hNbA, hAfree⟩ :=
            cell.exists_cutOutPiece_of_closure_subset (V₀ := W k) (hVopen k) (hWV k)
          have hZclosed : IsClosed (⋃ j, ⋃ (_ : j < k), closure (W j)) :=
            Set.Finite.isClosed_biUnion (Set.finite_lt_nat k) fun j _ => isClosed_closure
          obtain ⟨ηk, hηk, hstk⟩ := hcellstb k hk le_rfl
          obtain ⟨T, κ, δ, ε, hκ, hδ, hε, hTfin, hTspace, hTstar, hcert, hconv, hactive,
            hbdbuf⟩ :=
            exists_normalizationPreparation_on_prescribedRegion cell hcellloc hcellfib
              hcellbuf (hVopen k) (hWV k) ec hVec Rc Ac hRfin hAR hRdom hRV hAfree
          have hchartbuf : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
              dist z (ec (cell x)) < ε → z ∈ ⇑ec '' V k :=
            fun x hx z hz => (hconv x hx z hz).1
          obtain ⟨R, τ, Kt, hτ, hsub, hRsfin, -, hKcpt, hKV, hDKint, hcontrol⟩ :=
            exists_protectedSubdivision_in_adaptedChart cell hcellloc hcellfib hcellpr
              hcellC hOkcross hZclosed hOkopen hOkZ ec ℓ hec hℓ (hVopen k) hVcl hCchart
              hBdchart Rc Lc Ac hRfin hRman hLR hAR hRdom hRV hLspace hΩ hΩR hNb hNbfr hNbA
              (hWV k) hAfree hstk T hTfin hTspace hTstar hκ hδ hε hcert hconv
          have : Finite ↥(Set.Ioo k n) := (Set.finite_Ioo k n).to_subtype
          have : LocallyCompactSpace (double 3 K).space :=
            ChartedSpace.locallyCompactSpace (H := EuclideanSpace ℝ (Fin 3)) _
          obtain ⟨Kp, hKpcpt, hKKp, hKpV⟩ := exists_compact_between hKcpt (hVopen k) hKV
          obtain ⟨Bv, φ, hadm, hguard, hboundaryAffine, hwallskel, hwalltrans, hwallfold⟩ :=
            exists_genericVertexMap_in_adaptedChart cell hcellpr hcellC ec ℓ hℓ hVec hCchart
              hBdchart Rc Lc Ac hLR hAR hRdom hRV hLspace R hsub hRsfin ↥(Set.Ioo k n)
              (fun i => ecf i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => Qf k hk i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => closure (V k) ∩ closure (V i.1))
              (fun _ => (isClosed_closure.inter isClosed_closure).isCompact)
              (fun _ => inter_subset_left.trans hVcl)
              (fun i => inter_subset_right.trans (hVclf i.1 (Set.mem_Ioo.mp i.2).2))
              (fun i => hQfin k hk i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => hQcover k hk i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => hQsrc k hk i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => hQaff k hk i.1 (Set.mem_Ioo.mp i.2).2) hτ
          obtain ⟨hpl, hsmall, hfrozen, hpnonneg, hpzero, hsep, hmaps, hgK, hstar, hprot,
            hpersist⟩ := hcontrol Bv φ hadm
          obtain ⟨cell', hdom', hglue, hglueoff⟩ :=
            exists_gluedCell_of_vertexMap_in_adaptedChart cell (hVopen k) ec hec hVec Rc Ac
              hRfin hRman hAR hRdom hRV hΩ hΩR hNb hNbfr hNbA R φ hsub hRsfin hfrozen hpl
              hmaps
          have hbridge : ⇑cell' = regionGluedMap cell ec R φ Rc :=
            eq_regionGluedMap_of_eqOn hglue hglueoff
          have hclose : ∀ x ∈ cell.domain, dist (cell' x) (cell x) < δ := by
            intro x _
            by_cases hxR : x ∈ Rc.space
            · rw [hglue hxR]
              exact (hconv x hxR _ (hsmall x hxR)).2
            · rw [hglueoff hxR, dist_self]
              exact hδ
          have hstar' : StarInj T (⇑cell') := by
            rw [hbridge]
            exact hstar
          have hDK : ⇑cell '' Rc.space ⊆ Kt := hDKint.trans interior_subset
          have hD'K : ⇑cell' '' Rc.space ⊆ Kt := by
            rw [hbridge]
            exact hgK
          have hWK : ∀ y ∈ doublePointSet (⇑cell') cell.domain, y ∈ closure (W k) →
              y ∈ Kt := by
            rintro y ⟨x, hxd, z, hzd, hxz, hxy, hzy⟩ hyW
            by_contra hyK
            have hxR : x ∉ Rc.space := by
              intro hx
              refine hyK ?_
              rw [← hxy]
              exact hD'K ⟨x, hx, rfl⟩
            have hDx : cell x = y := by rw [← hxy, hglueoff hxR]
            exact hxR (hΩR ⟨hxd, hΩcover ⟨hxd, by simp only [mem_preimage, hDx]; exact hyW⟩⟩)
          have hfibKt : ∀ z ∉ Kt, ⇑cell' ⁻¹' {z} = ⇑cell ⁻¹' {z} := fun z hz =>
            preimage_singleton_eq_of_eqOn_compl_of_image_subset hglueoff hDK hD'K hz
          obtain ⟨hC', hfibV, hloc', hcard', hpr', H, hH0, hH1, hHtrack⟩ :=
            exists_globalInvariants_of_gluedCell cell cell' hcellpr hcellC hcellbuf hκ hcert
              hclose hstar' ec ℓ (hVopen k) hVec hCchart hBdchart Rc Lc Ac hRfin hRman hRdom
              hRV hLspace hΩ hΩR hNb hNbfr hNbA R φ hsub hsmall hfrozen hpnonneg hpzero
              hchartbuf hbdbuf hdom' hglue hglueoff
          have hlaterfam : ∀ i : ↥(Set.Ioo k n), ∃ ηm : ℝ, 0 < ηm ∧
              HasStableCrossingBlocks (⇑cell) cell.domain
                (ecf i.1 (Set.mem_Ioo.mp i.2).2) (ℓf i.1 (Set.mem_Ioo.mp i.2).2) Bd
                ((⋃ j, ⋃ (_ : j < k), closure (W j)) ∩
                  closure (V i.1 \ closure (W i.1))) ηm :=
            fun i => hcellstb i.1 (Set.mem_Ioo.mp i.2).2 (le_of_lt (Set.mem_Ioo.mp i.2).1)
          have hinjD : UniformInjectivityScale cell.domain (⇑cell) κ :=
            (hcert (⇑cell) (fun x _ => by rw [dist_self]; exact hδ) hTstar).1
          have hinjD' : UniformInjectivityScale cell.domain (⇑cell') κ :=
            (hcert (⇑cell') hclose hstar').1
          have hinjG : UniformInjectivityScale cell.domain
              (regionGluedMap cell ec R φ Rc) κ := by
            rw [← hbridge]
            exact hinjD'
          have hmixed : ∀ i : ↥(Set.Ioo k n), ∃ η' : ℝ, 0 < η' ∧
              HasStableCrossingBlocks (regionGluedMap cell ec R φ Rc) cell.domain
                (ecf i.1 (Set.mem_Ioo.mp i.2).2) (ℓf i.1 (Set.mem_Ioo.mp i.2).2) Bd
                ((((⋃ j, ⋃ (_ : j < k), closure (W j)) ∩
                    closure (V i.1 \ closure (W i.1))) ∩ Kp) \
                  {y | FreeSourceGerm R Ac (regionGluedMap cell ec R φ Rc) cell.domain y})
                η' := fun i =>
            exists_laterMarginBlocks_of_mixedGerms cell hcellfib hcellpr hcellC hκ hinjD
              hZclosed (hWV k) (hVopen k) hKcpt hKpcpt hKKp hKpV ec ℓ hec hℓ hVcl hCchart
              hBdchart Rc Lc Ac R φ hRfin hRdom hRV hLspace hsub hRsfin hε hsmall hpzero
              hfrozen hactive hsep hmaps hDK hgK hinjG hpersist hprot
              (ecf i.1 (Set.mem_Ioo.mp i.2).2) (ℓf i.1 (Set.mem_Ioo.mp i.2).2)
              (Qf k hk i.1 (Set.mem_Ioo.mp i.2).2) (closure (V k) ∩ closure (V i.1))
              (closure (V i.1 \ closure (W i.1)))
              ((isClosed_closure.inter isClosed_closure).isCompact)
              (inter_subset_left.trans hVcl)
              (inter_subset_right.trans (hVclf i.1 (Set.mem_Ioo.mp i.2).2))
              ((closure_mono Set.sdiff_subset).trans (hVclf i.1 (Set.mem_Ioo.mp i.2).2))
              (hQfin k hk i.1 (Set.mem_Ioo.mp i.2).2)
              (hQcover k hk i.1 (Set.mem_Ioo.mp i.2).2)
              (hQaff k hk i.1 (Set.mem_Ioo.mp i.2).2)
              (hecf i.1 (Set.mem_Ioo.mp i.2).2) (hℓf i.1 (Set.mem_Ioo.mp i.2).2)
              (hCf i.1 (Set.mem_Ioo.mp i.2).2) (hBdf i.1 (Set.mem_Ioo.mp i.2).2)
              isClosed_closure
              (fun x hx => ⟨subset_closure (hKpV hx.1.1),
                closure_mono Set.sdiff_subset hx.2⟩)
              (hlaterfam i).choose_spec.2
          obtain ⟨⟨O', hO'open, hO'Z, hcross'⟩, hstable'⟩ :=
            exists_normalCrossings_of_gluedCell cell cell' hcellfib hcard' hloc' hκ hinjD
              hinjD' hcellpr
              hOkcross hOkopen hOkZ hZclosed (hWopen k) (hWV k) (hVopen k) hKcpt.isClosed
              hKpcpt hKKp hKpV ec ℓ hec hℓ
              hVcl hCchart hBdchart Rc Lc Ac hRfin hRman hRdom hRV hLspace hDK hD'K hΩ
              hΩcover hΩR hNb hNbfr hNbA R Bv φ hε hsub hRsfin hadm.2.1 hsmall hpnonneg
              hpzero hfrozen hactive hsep hmaps hguard hprot hpersist ↥(Set.Ioo k n)
              (fun i => ecf i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => ℓf i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => Qf k hk i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => closure (V k) ∩ closure (V i.1))
              (fun i => closure (V i.1 \ closure (W i.1)))
              (fun _ => (isClosed_closure.inter isClosed_closure).isCompact)
              (fun _ => inter_subset_left.trans hVcl)
              (fun i => inter_subset_right.trans (hVclf i.1 (Set.mem_Ioo.mp i.2).2))
              (fun i => (closure_mono Set.sdiff_subset).trans
                (hVclf i.1 (Set.mem_Ioo.mp i.2).2))
              (fun i => hQfin k hk i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => hQcover k hk i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => hQaff k hk i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => hecf i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => hℓf i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => hCf i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => hBdf i.1 (Set.mem_Ioo.mp i.2).2)
              (fun _ => isClosed_closure)
              (fun _ x hx => ⟨subset_closure (hKpV hx.1.1),
                closure_mono Set.sdiff_subset hx.2⟩)
              hmixed hboundaryAffine
              hwallskel hwalltrans hwallfold hdom' hglue hglueoff
          have hstout : ∀ i : ↥(Set.Ioo k n),
              HasStableCrossingBlocks (⇑cell') cell.domain
                (ecf i.1 (Set.mem_Ioo.mp i.2).2) (ℓf i.1 (Set.mem_Ioo.mp i.2).2) Bd
                (((⋃ j, ⋃ (_ : j < k), closure (W j)) ∩
                  closure (V i.1 \ closure (W i.1))) \ interior Kp)
                (hlaterfam i).choose := by
            intro i
            have hQN : (((⋃ j, ⋃ (_ : j < k), closure (W j)) ∩
                closure (V i.1 \ closure (W i.1))) \ interior Kp) ⊆ Ktᶜ :=
              fun z hz hzK => hz.2 (hKKp hzK)
            have hin := hasStableCrossingBlocksIn_of_isCompact_subset
              (hlaterfam i).choose_spec.2
              cell.isPLBall_domain.isPolyhedron.isCompact cell.continuousOn hcellC
              (hCf i.1 (Set.mem_Ioo.mp i.2).2) (hBdf i.1 (Set.mem_Ioo.mp i.2).2) hκ hinjD
              (((hZclosed.inter isClosed_closure).sdiff isOpen_interior).isCompact)
              Set.sdiff_subset hKcpt.isClosed.isOpen_compl hQN
            exact (hasStableCrossingBlocksIn_of_preimage_singleton_eq hin hQN
              fun z hz => by rw [hfibKt z hz]).toHasStableCrossingBlocks
          have hbuf' : ∀ z ∈ Set.range cell'.boundary, B ∈ 𝓝[Bd] z := by
            rintro _ ⟨x, rfl⟩
            have hx : (x : EuclideanSpace ℝ (Fin 2)) ∈ frontier cell.domain := by
              rw [← hdom']
              exact x.2
            have h1 := hHtrack 1 ⟨(x : EuclideanSpace ℝ (Fin 2)), hx⟩
            rw [hH1 ⟨(x : EuclideanSpace ℝ (Fin 2)), hx⟩] at h1
            exact h1.2
          have hdpnew : doublePointSet (⇑cell') cell'.domain ⊆ ⋃ j, W j := by
            rw [hdom']
            exact doublePointSet_subset_of_preimage_singleton_eq_off cell.domain hfibV
              hcelldp (hVW k)
          have hHB : ∀ (t : unitInterval) (x : frontier cell.domain), H (t, x) ∈ B :=
            fun t x => mem_of_mem_nhdsWithin (hHtrack t x).1 (hHtrack t x).2
          obtain ⟨c, δ₀, hcδ, hδavoid⟩ :=
            exists_boundary_loop_of_buffered_homotopy S K cell cell' b g hdom' hC' hbparam
              hbavoid hbsurj H hH0 hH1 hHB hBspace
          refine ⟨cell', O', ⟨c, c.continuous⟩, δ₀, hdom'.trans hdom, hC', hloc', hcard',
            hpr', hbuf', hdpnew, hO'open, ?_, hcross', ?_, c.surjective, hcδ, hδavoid⟩
          · exact hZsucc.trans hO'Z
          · intro m hm hkm
            have hik : m ∈ Set.Ioo k n := Set.mem_Ioo.mpr ⟨by omega, hm⟩
            obtain ⟨ηm, hηm, hstm⟩ := hstable' ⟨m, hik⟩
            rw [hdom'] at hstm
            refine ⟨min ηm (hlaterfam ⟨m, hik⟩).choose,
              lt_min hηm (hlaterfam ⟨m, hik⟩).choose_spec.1, ?_⟩
            rw [hdom']
            refine (hstm.union (hstout ⟨m, hik⟩)).mono_doublePointSet ?_
            rintro y ⟨hy, hyZ, hyP⟩
            refine ⟨hy, ?_⟩
            by_cases hyKp : y ∈ Kp
            · exact Or.inl ⟨⟨hZsucc hyZ, hyP⟩, hyKp⟩
            · refine Or.inr ⟨⟨?_, hyP⟩, fun hint => hyKp (interior_subset hint)⟩
              rcases hZsucc hyZ with hZ | hW
              · exact hZ
              · exact absurd (interior_subset (hKKp (hWK y hy hW))) hyKp
        · refine ⟨cell, Ok, b, g, hdom, hcellC, hcellloc, hcellfib, hcellpr, hcellbuf,
            hcelldp, hOkopen, ?_, hOkcross, ?_, hbsurj, hbparam, hbavoid⟩
          · refine iUnion_subset fun j => iUnion_subset fun hj => ?_
            by_cases hjk : j < k
            · exact fun x hx => hOkZ (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hjk, hx⟩⟩)
            · rw [hWn j (by omega), closure_empty]
              exact empty_subset _
          · intro m hm hkm
            exact absurd hm (by have := not_lt.mp hk; omega)
  obtain ⟨A, On, b, g, hdom, hAC, hAloc, hAfib, hApr, hAbuf, hAdp, -, hOnZ, hAcross, -,
    hbsurj, hbparam, hbavoid⟩ := key n
  have hAcross' : ∀ y ∈ doublePointSet (⇑A) A.domain,
      ∃ e₃ ∈ atlas (EuclideanSpace ℝ (Fin 3)) (double 3 K).space, y ∈ e₃.source ∧
        HasPLNormalDoubleCrossingAt (e₃ ∘ ⇑A) (A.domain ∩ ⇑A ⁻¹' e₃.source)
          (e₃ '' (e₃.source ∩ Bd)) (e₃ y) :=
    fun y hy => hAcross y ⟨hy, hOnZ (hUW (hAdp hy))⟩
  have hAbd : Set.range A.boundary ⊆ B := by
    rintro _ ⟨x, rfl⟩
    have hx : (x : EuclideanSpace ℝ (Fin 2)) ∈ A.domain ∩ ⇑A ⁻¹' Bd := by
      rw [hApr]
      exact x.2
    exact mem_of_mem_nhdsWithin hx.2 (hAbuf _ ⟨x, rfl⟩)
  have hAimage : A '' A.domain ∩ Bd = Set.range A.boundary := by
    rw [← image_inter_preimage, hApr]
    ext y
    exact ⟨fun ⟨x, hx, hxy⟩ => ⟨⟨x, hx⟩, hxy⟩, fun ⟨x, hxy⟩ => ⟨x, x.2, hxy⟩⟩
  obtain ⟨hA⟩ := SingularTwoCell.nonempty_normalSingularCellData_of_fields (double 3 K)
    (isCombinatorialManifold_double_succ_succ K S.isManifold) A Bd B hAloc hAfib hAbd
    hAimage hAcross'
  obtain ⟨c, δ₁, hcδ, hδavoid⟩ :=
    exists_boundary_loop_of_buffered_homotopy S K A A b g rfl hAC hbparam hbavoid hbsurj
      ⟨fun z => A.boundary z.2, A.boundary.continuous.comp continuous_snd⟩
      (fun _ => rfl) (fun _ => rfl) (fun _ x => hAbd (mem_range_self x)) hBspace
  exact ⟨A, hA, hdom, hAC, hAbuf, c, δ₁, hcδ, hδavoid⟩

end DifferentialGeometry.Topology.PiecewiseLinear
