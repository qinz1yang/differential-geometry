# Collaborator brief (Lean): finish the Section 32 descent leaf (takeover of Codex item 13)

Written by the lead on 2026-09-24. One conversation for this package; say that you take it. Same
setting and rules as your earlier briefs (`consult/COLLABORATOR-item14-marked-rim-request.md`,
`consult/COLLABORATOR-item15-trace-request.md`): repository
`https://github.com/qinz1yang/differential-geometry-dev`, branch `codex/moise-integration` (branch
from its head at or after the commit "Register the Section 32 descent bricks (Codex item 13)"; the
96 bricks below are on it); NEW FILES ONLY; restate the frozen leaf byte-identically (statement and
`variable` block); never import a `Skeleton/` file; no `sorry`, docstrings or comments; lines ≤ 100
codepoints; no underscore in a `def`/`abbrev`/`structure` name; grep every new name and every
statement shape; zero warnings with the lead's flags `-DautoImplicit=false
-DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true -Dlinter.style.header=true
-Dlinter.style.longLine=true`; no named input added; do not touch `DifferentialGeometry.lean` or
`FREE_INPUTS.md`; PRs against `codex/moise-integration`, one per completed stage is welcome, each
with a ≤ 40-line report, receipts and the audit line (axioms within propext / Classical.choice /
Quot.sound, the thirteen environment linters; split the audit by module group if it hits the
heartbeat limit). Paths are relative to `DifferentialGeometry/Topology/PiecewiseLinear/`.

## Target

`exists_descentSequence` (`Skeleton/Section32PseudoCell.lean` line 265, `section Leaves`), the last
leaf of Section 32; with it Moise 32.1–32.3 become unconditional. Inputs: the tube `ht`, the edge
`{u, v}` with midpoint `P'`, the canonical tower `htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' …`
(produced by `exists_canonicalTower`, module `CanonicalTowerExists`, real), the avoidance `havoid`,
the closed separating initial surface (`hcl`, `hsep`; producer `InitialSurfaceSeparates`, real) and
the four named inputs `h303 h286 h267 h314`. Output: a bi-infinite annular chain
`IsAnnularChain H B Jlo Jhi (fun i => φ '' S i) S'' T'' P'`, a sequence `M n` of closed separators of
`h u` from `h v` in the pair interior, all containing `P'`, with `M 0 = initialSurface S'' T'' P'`,
closedness of the chain's preimage, and the local eventual equality
`M n ∩ U = annularChain H B P' ∩ U` at every point other than `P'`.

## Read first, in this order

1. `consult/Codex13-section32-descent-handoff.md` in full: the previous lane's handoff, with the
   completed stages and their exact consumer interfaces, the module table, the next acceptance
   target (single-step Type 2 elimination, eight required properties, a concrete six-step assembly),
   the bridge-nonemptiness obligation, and Type 3 / halves / recursion / leaf. The host paths in it
   (private roots, receipts, tokens) are not for you.
2. `consult/Codex13-section32-descent-route-draft.md`: the reviewed route for the bridge
   nonemptiness and the guarded recursion. It is a proof plan, not a checked theorem.
3. `consult/BP-section32-tower-descent-codex-answer.md` §2: the five stage producers, the phased
   natural-number measures per finite window, the relative finite-window normalisation, the
   dependent recursion over a compact exhaustion of `I \ {P'}`, and the two limit lemmas.
4. `Skeleton/FILL_QUEUE.md` "Codex item 13" (inputs, vocabulary, the order of work, and what may be
   copied from the probe `Skeleton/CanonicalTowerReduction.lean` section `DescentStages`: copy into
   real modules under unique names, never import it) and the "# Codex item 13" entries of
   `Skeleton/FILL_LOG.md`.

## What is already real (do not re-prove)

96 modules with clean receipts, lead-checked and audited on the host: the actual finite null-seam
normalisation (`CanonicalSurfaceNullNormalization`,
`IsCanonicalSurface.exists_window_null_normalization`); the finite-window component classification
(`CanonicalWindowComponentClassification`,
`IsCanonicalTower.exists_initial_window_component_classification`); the finite-window Type 1
elimination from the actual initial separator (`CanonicalAnnularWindow`,
`IsCanonicalTower.exists_initial_annular_window`, with `CanonicalClosedComponentDeletion`,
`CanonicalClosedWindowReduction`, `ComponentSubsurfaceRestriction`); and the checked tools for
Type 2/3: `Topology/Connected/BicollaredReplacement`
(`Separates.of_bicollared_frontier_replacement`), `SurfacePatchReplacement`
(`IsCombinatorialManifold.separates_of_connected_surface_patch`), `TorusCirclePair`
(`IsCombinatorialSolidTorus.exists_annulus_pair_of_essential_circles`, both complementary annuli),
`AnnulusPatchDeletion` (`IsPLAnnulusWithEnds.separates_after_delete_interior`),
`CanonicalSurfaceComponentRemoval` (`IsCanonicalSurface.of_component_complement`),
`ManifoldComponentComplement`, `CanonicalComponentSeamDisks`, `CanonicalTowerSurfaceClosed`,
`SurfaceTraceMonotonicity`. Their statements are the interfaces; the handoff's table names the role
of each. No generic `IsCanonicalComponentDeletion` structure and no Type 2 normaliser exist yet.

## The work, in order

- Type 2 finite-window elimination. First the single-step theorem on `IsCanonicalAnnularWindow`
  for an actual returning component `C` in row `i` (its two saved ends on the same even torus,
  indexed by `i` or `i+1`), with the eight properties listed in the handoff, including the real
  `IsTypeTwoDeletion` certificate under a unique name: the six-step assembly is component
  complement (`exists_component_complement`), seam-disk transfer (`CanonicalComponentSeamDisks`),
  gluing `C` to a complementary even-torus annulus with `AnnulusPatchDeletion`, relative closedness
  from `IsCanonicalTower.isClosed_towerSurface`, state reconstruction with
  `of_component_complement` (retained models by `ComponentSubsurfaceRestriction`, trace inclusion
  and null-rank by `SurfaceTraceMonotonicity`), and the Type 1 strong-induction pattern on
  `windowComponentRank` / the total component count. Then iterate it over the finite window.
- Bridge nonemptiness: an initial same-component witness carrying BOTH a lower and an upper
  essential seam, transported through the actual split/deletion histories (route draft: polygon
  carriers from spines, `carriesFirstHomologyOnto_or_subsingleton_of_disjoint` with
  `SolidTorusHurewiczOne`, a mixed adjacent pair among the finite essential circles, removal of the
  maximal null-disk islands, transport through `CircleCappingComponentInvariants` /
  `PLHomeomorphComponents` / `CanonicalSurfaceSplit`). No insufficiency of the inputs is known.
- Type 3 (redundant bridges) with `SurfacePatchReplacement` on two distinct bridge annuli plus one
  annulus on each endpoint torus; the even-torus halves with `TorusCirclePair`, using the whole even
  torus as the closed surface; the guarded recursion with the reviewed guard schedule (completed
  rows `[a, b]`, chosen interior halves `a+1, …, b`, the two guard even tori full, expansion at the
  outside seams, normalisation of the two new boundary rows); `M 0` = the original initial surface;
  then every `IsAnnularChain` field (exact end labels and meets, the three disjointness assertions,
  containment in the outer carriers, both fundamental-group surjectivity certificates) and the two
  limit clauses; restate and close the leaf.

`Set.ncard` of an infinite set is not a measure: every decrease must be on a finite window. If a
clause truly needs a fact that the tower, the initial surface and the four named inputs do not
supply, stop and report the exact clause with the counterexample checked against every Lean
hypothesis; do not add a named input.
