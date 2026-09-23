# Collaborator brief (Lean): Package G — the protected circle removal step (CGN leaf 4)

Written by the lead on 2026-09-23. One conversation per package; say that you take Package G so the
lead does not assign it elsewhere. Same setting and rules as the earlier briefs: repository
`https://github.com/qinz1yang/differential-geometry-dev`, branch `codex/moise-integration`; branch
from its head; NEW FILES ONLY; restate the frozen leaf byte-identically (its statement and the
`variable` block it uses, `Skeleton/ControlledGraphNeighborhood.lean` lines 255–271); never import a
`Skeleton/` file (read and copy from it); no `sorry`, docstrings or comments in delivered modules;
lines ≤ 100 codepoints; zero warnings; no unused binder; no underscore in a `def`/`abbrev`/`structure`
name; grep the statement shape before proving anything; do not touch `DifferentialGeometry.lean`,
`FREE_INPUTS.md` or any existing file; open a pull request with a ≤ 40-line report and `#print axioms`
for every public theorem. Paths are relative to `DifferentialGeometry/Topology/PiecewiseLinear/`.

Lanes in flight you must not touch (their files are untracked until accepted, so avoid these names):
the CGN edge matching (Codex: `Topology/LocalDegree/*`, `Topology/Manifold/BoundaryNormal*`,
`Topology/Covering/CyclicSections`, `PLBallPair*`), P4 compression (`Section34Compression*`), the §32
tower, the compact P7 residual balls, the C1 tube (`LoopTheorem/BranchCollar*`,
`ClosedBranchTubeCollarArcs`, `MarkedBranchChartPL`), the smoothing lane, Packages E and F if someone
else holds them, and your own §31 / Package D.

Independence: this leaf takes the preparation and the piercing conditions as hypotheses
(`Section34Frame.lean` lines 931 and 1016) and is consumed by the real global removal
`exists_section34ProtectedCircleRemoval` (skeleton line 519, a descent by `Section34CircleRemovalDescent`);
nothing else in the file depends on its proof, and it needs no proof of the other four leaves.

Read first: `consult/BO-cgn-first-four-leaves-codex-answer.md` §4 and the sub-leaf table. Its
corrections: the step requires `cnt' e₀ < cnt e₀` (strict, not a decrease by exactly one — removing two
crossings at once is allowed); the piercing predicate has 22 conjuncts.

## The leaf: `exists_section34ProtectedCircleRemovalStep` (line 389)

Given `hprep`, `hpack`, an edge `e₀` and `hlt : 1 < cnt e₀`, produce `G'`, `cnt'`, `Pg'` with
`Section34PiercingConditions … Sp Tp cnt' Pg' G'` (same `Sp`, `Tp`), `cnt' e₀ < cnt e₀`, all other
counts unchanged, `EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)}` for every vertex, and the
annulus images `G' (ends e).1 '' Aa e`, `G' (ends e).2 '' Bb e` unchanged at every other edge. `hpack` and
`hlt` are the only configuration inputs: no appeal to `Moise341` and no distance bound (the original
`ε` bound is not an invariant of the step and is not in this leaf).

Route (BO §4). Write `a = (ends e₀).1`, `b = (ends e₀).2`.
1. An innermost-removable-configuration lemma: distinguish a circle bounding a disk in the annulus from
   essential parallel circles bounding an annular band (a circle on `Bb` need not bound a disk IN `Bb`;
   several parallel essential crossings are not refuted by calling a circle innermost). Use the component
   clauses and the generator information to find the disk or the adjacent-band cancellation
   (`SphereInnermostDisk`, `Section28Annuli`, `LateralAnnulusLevels`).
2. Realise the cancellation by a relative PL modification of the parametrised enlarged cell, not by
   replacing its boundary as a set (`BoundaryCollarExtension`, `SurfaceSplitBallPair`). If the first
   endpoint moves, clause 4 forces both `G'_a '' Sn = Sp` and `G'_a '' Tn = Tp`: an ambient
   homeomorphism supported in `interior Sp` preserves `Sp` but not automatically `Tp`, so build the
   preservation of the inner tube into the move.
3. Verify the 22 clauses from the exact constructed move: relative PL extension and fixed tube images
   (1, 4, 11; off-support equality on all of `Cc`); support confinement, carriers, other edges (2–3, 5–6,
   10, 12–14, 21–22 — disjoint supports alone do not certify the whole overlaps in 21; prove where the
   modified lens lies); the cancellation with sides unchanged (7–9 and the component assertions 15–16);
   rebuild and enumerate the remaining trace (17–20, strict decrease at `e₀`, unchanged counts and
   annulus images elsewhere; `CrossingTraceCircles`).
4. Real helpers in the skeleton to copy, never import: `section34Marker_of_dist_lt` (line 407),
   `section34Core_of_eqOn_off_support` (418), `section34Step_eqOn_marker_and_boundary` (439: marker and
   unrelated-boundary equality from the off-support equality), `exists_section34PiercingConditions_count_le_one`
   (461). `Section34CircleRemovalDescent`, `Section34DeletedBalls`, `Section34CapDeletion` do the global
   descent and the literal deletion, not this cancellation.

Most likely surprise (BO): preserving the fixed inner tube and clauses 15–16 during an essential-band
cancellation. Test your configuration lemma on an edge with an additional local cancelling pair of
crossings (a count-one example does not exercise `hlt`).

Sub-leaves: `exists_innermost_piercing_cancellation` (NEW_THEORY),
`exists_relative_PL_piercing_cancellation` (NEW_THEORY), `piercing_conditions_after_cancellation`
(MEDIUM), `exists_reindexed_piercing_family_of_strict_decrease` (SMALL).

Delivery: real sub-leaf modules, then a module restating the leaf and proving it. Partial delivery is
welcome: a PR with real sub-leaves plus one clearly named `*Probe.lean` file assembling the leaf with
`sorry` only at the named remaining sub-leaves, and a report saying which.
