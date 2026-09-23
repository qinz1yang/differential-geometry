# Collaborator brief: close the two Section 31 leaves on a separate branch

Written by the lead on 2026-09-23 for an external collaborator (English). Independent of every
lane in flight; new files only, so the merge is trivial.

## Setting

Lean 4 / Mathlib v4.33.1 formalisation of Moise's route to the three-dimensional Poincaré
conjecture (Moise, *Geometric Topology in Dimensions 2 and 3*, GTM 47). Repository
`https://github.com/liao9yuan/differential-geometry-dev`, branch **`moise-integration`**;
branch from its current head into your own branch (say `collab/section31`). Paths below are
relative to `DifferentialGeometry/Topology/PiecewiseLinear/`.

The open obligations of each chain are stated as `theorem leaf … := by sorry` in a *skeleton*
file under `Skeleton/`, whose assembly down to the named endpoint is already proved; see
`Skeleton/README.md` (what a skeleton is), `FREE_INPUTS.md` (the ledger of every open input; the
only progress yardstick) and the module docstring of the skeleton you work on. A leaf is closed
by a **new real module** that restates the leaf **byte-identically** (same name, binders,
instance order, namespace) and proves it; the lead then deletes the leaf from the skeleton,
imports your module, registers it in the aggregate and updates the ledger. You never edit the
skeleton, the aggregate `DifferentialGeometry.lean`, or `FREE_INPUTS.md`.

## Rules (from the checkout's `AGENTS.md`; read its sections "Source discipline", "Soundness", "Linters")

- New files only, under `DifferentialGeometry/Topology/PiecewiseLinear/` (or
  `DifferentialGeometry/Topology/Homology/` for pure homology). Do not modify, move or delete any
  existing file.
- No `sorry`, `admit`, `native_decide`, new `axiom`, `nolint`, `set_option`, `maxHeartbeats` in
  delivered modules.
- No declaration docstrings and no inline comments. A file has: the copyright header used by
  every file in the tree, the imports, ONE module docstring (`/-! … -/`) with the mathematics and
  any hypothesis notes, then code. Lines ≤ 100 Unicode codepoints. No underscore in any
  `def`/`abbrev`/`structure` name; `theorem` names keep snake_case. Zero warnings.
- Never import a `Skeleton/` file. Never weaken a frozen statement. If you believe a leaf is false,
  stop and report the counterexample checked against every Lean hypothesis.
- Every new public name must be unique tree-wide: grep before using it. Before proving anything
  elementary, grep the tree for the statement shape; most basic PL and homology lemmas exist under
  unexpected names.
- Vacuity discipline: any new `structure` or `Prop`-valued `def` needs an inhabitant theorem;
  every hypothesis you add to a *brick* must have a named producer in the tree.

## Target: `Skeleton/Section31CanonicalConfiguration.lean`, its two remaining leaves

Both are deep on paper but have been reduced (by an earlier reconnaissance) to named sub-leaves
in two probe files, which you may read and copy from but never import:
`Skeleton/SpineCarrierReduction.lean` and `Skeleton/TorusLinkingReduction.lean`. Each probe proves
the leaf from its sub-leaves; once the sub-leaves are real theorems, copy the probe's assembly
into your real module and close the leaf.

1. `exists_polygon_carrier_of_spine` (line 470; Moise 31.4 (ii)–(iv) with the uncited 28.11):
   given combinatorial solid tori `S₁`, `S₂` inside topological solid tori `T₁`, `T₂` with a common
   spine `Z₁`, and a compact `Z₀ ⊆ interior S₁` disjoint from `S₂` carrying `π₁(S₁)`, there is a
   PL circle `K ⊆ frontier S₂ ∩ interior S₁` carrying `π₁(S₂)`. Remaining sub-leaves of the probe:
   - `exists_frontier_cycle_of_boundary_in_open` (line 37): a 1-cycle in `A` bounding a 2-chain in
     `A` modulo a cycle supported in `A \ S` is homologous, through a chain in `S`, to a cycle on
     `frontier S ∩ A` (cut the bounding chain at the PL frontier). The open-cover chain step is
     already real: `Topology/Homology/RelativeChainCut.lean`
     (`exists_interface_cycle_of_boundary_difference`); the exact PL-frontier cut is what is left.
   - `exists_disjoint_oriented_polygons_of_cycle` (line 63): from a cycle on the boundary torus,
     finitely many pairwise disjoint oriented PL polygons with the same class.
   Already real (do not re-prove): `integralFirstHomology_interior_injective` is
   `IsTopologicalSolidTorus.integralSingularHomologyMap_interior_injective`
   (`SolidTorusInteriorHomology.lean`) after unfolding the probe's local `firstHomologyInclusion`;
   `hurewiczOne_injective_of_isTopologicalSolidTorus` is `IsTopologicalSolidTorus.hurewiczOne_injective`
   (`SolidTorusHurewiczOne.lean`); `exists_maximal_firstHomology_image_of_disjoint_polygons` is in
   `MaximalPolygonHomologyImage.lean` (same binders, map unfolded).
2. `exists_isPLCell_frontier_of_polygon_nullhomotopic` (line 481; Moise 28.8 in the tree's
   vocabulary): a polygon `G` on the boundary torus of a combinatorial solid torus `S`, bounding a
   PL disk `Δ` disjoint from a set `Z ⊆ interior S` carrying `π₁(S)`, and null-homotopic in `S`,
   bounds a PL disk `Δ'` on `frontier S`. Remaining sub-leaves of the probe, in the suggested order:
   - `subsingleton_firstHomology_complement_of_isPLBall` (line 66): `H₁(ℝ³ \ Δ; ℤ) = 0` for a PL
     2-disk `Δ` (a PL regular neighbourhood `N ≅ D² × [-1, 1]` of `Δ`, then Mayer–Vietoris between
     the exterior of `N` and its two disk sides).
   - `exists_integer_linking_equiv_of_isPLSphere` (line 61): `H₁(ℝ³ \ G; ℤ) ≅ ℤ` for a PL circle `G`
     (a PL solid-torus regular neighbourhood of the possibly knotted circle; Mayer–Vietoris on
     `ℝ³ = Int N ∪ Ext N`; the meridian is a primitive kernel generator). No general Alexander
     duality is in the tree and none is expected.
   - `surjective_firstHomologyInclusion_complement_of_null_meridian` (line 76): for a nonseparating
     boundary circle whose class dies in `π₁(S)`, the inclusion `Int S → Gᶜ` is surjective on `H₁`
     (its slope is primitive, so it is the meridian of the actual solid torus; a linking degree
     `±1` through a collar / regular-neighbourhood Mayer–Vietoris diagram). No unknotted ambient
     model may be assumed.
   Already real: `injective_firstHomologyInclusion_interior_solidTorus` (same as above, via
   `SolidTorusInteriorHomology`); helpers `Topology/Homology/EuclideanThreePunctureFirstHomology.lean`
   (`H₁(ℝ³ \ {p}) = 0`) and `ComplementHomeomorphHomology.lean` (complement homeomorphisms induced
   by ambient homeomorphisms and their `H₁` equivalence).

Read first: the skeleton's module docstring (its paragraphs on these two leaves, around lines
105–130 and 200–210), the two probes, and `Skeleton/FILL_LOG.md` sections
"Codex day queue item 2" and "item 3" (the routes above, with what was tried). Vocabulary to grep:
`integralSingularHomology`, `integralSingularHomologyMap`, `integralSingularChainsIn`,
`CarriesFirstHomologyOnto`, `CarriesFundamentalGroupOnto`, `HurewiczOne`, `IsPLSphere`, `IsPLBall`,
`IsCombinatorialSolidTorus`, `IsTopologicalSolidTorus`, `IsSpine`, `IsPLHomeomorphOn`,
`stdSimplexBoundary`, `PolygonalSchoenflies`, `TorusCircleHomology`, `TorusSubsurfaceCarrier`,
`ArcDerivedNeighborhood`, `derivedNeighborhood`, `BoundaryTube*`, `CyclicBallUnion`.

## Building and checking

The tree is large; the first build of the imports takes hours. `lake exe cache get` for Mathlib,
then `lake build <Module.Name>` for each module you import (for example
`lake build DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusInteriorHomology`), then check
your own file with `lake env lean <path>` and expect no output at all (zero warnings). Do not run
`lake build` of the whole root aggregate unless you want to; it is not required.

## Deliverable

A branch with the new files and a short report (≤ 40 lines): verdict per leaf (done / partial /
target false), the files with their public names, which sub-leaf each closes, the import lines
`import DifferentialGeometry.Topology.PiecewiseLinear.<Name>` for the aggregate, and for every
public theorem the output of `#print axioms` (only `propext`, `Classical.choice`, `Quot.sound` are
acceptable). The lead runs the acceptance pipeline on merge (statement identity against the
skeleton, name scan, zero-diagnostic check, axiom and linter audit) and wires the skeleton.

## If Section 31 is not to your taste

An equally independent alternative: the four frontiers of
`Skeleton/CompactSourceFaceOrderReduction.lean` (regular-cell-complex thinness for the Section 34
compact cut frame, from clauses 7–10 of `Section34CompactCutFrame` in
`Section34CompactVocabulary.lean` and the API of `PLCellOnBoundary.lean`), which close
`compactSourceFace_iff_cutLe` in `Skeleton/Section34Compact.lean`; read
`consult/BM-section34-compact-source-face-cut-order-review-digest.md` first.
