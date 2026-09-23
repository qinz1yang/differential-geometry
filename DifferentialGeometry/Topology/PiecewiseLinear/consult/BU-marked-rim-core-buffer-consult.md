# BU — consult: the zero-marked rim core buffer (compact graph-frame clause 9)

Written by the lead on 2026-09-24 after two failed routes by the Codex lane on item 14 (log
`Skeleton/FILL_LOG.md` from line 10538 and line 11201). For an external reviewer; answer in
`consult/BU-marked-rim-core-buffer-answer.md` (new file; no git writes; no frozen statement edited).
About 1500 words plus Lean signatures; the six checks of `consult/REVIEW-TEMPLATE.md` apply, with
the weight on checks 4 and 6. Paths are relative to `DifferentialGeometry/Topology/PiecewiseLinear/`
on `liao9yuan/differential-geometry-dev:moise-integration` (mirror of `qinz1yang:codex/moise-integration`).

## The obligation

Everything else of the compact leaf `exists_compactCutAndGraph` (`Skeleton/Section34Compact.lean`)
is proved (56 registered modules; see ledger row B1.b.8). What remains is one brick of graph-frame
clause 9, as the BT answer (`consult/BT-compact-cut-graph-clauses-nine-eleven-answer.md`) named it:

```lean
-- proposed; K ⊆ M finite combinatorial 3-manifolds in ℝ³, K.space ⊆ interior M.space,
-- s a triangle of K, L := restrict K (section34CompactGraphSkeleton K) the graph (1-skeleton of K').
exists_compactRimCoreBuffer :
    let Ns := ⋃ v ∈ (s.1 : Set E3), (graphDualCell M L v).space
    ∃ P : Set E3, P ⊆ interior M.space ∧ Ns ⊆ interior P ∧
      ∃ Φ : (D² × S¹) ≃ₜ P, section34CompactSimplexRim s.1 = Subtype.val '' (Φ '' {q | (q.1 : E2) = 0})
```

i.e. a solid torus `P` around the cyclic union of the dual vertex cells along the rim of `s`, with a
product parametrisation whose zero section is exactly the rim (a polygon in the 1-skeleton of the
first derived subdivision `K'`), `P` containing the vertex cells together with their arms.

Definitions (`DualCells.lean` line 386, `DerivedNeighborhood.lean` line 67):
`graphDualCell K L v = restrict (derivedNeighborhood K L) (closedStar (barycentricSubdivision K) v)`:
the dual cell of a graph vertex `v` is the part of the derived neighbourhood of the graph `L` (in
the second derived `K''`) lying in the closed star of `v` in `K'`. Consecutive vertex cells along
the rim meet in the splitting disks; the cyclic union is a combinatorial solid torus
(`Section34CompactFaceTorusCycle`, real).

## What is proved to fail (both verified, zero diagnostics)

1. `TubeEdgePairOverlap.lean`: gluing the per-edge unit solid cylinders
   (`IsTube.exists_unitSolidCylinder_coordinates`, on `C_u ∪ C_v` with the edge as axis) along
   end disks is impossible: for consecutive edges `uv`, `vw`,
   `(C_u ∪ C_v) ∩ (C_v ∪ C_w) = C_v ∪ D_uw` has `v` in its interior, so the overlap is
   3-dimensional, not an end disk. Also the accepted coordinates record only
   `φ 0 = h (edge centroid)`, not that the whole axis is the edge.
2. `GraphDualCellRadialBoundary.lean`: `C_v` is not a cone from `v`: for a flag `v ⊂ e ⊂ t` with
   `c = b(e)`, `d = b(t)`, the points `y = (c + d)/2` and `x = (v + c + d)/3` both lie on
   `frontier C_v`, and `x = v + (2/3)(y − v)`; so `frontier C_v` is not radially injective from `v`
   and cannot serve as an `IsConeBase`; the cone-extension route for a per-vertex marked prism
   (fixed end-disk coordinates, axis `rim ∩ C_v`) fails as stated.

## Questions

(a) Which construction gives the marked product? Candidates the lead sees:
   - (A) strengthen the existing unmarked product: `isTopologicalSolidTorus_derivedNeighborhood_circle`
     (`SolidTorusProduct.lean` line 48) goes through
     `exists_cylindricalDiagram_derivedNeighborhood_circle_eq_ends` (a cylindrical diagram of the
     derived neighbourhood of a combinatorial circle `J` with identified ends). Does that diagram, as
     constructed, send the axis of the model cylinder onto `J`? If yes, the missing brick is a
     re-export with the core clause; if not, what does the construction send to `J`?
   - (B) work with the rim's OWN derived neighbourhood `N(J) := derivedNeighborhood K J`
     (`J` = the rim as a subcomplex of `K'`), whose pieces `N(J) ∩ closedStar(K', v)` meet only in the
     2-disks `N(J) ∩ closedStar(K', v) ∩ closedStar(K', w)` — avoiding failure 1 — and build the
     prism on each piece; then show `N(J) ⊆ interior (⋃ C_v)` and `⋃ C_v ⊆ interior` of a radial
     enlargement of `N(J)` (the buffer). Which existing modules give the per-piece prism with the
     axis `J ∩ piece` (`TubeCenteredPrismCoordinates`, `SplitDiskCylinderCoordinates`,
     `CylindricalMeridian`, `CombinatorialSolidTorusOfCylindricalDiagram`)?
   - (C) a per-vertex bent prism on `C_v` itself from the flag structure of `N(L) ∩ Star(v)`,
     with a different cone point or a two-step straightening.
(b) For the chosen route, state the sub-leaves with exact Lean signatures over the tree's
   vocabulary, sized SMALL / MEDIUM / NEW_THEORY, and say which of failures 1–2 each avoids.
(c) Check the extremes: a rim of three `K`-vertices subdivided in `K'` (six rim vertices); a rim
   vertex of graph degree ≥ 3 (the arms leaving the rim); `s` with a boundary edge of `K`; the
   case `K' = K` that the worker chose. Is the marked product still there when the arms of `C_v`
   leave the rim in a third direction (the buffer must contain them)?
(d) State whether any proposed statement is FALSE for the tree's actual `graphDualCell`; verdicts
   are evidence, not rulings; the lead verifies against Lean.
