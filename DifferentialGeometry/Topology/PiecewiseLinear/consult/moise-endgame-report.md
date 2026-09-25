# Moise endgame: the unconditional chain to smooth structures on compact three-manifolds

Branch `codex/moise-endgame`, cut from `origin/codex/moise-pc-merge-20260924` @ `bd97f38e1`
(the lead's merge of the confined-tube circle removal). Date 2026-09-24.

## Result

`exists_isManifold_three` (module `Moise352Producer`): every compact Hausdorff topological
three-manifold, charted on `EuclideanSpace ℝ (Fin 3)`, carries a `ChartedSpace` structure that is a
smooth manifold. No hypotheses. This is the ledger's Level-0 endpoint, previously conditional on
`PLApproximation 3` and `PLSmoothing 3`; it is now obtained from `plApproximation_three` and the
compact smoothing `plSmoothingCompact_three`.

The chain, every link a theorem with no hypotheses beyond instance binders:

| Named input | Producer | Module |
|---|---|---|
| `Moise252` | `moise252` | `LoopTheorem/Moise252Producer` (new) |
| `Moise264Orientable` | `moise264Orientable` | `LoopTheorem/Moise252Producer` (new) |
| `Moise306`, `Moise307` | `moise306`, `moise307` | `Section30Torus` |
| `Moise321`, `Moise322`, `Moise323` | `moise321`, `moise322`, `moise323` | `Section32PseudoCell` |
| `Moise331OnTube`, `Moise331` | `moise331OnTube`, `moise331` | `Moise341Producer` (new) |
| `Moise341` | `moise341` | `Moise341Producer` (new) |
| `ControlledGraphNeighborhoodStatement` | `controlledGraphNeighborhoodStatement` | `ControlledGraphNeighborhood` (promoted from `Skeleton/`) |
| `Section34NormalFamilyStatement` | `section34NormalFamilyStatement` | `Section34Normalization` |
| `Section34CellDiagram` | `section34CellDiagram` | `Section34Terminal` (promoted from `Skeleton/`, leaf deleted) |
| `Moise352Open 3`, `Moise352 3` | `moise352Open`, `moise352` | `Moise352Producer` (new) |
| `PLApproximationManifold 3`, `PLApproximation 3` | `plApproximationManifold_three`, `plApproximation_three` | `Moise352Producer` (new) |
| `PLSmoothingCompact 3` | `plSmoothingCompact_three` | `Moise352Producer` (new) |
| Level 0 | `exists_isManifold_three` | `Moise352Producer` (new) |

## The one mathematical change: Section 33 consumes the orientable extended loop theorem

Section 33 (`moise331`, `moise331OnTube`, Lemma 10 in `Section33FundamentalGroupBijective`) took
the unrestricted `Moise264`, which has no producer in the tree; only `Moise264Orientable` is proved
(`moise264_orientable`, from `Moise252`). The dependency is narrowed in
`Section33LoopTheoremInjective`, the only place where the loop theorem is applied:

* the null-homotopy of a loop of the surface `|L|` in the open set `U ⊆ ℝ³` is enclosed in a compact
  connected combinatorial three-manifold `N₀ ⊆ U` with `|L| ⊆ interior N₀`
  (`exists_connected_neighborhood_fundamentalGroup_map_eq_one`, unchanged);
* `N₀` is orientable: it is a bounded polyhedron of a three-dimensional space, so it lies in the
  convex hull of an affinely independent `4`-set (`exists_affineIndependent_openSimplex_superset`)
  and `isOrientable_of_space_subset_convexHull` applies;
* `|L|` is two-sided in `N₀` in the intrinsic sense that `Moise264Orientable` asks
  (`IsTwoSided (((↑) : N₀.space → E) ⁻¹' L.space)`): it is two-sided in `ℝ³`
  (`IsCombinatorialManifold.isTwoSided`) and `N₀` is a neighbourhood of it, so
  `IsTwoSided.preimage_of_isInducing` with the inducing map `Subtype.val` transfers it.

The theorem is renamed `injective_fundamentalGroup_map_of_moise264Orientable`; the three consumers
now take `(h264 : Moise264Orientable)`. The unrestricted `Moise264` stays open and off the goal path.

## Renames and interface changes (consumers updated; none outside these files)

| Before | After | Reason |
|---|---|---|
| `injective_fundamentalGroup_map_of_moise264 (h264 : Moise264)` | `injective_fundamentalGroup_map_of_moise264Orientable (h264 : Moise264Orientable)` | narrowing |
| `section33_fundamentalGroup_map_bijective_of_isTube (h264 : Moise264)` | same name, `(h264 : Moise264Orientable)` | narrowing |
| `moise331 (h323) (h324) (h264 : Moise264)` | `moise331_of_moise323_of_moise324_of_moise264Orientable (h323) (h324) (h264 : Moise264Orientable)`; plain `moise331 : Moise331` unconditional | plain name = unconditional, as `moise304` |
| `moise331OnTube (h323) (h324) (h264 : Moise264)` | `moise331OnTube_of_moise323_of_moise324_of_moise264Orientable …`; plain `moise331OnTube` unconditional | same |
| `moise321/322/323 (h307) (h303) (h286) (h267) (h314)` | `moise32x_of_moise307 (h307)` with `moise303`, `moise286`, `moise267`, `moise314` supplied internally; plain `moise321/322/323` unconditional | proved inputs removed from the hypothesis list |
| `Skeleton/ControlledGraphNeighborhood.lean` | `ControlledGraphNeighborhood.lean` (+ `controlledGraphNeighborhoodStatement`) | promotion |
| `Skeleton/Section34Terminal.lean` | `Section34Terminal.lean`; leaf `exists_section34NormalFamily` deleted, the assembly calls `section34NormalFamilyStatement` | promotion |

New imports: `Section32PseudoCell` imports `Section26ThreeSurfaces`, `Section28Annuli`,
`Section30Separation`, `Section30Torus`, `Section31CanonicalConfiguration`; `Section30Torus` imports
`LoopTheorem/Moise252Producer`; `Section34Normalization` imports `ControlledGraphNeighborhood` and
`Section34Control`; `ControlledGraphNeighborhood` imports `Moise341Producer`; `Section34Terminal`
imports `Section34Normalization`. Five modules registered in the root aggregate. The ledger
`FREE_INPUTS.md` is updated in the same commit (Level 0, B1 rows, C1, the skeleton table, the sorry
count `2 → 0`, the `Moise264` note).

## Verification

Compiled and axiom-checked, on the worktree of this branch with its own `.lake` build directory
(seeded from the lead's merge build for modules whose sources are identical):

* Focused build: `lake build` of the 109 targets = the 13 changed or new modules and every module
  of the tree that depends on them (reverse import closure), 12 workers. 7522 jobs, 1975 modules
  compiled from source, 0 errors, 0 warnings, no `info`/`Try this` output; 18:58–19:52 PDT.
* `#print axioms` on the 22 theorems of the chain (`exists_isManifold_three`,
  `plApproximation_three`, `plApproximationManifold_three`, `moise352`, `moise352Open`,
  `plSmoothingCompact_three`, `section34CellDiagram`, `section34NormalFamilyStatement`,
  `controlledGraphNeighborhoodStatement`, `controlledGraphNeighborhood`, `moise341`, `moise331`,
  `moise331OnTube`, `moise323`, `moise322`, `moise321`, `moise307`, `moise306`,
  `moise264Orientable`, `moise252`, `injective_fundamentalGroup_map_of_moise264Orientable`,
  `section33_fundamentalGroup_map_bijective_of_isTube`): each depends on exactly `propext`,
  `Classical.choice`, `Quot.sound`.
* All-declaration audit of the 13 modules (foundational axioms plus the Mathlib standard linter set
  minus `docBlame`/`docBlameThm`, thirteen linters): 49 declarations, 0 failures.
* Sorry census of the tree (excluding `External/`): no `sorry` in any real module; fourteen remain
  in the four reconnaissance `Skeleton/*Reduction.lean` files, none on the endpoint path.
* `git diff --check` clean.

Not verified: no root `lake build DifferentialGeometry` (owner rule). Modules outside the reverse
closure of the changed modules are byte-identical to the merge tip and were not recompiled here.

Known stale text, deliberately left: `Section34Control.lean:27` compares its existential ambient
with the deleted leaf `exists_section34NormalFamily`; rewording it would recompile the 218
modules depending on `Section34Control`. Replace by `Section34NormalFamilyStatement` when that
module is next edited.

## Not done

* `Skeleton/ControlledGraphNeighborhoodReduction.lean`, `Skeleton/CanonicalTowerReduction.lean`,
  `Skeleton/SpineCarrierReduction.lean`, `Skeleton/TorusLinkingReduction.lean` (fourteen `sorry`s)
  are reconnaissance skeletons off the endpoint path; untouched.
* The unrestricted `Moise264` and the non-compact `PLSmoothingModel 3` remain open; neither is on the
  goal path.
* D1 (smooth Poincaré) lives in the main repository.
* No root `lake build DifferentialGeometry` was run (owner rule); the focused build covers the
  changed modules and every module of the tree that depends on them.
