# Reproducible verification

The reviewed Lean snapshot is proof commit
`3b12c1abf575960b58f7adca8f73c54c7ea5049b`. The following handoff commit changes documentation,
its verification script, and the documentation tracking rule only. Source locations and results below refer to that unchanged Lean tree.

## One command

```sh
cd /Users/bennettchow/Documents/Codex/wt17/ziyang
bash docs/handoffs/kappa-solutions-2026-09-20/verify.sh
```

Requirements: the pinned Lake/Lean installation, project dependencies, Git, `rg`, Python 3, and Bash.
The script performs no Git mutations or network operations. It writes build artifacts through Lake
and creates a unique `/private/tmp/wt17-kappa-verification.*` directory for scratch Lean probes and
logs. Its inventory assertions are deliberately for this snapshot; future proofs may reduce the
expected debt and require updating those assertions. Do not weaken an axiom or linter gate.

The script runs, sequentially:

1. A Lake build of all four headlines, `AncientRankOne`, `CylinderPreservation`, and `Preservation.Cylinder`.
2. Fresh source elaboration of those seven modules under the project's exact Lean options.
3. The full `lake build DifferentialGeometry` root build.
4. Comparison against the original declarations at `7c2e6848c`, and compilation of both original
   shrinker statements as corollaries.
5. The 13 applicable Mathlib declaration linters on the four headlines and five new public engines;
   exact elaborated type queries and transitive axiom queries.
6. A dependency traversal through declaration types and values for `arbitrary_high_curvature_blowup`,
   plus transitive axiom queries on the target and four reusable downstream lemmas.
7. A fresh `sorry` inventory and `git diff --check`.

The two documentation-presence linters, `docBlame` and `docBlameThm`, are excluded as required by
repository AGENTS.md, which forbids docstrings in non-vendored Lean source. No source linter is
suppressed. The script uses `getChecks true none none`, filters those two, calls `lintCore`, and
fails if any finding remains. Temporary `#print axioms` and `#check @...` queries supply evidence;
no diagnostic Lean module is added to the library.

## Recorded results

All commands below finished with exit code 0 after the last Lean edit.

| Check | Result |
|---|---|
| `lake build DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.AncientRankOne` | 12,070 jobs; zero diagnostics. |
| Lake build of the four headline modules | 13,218 jobs; zero diagnostics. |
| `lake build DifferentialGeometry` | 20,143 jobs; 21 warnings, all declarations using the explicitly retained `sorry`s in REMAINING_WORK.md; no errors or other diagnostics. |
| Fresh `lake env lean` of all four headline source files | Zero diagnostics in each file. |
| Final declaration-linter audit | 9 declarations × 13 linters; no findings. |
| Original shrinker-statement compatibility driver | Zero diagnostics. |
| Final source and diff review | New leaf registered in the flat root; no new proof debt, comments, diagnostics, linter suppressions, or resource-budget overrides. `git diff --check` clean. |
| Packaged `verify.sh` replay | Seven freshly elaborated modules; full root, original contracts, linters, axioms, and debt inventory all pass. |

Normal build-progress lines are expected. The retained `sorry` warnings are the repository's explicit
exception; the four headline dependency closures contain none of that debt.

The fresh-elaboration command pattern is:

```sh
lake env lean -Dpp.unicode.fun=true -DmaxSynthPendingDepth=3 -DautoImplicit=false \
  -Dweak.linter.mathlibStandardSet=true \
  -Dlinter.style.header=false -Dlinter.style.longLine=false \
  DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/KappaSolutions/AncientSplitting.lean
```

## Transitive axiom closures

Let `K = DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions` and
`R = DifferentialGeometry.PDE.RicciFlow`. Every row below was queried separately, not inferred
from a source search or from another theorem's result.

| Fully qualified name (using the prefixes above) | Transitive axioms |
|---|---|
| `K.exists_backward_slice_asymptotic_shrinker` | `propext`, `Classical.choice`, `Quot.sound` |
| `K.exists_samePole_normalized_asymptotic_shrinker` | `propext`, `Classical.choice`, `Quot.sound` |
| `K.klim_terminal_curvature_trichotomy` | `propext`, `Classical.choice`, `Quot.sound` |
| `K.ancient_fixed_universal_cover_product_of_null_plane` | `propext`, `Classical.choice`, `Quot.sound` |
| `R.curvatureOperatorImageAt_finrank_eq_one_of_complete_ancient_rank_one` | `propext`, `Classical.choice`, `Quot.sound` |
| `R.laplacian_height_eq_zero_of_initial_cylinder` | `propext`, `Classical.choice`, `Quot.sound` |
| `R.normGradSqFun_height_eq_one_of_initial_cylinder` | `propext`, `Classical.choice`, `Quot.sound` |
| `R.covariantDerivative_gradFun_height_eq_zero_of_initial_cylinder` | `propext`, `Classical.choice`, `Quot.sound` |
| `R.curvatureOperatorImageAt_finrank_le_one_of_initial_cylinder` | `propext`, `Classical.choice`, `Quot.sound` |

The nine declarations also form the final declaration-linter set. The four cylinder lemmas are at
`Preservation/Cylinder.lean:21,54,85` and `DimensionThree/CylinderPreservation.lean:20`, under
`DifferentialGeometry/Geometry/Flow/RicciFlow/`.

For `C = DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn`,
`C.good_point_derivatives`, `C.local_propagation`, `C.first_backward_slab`, and
`C.ancientExtension_nonempty_of_halfLineAncientLimitFrontier` separately have only the same three
foundational axioms. `C.arbitrary_high_curvature_blowup` still additionally uses **`sorryAx`**.
The dependency probe finds exactly the three unfinished declarations listed in REMAINING_WORK.md.

## Original statements and adversarial review

The comparison baseline is `7c2e6848cb8678a932191bc810a64ecd803627ba`.
The script recovers the original source with `git show`, rather than trusting this prose.

- The first two theorem declarations differ only by removal of the `2 ≤ finrank` hypothesis
  (ignoring whitespace). Exact original statement bodies are compiled as `example`s in fresh
  namespaces using the current source context. The proof calls the current theorem, so the
  stronger original contract remains derivable. `let _ := hdim` is confined to this compatibility
  probe to account for the intentionally redundant old binder.
- The third and fourth declaration texts, from `theorem` through the start of the proof,
  compare byte-for-byte equal. The audit also prints each current fully elaborated type.
- Shrinker witnesses remain tied to the rescaled slice sequence by actual convergence maps and
  metric data; nonflatness and the shrinker equation are conclusions, not supplied hypotheses.
- The normalized shrinker uses the same pole in the reduced-length and volume statements and
  exposes both the potential normalization and mass convergence.
- The terminal trichotomy is at time zero, with endpoint arguments respecting the regular interval.
- Ancient splitting returns one fixed diffeomorphism before the universal time quantifier, a
  complete surface at every past time, and the actual pulled-back metric identity.
- The new rank-one theorem has no artificial κ, compactness, simple-connectedness, or supplied
  splitting assumptions. Nonflatness follows from rank one at the given point. Generalized normed
  model spaces and the genuine terminal endpoint are retained.

## Evidence retention

The durable evidence is these recorded results, the checked-in source, its commit identity, and the
replay script. Original local logs were `/private/tmp/wt17-kappa-final-root.log`,
`/private/tmp/wt17-kappa-final-audit.log`, `/private/tmp/wt17-blowup-debt.log`, and
`/private/tmp/wt17-original-shrinker-statements.log`. Temporary logs can disappear; replay does not
rely on them. Diagnostic output is not committed as library source.
