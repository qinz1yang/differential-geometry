# Local source modifications

Upstream: Yury Kudryashov, mathlib4 PR #33505, commit d43061d911b1aeae0788591da437a3b115098962 (Apache-2.0).

- Preserved exact upstream source snapshots and LICENSE under upstream/; UPSTREAM.json records URLs and SHA-256 hashes.
- RiemannMapIncrease.lean extracts the normalized disk seed and square-root derivative-improvement development, preserving its proof comments and attribution.
- Replaced the upstream draft branch-root producer with current canonical Complex.exists_continuousOn_pow_eq.
- Removed the duplicated upstream INTO theorem; use current canonical Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero.
- Exact subsequent API/compiler adaptations will be appended before freeze.

No shared Mathlib files, package versions, or caches are modified.

## RiemannMapIncrease compiler adaptations

- Reuse the already merged `Complex.UnitDisc.exists_continuousOn_pow_eq`; removed the duplicate UnitDisc root-branch proof.
- The current Mathlib RiemannMapping INTO declarations are private under the module system. Added `import all Mathlib.Analysis.Complex.RiemannMapping` to reuse that exact compiler-checked theorem, without copying or naming its mangled private identifier.
- Imported the precise derivative-of-quotient module and used `convert!` where updated structure instances otherwise generate irrelevant equality goals; supplied denominator nonzero witnesses explicitly.
- Simplified the square-root derivative arithmetic with current `field_simp`, removing a now-redundant `ring`.
- Generalized the normalized disk seed's unused `x in U` hypothesis to an explicit arbitrary point `x`; the conclusion is valid because the totalized UnitDisc map can be normalized even off U. The actual extremal headline still requires its chosen base point in U.
- Core omitted-value square-root/shift construction, strict derivative-improvement formula, and conclusion are unchanged.

## Current-epoch replay repair

- RiemannMapIncrease.lean is unchanged from its frozen source. Preserve both `public import Mathlib.Analysis.Complex.RiemannMapping` and `import all Mathlib.Analysis.Complex.RiemannMapping`; these have distinct Lean visibility semantics and must not be deduplicated.

## Hurwitz source extraction modifications

# Local modifications

- Extract the four supporting declarations from upstream RiemannMapping.lean lines 101–340 into HurwitzInjectivity.lean. Preserve the original Apache copyright/authors header and proof comments.
- Use precise canonical imports and a focused module description; omit the already merged upstream helper declarations.
- Replace deprecated `finite_diff_of_mem_codiscreteWithin` by `finite_sdiff_of_mem_codiscreteWithin`.
- Replace deprecated `codiscreteWithin_setOf_analyticOrderAt_eq_zero_or_top` by `codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top`.
- Replace upstream `Tendsto.tendstoUniformly_fun_const` by canonical `Tendsto.tendstoUniformly_const`.

Compiler compatibility edits after extraction will be recorded here. No mathematical statement change is intended.

- Replace deprecated set-membership and tactic spellings: `mem_diff` → `mem_sdiff`, `mem_setOf_eq` → `mem_ofPred_eq`, `setOf_mem_eq` → `ofPred_mem_eq`, and `push_neg` → `push Not`.
- Replace a fragile `convert` membership rewrite in the zero-count proof by an explicit equality `z = w` derived from the vanishing power, then transport the original finite-set membership. This preserves the proof and statement.

- Qualify `Set.mem_sdiff` to disambiguate it from `Filter.mem_sdiff` after the canonical rename.

- Wrapped one line in the zero-count proof at an existing function application to satisfy the strict line-length linter. Tokens, statements, proof semantics, author header, comments and documentation are unchanged.

- Adapt the logarithmic-derivative product rewrite to the current Mathlib API using `logDeriv_fun_mul` and `logDeriv_fun_prod` for explicit function expressions. This replaces the corresponding pointwise-function product lemma names only; all theorem statements, hypotheses, remaining proof steps, attribution, and upstream snapshots are unchanged.

## Unit-disc shift adaptation record

# Modifications log

Upstream: https://github.com/urkud/mathlib4

Commit: `d43061d911b1aeae0788591da437a3b115098962`

Pull request: https://github.com/leanprover-community/mathlib4/pull/33505

Author: Yury Kudryashov. License: Apache-2.0; see `LICENSE`.

## 2026-09-20 — attributed scratch vendoring

Copied `Mathlib/Analysis/Complex/UnitDisc/Shift.lean` to `UnitDisc/Shift.lean`.
Preserved the full Apache header, author attribution, original module documentation,
declaration documentation, public sections, imports, and public API.

Updated `shift.right_inv` to introduce its point explicitly (`right_inv w := ... w`).
This adapts the proof to Lean 4.33.1's elaboration of `Function.RightInverse`; the
map, inverse map, theorem statements, and mathematical proof are unchanged.

The bare `UnitDiscShift.lean` file at the scratch root is a byte-identical compile
copy for the parent Riemann mapping proof. The intended vendor location is
`DifferentialGeometry/External/RiemannMapping/UnitDisc/Shift.lean`.

## Extremal mapping extraction record

# Local modifications

Upstream: Mathlib PR 33505, `Mathlib/Analysis/Complex/RiemannMapping.lean`.
Source copied from `/private/tmp/pc-riemann-mapping-onto-20260920/upstream/Mathlib/Analysis/Complex/RiemannMapping.lean`.
Upstream source SHA-256: `335a97ee3cf41c2f56581b80176decde8de8bb60491a342d3b7eec2146aa8caa`.

- Extracted upstream lines 608–778: the two equicontinuity lemmas and the Ascoli extremal proof of `Complex.exists_bijOn_unitBall_map_eq_zero`.
- Preserved the original Apache copyright/authors header, draft module docstring, theorem statements, and proof comments.
- Replaced broad draft imports by `RiemannMapIncrease`, `HurwitzInjectivity`, and precise existing Mathlib dependencies.
- Removed `module`/`public section` wrappers for the legacy scratch module format; preserved `Complex` namespace and declaration names.
- Replaced deprecated `Set.mem_setOf` by canonical `Set.mem_ofPred` in the equicontinuity proof. No mathematical statement change.
- Updated the normalized-seed call to pass the basepoint explicitly (`x₀`) instead of membership (`hx₀`), matching the predecessor's natural generalization after reuse of the current Mathlib INTO theorem. The extremal theorem's statement is unchanged.
- Compiled against the frozen predecessor modules using Lean v4.33.1, `-j1`, and default resource budgets. First native run exited 0 with an empty log. No further proof edits were needed.

## Canonical source placement

- Place the unit-disc automorphism source at `UnitDisc/Shift.lean`, as designated by its original vendor manifest.
- Place the extracted Hurwitz, derivative-improvement, and extremal developments at `HurwitzInjectivity.lean`, `RiemannMapIncrease.lean`, and `RiemannMapExtremal.lean` in this vendor directory. Their existing source interfaces are preserved.
- Replace only scratch-module imports with canonical `DifferentialGeometry.External.RiemannMapping` imports. Retain each import qualifier, including BOTH `public import Mathlib.Analysis.Complex.RiemannMapping` and `import all Mathlib.Analysis.Complex.RiemannMapping`.
- Preserve all author headers, module and declaration documentation, proof comments, citations, public sections, theorem statements and proof bodies byte-for-byte outside these import replacements.
- The Hurwitz source already contains the strict replay's whitespace-only line wrapping. No further proof-token changes are introduced by placement.
- Preserve upstream snapshot bytes under `upstream/`, with `.lean.txt` suffixes to prevent raw upstream files from becoming unintended local Lean modules. `SNAPSHOTS.json` relates each original path to its exact snapshot and SHA-256.
- The non-vendored `Complex.riemann_mapping` and `Complex.exists_biholomorphic_map_to_unit_disk` assembly uses these producer theorems from `Analysis/Complex/RiemannMapping/Onto.lean`.
- This placement packet is source-only; root's subsequent compilation, linter and axiom receipt remains required for the canonical modules.
