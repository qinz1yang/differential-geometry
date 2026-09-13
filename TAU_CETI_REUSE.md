# Tau Ceti proof adaptations

These native modules adapt Apache 2.0 source from
[Tau Ceti at 3358033ba2fd35f321356dceaf2372a0fd6c0bfd](https://github.com/TauCetiProject/TauCeti/tree/3358033ba2fd35f321356dceaf2372a0fd6c0bfd).
The repository LICENSE supplies the license text. Original copyright and
author headers remain in both Lean files; NOTICE also records attribution.
The upstream root NOTICE path returns 404 at this pinned revision.

| Native module | Upstream source and authors |
| --- | --- |
| Analysis/Calculus/Sard | [Sard/EqualDimension.lean](https://github.com/TauCetiProject/TauCeti/blob/3358033ba2fd35f321356dceaf2372a0fd6c0bfd/TauCeti/Analysis/Calculus/Sard/EqualDimension.lean), Joseph Tooby-Smith and Codex |
| Topology/Morse/Generic | [Morse/Generic.lean](https://github.com/TauCetiProject/TauCeti/blob/3358033ba2fd35f321356dceaf2372a0fd6c0bfd/TauCeti/Analysis/Calculus/Morse/Generic.lean), The Tau Ceti contributors |

The Haar-null transport also adapts
[Haar/NormedSpace.lean](https://github.com/TauCetiProject/TauCeti/blob/3358033ba2fd35f321356dceaf2372a0fd6c0bfd/TauCeti/MeasureTheory/Measure/Haar/NormedSpace.lean),
Copyright 2026 The Tau Ceti contributors, under the same license.

## Local modifications, 2026-09-13

The port uses the existing Lean 4.33.1 and Mathlib
0df444a360eaa60ab8c11dca51a86af692955474. No Tau Ceti dependency is installed;
its 4.34.0-rc2 environment is not substituted for the local pins.
Upstream module-system syntax and explanatory docstrings are removed while
the required attribution headers are preserved.

The Sard proof uses Mathlib's actual Jacobian null-image theorem, constructs
the domain Borel structure locally, and transports Haar-null sets through a
continuous linear equivalence. Source and target may have different norms
and universes, with equal finite dimension. Rank zero and empty sets are allowed.

The Morse proof uses DG's existing IsCriticalPointAt,
IsNondegenerateCriticalPointAt and native quadratic Hessian. It introduces
no competing critical-point vocabulary. Actual second-derivative surjectivity
implies the native Hessian's separating condition. Public results give almost
everywhere, density and arbitrarily small operator-norm perturbations on the
original open set. Tangent-space coercions, obsolete lemma names and the
quadratic consumer were adapted to the pinned compiler. Mechanics stay private.

## Verification

Source request 1789297179397566825-schoenflies-73efb952 passed in Slurm 13821107
on della-r3c4n2 in 35.43 seconds: 28 guards and eight signature/axiom pairs.
Imported gate 1789297419650760082-schoenflies-50b26acf passed in 112.58 seconds,
with 31 guards and six public/consumer pairs matching the source readbacks
except Function.Surjective qualification. Both new modules freshly compiled
offline in 1:18.39 with zero diagnostics.

The imported DG declarations and consumers pass unusedArguments, simpNF,
synTaut and checkType. defLemma is unavailable in this pinned Mathlib; source
declaration-kind review is retained. All audited transitive axioms lie in
propext, Classical.choice and Quot.sound. Consumers exhibit the actual critical
point of a perturbed real quadratic and a nondegenerate point of a constant
function on the rank-zero model. Both leaves are registered in the flat root.
These checks are not a completed full DifferentialGeometry aggregate build.

Distinct critical values, global positioning of an embedded sphere, smooth
relative disk absorption and full Schoenflies remain open.
