# Tau Ceti proof adaptations

These native modules adapt Apache 2.0 source from
[Tau Ceti at 3358033ba2fd35f321356dceaf2372a0fd6c0bfd](https://github.com/TauCetiProject/TauCeti/tree/3358033ba2fd35f321356dceaf2372a0fd6c0bfd).
The repository LICENSE supplies the license text. Original copyright and
author headers remain in the Lean files; NOTICE also records attribution.
The upstream root NOTICE path returns 404 at this pinned revision.

| Native module | Upstream source and authors |
| --- | --- |
| Analysis/Calculus/Sard | [Sard/EqualDimension.lean](https://github.com/TauCetiProject/TauCeti/blob/3358033ba2fd35f321356dceaf2372a0fd6c0bfd/TauCeti/Analysis/Calculus/Sard/EqualDimension.lean), Joseph Tooby-Smith and Codex |
| Topology/Morse/Generic | [Morse/Generic.lean](https://github.com/TauCetiProject/TauCeti/blob/3358033ba2fd35f321356dceaf2372a0fd6c0bfd/TauCeti/Analysis/Calculus/Morse/Generic.lean), The Tau Ceti contributors |
| Topology/Embedding/SliceChart | [LocallyFlat/Smooth.lean](https://github.com/TauCetiProject/TauCeti/blob/3358033ba2fd35f321356dceaf2372a0fd6c0bfd/TauCeti/Geometry/Manifold/LocallyFlat/Smooth.lean), The Tau Ceti contributors |

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

The slice-chart proof retains the two open restrictions from Tau Ceti: one
forces slice points to belong to the immersion chart, and the other excludes
distant branches of the embedded range. It uses native immersion charts and
returns an OpenPartialHomeomorph with ContMDiffOn laws for both directions.
Its exact image equation uses the entire range of the given map. The source
may have corners; only the ambient model must be boundaryless. The general
engine needs a topologically inducing map and an immersion at the given point;
the smooth-embedding method is its corollary. No Tau embedding, slice or local
flatness definitions are imported. Continuous-linear-equivalence smoothness
and the Euclidean sphere's dimension instance were adapted to the pinned APIs.

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

The slice-chart source gate, 1789301170338217570-schoenflies-b3900a3e, passed
in the same Slurm allocation in 34.41 seconds, with 14 guards and five
signature/axiom pairs. The final imported gate,
1789301267798740740-schoenflies-d05544f3, passed in 81.91 seconds, with 16
guards and five pairs. The new module freshly compiled with zero diagnostics;
artifact generation took 50.32 seconds with maximum RSS 1639036 KiB.
Both public methods and all three consumers have standard-only transitive
axioms and pass the stock declaration linters listed above. Consumers cover
an arbitrary smooth embedded two-sphere, the actual unit sphere inclusion,
and a model-with-corners inclusion. The leaf is registered in the flat root;
this is a fresh leaf and imported-source gate, not a full aggregate build.
Local slice charts do not establish a global tubular neighborhood or ambient
isotopy extension.

## Native local retraction, 2026-09-13

Topology/Embedding/Retraction consumes the accepted slice-chart theorem and
constructs an open neighborhood stable under projection onto the embedded
slice. The original source manifold is recovered through Mathlib's embedding
homeomorphism and its immersion criterion for smoothness. The resulting map
is smooth, its embedded image remains in the same neighborhood, and it fixes
every source point whose image lies in that neighborhood. Both source and
ambient models are boundaryless. No replacement smooth structure is introduced.

This is original native glue. Inspected proof patterns include the coordinate
projection and immersion-lifting step in Tau Ceti's
[Boundary/Collar/Diffeomorph.lean](https://github.com/TauCetiProject/TauCeti/blob/3358033ba2fd35f321356dceaf2372a0fd6c0bfd/TauCeti/Geometry/Manifold/Boundary/Collar/Diffeomorph.lean#L105)
and the native embedding inverse in
[LocallyFlat/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/3358033ba2fd35f321356dceaf2372a0fd6c0bfd/TauCeti/Geometry/Manifold/LocallyFlat/Basic.lean#L754).
Those sources belong to The Tau Ceti contributors under the same Apache 2.0
license. Their supplied collar structures are not imported or assumed here.

Source gate 1789302206549346026-schoenflies-1067041b passed in 3.43 seconds
with 16 guards and three signature/axiom pairs. Imported gate
1789302368061612316-schoenflies-b705f016 passed in 73.77 seconds with 18
guards and three pairs. The new module freshly compiled without diagnostics;
the public method and arbitrary-embedded-S2 and unit-sphere consumers pass
the stock declaration linters and standard-only transitive axiom checks.
The leaf is registered in the flat root. These checks do not establish a
full aggregate build, a global retraction, or a joint-time tubular neighborhood.

Distinct critical values, global positioning of an embedded sphere, smooth
relative disk absorption and full Schoenflies remain open.
