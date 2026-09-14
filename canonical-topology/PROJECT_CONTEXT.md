# Poincare local-homology checkpoint

This directory is a separate portable `PoincareLean` project prepared for
additive publication within the shared DifferentialGeometry Git repository.
Its sources retain the original mathematical objects and namespaces.

The recovered Chapter 35 baseline is commit
`b45bfa009368c8f5f531e10f4f5280e90079d6ad`, supplemented by recovered working-tree
proofs with separately recorded provenance. This checkpoint includes 145 modules
and 180 curated tracked added public exports.

Actual continuous local tangent frames representing a supplied orientation field
now imply local constancy of its coordinates in each fixed tangent chart. This
uses the native Mathlib local-frame, orientation and tangent trivialization APIs.
The frame theorem allows independent model, manifold and index universes and
includes rank zero. Two corollaries feed this locality into the existing unique
local integral-homology family and global fundamental-class constructions.
They retain all actual chart, excision and translation equations. The local
model class may be zero; a global generator requires a model generator and a
nonempty compact connected manifold. The more general locality-based engines
retain their public statements and proofs.

Source 8ce18e56 passed in 59.72s with 223 guards and 41 signature/axiom pairs.
Original imported 473d714f passed in 173.57s with 217 guards and 23 pairs.
Portable e4a3e8f8 passed in Slurm 13864417 in 262.34s with 708 guards and 339 pairs.
All three affected leaves and the portable root freshly compiled in 2:21.07,
maximum RSS 1985840KiB, with zero diagnostics. All 330 previous readback pairs
are byte-identical and all 142 other leaves unchanged. All 23 common source,
original and portable types agree modulo only qualification and whitespace;
axiom readbacks are exact. Strict source and stock declaration linters and
standard-only transitive axioms pass. Consumers include actual Fin0 frames,
opposite-orientation exclusion, exact local class equations and a nonzero global
generator; previous negative rank-zero, zero-model and reversal probes remain.

These are conditional results from supplied compatible local frames. The native
coherent orientation producer, outward sphere normalization, general manifold
duality and the missing frozen canonical-topology contract remain open.

The preceding all-degree sphere, Euclidean point and bounded star-convex cap
bijections retain their exact public statements and proof bodies. Their classes,
normalizations and degree-zero consumers are unchanged.

The preceding cohomology cover shift, its actual forward/inverse equations,
and relative-to-absolute comparison in every positive degree are unchanged.

The preceding unique real-line local class, its normalization and actual cap
bijection, and the generic pair-map cap transport remain unchanged.

The preceding actual relative homology/cohomology comparison theorem and its
sphere-to-puncture consumer retain their exact statements and bodies.

The preceding empty-pair cohomology equivalence and its actual forward-map
equation retain their exact statements and bodies.

The preceding degree-zero relative and empty-space cohomology results retain
their exact statements and bodies, including the nonempty-subspace assumption
for relative H0 vanishing and its nonzero empty-subspace consumer.

The earlier relative cohomology connecting-map bijections and higher-degree
vanishing retain their exact statements and bodies.

The previously published positive-degree cohomology vanishing, including its
nonzero H0 consumer, retains its exact statements and bodies.

The actual cochain comparison, naturality, homotopy invariance and excision
results retain their exact public statements and bodies.

The earlier uniquely normalized two-point cap-duality theorem and its fifteen
unchanged recovered working-tree prerequisites retain their exact statements
and bodies. Those prerequisites were absent from the recovered Git baseline;
their provenance remains separately recorded. The concrete simply connected
T1 two-point duality case does not close general manifold duality, the native
orientation producer or the full canonical theorem suite.

The preceding signed-chart extension retains its exact public statements.

The signed-chart theorem identifies the change between the actual normalized
local top-homology maps of two manifold charts with the sign of their actual
transition derivative determinant. C¹ regularity and finite-dimensional real
normed models suffice, including rank zero. The earlier oriented-map theorem
retains its exact statement and now follows from this general sign formula;
the compact oriented-neighborhood class theorem is unchanged.

The actual absolute-to-relative-empty map is now a linear equivalence in
every degree and topological space, with its defining map equation exposed.
Nonzero degree-zero and naturality consumers pass.

The new results construct a compact neighborhood on which a class's
restriction vanishes when its actual point restriction is zero. Compact
relative homology on any Hausdorff manifold charted over a finite-dimensional
real normed model vanishes above the model dimension. In the model dimension
or above, point restrictions determine compact classes, and every nonzero
compact class has a nonzero point restriction. Rank zero, nonclosed supports
for local vanishing, and noncompact ambient manifolds are included.
No orientation or smoothness is required by these results.

The earlier actual Mayer–Vietoris lifts, conditional uniqueness, compact
carrier and neighborhood-extension results, and oriented compact chart classes
retain their public statements and proof bodies. Producing coherent generators from a tangent orientation remains open.
[provenance/SNAPSHOT.json](provenance/SNAPSHOT.json) records exact source and
configuration identity and preserves the earlier validation records. It is not
the full recovered Chapter 35 project.

Preserve Lean `leanprover/lean4:v4.33.1`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and DifferentialGeometry `v0.1.2`
at `1b535dd102b94cc42b107cca27059687888f08b3`. Use DifferentialGeometry only
as a pinned upstream dependency; no included Lean module currently imports it.

The mathematical work belongs to the canonical-topology workstream described
in the enclosing Schoenflies controller's
[two-project prompt](../../plan/della_two_projects_prompt.md),
[topology brief](../../plan/CANONICAL_TOPOLOGY_SPINOFF_BRIEF.md), and
[active plan](../../plan/plan_smooth_schoenflies.md). Those controller records
are external to this portable package. The package README records its limited
delivered scope and checkpoint status independently.

The frozen topology handoff is still missing. Do not reconstruct its public
contract from this foundations checkpoint. Neither the full canonical topology
suite nor the combined Schoenflies/topology goal is complete.

The older project context and agent instructions are preserved under
`provenance/RECOVERED_*.md` as historical source records. Their old machine paths,
branch destinations and release claims are not current operating instructions.
