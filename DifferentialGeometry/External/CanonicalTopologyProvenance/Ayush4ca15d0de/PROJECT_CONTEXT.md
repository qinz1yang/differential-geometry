# Poincare local-homology checkpoint

This directory is a separate portable `PoincareLean` project prepared for
additive publication within the shared DifferentialGeometry Git repository.
Its sources retain the original mathematical objects and namespaces.

The recovered Chapter 35 baseline is commit
`b45bfa009368c8f5f531e10f4f5280e90079d6ad`, supplemented by recovered working-tree
proofs with separately recorded provenance. This checkpoint includes 146 modules
and 185 curated tracked added public exports.

Actual top local integral homology now has a generator in every finite-dimensional
real normed space, including ranks zero and one. On a compact simply connected
Hausdorff C1 manifold without boundary, the actual top-degree absolute-to-point
restriction is bijective. Every prescribed local class therefore has a unique
absolute preimage. These statements construct the model generator and tangent
orientation internally and require no supplied orientation field or locality.

Source 67ea80b6 passed in 52.58s with 222 guards and seven pairs. Original
imported 303a2b3a passed in 137.86s with 984 guards and 34 pairs. Portable efa87b9b
passed in Slurm 13879784 in 217.19s with 1272 guards and 350 pairs. Nine affected
leaves and the portable root freshly compiled in 2:01.42, maximum RSS 2844500KiB,
with zero diagnostics. All 344 previous portable and 28 previous original
pairs are byte-identical; all 144 other source leaves are unchanged. All six
shared new source/original/portable pairs agree modulo qualification and
whitespace, with exact standard-only axioms. Strict source and stock declaration
linters pass. Rank-zero and real-line consumers force actual nonzero generators;
the rank-zero unique absolute-preimage consumer also passes.

The preceding orientation checkpoint remains available unchanged:

A simply connected finite-dimensional real C1 manifold now has an actual tangent
orientation field prescribed at any supplied point, with locally constant
orientation coordinates in every fixed native chart. The proof constructs the
orientation covering from actual tangent transitions and lifts the identity.
It requires no compactness, Hausdorffness, positive rank, supplied global frame
or orientation field. The model and manifold universes are independent.

Three external consumers preserve a negative rank-zero orientation and feed the
produced field into the existing unique local integral-class family and global
fundamental-class engines, retaining all actual chart, excision and translation
equations. Those general oriented engines retain an explicit model local class;
their generator conclusions accept a model generator and a nonempty compact
connected manifold. The new simply connected corollaries construct these inputs. Existing
local-frame and locality-based public interfaces remain unchanged.

Source 0413d3cf passed in 75.81s with 249 guards and 46 signature/axiom pairs.
Original imported 926c3536 passed in 192.45s with 966 guards and 28 pairs.
Portable 6e8cae83 passed in Slurm 13864417 in 278.82s with 1254 guards and 344 pairs.
Four affected leaves and the portable root freshly compiled in 2:39.99,
maximum RSS 1985332KiB, with zero diagnostics. All 339 previous pairs are
byte-identical and all 143 other preceding leaves unchanged. All 28 common
source/original/portable types agree modulo only qualification and whitespace;
axiom readbacks are exact. Strict source and stock declaration linters and
standard-only transitive axioms pass.

Outward sphere normalization, general manifold duality and the missing frozen
canonical-topology contract remain open. The historical results below retain
their established public statements and proof bodies except for sharing the
general orientation-map composition law in Poincare.LinearAlgebra.Orientation.

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
T1 two-point duality case does not close general manifold duality or the full
canonical theorem suite.

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
retain their public statements and proof bodies. Coherent generators now follow
from tangent locality and a supplied model generator.
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
