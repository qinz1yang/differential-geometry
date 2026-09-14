# Poincare local-homology checkpoint

This directory is a separate portable `PoincareLean` project prepared for
additive publication within the shared DifferentialGeometry Git repository. Its Lean
library is `Poincare`; its sources retain the original mathematical namespaces.

The source baseline is the recovered Chapter 35 commit
`b45bfa009368c8f5f531e10f4f5280e90079d6ad`, supplemented by recovered working-tree
proofs with separately recorded provenance. This checkpoint includes 144 modules
and 177 curated tracked added public exports. From a tangent orientation field
whose coordinates are locally constant in each fixed chart, the new theorem
constructs a unique family of actual local integral homology classes with all
chart/excision/translation equations and compact local realizations. Any model
class is permitted, including zero. With a model generator and a nonempty compact
connected manifold, the second theorem constructs the unique absolute integral
generator with the same chart equations and bijective point restrictions.
These are conditional class-production results. The native compatible tangent
orientation producer, outward normalization and general manifold duality remain open.

Source b6c3464d passed in 59.54s, with 217 guards and 32 type/axiom pairs.
Original imported d4ad29d5 passed in 123.12s, with 210 guards and 14 pairs.
Portable d9ef4819 passed in 209.63s, with 678 guards and 330 pairs. Both changed
leaves and the root freshly compiled in 1:39.96, RSS1981068KiB, zero diagnostics.
All322 preceding pairs are byte-identical and all142 other leaves unchanged.
All14 common source/original/portable types agree modulo only Set.univ,
Module.finrank and Set.MapsTo qualification and whitespace; axioms are exact.
Strict source and stock declaration linters and standard-only transitive axioms
pass. Consumers check actual model coordinates, a nonzero negative rank-zero
global generator, reversal of the orientation field and the zero model class
with actual compact local realization. Pins and deferred inputs remain unchanged.

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
