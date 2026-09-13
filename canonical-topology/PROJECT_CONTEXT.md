# Poincare local-homology checkpoint

This directory is a separate portable `PoincareLean` project prepared for
additive publication within the shared DifferentialGeometry Git repository. Its Lean
library is `Poincare`; its sources retain the original mathematical namespaces.

The source baseline is the recovered Chapter 35 commit
`b45bfa009368c8f5f531e10f4f5280e90079d6ad`, supplemented by recovered working-tree
proofs with separately recorded provenance. This checkpoint includes 135 modules
and 144 curated tracked added public exports. The latest 54-line leaf proves
bijectivity of the actual relative-cohomology connecting map when both adjacent
ambient groups vanish, and its positive-degree contractible-space specialization.
For a contractible ambient space and a totally disconnected subspace, actual
relative integral cohomology vanishes in every degree greater than one.

Final request `1789340590892191690-topology_checkpoint-29ccbfc4` passed in
Slurm 13846673 in 165.16 seconds, with 536 guards and 252 signature/axiom pairs.
All 247 earlier pairs are byte-identical; the five new public/consumer pairs
match source gated19badad and original imported gate77c322e0 exactly.
The new leaf and root freshly compiled in 1:09.79, maximum RSS1825220KiB,
with zero diagnostics. All 134 previously published leaves remain byte-identical.
A consumer proves that H1 of the real line relative to {0,1} is nonzero while
all higher groups vanish; the empty-subspace case also passes. Stock declaration
linters and standard-only transitive axioms pass. No dependency or deferred
input changed.

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
