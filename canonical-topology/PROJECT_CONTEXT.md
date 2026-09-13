# Poincare local-homology checkpoint

This directory is a separate portable `PoincareLean` project prepared for
additive publication within the shared DifferentialGeometry Git repository. Its Lean
library is `Poincare`; its sources retain the original mathematical namespaces.

The source baseline is the recovered Chapter 35 commit
`b45bfa009368c8f5f531e10f4f5280e90079d6ad`, supplemented by recovered working-tree
proofs with separately recorded provenance. This checkpoint includes 133 modules
and 139 tracked added public exports. The latest coherent 95-line leaf constructs
actual chain homotopies between the original integral cochain pullback maps.
Homotopic continuous maps induce equal integral cohomology maps in every degree;
native homotopy equivalences induce bijective pullbacks. The natural comparison
with dual singular chains is now shared with the existing excision proof,
removing 27 duplicated lines while preserving both public excision signatures.

Final request `1789336555099403798-topology_checkpoint-5d3553b1` passed in
Slurm 13821107 in 186.49 seconds, with 516 guards and 242 signature/axiom pairs.
All 234 earlier pairs are byte-identical; eight new pairs match both the combined
source gate db318cb3 and original imported gate efb76a39 exactly. The two changed
leaves and root freshly compiled in 1:34.82, with maximum RSS 1825276 KiB and
zero diagnostics. All 131 other published leaves remain byte-identical.
Cylinder-collapse, nonzero real H0 unit and empty-space consumers pass, with
stock linters and standard-only axioms. No dependency or deferred input changed.

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
