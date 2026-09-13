# Poincare local-homology checkpoint

This directory is a separate portable `PoincareLean` project prepared for
additive publication within the shared DifferentialGeometry Git repository. Its Lean
library is `Poincare`; its sources retain the original mathematical namespaces.

The source baseline is the recovered Chapter 35 commit
`b45bfa009368c8f5f531e10f4f5280e90079d6ad`. This checkpoint includes 114 modules
and 124 added public exports. The latest coherent 226-line leaf constructs
cap of actual relative cochains and relative chains with absolute-chain output,
with the original projection law, compatibility with the preceding relative
cap product, actual pair-map naturality, signed boundary and cycle laws.
It uses the original kernel/cokernel, cap naturality and Mathlib quotient lift.
All 113 earlier leaves are unchanged.

Final request `1789328051059665070-topology_checkpoint-3eafcb3e` passed in
Slurm 13821107 in 160.12 seconds, with 297 guards and 214 signature/axiom pairs.
All 205 earlier pairs are byte-identical. The new leaf and root freshly compiled
in 1:14.06 with maximum RSS 1813376 KiB and zero diagnostics. Source 98ee7c44
and original imported c9515b2c pass 58/14 and 60/10 guards/pairs. All six new
public and three new consumer pairs match the original; the unchanged
cochain producer is reused from the earlier harness. Nonzero relative vertex,
negative-cochain action, odd-degree boundary sign and actual doubling-map
consumers pass. Stock linters and standard-only axioms pass. Relative-cohomology
descent of this pairing, general duality, the native orientation producer
and the full oriented-manifold suite remain open.

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
