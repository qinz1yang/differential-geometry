# Poincare local-homology checkpoint

This directory is a separate portable `PoincareLean` project prepared for
additive publication within the shared DifferentialGeometry Git repository. Its Lean
library is `Poincare`; its sources retain the original mathematical namespaces.

The source baseline is the recovered Chapter 35 commit
`b45bfa009368c8f5f531e10f4f5280e90079d6ad`. This checkpoint includes 108 modules
and 96 added public exports. The latest 381-line CapHomology leaf descends the
actual cap product to both cohomology and homology. It exposes the actual cycle
map, representative law, map naturality, constant-one H^0 unit, unit cap action
in every degree and unit naturality. All 107 earlier leaves are unchanged.

Final request `1789315948183120646-topology_checkpoint-62c7e035` passed in
Slurm 13821107 in 152.18 seconds, with 254 guards and 171 signature/axiom pairs.
All 160 earlier pairs are byte-identical. New CapHomology and the root freshly
compiled in 1:15.15 with maximum RSS 1814324 KiB and zero diagnostics. Source
57c362c8 and original imported 204a2b9d pass with 40/24 and 42/11 guards/pairs;
the new portable pairs match the original. Actual nonzero H0/unit classes,
negative-unit action, doubling-map naturality and degree-one representative
consumers pass. Stock linters and standard-only axioms pass. Relative cap
products, duality isomorphisms and the full oriented-manifold suite remain open.

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
