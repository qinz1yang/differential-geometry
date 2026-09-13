# Poincare local-homology checkpoint

This directory is a separate portable `PoincareLean` project prepared for
additive publication within the shared DifferentialGeometry Git repository. Its Lean
library is `Poincare`; its sources retain the original mathematical namespaces.

The source baseline is the recovered Chapter 35 commit
`b45bfa009368c8f5f531e10f4f5280e90079d6ad`, supplemented by recovered working-tree
proofs with separately recorded provenance. This checkpoint includes 132 modules
and 134 tracked added public exports. The latest coherent 301-line leaf proves
that any simply connected T1 space relative to two distinct points has a unique
relative H₁ class normalized by connecting image [y] − [x], and that cap with
this class is a bijection from actual relative H¹ to actual absolute H₀.

Fifteen existing recovered working-tree sources, totaling 1,207 lines, supply
first-homology and first-cohomology vanishing through actual path/cochain cones,
triangle fillings and disk contractions. These sources were absent from the
recovered Git baseline and are included unchanged. All 116 earlier published
leaves are unchanged. No Hurewicz axiom is used for this result.

Final request `1789334015172615434-topology_checkpoint-405abd43` passed in
Slurm 13821107 in 439.35 seconds, with 408 guards and 234 signature/axiom pairs.
All 231 earlier pairs are byte-identical. The sixteen added leaves and root
freshly compiled in 5:47.42 with maximum RSS 1890444 KiB and zero diagnostics.
Source fe1516cb and original imported 32ae5cfd pass 104/14 and 106/3 guards/pairs.
All three new portable readbacks match both earlier gates. Nonzero real-line
pair consumers check positive and negative cap values and the negated-class
bijection. Stock linters and standard-only axioms pass. This concrete case does
not close general duality, the native orientation producer or the full suite.

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
